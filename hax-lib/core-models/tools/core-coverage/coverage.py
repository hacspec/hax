#!/usr/bin/env python3
"""Generate a per-module coverage report of real `core`/`alloc` by our models.

Numerator: rustdoc JSON of our model crates (`cargo +nightly rustdoc
--output-format json`). Denominator: rustdoc JSON of the real std crates
(the `rust-docs-json` rustup component). Both must come from the *same*
nightly so their `format_version` agrees.

Why rustdoc JSON (not charon): the question "how much of core do we model" is a
source-level, tool-agnostic one. rustdoc JSON is the canonical public-API
description of the real std crates and of ours, so the comparison is symmetric.

What is counted (the "API surface"), attributed to its TOP-LEVEL module:
  - module-level items: fn / struct / enum / union / trait / constant /
    type_alias / macro / proc_macro / trait_alias
  - inherent methods (impl with no trait): keyed `Type::method`
  - trait-definition methods: keyed `Trait::method`
Derived trait-impl methods (`impl Clone for T`, Debug, From, …), auto/blanket
impls are NOT counted — they are boilerplate, not API to model.

Matching is by (top-level module, leaf key) and is crate-root agnostic, so the
flat model layout lines up with real core's deep nesting
(`core::iter::traits::iterator::Iterator::next` ↔ `core_models::iter` → both
bucket `iter`, key `Iterator::next`).

Run via `tools/core-coverage/gen.sh`, which locates the JSONs for you.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path

API_KINDS = {"function", "struct", "enum", "union", "trait", "constant",
             "type_alias", "macro", "proc_macro", "trait_alias", "primitive"}
TYPE_KINDS = {"struct", "enum", "union", "primitive"}

# Pure re-export aggregators: they expose other modules' items, not their own,
# so walking them would double-count. Skipped entirely.
SKIP_MODULES = {"prelude"}

# Primitive type name -> the module its methods should count under.
PRIM_BUCKET = {
    **{t: "num" for t in ("u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize "
                          "bool").split()},
    "f16": "f16", "f32": "f32", "f64": "f64", "f128": "f128",
    "char": "char", "str": "str", "slice": "slice", "array": "array",
    "pointer": "ptr", "reference": "ptr",
}

# Model owners spelled differently from core: primitive stand-ins and companion traits.
MODEL_OWNER_ALIASES = {
    # primitive stand-ins
    "Slice": "slice",
    "Array": "array",
    # companion traits carrying trait default methods
    "ErrorDefaults": "Error",
}

# Modules that a pure-Rust verification model of core/alloc is not trying to
# provide (platform/runtime/compiler surface). Reported separately, not in the
# headline. Edit this to re-scope the report.
OUT_OF_SCOPE = {
    "core": {"intrinsics", "arch", "simd", "sync", "os", "ffi", "net", "time",
             "random", "async_iter", "future", "task", "autodiff", "contracts",
             "unsafe_binder", "pat", "bstr", "io", "panic", "alloc"},
    "alloc": {"sync", "task", "ffi", "bstr"},
}


def kind_of(item):
    return next(iter(item["inner"]))


def collect(doc) -> dict[str, set[str]]:
    """top-level-module -> set of API-item keys.

    Bucket attribution is **order-independent** (so a freshly-built rustdoc
    JSON, whose item ordering can vary between machines/builds, always yields
    the same report): we first gather, for every item, the complete set of
    top-level modules it is reachable under — distinguishing where it is
    *defined* (a direct module child) from where it is *re-exported* (reached
    via a `use`) — then assign each item to a single bucket with a
    deterministic rule.
    """
    index = doc["index"]

    def get(i):
        return index.get(str(i))

    home: dict[int, set[str]] = {}     # id -> modules that define it directly
    reexport: dict[int, set[str]] = {}  # id -> modules that re-export it
    item_by_id: dict[int, dict] = {}
    visited: set = set()                # (module_id, top) — explore every path

    def reach(c, top, via_use):
        k = kind_of(c)
        if k == "use":
            # Follow re-exports: real core's `iter`/`ops` expose their whole
            # public API via `pub use` from private submodules. (`use` items
            # carry no top-level `name`, so this must precede the name check.)
            tid = c["inner"]["use"].get("id")
            target = get(tid) if tid is not None else None
            if target is not None:
                reach(target, top, via_use=True)
            return
        name = c.get("name")
        if not name:
            return
        if k == "module":
            if name in SKIP_MODULES:        # pure re-export aggregators
                return
            walk(c["id"], top or name)
            return
        bucket = (PRIM_BUCKET.get(name) if k == "primitive"
                  else (top or "(root)"))
        if bucket is None:                  # primitive we don't map (tuple, fn…)
            return
        (reexport if via_use else home).setdefault(c["id"], set()).add(bucket)
        item_by_id[c["id"]] = c

    def walk(mod_id, top):
        if (mod_id, top) in visited:        # same module under a new top is OK;
            return                          # the (id, top) guard still bounds it
        visited.add((mod_id, top))
        m = get(mod_id)
        if not m or "module" not in m["inner"]:
            return
        for cid in m["inner"]["module"]["items"]:
            c = get(cid)
            if c:
                reach(c, top, via_use=False)

    walk(doc["root"], None)

    # Assign each item to one bucket: prefer where it is defined; fall back to
    # the re-export site (real core's iter/ops items are only reachable that way
    # because their defining submodule is private and stripped). `min` makes the
    # tie-break deterministic. `home` wins so a root/cross re-export can't steal
    # an item from its real module.
    out: dict[str, set[str]] = {}

    def add(bucket, key):
        out.setdefault(bucket, set()).add(key)

    def type_methods(type_item, type_name, bucket):
        inner = type_item["inner"][kind_of(type_item)]
        for iid in inner.get("impls", []):
            impl = get(iid)
            if not impl:
                continue
            imp = impl["inner"]["impl"]
            if (imp.get("trait") is not None or imp.get("is_synthetic")
                    or imp.get("blanket_impl")):
                continue  # only inherent impls
            for mid in imp.get("items", []):
                m = get(mid)
                if m and m.get("name"):
                    add(bucket, f"{type_name}::{m['name']}")

    for iid, c in item_by_id.items():
        bucket = min(home.get(iid) or reexport[iid])
        k, name = kind_of(c), c["name"]
        if k == "primitive":
            type_methods(c, name, bucket)
        else:
            add(bucket, name)
            if k in TYPE_KINDS:
                type_methods(c, name, bucket)
            elif k == "trait":
                for mid in c["inner"]["trait"].get("items", []):
                    m = get(mid)
                    if m and m.get("name"):
                        add(bucket, f"{name}::{m['name']}")
    return out


def apply_model_aliases(mods: dict[str, set[str]]) -> dict[str, set[str]]:
    """Add, for every aliased model key, the key real core uses for it.

    Additive: the original key stays, so an alias can never remove coverage.
    """
    out = {}
    for mod, keys in mods.items():
        aliased = set(keys)
        for key in keys:
            owner, _, method = key.partition("::")
            alias = MODEL_OWNER_ALIASES.get(owner)
            if alias is None:
                continue
            if method:
                aliased.add(f"{alias}::{method}")
            else:
                aliased.add(alias)
        out[mod] = aliased
    return out


def crate_report(den_doc, num_doc, out_of_scope: set[str]) -> dict:
    den, num = collect(den_doc), apply_model_aliases(collect(num_doc))
    mods = []
    for mod in sorted(den):
        covered = sorted(den[mod] & num.get(mod, set()))
        mods.append({
            "module": mod,
            "covered": len(covered),
            "total": len(den[mod]),
            "in_scope": mod not in out_of_scope,
            "covered_items": covered,
            "missing_items": sorted(den[mod] - num.get(mod, set())),
        })
    return {"format_version": den_doc.get("format_version"), "modules": mods}


def _subtotal(rows):
    c = sum(r["covered"] for r in rows)
    t = sum(r["total"] for r in rows)
    modeled = sum(1 for r in rows if r["covered"])
    return c, t, modeled


def md_section(label: str, rep: dict) -> str:
    in_scope = [r for r in rep["modules"] if r["in_scope"]]
    out_scope = [r for r in rep["modules"] if not r["in_scope"]]
    c, t, modeled = _subtotal(in_scope)
    L = [f"## `{label}`", ""]
    L.append(f"**Targeted coverage: {c}/{t} items ({100*c/t:.0f}%) "
             f"across {len(in_scope)} modules — {modeled} have at least a "
             f"partial model.**")
    L += ["", "| module | covered | total | coverage |",
          "|---|--:|--:|---|"]
    for r in sorted(in_scope, key=lambda r: r["module"]):
        pct = 100 * r["covered"] / r["total"] if r["total"] else 0
        L.append(f"| `{r['module']}` | {r['covered']} | {r['total']} | "
                 f"{pct:.0f}% |")
    L.append(f"| **subtotal** | **{c}** | **{t}** | **{100*c/t:.0f}%** |")
    if out_scope:
        oc, ot, _ = _subtotal(out_scope)
        names = ", ".join(f"`{r['module']}`" for r in sorted(out_scope, key=lambda r: r["module"]))
        L += ["", "<details><summary>Non-targeted modules: "
              f"{len(out_scope)} modules, {oc}/{ot} items</summary>",
              "", names, "</details>"]
    return "\n".join(L) + "\n"


def render_markdown(sections: list[tuple[str, dict]], toolchain: str) -> str:
    head = [
        "# core / alloc model coverage",
        "",
        "Auto-generated by `tools/core-coverage/gen.sh` — **do not edit by "
        "hand**. Regenerate with `make coverage`.",
        "",
        f"Numerator: rustdoc JSON of the model crates / Denominator: rustdoc "
        f"JSON of the real `core` and `alloc` (`{toolchain}`).",
        "",
        "Some platform and runtime modules are not targeted and taken out of "
        "the count. See `tools/core-coverage/README.md` for what is counted "
        "and how modules are scoped.",
        "",
    ]
    return "\n".join(head) + "\n" + "\n".join(md_section(l, r) for l, r in sections)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--core-den", required=True)
    ap.add_argument("--core-model", required=True)
    ap.add_argument("--alloc-den", required=True)
    ap.add_argument("--alloc-model", required=True)
    ap.add_argument("--toolchain", default="nightly")
    ap.add_argument("--markdown", type=Path, required=True)
    ap.add_argument("--json", type=Path, required=True)
    args = ap.parse_args()

    def load(p):
        return json.loads(Path(p).read_text())

    core = crate_report(load(args.core_den), load(args.core_model),
                        OUT_OF_SCOPE["core"])
    alloc = crate_report(load(args.alloc_den), load(args.alloc_model),
                         OUT_OF_SCOPE["alloc"])

    args.markdown.write_text(render_markdown([("core", core), ("alloc", alloc)],
                                             args.toolchain))
    args.json.write_text(json.dumps({"core": core, "alloc": alloc}, indent=1) + "\n")
    print(f"wrote {args.markdown} and {args.json}")


if __name__ == "__main__":
    main()
