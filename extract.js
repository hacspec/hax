const STOP = 'STOP';
let walk = (o, f) =>
    f(o) ||
        (typeof o === 'object'
         && Object.keys(o || {}).map(k => walk(o[k], f)).filter(x => x)[0]);

let expects = {
    array: [e => e instanceof Array && e],
    expr: [({e, span, typ}) => span && typ && e, 'array'],
    app: ['expr', ([tag, data]) => tag == 'App' && data.f && data.args && data],
    global_var: ['array', ([tag, data]) => tag == 'GlobalVar' && data],
    concrete_var: ['global_var', ([tag, data]) => tag == '`Concrete' && data?.def_id],
    concrete_var_last: ['concrete_var', ({krate, path}) => path?.slice(-1)?.[0]?.data[1][1]],
    mark: ['concrete_var_last', last => last == 'mark'],
    expr_mark: ['app', ({f, args}) => expects.mark(f?.e) && args?.[1]],
    skip_typ: ['concrete_var_last', last => last == 'skip'],
    expr_skip_typ: ['app', ({f, args}) => {
        if (expects.skip_typ(f?.e)) {
            let [_native_list_tag, field, inner] = args;
            field = field.e[1].e.e[1].args[1].e[1][1][1];
            return {field, inner};
        }
        return false;
    }],
};


for (let k in expects) {
    expects[k] = expects[k].map(f => typeof f == 'string' ? (o => expects[f](o)) : f);
}
let DEBUG = false;
let inspect = s => require('util').inspect(s, false, null, true);
for (let k in expects) {
    let filters = expects[k];
    expects[k] = o => {
        // let DEBUG = k == 'mark';
        DEBUG && console.log('DEBUG['+k+'](', o, ')');
        let current = o;
        for (let i in filters) {
            let f = filters[i];
            if(!current) {
                return current;
            }
            let prev = current;
            current = f(current);
            DEBUG && console.log('DEBUG['+k+']['+i+'](',inspect(prev),')\n -> ', inspect(current));
        }
        return current;
    };
}

let isVariantName = s => typeof s == 'string' && s.match(/^[`]?(Native:)?([A-Z]+[a-z]*)+$/) !== null;
const DENYKEYS = ['span', 'region', 'witness'];
const WILDCARD = Symbol();

const KINDS = {
    RECORD: 'record',
    CONSTRUCTOR: 'cons',
    LIST: 'list',
    TUPLE: 'tuple',
    RAW_OCAML: 'raw_ocaml',
    WILDCARD: 'wildcard',
    PAT_VAR: 'pat_var',
};

function parse(o) {
    function aux(o, tab = '') {
        try {
            return aux_(o, tab);
        } catch(e) {
            if (typeof e == 'object' && 'N' in e && 'name' in e) {
                if (e?.N > 0)
                    throw {...e, N: e.N - 1};
                return [KINDS.PAT_VAR, e.name];
            } else
                throw e;
        }
    }
    function aux_(o, tab = '') {
        let skip = expects.expr_skip_typ(o);
        if (skip) {
            o = skip.inner;
            o[skip.field] = WILDCARD;
        }
        if(o == WILDCARD){
            return [KINDS.WILDCARD];
        }
        let h = o => aux(o, '   ' + tab);
        let as_json = o => {
            if(o == WILDCARD){
                return [KINDS.WILDCARD];
            }
            let is_pat = (o||'').toString().match(/^_pat_(?<N>\d+)_(?<name>[a-z_\d]+)$/);
            if(is_pat?.groups) {
                let groups = is_pat.groups;
                throw {...groups, N: +groups.N};
            }
            return [KINDS.RAW_OCAML, JSON.stringify(o)];
        };
        if (o instanceof Array && isVariantName(o?.[0])) {
            let [tag, ...args] = o;
            let [native_kwd, native_kind] = tag.split(':');
            if (native_kwd == 'Native' && native_kind){
                return (({
                    String: as_json,
                    Char: as_json,
                    Int: as_json,
                    Bool: as_json,
                    Tuple: (...args) => [KINDS.TUPLE, ...args.map(h)],
                    List: (...args) => [KINDS.LIST, ...args.map(h)],
                })[native_kind] || (_ => {throw native_kind;}))(...args);
            } else {
                if (args.length == 1 && args?.[0] instanceof Array && typeof args?.[0]?.[0] != 'string'){
                    args = args[0];
                }
                return [KINDS.CONSTRUCTOR, tag, ...args.map(h)];
            }
        } else if (typeof o == 'object') {
            return [
                KINDS.RECORD,
                ...Object.entries(o).map(([k, v]) =>
                    [k, DENYKEYS.includes(k) ? [KINDS.WILDCARD] : h(v)]
                )
            ];
        }
        return as_json(o);
    };
    return aux(o);
}

function merge(a, b) {
    // console.log(a);
    let [a_kind, ...a_args] = a;
    let [b_kind, ...b_args] = b;
    let wild = [KINDS.WILDCARD];
    if (a_kind == KINDS.PAT_VAR) {
        return a;
    }
    if (a_kind !== b_kind || a_args.length != b_args.length) {
        return wild;
    }
    let default_merger = (a_args, b_args) =>
        a_args.map((a_arg, i) => merge(a_arg, b_args[i]));
    let merger = ({
        [KINDS.RECORD]: (a_fields, b_fields) => a_fields.map(([af, av], i) => {
              let [bf, bv] = b_fields[i];
              if (bf !== af) return WILDCARD;
              return [af, merge(av, bv)];
           }),
        [KINDS.CONSTRUCTOR]: ([a_tag, ...a_args], [b_tag, ...b_args]) => {
            if (a_tag !== b_tag) return WILDCARD;
            return [a_tag, ...default_merger(a_args, b_args)];
        },
        [KINDS.LIST]: default_merger,
        [KINDS.TUPLE]: default_merger,
        [KINDS.RAW_OCAML]: ([a], [b]) => a === b ? [a] : WILDCARD,
        [KINDS.WILDCARD]: (_a, _b) => [],
        [KINDS.PAT_VAR]: ([name], _) => [name],
    })[a_kind] || (_ => {throw {unknown_kind: kind};});
    let args = merger(a_args, b_args);
    return args === WILDCARD ? wild : [a_kind, ...args];
}
function merge_n(l) {
    return l.reduce(merge);
}

function rewrite_concrete_nodes(o) {
    let id = 0;
    let guards = [];
    walk(o, x => {
        if (x?.[0] == KINDS.CONSTRUCTOR && x?.[1] == '`Concrete') {
            let pat_var = `def_id_${id++}`;
            let concrete_ident = x[2];
            let [_, def_id] = concrete_ident.slice(1).find(([k, v]) => k == 'def_id');
            guards.push(`Concrete_ident.eq_def_id ${print(def_id)} ${pat_var}`);
            x[2] = [KINDS.PAT_VAR, pat_var];
        }
    });
    return guards;
}

function print(a) {
    let [kind, ...args] = a;
    let printer = ({
        [KINDS.RECORD]: (...fields) => `{${fields.map(([k, v]) => `${k} = ${print(v)}`).join(';')}}`,
        [KINDS.CONSTRUCTOR]: (tag, ...args) => {
            if (args.length == 0)
                return tag;
            let first = args[0];
            if (args.length == 1 && first[0] == KINDS.RECORD)
                return `${tag} ${print(first)}`;
            return `${tag}(${args.map(print).join(',')})`;
        },
        [KINDS.LIST]: (...args) => `[${args.map(print).join(';')}]`,
        [KINDS.TUPLE]: (...args) => `(${args.map(print).join(',')})`,
        [KINDS.RAW_OCAML]: (str) => str,
        [KINDS.WILDCARD]: () => "_",
        [KINDS.PAT_VAR]: (name) => name,
    })[kind] || (_ => {throw {unknown_kind: kind};});
    return printer(...args);
}

function run(stdin) {
    let o = JSON.parse(stdin);
    let items = o[0].items;
    let results = [];
    let r = walk(items, x => {
        let r = expects.expr_mark(x);
        r && results.push(r);
    });
    console.log(inspect({items}));
    let merged = merge_n(results.map(parse));
    let when_clause = rewrite_concrete_nodes(merged).join(' && ');
    // console.log(inspect(merged));
    console.log(print(merged) + (when_clause ? ' when ' + when_clause : ''));
}

async function read(stream) {
    const chunks = [];
    for await (const chunk of stream) chunks.push(chunk); 
    return Buffer.concat(chunks).toString('utf8');
}

async function main(){
    try {
        run(await read(process.stdin));
    } catch (e) {
        console.error(e);
        throw e;
    }
}
main();
