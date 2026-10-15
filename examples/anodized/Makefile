# Two scenarios over the same annotations: F* gets `anodized`'s cfg flags
# through `RUSTFLAGS`, Lean through charon's `host.rustflags`.
.PHONY: default fstar lean clean

default: fstar lean

fstar:
	cargo hax extract anodized-fstar
	make -C proofs/anodized/fstar/extraction

lean:
	cargo hax extract anodized-lean
	(cd proofs/anodized/lean && \
		elan default $$(cat lean-toolchain) && \
		lake exe cache get && \
		lake build)

clean:
	rm -f proofs/anodized/fstar/extraction/.depend
	rm -f proofs/anodized/fstar/extraction/*.fst
	-rm -rf proofs/anodized/lean/AnodizedLean/Extraction
	-rm -rf proofs/anodized/lean/.lake
