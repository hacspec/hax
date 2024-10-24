check: ./proofs/proverif/extraction/lib.pvl
	timeout 30 proverif -lib ./proofs/proverif/extraction/lib.pvl ./proofs/proverif/extraction/analysis.pv

proofs/proverif/extraction/lib.pvl:
	cargo hax into pro-verif

clean:
	rm -f proofs/proverif/extraction/lib.pvl
