.PHONY: coq clean

COQC=coqc -q -R ./frap Frap

coq:
	$(COQC) StructTactics
	$(COQC) ASCIIRegex

clean:
	rm -f *.vo *.glob
