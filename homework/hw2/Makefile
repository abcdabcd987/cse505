.PHONY: coq clean

COQC=coqc -q -R frap Frap

coq:
	$(COQC) HW2Sig
	$(COQC) HW2
	$(COQC) HW2Check

clean:
	rm -f *.vo *.glob
