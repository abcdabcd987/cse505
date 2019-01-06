.PHONY: proof
proof: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: clean
clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm Makefile.coq
	find . -name '.*.aux' -delete

.PHONY: cleaner
cleaner: clean
	rm -f _CoqProject
