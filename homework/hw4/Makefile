OCB_FLAGS = -use-ocamlfind -package num -libs unix -I extract/ -I ml/ -r
OCB_FLAGS := -use-menhir -yaccflags --explain $(OCB_FLAGS)

Imp.native: proof
	ocamlbuild $(OCB_FLAGS) ml/Imp.native

Imp.d.byte: proof
	ocamlbuild $(OCB_FLAGS) ml/Imp.d.byte

.PHONY: proof
proof: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: test
test: Imp.native
	./test/regression/test.sh
	./test/bounded/test.sh -2 2

.PHONY: clean-coq
clean-coq: Makefile.coq
	rm -f extract/*
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
	find . -name '.*.aux' -delete

.PHONY: clean-ml
clean-ml:
	ocamlbuild -clean

.PHONY: clean
clean: clean-coq clean-ml

.PHONY: clean-test
clean-test:
	rm -f test/regression/*.imp.input
	rm -f test/regression/*.imp.result
	rm -f test/bounded/TESTIMP.*

.PHONY: clean-all
clean-all: clean clean-test
	rm -f _CoqProject
