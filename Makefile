all: build html

build: Makefile.coq
	make -f Makefile.coq

html: Makefile.coq
	make -f Makefile.coq2html coq2html

clean: Makefile.coq
	make -f Makefile.coq cleanall
	rm Makefile.coq

.PHONY: all build html clean

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@
