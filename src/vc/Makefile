COQMFFLAGS := -Q . VC  

ALLVFILES := sumarray.v reverse.v append.v stack.v strlib.v hash.v hints.v Preface.v Verif_sumarray.v Verif_reverse.v Verif_stack.v Verif_triang.v Verif_append1.v Verif_append2.v Verif_strlib.v Hashfun.v Verif_hash.v Postscript.v Bib.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

.PHONY: build clean
