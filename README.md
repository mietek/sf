_software-foundations_
======================

Mirror of [“Software Foundations”](http://www.cis.upenn.edu/~bcpierce/sf/), by Benjamin Pierce et al., version 3.2 (January 2015).

Includes a [PDF version](doc/pdf/pierce-2015.pdf) of the book.


Usage
-----

To rebuild the PDF, ensure Coq and LaTeX are installed, then:

```
$ make
```

### Notes

The original [`Makefile`](src/Makefile) has been modified to generate chapters in the right order:

```diff
@@ -68 +68 @@ COQCHK?=$(COQBIN)coqchk
-VFILES:=Symbols.v\
+RVFILES:=\
@@ -107,0 +108,3 @@ VFILES:=Symbols.v\
+reverse=$(if $1,$(call reverse,$(wordlist 2,$(words $1),$1))) $(firstword $1)
+VFILES:=$(call reverse,$(RVFILES))
+
```


About
-----

Packaged by [Miëtek Bak](https://mietek.io/).
