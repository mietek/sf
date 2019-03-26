_sf_
====

Mirror of the [Software Foundations](http://softwarefoundations.cis.upenn.edu/) series of books.  Includes generated PDFs.

- B. Pierce, et al. (2019) [“Logical Foundations”](doc/pdf/lf.pdf)  
  _Version 5.6 (09 Jan 2019, Coq 8.8.2)_

- B. Pierce, et al. (2019) [“Programming Language Foundations”](doc/pdf/plf.pdf)  
  _Version 5.7 (08 Feb 2019, Coq 8.8.2)_

- A. Appel (2018) [“Verified Functional Algorithms”](doc/pdf/vfa.pdf)  
  _Version 1.4 (25 Aug 2018, Coq 8.8.2)_

- L. Lampropoulos and B. Pierce (2018) [“QuickChick: Property-Based Testing in Coq”](doc/pdf/qc.pdf)  
  _Version 1.0 (09 Oct 2018, Coq 8.8.2)_


Usage
-----

To regenerate the PDFs, ensure Coq, QuickChick, and LaTeX are installed, then:

```
$ make
```

### Notes

The [Makefiles](src/Makefile.patch) are patched during the build process, so that chapters are generated in the right order, and the LaTeX nesting limit is not reached.

Similarly, the [Typeclasses](src/Typeclasses.v.patch) and [QuickChickTool](src/QuickChickTool.v.patch) chapters of the QuickChick book are patched, so that a diacritic does not confuse LaTeX, and code listings appear in the output as intended.


About
-----

Packaged by [Miëtek Bak](https://mietek.io/).
