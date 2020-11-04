_sf_
====

Mirror of the [Software Foundations](http://softwarefoundations.cis.upenn.edu/) series of books.  Includes generated PDFs.

- B. Pierce, et al. (2020) [“Logical Foundations”](doc/pdf/lf.pdf)  
  _Version 5.8 (2020-09-09 20:57, Coq 8.12)_

- B. Pierce, et al. (2020) [“Programming Language Foundations”](doc/pdf/plf.pdf)  
  _Version 5.8 (2020-09-09 21:10, Coq 8.12)_

- A. Appel (2020) [“Verified Functional Algorithms”](doc/pdf/vfa.pdf)  
  _Version 1.4 (2020-08-07 17:12, Coq 8.9.1 or later)_

- L. Lampropoulos and B. Pierce (2020) [“QuickChick: Property-Based Testing in Coq”](doc/pdf/qc.pdf)  
  _Version 1.1 (2020-10-14 10:24, Coq 8.12)_

- A. Appel and Q. Cao (2020) [“Verifiable C”](doc/pdf/vc.pdf)  
  _Version 0.9.7 (2020-09-18 15:40, Coq 8.12) Compatible with VST 2.6 (July 2020)_


Usage
-----

To regenerate the PDFs, ensure Coq, QuickChick, VST and LaTeX are installed, then:

```
$ make
```

### Notes

The [Makefiles](src/Makefile.patch) are patched during the build process, so that chapters are generated in the right order, and the LaTeX nesting limit is not reached.

Similarly, the following chapters are patched:

- Logical Foundation book
  - [Preface](src/lf-Preface.v.patch) _To fill BibTeX info_
- Programming Language Foundation book
  - [Preface](src/plf-Preface.v.patch) _To fill BibTeX info_
- Verified Functional Algorithms book
  - [Preface](src/vfa-Preface.v.patch) _To fill BibTeX info_
  - [Extract](src/Extract.v.patch) _To escape code listings_
  - [Redblack](src/Redblack.v.patch) _To escape code listings_
- QuickChick book
  - [Preface](src/qc-Preface.v.patch) _To fill BibTeX info_
  - [Typeclasses](src/Typeclasses.v.patch) _To combine diacritic mark to avoid LaTeX confusion_
  - [QuickChickTool](src/QuickChickTool.v.patch) _To escape code listings_
- Verifiable C book
  - [Preface](src/vc-Preface.v.patch) _To fill BibTeX info_
  - [Verif_sumarray](src/Verif_sumarray.v.patch) _To escape code listings_
  - [Verif_reverse](src/Verif_reverse.v.patch) _To escape code listings_
  - [Verif_strlib](src/Verif_strlib.v.patch) _To escape code listings_
  - [Verif_hash](src/Verif_hash.v.patch) _To escape code listings_


About
-----

Packaged by [Miëtek Bak](https://mietek.io/).
