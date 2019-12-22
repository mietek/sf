all: lf plf vfa qc

.PHONY: lf plf vfa qc

lf: doc/pdf/lf.pdf
plf: doc/pdf/plf.pdf
vfa: doc/pdf/vfa.pdf
qc: doc/pdf/qc.pdf

doc/pdf/%.pdf: src/%/all.tex
	mkdir -p tmp doc/pdf
	gawk -f src/hack-latex.gawk $< > tmp/all.tex
	cp src/$*/coqdoc.sty tmp
	( cd tmp ; pdflatex all.tex && pdflatex all.tex )
	mv tmp/all.pdf $@
	@rm -rf tmp

src/lf/all.tex:
	cp src/Makefile.local src/lf/
	$(MAKE) -C src/lf all
	$(MAKE) -C src/lf all.tex
		
src/plf/all.tex:
	cp src/Makefile.local src/plf
	$(MAKE) -C src/plf all
	$(MAKE) -C src/plf all.tex SKIP="Maps.v Imp.v"
	
src/vfa/all.pdf:
	make -C src/vfa all
	-patch -N -d src/vfa < src/Makefile.patch
	make -C src/vfa all.pdf
	
src/qc/all.pdf:
	-patch -N -d src/qc < src/Typeclasses.v.patch
	-patch -N -d src/qc < src/QuickChickTool.v.patch
	make -C src/qc all
	-patch -N -d src/qc < src/Makefile.patch
	make -C src/qc all.pdf	
