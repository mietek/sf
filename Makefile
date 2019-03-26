all: lf plf vfa qc

.PHONY: lf plf vfa qc

lf: doc/pdf/lf.pdf
plf: doc/pdf/plf.pdf
vfa: doc/pdf/vfa.pdf
qc: doc/pdf/qc.pdf

doc/pdf/lf.pdf: src/lf/all.pdf
	mkdir -p doc/pdf
	mv src/lf/all.pdf doc/pdf/lf.pdf

doc/pdf/plf.pdf: src/plf/all.pdf
	mkdir -p doc/pdf
	mv src/plf/all.pdf doc/pdf/plf.pdf
	
doc/pdf/vfa.pdf: src/vfa/all.pdf
	mkdir -p doc/pdf
	mv src/vfa/all.pdf doc/pdf/vfa.pdf
	
doc/pdf/qc.pdf: src/qc/all.pdf
	mkdir -p doc/pdf
	mv src/qc/all.pdf doc/pdf/qc.pdf

src/lf/all.pdf:
	make -C src/lf all
	-patch -N -d src/lf < src/Makefile.patch
	make -C src/lf all.pdf
	
src/plf/all.pdf:
	make -C src/plf all
	-patch -N -d src/plf < src/Makefile.patch
	make -C src/plf all.pdf
	
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
