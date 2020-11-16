all: lf plf vfa qc vc

.PHONY: lf plf vfa qc vc

lf: doc/pdf/lf.pdf
plf: doc/pdf/plf.pdf
vfa: doc/pdf/vfa.pdf
qc: doc/pdf/qc.pdf
vc: doc/pdf/vc.pdf

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

doc/pdf/vc.pdf: src/vc/all.pdf
	mkdir -p doc/pdf
	mv src/vc/all.pdf doc/pdf/vc.pdf

src/lf/all.pdf:
	-patch -N -d src/lf < src/lf-Preface.v.patch
	make -C src/lf
	-patch -N -d src/lf < src/Makefile.patch
	make -C src/lf -f Makefile.coq all.pdf
	
src/plf/all.pdf:
	-patch -N -d src/plf < src/plf-Preface.v.patch
	-patch -N -d src/plf < src/Hoare.v.patch
	make -C src/plf
	-patch -N -d src/plf < src/Makefile.patch
	make -C src/plf -f Makefile.coq all.pdf
	
src/vfa/all.pdf:
	-patch -N -d src/vfa < src/vfa-Preface.v.patch
	-patch -N -d src/vfa < src/Extract.v.patch
	-patch -N -d src/vfa < src/Redblack.v.patch
	make -C src/vfa
	-patch -N -d src/vfa < src/Makefile.patch
	make -C src/vfa -f Makefile.coq all.pdf
	
src/qc/all.pdf:
	-patch -N -d src/qc < src/qc-Preface.v.patch
	-patch -N -d src/qc < src/Typeclasses.v.patch
	-patch -N -d src/qc < src/QuickChickTool.v.patch
	make -C src/qc
	-patch -N -d src/qc < src/Makefile.patch
	make -C src/qc -f Makefile.coq all.pdf

src/vc/all.pdf:
	-patch -N -d src/vc < src/vc-Preface.v.patch
	-patch -N -d src/vc < src/Verif_sumarray.v.patch
	-patch -N -d src/vc < src/Verif_reverse.v.patch
	-patch -N -d src/vc < src/Verif_strlib.v.patch
	-patch -N -d src/vc < src/Verif_hash.v.patch
	make -C src/vc
	-patch -N -d src/vc < src/Makefile.patch
	make -C src/vc -f Makefile.coq all.pdf
