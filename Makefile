all:
	$(MAKE) -C src all
	$(MAKE) -C src all.pdf
	mv src/all.pdf doc/pdf/pierce-2016.pdf
