all:
	$(MAKE) -C Polygraph $@

website:
	mkdir -p $@
	cd Polygraph && agda --html --html-dir=../$@ Polygraph.agda
	cd $@ && rm -f index.html && ln -s Polygraph.html index.html

.PHONY: website
