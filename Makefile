AGDA = $(wildcard *.agda)
AGDAI = $(AGDA:.agda=.agdai)

all: $(AGDAI)
	$(MAKE) -C KvR $@

website:
	mkdir -p $@
	agda --html --html-dir=$@ Polygraph.agda
	cd $@ && rm -f index.html && ln -s Polygraph.html index.html

%.agdai: %.agda
	agda $<

.PHONY: website
