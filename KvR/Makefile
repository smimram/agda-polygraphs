AGDA = $(wildcard *.agda)
AGDAI = $(AGDA:.agda=.agdai)

all: $(AGDAI)

clean:
	rm -f *.agdai

ci:
	$(MAKE) -C .. $@

%.agdai: %.agda
	agda $<
