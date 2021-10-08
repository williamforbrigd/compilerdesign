.PHONY: all test clean

SUBMIT := hellocaml.ml providedtests.ml

HWNAME := hw01
TIMESTAMP := $(shell /bin/date "+%Y-%m-%d-%H:%M:%S")
ZIPNAME := $(HWNAME)-submit($(TIMESTAMP)).zip


main.native: $(SUBMIT)
	ocamlbuild -Is util -libs unix,str main.native

main.byte:
	ocamlbuild -Is util -libs unix,str main.byte

all: main.native

test: main.native
	./main.native --test

clean:
	ocamlbuild -clean


zip: $(SUBMIT)
	zip '$(ZIPNAME)' $(SUBMIT)

