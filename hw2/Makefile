DIRS := util,grading,x86
LIBS := unix,str,nums
SUBMIT := simulator.ml team.txt
OTHER := gradedtests.ml studenttests.ml main.ml 
HWNAME := hw02
TIMESTAMP := $(shell /bin/date "+%Y-%m-%d-%H-%M-%S")
ZIPNAME := $(HWNAME)-submit($(TIMESTAMP)).zip

.PHONY: all test clean zip

main.native: $(SUBMIT) $(OTHER)
	ocamlbuild -use-ocamlfind -Is $(DIRS) -libs $(LIBS) main.native

main.byte: $(SUBMIT) $(OTHER)
	ocamlbuild -use-ocamlfind -Is $(DIRS) -libs $(LIBS) main.byte

all: main.byte main.native

test: main.native
	./main.native --test

zip: $(SUBMIT)
	zip '$(ZIPNAME)' $(SUBMIT)


clean:
	ocamlbuild -clean
