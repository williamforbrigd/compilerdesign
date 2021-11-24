INCLUDES= util,x86,grading,ll
LIBS = unix,str,nums
SUBMIT := lexer.mll parser.mly frontend.ml team.txt

HWNAME := hw04
TIMESTAMP := $(shell /bin/date "+%Y-%m-%d-%H:%M:%S")
ZIPNAME := $(HWNAME)-submit($(TIMESTAMP)).zip


all: main.native

.PHONY: test
test: main.native
	./main.native --test

main.native: $(SUBMIT) ast.ml astlib.ml backend.ml driver.ml main.ml progasts.ml runtime.c 
	ocamlbuild -Is $(INCLUDES) -libs $(LIBS) main.native -use-menhir -yaccflag --explain

zip: $(SUBMIT)
	zip '$(ZIPNAME)' $(SUBMIT)

.PHONY: clean
clean:
	ocamlbuild -clean
	rm -rf output a.out
