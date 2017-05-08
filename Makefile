.PHONY: all clean bc validate

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq


# want to be able to distribute with a makefile
clean:
	find . -name "*.vo" -print -delete
	find . -name "*.glob" -print -delete
	find . -name "*.d" -print -delete
	find . -name "*.o" -print -delete
	find . -name "*.cmi" -print -delete
	find . -name "*.cmx" -print -delete
	find . -name "*.cmxs" -print -delete
	find . -name "*.cmo" -print -delete
	find . -name "*.bak" -print -delete
	find . -name "*~" -print -delete
	rm -f Makefile.coq

bc:
	coqwc *.v


validate: Makefile.coq
	$(MAKE) -f Makefile.coq validate
