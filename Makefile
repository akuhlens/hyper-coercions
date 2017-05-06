.PHONY: plugin install clean

# Here is a hack to make $(eval $(shell work
# (copied from coq_makefile generated stuff):
# define donewline


# endef

# includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
# $(call includecmdwithout@,$(COQBIN)coqtop -config)

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Make
	coq_makefile -f _CoqProject -o Makefile.coq


distclean:
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

# want to be able to distribute with a makefile
clean: distclean 
	rm -f Makefile.coq

bc:
	coqwc *.v
