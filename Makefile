

all: HCoercionsIso.vo

LibTactics.vo: LibTactics.v
	coqc LibTactics.v

General.vo: General.v LibTactics.vo
	coqc General.v

SolveMax.vo: SolveMax.v General.vo
	coqc SolveMax.v

Types.vo: Types.v General.vo
	coqc Types.v

Coercions.vo: Coercions.v Types.vo SolveMax.vo
	coqc Coercions.v

HCoercions.vo: HCoercions.v Coercions.vo SolveMax.vo
	coqc HCoercions.v

HCoercionsCompose.vo: HCoercionsCompose.v HCoercions.vo
	coqc HCoercionsCompose.v

HCoercionsIso.vo: HCoercionsIso.v HCoercionsCompose.vo
	coqc HCoercionsIso.v

clean:
	$(RM) *.vo *.glob
