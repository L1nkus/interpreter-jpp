## File generated by the BNF Converter (bnfc 2.9.4).

# Makefile for building the parser and test program.

# GHC        = ghc
GHC        = ghc -package mtl
HAPPY      = happy
HAPPY_OPTS = --array --info --ghc --coerce
ALEX       = alex
ALEX_OPTS  = --ghc

# List of goals not corresponding to file names.

.PHONY : all clean distclean

# Default goal.

all : TestLintte Lintte

Lintte : Lintte.hs Interpreter.hs TypeChecker.hs TestLintte
	ghc --make Lintte.hs

# Rules for building the parser.

AbsLintte.hs LexLintte.x ParLintte.y PrintLintte.hs TestLintte.hs : lintte.cf
	bnfc --haskell --functor lintte.cf

%.hs : %.y
	${HAPPY} ${HAPPY_OPTS} $<

%.hs : %.x
	${ALEX} ${ALEX_OPTS} $<

TestLintte : AbsLintte.hs LexLintte.hs ParLintte.hs PrintLintte.hs TestLintte.hs
	${GHC} ${GHC_OPTS} $@

# Rules for cleaning generated files.

clean :
	-rm -f *.hi *.o *.log *.aux *.dvi

distclean : clean
	-rm -f AbsLintte.hs AbsLintte.hs.bak ComposOp.hs ComposOp.hs.bak DocLintte.txt DocLintte.txt.bak ErrM.hs ErrM.hs.bak LayoutLintte.hs LayoutLintte.hs.bak LexLintte.x LexLintte.x.bak ParLintte.y ParLintte.y.bak PrintLintte.hs PrintLintte.hs.bak SkelLintte.hs SkelLintte.hs.bak TestLintte.hs TestLintte.hs.bak XMLLintte.hs XMLLintte.hs.bak ASTLintte.agda ASTLintte.agda.bak ParserLintte.agda ParserLintte.agda.bak IOLib.agda IOLib.agda.bak Main.agda Main.agda.bak lintte.dtd lintte.dtd.bak TestLintte LexLintte.hs ParLintte.hs ParLintte.info ParDataLintte.hs Makefile


# EOF
