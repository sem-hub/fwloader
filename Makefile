PROGNAME=	fw-loader
CCFLAGS!=	./check-features.sh

all:	${PROGNAME}

debug:	${PROGNAME}
CCFLAGS+=-g -lutil


lex.yy.c: fw-parse.l
	lex fw-parse.l

y.tab.c: lex.yy.c fw-parse.l fw-parse.y
	yacc -d fw-parse.y

${PROGNAME}: y.tab.c main.c
	cc ${CCFLAGS} y.tab.c main.c -ll -o ${PROGNAME}

clean:
	rm -f ${PROGNAME} lex.yy.c y.tab.c y.tab.h *.bak *.core y.output
