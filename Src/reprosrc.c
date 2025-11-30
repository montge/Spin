/***** spin: reprosrc.c *****/

/*
 * This file is part of the public release of Spin. It is subject to the
 * terms in the LICENSE file that is included in this source directory.
 * Tool documentation is available at http://spinroot.com
 */

#include <stdio.h>
#include <assert.h>
#include "spin.h"
#include "y.tab.h"

static int indent = 1;

extern YYSTYPE yylval;
extern ProcList	*ready;
static void repro_seq(Sequence *);

void
doindent(void)
{	int i;
	for (i = 0; i < indent; i++)
		printf("   ");
}

void
repro_sub(Element *e)
{
	doindent();
	switch (e->n->ntyp) {
	case D_STEP:
		printf("d_step {\n");
		break;
	case ATOMIC:
		printf("atomic {\n");
		break;
	case NON_ATOMIC:
		printf(" {\n");
		break;
	}
	indent++;
	repro_seq(e->n->sl->this);
	indent--;

	doindent();
	printf(" };\n");
}

static void
repro_seq(Sequence *s)
{	Element *e;
	Symbol *v;
	SeqList *h;

	for (e = s->frst; e; e = e->nxt)
	{
		v = has_lab(e, 0);
		if (v) printf("%s:\n", v->name);

		if (e->n->ntyp == UNLESS)
		{	printf("/* normal */ {\n");
			repro_seq(e->n->sl->this);
			doindent();
			printf("} unless {\n");
			repro_seq(e->n->sl->nxt->this);
			doindent();
			printf("}; /* end unless */\n");
		} else if (e->sub)
		{
			switch (e->n->ntyp) {
			case DO: doindent(); printf("do\n"); indent++; break;
			case IF: doindent(); printf("if\n"); indent++; break;
			}

			for (h = e->sub; h; h = h->nxt)
			{	indent--; doindent(); indent++; printf("::\n");
				repro_seq(h->this);
				printf("\n");
			}

			switch (e->n->ntyp) {
			case DO: indent--; doindent(); printf("od;\n"); break;
			case IF: indent--; doindent(); printf("fi;\n"); break;
			}
		} else
		{	if (e->n->ntyp == ATOMIC
			||  e->n->ntyp == D_STEP
			||  e->n->ntyp == NON_ATOMIC)
				repro_sub(e);
			else if (e->n->ntyp != '.'
			     &&  e->n->ntyp != '@'
			     &&  e->n->ntyp != BREAK)
			{
				doindent();
				if (e->n->ntyp == C_CODE)
				{	printf("c_code ");
					plunk_inline(stdout, e->n->sym->name, 1, 1);
				} else if (e->n->ntyp == 'c'
				       &&  e->n->lft->ntyp == C_EXPR)
				{	printf("c_expr { ");
					plunk_expr(stdout, e->n->lft->sym->name);
					printf("} ->\n");
				} else
				{	comment(stdout, e->n, 0);
					printf(";\n");
			}	}
		}
		if (e == s->last)
			break;
	}
}

void
repro_proc(ProcList *p)
{
	if (!p) return;
	if (p->nxt) repro_proc(p->nxt);

	if (p->det) printf("D");	/* deterministic */
	printf("proctype %s()", p->n->name);
	if (p->prov)
	{	printf(" provided ");
		comment(stdout, p->prov, 0);
	}
	printf("\n{\n");
	repro_seq(p->s);
	printf("}\n");
}

void
repro_src(void)
{
	repro_proc(ready);
}

static int in_decl;
static int in_c_decl;
static int in_c_code;

void
blip(int n, char *b)
{	char mtxt[1024];

	mtxt[0] = '\0';

	switch (n) {
	default:	if (n > 0 && n < 256)
				snprintf(mtxt, sizeof(mtxt), "%c", n);
			else
				snprintf(mtxt, sizeof(mtxt), "<%d?>", n);

			break;
	case '(':	snprintf(mtxt, sizeof(mtxt), "("); in_decl++; break;
	case ')':	snprintf(mtxt, sizeof(mtxt), ")"); in_decl--; break;
	case '{':	snprintf(mtxt, sizeof(mtxt), "{"); break;
	case '}':	snprintf(mtxt, sizeof(mtxt), "}"); break;
	case '\t':	snprintf(mtxt, sizeof(mtxt), "\\t"); break;
	case '\f':	snprintf(mtxt, sizeof(mtxt), "\\f"); break;
	case '\n':	snprintf(mtxt, sizeof(mtxt), "\\n"); break;
	case '\r':	snprintf(mtxt, sizeof(mtxt), "\\r"); break;
	case 'c':	snprintf(mtxt, sizeof(mtxt), "condition"); break;
	case 's':	snprintf(mtxt, sizeof(mtxt), "send"); break;
	case 'r':	snprintf(mtxt, sizeof(mtxt), "recv"); break;
	case 'R':	snprintf(mtxt, sizeof(mtxt), "recv poll"); break;
	case '@':	snprintf(mtxt, sizeof(mtxt), "@"); break;
	case '?':	snprintf(mtxt, sizeof(mtxt), "(x->y:z)"); break;
	case NEXT:	snprintf(mtxt, sizeof(mtxt), "X"); break;
	case ALWAYS:	snprintf(mtxt, sizeof(mtxt), "[]"); break;
	case EVENTUALLY: snprintf(mtxt, sizeof(mtxt), "<>"); break;
	case IMPLIES:	snprintf(mtxt, sizeof(mtxt), "->"); break;
	case EQUIV:	snprintf(mtxt, sizeof(mtxt), "<->"); break;
	case UNTIL:	snprintf(mtxt, sizeof(mtxt), "U"); break;
	case WEAK_UNTIL: snprintf(mtxt, sizeof(mtxt), "W"); break;
	case IN: snprintf(mtxt, sizeof(mtxt), "in"); break;
	case ACTIVE:	snprintf(mtxt, sizeof(mtxt), "active"); break;
	case AND:	snprintf(mtxt, sizeof(mtxt), "&&"); break;
	case ARROW:	snprintf(mtxt, sizeof(mtxt), "->"); break;
	case ASGN:	snprintf(mtxt, sizeof(mtxt), "="); break;
	case ASSERT:	snprintf(mtxt, sizeof(mtxt), "assert"); break;
	case ATOMIC:	snprintf(mtxt, sizeof(mtxt), "atomic"); break;
	case BREAK:	snprintf(mtxt, sizeof(mtxt), "break"); break;
	case C_CODE:	snprintf(mtxt, sizeof(mtxt), "c_code"); in_c_code++; break;
	case C_DECL:	snprintf(mtxt, sizeof(mtxt), "c_decl"); in_c_decl++; break;
	case C_EXPR:	snprintf(mtxt, sizeof(mtxt), "c_expr"); break;
	case C_STATE:	snprintf(mtxt, sizeof(mtxt), "c_state"); break;
	case C_TRACK:	snprintf(mtxt, sizeof(mtxt), "c_track"); break;
	case CLAIM:	snprintf(mtxt, sizeof(mtxt), "never"); break;
	case CONST:	snprintf(mtxt, sizeof(mtxt), "%d", yylval->val); break;
	case DECR:	snprintf(mtxt, sizeof(mtxt), "--"); break;
	case D_STEP:	snprintf(mtxt, sizeof(mtxt), "d_step"); break;
	case D_PROCTYPE: snprintf(mtxt, sizeof(mtxt), "d_proctype"); break;
	case DO:	snprintf(mtxt, sizeof(mtxt), "do"); break;
	case DOT:	snprintf(mtxt, sizeof(mtxt), "."); break;
	case ELSE:	snprintf(mtxt, sizeof(mtxt), "else"); break;
	case EMPTY:	snprintf(mtxt, sizeof(mtxt), "empty"); break;
	case ENABLED:	snprintf(mtxt, sizeof(mtxt), "enabled"); break;
	case EQ:	snprintf(mtxt, sizeof(mtxt), "=="); break;
	case EVAL:	snprintf(mtxt, sizeof(mtxt), "eval"); break;
	case FI:	snprintf(mtxt, sizeof(mtxt), "fi"); break;
	case FOR:	snprintf(mtxt, sizeof(mtxt), "for"); break;
	case FULL:	snprintf(mtxt, sizeof(mtxt), "full"); break;
	case GE:	snprintf(mtxt, sizeof(mtxt), ">="); break;
	case GET_P:	snprintf(mtxt, sizeof(mtxt), "get_priority"); break;
	case GOTO:	snprintf(mtxt, sizeof(mtxt), "goto"); break;
	case GT:	snprintf(mtxt, sizeof(mtxt), ">"); break;
	case HIDDEN:	snprintf(mtxt, sizeof(mtxt), "hidden"); break;
	case IF:	snprintf(mtxt, sizeof(mtxt), "if"); break;
	case INCR:	snprintf(mtxt, sizeof(mtxt), "++"); break;

	case INLINE:	snprintf(mtxt, sizeof(mtxt), "inline"); break;
	case INIT:	snprintf(mtxt, sizeof(mtxt), "init"); break;
	case ISLOCAL:	snprintf(mtxt, sizeof(mtxt), "local"); break;

	case LABEL:	snprintf(mtxt, sizeof(mtxt), "<label-name>"); break;

	case LE:	snprintf(mtxt, sizeof(mtxt), "<="); break;
	case LEN:	snprintf(mtxt, sizeof(mtxt), "len"); break;
	case LSHIFT:	snprintf(mtxt, sizeof(mtxt), "<<"); break;
	case LT:	snprintf(mtxt, sizeof(mtxt), "<"); break;
	case LTL:	snprintf(mtxt, sizeof(mtxt), "ltl"); break;

	case NAME:	snprintf(mtxt, sizeof(mtxt), "%s", yylval->sym->name); break;

	case XU:	switch (yylval->val) {
			case XR:	snprintf(mtxt, sizeof(mtxt), "xr"); break;
			case XS:	snprintf(mtxt, sizeof(mtxt), "xs"); break;
			default:	snprintf(mtxt, sizeof(mtxt), "<?>"); break;
			}
			break;

	case TYPE:	switch (yylval->val) {
			case BIT:	snprintf(mtxt, sizeof(mtxt), "bit"); break;
			case BYTE:	snprintf(mtxt, sizeof(mtxt), "byte"); break;
			case CHAN:	snprintf(mtxt, sizeof(mtxt), "chan"); in_decl++; break;
			case INT:	snprintf(mtxt, sizeof(mtxt), "int"); break;
			case MTYPE:	snprintf(mtxt, sizeof(mtxt), "mtype"); break;
			case SHORT:	snprintf(mtxt, sizeof(mtxt), "short"); break;
			case UNSIGNED:	snprintf(mtxt, sizeof(mtxt), "unsigned"); break;
			default:	snprintf(mtxt, sizeof(mtxt), "<unknown type>"); break;
			}
			break;

	case NE:	snprintf(mtxt, sizeof(mtxt), "!="); break;
	case NEG:	snprintf(mtxt, sizeof(mtxt), "!"); break;
	case NEMPTY:	snprintf(mtxt, sizeof(mtxt), "nempty"); break;
	case NFULL:	snprintf(mtxt, sizeof(mtxt), "nfull"); break;

	case NON_ATOMIC: snprintf(mtxt, sizeof(mtxt), "<sub-sequence>"); break;

	case NONPROGRESS: snprintf(mtxt, sizeof(mtxt), "np_"); break;
	case OD:	snprintf(mtxt, sizeof(mtxt), "od"); break;
	case OF:	snprintf(mtxt, sizeof(mtxt), "of"); break;
	case OR:	snprintf(mtxt, sizeof(mtxt), "||"); break;
	case O_SND:	snprintf(mtxt, sizeof(mtxt), "!!"); break;
	case PC_VAL:	snprintf(mtxt, sizeof(mtxt), "pc_value"); break;
	case PRINT:	snprintf(mtxt, sizeof(mtxt), "printf"); break;
	case PRINTM:	snprintf(mtxt, sizeof(mtxt), "printm"); break;
	case PRIORITY:	snprintf(mtxt, sizeof(mtxt), "priority"); break;
	case PROCTYPE:	snprintf(mtxt, sizeof(mtxt), "proctype"); break;
	case PROVIDED:	snprintf(mtxt, sizeof(mtxt), "provided"); break;
	case RETURN:	snprintf(mtxt, sizeof(mtxt), "return"); break;
	case RCV:	snprintf(mtxt, sizeof(mtxt), "?"); break;
	case R_RCV:	snprintf(mtxt, sizeof(mtxt), "??"); break;
	case RSHIFT:	snprintf(mtxt, sizeof(mtxt), ">>"); break;
	case RUN:	snprintf(mtxt, sizeof(mtxt), "run"); break;
	case SEP:	snprintf(mtxt, sizeof(mtxt), "::"); break;
	case SEMI:	snprintf(mtxt, sizeof(mtxt), ";"); break;
	case SET_P:	snprintf(mtxt, sizeof(mtxt), "set_priority"); break;
	case SHOW:	snprintf(mtxt, sizeof(mtxt), "show"); break;
	case SND:	snprintf(mtxt, sizeof(mtxt), "!"); break;

	case INAME:
	case UNAME:
	case PNAME:
	case STRING:	snprintf(mtxt, sizeof(mtxt), "%s", yylval->sym->name); break;

	case TRACE:	snprintf(mtxt, sizeof(mtxt), "trace"); break;
	case TIMEOUT:	snprintf(mtxt, sizeof(mtxt), "(timeout)"); break;
	case TYPEDEF:	snprintf(mtxt, sizeof(mtxt), "typedef"); break;
	case UMIN:	snprintf(mtxt, sizeof(mtxt), "-"); break;
	case UNLESS:	snprintf(mtxt, sizeof(mtxt), "unless"); break;
	}
	strncat(b, mtxt, 1023 - strlen(b));
}

void
purge(char *b)
{
	if (strlen(b) == 0) return;

	if (b[strlen(b)-1] != ':')	/* label? */
	{	if (b[0] == ':' && b[1] == ':')
		{	indent--;
			doindent();
			indent++;
		} else
		{	doindent();
		}
	}
	printf("%s\n", b);
	b[0] = '\0';

	in_decl = 0;
	in_c_code = 0;
	in_c_decl = 0;
}

int pp_mode;
extern int lex(void);

void
pretty_print(void)
{	int c, lastc = 0;
	char buf[1024];

	pp_mode = 1;
	indent = 0;
	buf[0] = '\0';
	while ((c = lex()) != EOF)
	{
		if ((lastc == IF || lastc == DO) && c != SEP)
		{	indent--;	/* c_code if */
		}
		if (c == C_DECL  || c == C_STATE
		||  c == C_TRACK || c == SEP
		||  c == DO      || c == IF
		|| (c == TYPE && !in_decl))
		{	purge(buf); /* start on new line */
		}

		if (c == '{'
		&& lastc != OF && lastc != IN
		&& lastc != ATOMIC && lastc != D_STEP
		&& lastc != C_CODE && lastc != C_DECL && lastc != C_EXPR)
		{	purge(buf);
		}

		if (c == PREPROC)
		{	int oi = indent;
			purge(buf);
			assert(strlen(yylval->sym->name) < sizeof(buf));
			snprintf(buf, sizeof(buf), "%s", yylval->sym->name);
			indent = 0;
			purge(buf);
			indent = oi;
			continue;
		}

		if (c != ':' && c != SEMI
		&&  c != ',' && c != '('
		&&  c != '#' && lastc != '#'
		&&  c != ARROW && lastc != ARROW
		&&  c != '.' && lastc != '.'
		&&  c != '!' && lastc != '!'
		&&  c != SND && lastc != SND
		&&  c != RCV && lastc != RCV
		&&  c != O_SND && lastc != O_SND
		&&  c != R_RCV && lastc != R_RCV
		&&  (c != ']' || lastc != '[')
		&&  (c != '>' || lastc != '<')
		&&  (c != GT || lastc != LT)
		&&  c != '@' && lastc != '@'
		&& (lastc != '(' || c != ')')
		&& (lastc != '/' || c != '/')
		&&  c != DO && c != OD && c != IF && c != FI
		&&  c != SEP && strlen(buf) > 0)
			strncat(buf, " ", sizeof(buf) - strlen(buf) - 1);

		if (c == '}' || c == OD || c == FI)
		{	purge(buf);
			indent--;
		}
		blip(c, buf);

		if (c == '{' || c == DO || c == IF)
		{	purge(buf);
			indent++;
		}

		if (c == '}' || c == BREAK || c == SEMI || c == ELSE
		|| (c == ':' && lastc == NAME))
		{	purge(buf);
		}
		lastc = c;
	}
	purge(buf);
}
