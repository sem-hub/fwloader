/*
 * Copyright (c) 2007 Sergey Matveychuk
 *      Yandex company.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 4. Neither the name of the company nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

%{
#include <stdio.h>
#include <stdlib.h>

void
print_bar()
{
	if(!quiet) {
	    if(line%100 == 0)
		printf(".");
	    if(line > 0 && line%1000 == 0)
		printf("%d", line);
	    fflush(stdout);
	}
}
%}

digit	[0-9]
digits	{digit}+
float	{digits}\.{digits}
hexdigit [0-9a-fA-F]
octet	{digit}{1,3}
ip4	({octet}\.){3}{octet}
network	{ip4}\/{digit}{1,2}
hexadecatet {hexdigit}{1,4}
ip6	({hexadecatet}:){7}{hexadecatet}|({hexadecatet}:){0,7}:((({hexadecatet}:){0,6}{hexadecatet})?)
network6 {ip6}\/{digit}{1,3}
label	:[-0-9a-zA-Z_]+

%%
{label}			{ strcpy(yylval.sval, yytext); return LABEL; }
add			return ADD;
allow|accept|pass|permit	return ALLOW;
deny_in			return DENY_IN;
deny|drop		return DENY;
reject			return REJECTT;
unreach			return UNREACH;
skipto			return SKIPTO;
divert			return DIVERT;
tee			return TEE;
count			return COUNT;
setipprec		return SETIPPREC;
tag			return TAG;
altq			return ALTQ;
pipe			return PIPE;
queue			return QUEUE;
reass			return REASS;
config			return CONFIG;
bw			return BW;
weight			return WEIGHT;
buckets			return BUCKETS;
mask			return MASK;
noerror			return NOERROR;
plr			return PLR;
gred|red		{ strcpy(yylval.sval, yytext); return RED; }
droptail		return DROPTAIL;
flow-id			return FLOWID;
delay			return PDELAY;
check-state		return CHECKSTATE;
fwd|forward		return FWD;
log			return LOG;
logamount		return LOGAMOUNT;
setup			return SETUP;
established		return ESTABLISHED;
frag			return FRAG;
keep-state		return KEEPSTATE;
icmptype|icmptypes	return ICMPTYPES;
icmp6type|icmp6types	return ICMP6TYPES;
from			return FROM;
to			return TO;
me			return ME;
me6			return ME6;
any			return ANY;
in			return IN;
out			return OUT;
via			return VIA;
xmit			return XMIT;
recv			return RECV;
or			return OR;
not			return NOT;
limit			return LIMIT;
table			return TABLE;
tcpflags		return TCPFLAGS;
tcpoptions		return TCPOPTIONS;
ip			return T_IP;
iplen			return IPLEN;
ipoptions		return IPOPTIONS;
iptos			return IPTOS;
ipttl			return IPTTL;
tcpdatalen		return TCPDATALEN;
tcpseq			return TCPSEQ;
fin			return FIN;
syn			return SYN;
rst			return RST;
psh			return PSH;
ack			return ACK;
urg			return URG;
mss			return MSS;
window			return WINDOW;
sack			return SACK;
ts			return TS;
cc			return CC;
ssrr			return SSRR;
lsrr			return LSRR;
rr			return RR;
lowdelay		return LOWDELAY;
throughput		return THROUGHPUT;
reliability		return RELIABILITY;
mincost			return MINCOST;
congestion		return CONGESTION;
net			return NET;
host			return HOST;
protocol		return PROTOCOL;
proto			return PROTO;
port			return PORT;
needfrag		return NEEDFRAG;
srcfail			return SRCFAIL;
net-unknown		return NETUNKNOWN;
host-unknown		return HOSTUNKNOWN;
isolated		return ISOLATED;
net-prohib		return NETPROHIB;
host-prohib		return HOSTPROHIB;
tosnet			return TOSNET;
toshost			return TOSHOST;
filter-prohib		return FILTERPROHIB;
host-precedence		return HOSTPRECEDENCE;
precedence-cutoff	return PRECEDENCECUTOFF;
diverted-loopback	return DIVERTEDLOOPBACK;
diverted-output		return DIVERTEDOUTPUT;
diverted		return DIVERTED;
nat			return NAT;
netgraph		return NETGRAPH;
same_ports		return SAME_PORTS;
if			return IF;
unreg_only		return UNREG_ONLY;
verrevpath		return VERREVPATH;
versrcreach		return VERSRCREACH;
antispoof		return ANTISPOOF;
reset			return RESET;
reverse			return REVERSE;
proxy_only		return PROXY_ONLY;
redirect_addr		return REDIRECT_ADDR;
redirect_port		return REDIRECT_PORT;
redirect_proto		return REDIRECT_PROTO;
ext6hdr			return EXT6HDR;
hopopt			return HOPOPT;
route			return ROUTE;
dstopt			return DSTOPT;
ah			return AH;
esp			return ESP;
rthdr0			return RTHDR0;
rthdr2			return RTHDR2;
ipsec			return IPSEC;
ipversion		return IPVER;
!			return NOTCHAR;
src-addr		{ strcpy(yylval.sval, yytext); return SRCADDR; }
dst-addr		{ strcpy(yylval.sval, yytext); return DSTADDR; }
src-port		{ strcpy(yylval.sval, yytext); return SRCPORT; }
dst-port		{ strcpy(yylval.sval, yytext); return DSTPORT; }
dst-ip			{ strcpy(yylval.sval, yytext); return DSTIP; }
src-ip			{ strcpy(yylval.sval, yytext); return SRCIP; }
\{			return OBRACE;
\}			return EBRACE;
\(			return LBRACE;
\)			return RBRACE;
{ip4}			{ strcpy(yylval.sval, yytext); return IP; }
{ip6}			{ strcpy(yylval.sval, yytext); return IP6; }
all			{ strcpy(yylval.sval, "all"); return ALL; }
{network}		{ strcpy(yylval.sval, yytext); return NETWORK; }
{network6}		{ strcpy(yylval.sval, yytext); return NETWORK6; }
{digits}-{digits}	{ strncpy(yylval.sval, yytext, MAX_TOKEN-1); return RANGE; };
,			return COMMA;
{float}\/{digits}\/{digits}\/{float}	{ strcpy(yylval.sval, yytext); return REDPARAM; }
{float}			{ yylval.fval = strtof(yytext, NULL); return FLOAT; }
0x{hexdigit}+		{ yylval.ival = strtol(yytext+2, NULL, 16); return HEXMASK; }
{digits}[Bb]it\/s		{ yylval.ival = strtol(yytext, NULL, 10); return BWBS; }
{digits}[Bb]yte\/s		{ yylval.ival = strtol(yytext, NULL, 10); return BWBTS; }
{digits}[Kk][Bb]it\/s	{ yylval.ival = strtol(yytext, NULL, 10); return BWKBS; }
{digits}[Kk][Bb]yte\/s	{ yylval.ival = strtol(yytext, NULL, 10); return BWKBTS; }
{digits}[Mm][Bb]it\/s	{ yylval.ival = strtol(yytext, NULL, 10); return BWMBS; }
{digits}[Mm][Bb]yte\/s	{ yylval.ival = strtol(yytext, NULL, 10); return BWMBTS; }
{digits}[Bb]ytes	{ yylval.ival = strtol(yytext, NULL, 10); return SIZEK; }
{digits}[Kk][Bb]ytes	{ yylval.ival = strtol(yytext, NULL, 10)*1024; return SIZEK; }
{digits}		{ yylval.ival = strtol(yytext, NULL, 10); return NUMBER; }
[a-zA-Z0-9][-\\a-zA-Z0-9]+	{ strncpy(yylval.sval, yytext, MAX_TOKEN-1); return TOKEN; }
[a-zA-Z0-9][-\.a-zA-Z0-9]+	{ strncpy(yylval.sval, yytext, MAX_TOKEN-1); return FQDN; }
\/\/[ ][^\n]*			{ strncpy(yylval.sval, yytext+3, MAX_TOKEN-1); return COMMENT; }
_[\_\-\.a-zA-Z0-9]+_	{ strncpy(yylval.sval, yytext, MAX_TOKEN-1); return TABLENAME; }
#.*\n			{ line++; print_bar(); /* ignore comments */ };
[ \t]+			/* ignore spaces */;
^[ \t]*\n		{ line++; print_bar(); /* ignore empty lines */ };
\n			{ line++; print_bar(); return EOL; }
.			{ printf("Invalid character: %s, line: %d\n", yytext, line); exit(1); }
%%
