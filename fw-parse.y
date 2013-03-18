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
#include <stddef.h>
#include <stdarg.h>
#include <string.h>
#include <ctype.h>
#include <fcntl.h>
#include <err.h>
#include <errno.h>
#include <unistd.h>
#include <sys/types.h>
#include <arpa/inet.h>
#include <netinet/ip_compat.h>
#include <netdb.h>
#include <sys/queue.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/sysctl.h>
#include <net/pfvar.h>
#include <net/if.h>
#include <net/if_dl.h>
#define IF_NAMESIZE   16
/* For compatibility with 7.x and bellow */
#if !defined(IFNAMSIZ)
#define IFNAMSIZ     IF_NAMESIZE
#endif
#define IPFW_INTERNAL   /* Access to protected structures in ip_fw.h. */
#include <netinet/ip_fw.h>
#include <netinet/ip_dummynet.h>
#include <alias.h>

#define MAX_TOKEN	1024

#if __FreeBSD_version >= 700000
#define ipfw_insn_pipe ipfw_insn
#endif

/* Check if extended tables are supported */
#ifdef IP_FW_TABLE_XADD
#define IPFW_EXTENDED_TABLES
#endif

/* init macro */
#define START_LINE \
	bzero(actbuf, sizeof(actbuf)); \
        bzero(cmdbuf, sizeof(cmdbuf)); \
        bzero(rulebuf, sizeof(rulebuf)); \
        cmd = (ipfw_insn *)cmdbuf; \
	action = (ipfw_insn *)actbuf; \
	rule = (struct ip_fw *)rulebuf; \
	is_not = 0; \
	empty_rule = 0; \
	curr_proto[0] = 0; \
	have_state = have_log = have_altq = have_tag = NULL; \
	prev = save_label = NULL; \
	save_action = NULL; \
	STAILQ_INIT(&addr_head); \
	SLIST_INIT(&port_head); \
	SLIST_INIT(&icmp_head)

/* external variables */
extern unsigned int line, rule_base, rule_step, quiet, debug, ignore_unresolved, only_test, unclean_test, enable_ipv6;
extern struct ip_fw *rules[];
#ifdef HAS_DUMMYNET2
extern struct dn_pipe *dummynet[];
#endif
#ifdef HAS_IPFWNAT
extern struct cfg_nat *nat_rules[];
#endif
extern int rule_line[];
extern int rule_count, dummynet_count, nat_count, table_count;
extern uint32_t rule_num;
extern int verbose_limit;

/* static variables */
#define MAX_RULESIZE 512
#define LARGE_NUMINSN 16384
static uint32_t rulebuf[LARGE_NUMINSN], actbuf[LARGE_NUMINSN], cmdbuf[LARGE_NUMINSN];
static int empty_rule = 0;
char curr_proto[32];
ipfw_insn *src, *dst, *cmd, *action, *prev=NULL;
ipfw_insn *have_state = NULL, *have_log = NULL, *have_altq = NULL, *have_tag = NULL;
struct ip_fw *rule;
#ifdef HAS_DUMMYNET2
struct dn_pipe dn;
#endif
#ifdef HAS_IPFWNAT
struct cfg_nat cn;
#endif
size_t len;
long bw_val;
int action_opcode;
struct port_list *port_prev;
struct icmp_list *icmp_prev;
struct labels *label_prev, *lhave_prev;
int is_not,optionset=0,altq_fetched=0;
uint8_t set=0, clear=0;
uint32_t last_rule_num;
static TAILQ_HEAD(, pf_altq) altq_entries =
        TAILQ_HEAD_INITIALIZER(altq_entries);


enum {
	ADDR_IPV4,
	ADDR_IPV6,
	ADDR_TABLE,
	ADDR_HOSTNAME
};

/* list descriptions */
STAILQ_HEAD(addr_list_head, addr_list) addr_head;
struct addr_list {
	int is_not;
	int addr_type;
	in_addr_t ip;
	struct in6_addr ip6;
	char *hostname;
	uint16_t mask;
	unsigned int value;	/* Associated data */
	int line;
#define ME_MASK 65535
	STAILQ_ENTRY(addr_list) next;
};
struct addr_list_head *curr_addr_head = NULL;
struct addr_list *curr_addr_list = NULL;

SLIST_HEAD(port_list_head, port_list) port_head;
struct port_list {
	int is_not;
	uint16_t port1;
	uint16_t port2;
	SLIST_ENTRY(port_list) next;
};

SLIST_HEAD(icmp_list_head, icmp_list) icmp_head;
struct icmp_list {
	uint8_t icmptype;
	SLIST_ENTRY(icmp_list) next;
};

SLIST_HEAD(labels_head, labels) labels_head = SLIST_HEAD_INITIALIZER(labels_head);
SLIST_HEAD(lhave_head, labels) lhave_head = SLIST_HEAD_INITIALIZER(lhave_head);
struct labels {
	char		*name;
	ipfw_insn	*pact;
	unsigned int	line;
	SLIST_ENTRY(labels) next;
};
static char *has_a_label=NULL;
static ipfw_insn *save_label;
static ipfw_insn **save_action;
static ipfw_insn *was_a_label=NULL;

#ifdef IPFW_EXTENDED_TABLES
/* compiled table entry */
struct table_xentry {
	ip_fw3_opheader		op;
	ipfw_table_xentry	xentry;
	STAILQ_ENTRY(table_xentry)	next;
};

STAILQ_HEAD(atables_head, table) atables_head = STAILQ_HEAD_INITIALIZER(atables_head);
STAILQ_HEAD(tables_head, table) tables_head = STAILQ_HEAD_INITIALIZER(tables_head);
struct table {
	char		*name;	/* Table name */
	unsigned int	number;	/* Assigned table number */
	int		used;	/* Is the table resolved? */
	unsigned int	line;
	struct addr_list_head	addrs_head; /* List of hosts in the table */
	STAILQ_HEAD(compiled_head, table_xentry)	compiled_head;	/* List of addresses in the table */
	STAILQ_ENTRY(table) next; /* global tables list */
	STAILQ_ENTRY(table) hnext; /* per-hash tables list */
	STAILQ_ENTRY(table) anext; /* Active tables list */
};

struct table_list {
	STAILQ_HEAD(tlist_head, table)	tables;
};

#define	TABLES_HASH_SIZE	32
struct table_list *tables_hash[TABLES_HASH_SIZE];
extern int table_lower, table_upper;
int table_offset = 0;
struct table_record *table_rec = NULL;
#endif

/* utility functions */
static ipfw_insn *
next_cmd(ipfw_insn *cmd)
{
	cmd += F_LEN(cmd);
	bzero(cmd, sizeof(*cmd));
	return cmd;
}

void
yyerror(const char *s, ...)
{
	va_list ap;
	va_start(ap, s);

	fprintf(stderr,"\n");
	vfprintf(stderr,s,ap);
	fprintf(stderr,": line %d\n", line);
	va_end(ap);
	exit(1);
}

void
yywarning(const char *s, ...)
{
	va_list ap;
	va_start(ap, s);

	fprintf(stderr,"\n");
	vfprintf(stderr,s,ap);
	fprintf(stderr,": line %d\n", line);
	va_end(ap);
	unclean_test = 1;
}

in_addr_t
get_ip(const char *string)
{
       in_addr_t p;

       p = inet_addr(string);
       if(p == INADDR_NONE && strcmp(string, "255.255.255.255") != 0)
	      yyerror("Wrong IP: %s", string);

       return p;
}

struct in6_addr
get_ip6(const char *string)
{
        struct in6_addr p;

	if (inet_pton(AF_INET6, string, &p) != 1)
		return p;

	return p;
}

void
add_proto(char *proto, int flags)
{
	struct protoent *p;

	strncpy(curr_proto, proto, 31);

	/* if proto == "all" or "ip", do not set either */
	if(strcmp(proto, "all") != 0 && strcmp(proto, "ip") != 0 && strcmp(proto, "ip6") != 0) {
		p = getprotobyname(proto);
		if(p == NULL)
			yyerror("Unknown protocol: %s", proto);
		cmd->opcode = O_PROTO;
		cmd->len = flags | 1;
		cmd->arg1 = p->p_proto;
		if(prev)
			prev->len |= F_OR;
		prev = cmd;
		cmd = next_cmd(cmd);
	}
	if(debug)
		fprintf(stderr, "proto: %s ", proto);
}

void
fill_iface(char *iface)
{
	((ipfw_insn_if *)cmd)->name[0] = '\0';
	((ipfw_insn_if *)cmd)->o.len |= F_INSN_SIZE(ipfw_insn_if);

	if(is_not)
		cmd->len |= F_NOT;
	is_not = 0;
	if (strcmp(iface, "any") == 0)
		((ipfw_insn_if *)cmd)->o.len = 0;
	else if (!isdigit(*iface)) {
		strlcpy(((ipfw_insn_if *)cmd)->name, iface, sizeof(((ipfw_insn_if *)cmd)->name));
		((ipfw_insn_if *)cmd)->p.glob = strpbrk(iface, "*?[") != NULL ? 1 : 0;
	} else
		yyerror("interface name error: %s", iface);
}

static void
fill_ip6_mask(struct in6_addr *mask, unsigned int len) {
	int i = 0;
	if (len > 128)
		yyerror("Invalid IPv6 netmask %u\n", len);
	while (len >= 8) {
		mask->s6_addr[i++] = 0xff;
		len -= 8;
	}
	if (len > 0)
		mask->s6_addr[i++] = (0xff << (8-len));
	while (i < 16) {
		mask->s6_addr[i++] = 0;
	}
}

void
fill_addr_port_set(int from)
{
	struct addr_list *addr_entry, *addr_temp;
	struct port_list *port_entry, *port_temp;
	int i=0;
	int skipped_conds = 0;
	uint16_t *p;

	prev = NULL;
	STAILQ_FOREACH_SAFE(addr_entry, &addr_head, next, addr_temp) {
	        if (addr_entry->addr_type == ADDR_IPV6 && !addr_entry->is_not && !enable_ipv6) {
	                skipped_conds = 1;
	                STAILQ_REMOVE(&addr_head, addr_entry, addr_list, next);
	                free(addr_entry);
	                continue;
	        }
		if( i > 0 ) 
			prev->len |= F_OR;
		if(addr_entry->is_not)
			cmd->len |= F_NOT;
		cmd->len &= ~F_LEN_MASK;

		if (addr_entry->addr_type == ADDR_IPV6) {
        		if(addr_entry->mask == ME_MASK) {
        			/* /ME_MASK means "me" */
        			cmd->len |= F_INSN_SIZE(ipfw_insn);
        			cmd->opcode = from ? O_IP6_SRC_ME : O_IP6_DST_ME;
        		} else {
        			((ipfw_insn_ip6*)cmd)->addr6 = addr_entry->ip6;
        			if(addr_entry->mask != 128) {
					fill_ip6_mask(&((ipfw_insn_ip6*)cmd)->mask6, addr_entry->mask);
        				cmd->opcode = from ? O_IP6_SRC_MASK : O_IP6_DST_MASK;
        				cmd->len |= F_INSN_SIZE(ipfw_insn_ip6);
        			} else {
        				cmd->opcode = from ? O_IP6_SRC : O_IP6_DST;
        				cmd->len |= (F_INSN_SIZE(ipfw_insn) + 4);
				}
        		}
		} else {
			uint32_t *d;
			d = ((ipfw_insn_u32*)cmd)->d;
        		if(addr_entry->addr_type == ADDR_TABLE) {
        			cmd->opcode = from ? O_IP_SRC_LOOKUP : O_IP_DST_LOOKUP;

        			((ipfw_insn_ip*)cmd)->o.arg1 = addr_entry->mask;
				/* This is a type conversion, not a substraction! */
        			if(addr_entry->ip != (in_addr_t)-1) {
        				((ipfw_insn_ip*)cmd)->o.len |= F_INSN_SIZE(ipfw_insn_u32);
        				d[0] = addr_entry->ip;
        			} else
        				((ipfw_insn_ip*)cmd)->o.len |= F_INSN_SIZE(ipfw_insn);
        		} else if(addr_entry->mask == ME_MASK) {
        			/* /ME_MASK means "me" */
        			cmd->len |= F_INSN_SIZE(ipfw_insn);
        			cmd->opcode = from ? O_IP_SRC_ME : O_IP_DST_ME;
        		} else {
        			d[0] = addr_entry->ip;
        			d[1] = htonl(~0 << (32 - addr_entry->mask));
        			d[0] &= d[1];
        			if(addr_entry->mask != 32) {
        				cmd->opcode = from ? O_IP_SRC_MASK : O_IP_DST_MASK;
        				cmd->len |= 3;
        			} else {
        				cmd->opcode = from ? O_IP_SRC : O_IP_DST;
	        			cmd->len |= F_INSN_SIZE(ipfw_insn_u32);
				}
        		}
		}
		prev = cmd;
		cmd = next_cmd(cmd);

                i++;
		/* XXX warning on inet_ntoa argument on 5.x
		if(debug)
			fprintf(stderr, "%s: %s, mask: %d ", from ? "from-ip" : "to-ip", inet_ntoa(addr_entry->ip), addr_entry->mask);
		*/

		STAILQ_REMOVE(&addr_head, addr_entry, addr_list, next);
		free(addr_entry);

	}
	if (i == 0 && skipped_conds)
	        empty_rule = 1;

	i=0; prev=NULL;
	p = ((ipfw_insn_u16*)cmd)->ports;
	SLIST_FOREACH_SAFE(port_entry, &port_head, next, port_temp) {
		if(from)
			cmd->opcode = O_IP_SRCPORT;
		else
			cmd->opcode = O_IP_DSTPORT;

		if(port_entry->is_not)
			cmd->len |= F_NOT;
		p[0] = port_entry->port1;
		p[1] = port_entry->port2;

		SLIST_REMOVE(&port_head, port_entry, port_list, next);
		free(port_entry);

		i++;
		p += 2;
		if(debug)
			fprintf(stderr, "%s: %hd-%hd ", from ? "from-port" : "to-port", port_entry->port1, port_entry->port2);
	}
	if(i > 0) {
		((ipfw_insn_ip*)cmd)->o.len |= i + 1;
		cmd = next_cmd(cmd);
	}
}

static struct addr_list *
add_addr_to_list(in_addr_t ip, uint16_t mask, int is_not)
{
	struct addr_list *ip_entry = calloc(1, sizeof(struct addr_list));

	if(mask > 32 && mask != ME_MASK)
		yyerror("Invalid network mask: %d", mask);

	ip_entry->ip = ip;
	ip_entry->mask = mask;
	ip_entry->is_not = is_not;
	ip_entry->addr_type = ADDR_IPV4;

	STAILQ_INSERT_HEAD(curr_addr_head, ip_entry, next);
}

static struct addr_list *
add_addr6_to_list(struct in6_addr ip6, uint16_t mask, int is_not)
{
	struct addr_list *ip_entry;

	if(mask > 128 && mask != ME_MASK)
		yyerror("Invalid network6 mask: %d", mask);

	ip_entry = calloc(1, sizeof(struct addr_list));
	ip_entry->ip6 = ip6;
	ip_entry->mask = mask;
	ip_entry->is_not = is_not;
	ip_entry->addr_type = ADDR_IPV6;

	STAILQ_INSERT_HEAD(curr_addr_head, ip_entry, next);
}

#ifdef IPFW_EXTENDED_TABLES
static struct addr_list *
add_table_to_list(in_addr_t filter, uint16_t number, int is_not)
{
	struct addr_list *ip_entry = calloc(1, sizeof(struct addr_list));

	ip_entry->ip = filter;
	ip_entry->mask = number;
	ip_entry->is_not = is_not;
	ip_entry->addr_type = ADDR_TABLE;

	STAILQ_INSERT_HEAD(curr_addr_head, ip_entry, next);
}
#endif

static struct addr_list *
add_host_to_list(char *hostname, int line, int is_not)
{
	struct addr_list *ip_entry = calloc(1, sizeof(struct addr_list));

	if (debug)
		fprintf(stderr, "Added host %s, line %d\n", hostname, line);

	ip_entry->hostname = strdup(hostname);
	ip_entry->line = line;
	ip_entry->is_not = is_not;
	ip_entry->addr_type = ADDR_HOSTNAME;

	STAILQ_INSERT_HEAD(curr_addr_head, ip_entry, next);
}

void
add_port_to_list(uint16_t port1, uint16_t port2, int is_not)
{
	struct port_list *port_entry = malloc(sizeof(struct port_list));

	port_entry->port1 = port1;
	port_entry->port2 = port2;
	port_entry->is_not = is_not;

	if(SLIST_EMPTY(&port_head)) {
		SLIST_INSERT_HEAD(&port_head, port_entry, next);
		port_prev = port_entry;
	} else {
		SLIST_INSERT_AFTER(port_prev, port_entry, next);
		port_prev = port_entry;
	}
}

void
add_port(char *port)
{
	struct servent *serv;
	char str[32], *p;

	strncpy(str, port, 31);
	if((p = strchr(str, '\\')) != NULL)
		strcpy(p, p+1);

	/*
	 * XXX if not tcp|udp, use tcp by default to detect a port number.
	 * It's not quite corecctly and will work only for "all" and "ip" proto.
	 */
	if(strcmp(curr_proto, "tcp") != 0 && strcmp(curr_proto, "udp") != 0)
		strcpy(curr_proto, "tcp");

	if((serv = getservbyname(str, curr_proto)) == NULL)
		yyerror("port name error: %s", port);

	add_port_to_list(ntohs(serv->s_port), ntohs(serv->s_port), is_not);
	is_not = 0;

}

static void
altq_fetch()
{
        struct pfioc_altq pfioc;
        struct pf_altq *altq;
        int pffd, mnr;

        if (altq_fetched)
                return;
        altq_fetched = 1;
        pffd = open("/dev/pf", O_RDONLY);
        if (pffd == -1) {
                warn("altq support opening pf(4) control device");
                return;
        }
        bzero(&pfioc, sizeof(pfioc));
        if (ioctl(pffd, DIOCGETALTQS, &pfioc) != 0) {
                warn("altq support getting queue list");
                close(pffd);
                return;
        }
        mnr = pfioc.nr;
        for (pfioc.nr = 0; pfioc.nr < mnr; pfioc.nr++) {
                if (ioctl(pffd, DIOCGETALTQ, &pfioc) != 0) {
                        if (errno == EBUSY)
                                break;
                        warn("altq support getting queue list");
                        close(pffd);
                        return;
                }
                if (pfioc.altq.qid == 0)
                        continue;
                altq = malloc(sizeof(*altq));
                if (altq == NULL)
                        err(1, "malloc");
                *altq = pfioc.altq;
                TAILQ_INSERT_TAIL(&altq_entries, altq, entries);
        }
        close(pffd);
}

static u_int32_t
altq_name_to_qid(const char *name)
{
        struct pf_altq *altq;

        altq_fetch();
        TAILQ_FOREACH(altq, &altq_entries, entries)
                if (strcmp(name, altq->qname) == 0)
                        break;
        if (altq == NULL)
                errx(1, "altq has no queue named `%s'", name);
        return altq->qid;
}

#ifdef HAS_IPFWNAT
static void
set_addr_dynamic(const char *ifn, struct cfg_nat *n)
{
	size_t needed;
	int mib[6];
	char *buf, *lim, *next;
	struct if_msghdr *ifm;
	struct ifa_msghdr *ifam;
	struct sockaddr_dl *sdl;
	struct sockaddr_in *sin;
	int ifIndex, ifMTU;

	mib[0] = CTL_NET;
	mib[1] = PF_ROUTE;
	mib[2] = 0;
	mib[3] = AF_INET;	
	mib[4] = NET_RT_IFLIST;
	mib[5] = 0;		
/*
 * Get interface data.
 */
	if (sysctl(mib, 6, NULL, &needed, NULL, 0) == -1)
		err(1, "iflist-sysctl-estimate");
	buf = malloc(needed);
	if (sysctl(mib, 6, buf, &needed, NULL, 0) == -1)
		err(1, "iflist-sysctl-get");
	lim = buf + needed;
/*
 * Loop through interfaces until one with
 * given name is found. This is done to
 * find correct interface index for routing
 * message processing.
 */
	ifIndex	= 0;
	next = buf;
	while (next < lim) {
		ifm = (struct if_msghdr *)next;
		next += ifm->ifm_msglen;
		if (ifm->ifm_version != RTM_VERSION) {
			if (!quiet)
				warnx("routing message version %d "
				    "not understood", ifm->ifm_version);
			continue;
		}
		if (ifm->ifm_type == RTM_IFINFO) {
			sdl = (struct sockaddr_dl *)(ifm + 1);
			if (strlen(ifn) == sdl->sdl_nlen &&
			    strncmp(ifn, sdl->sdl_data, sdl->sdl_nlen) == 0) {
				ifIndex = ifm->ifm_index;
				ifMTU = ifm->ifm_data.ifi_mtu;
				break;
			}
		}
	}
	if (!ifIndex)
		errx(1, "unknown interface name %s", ifn);
/*
 * Get interface address.
 */
	sin = NULL;
	while (next < lim) {
		ifam = (struct ifa_msghdr *)next;
		next += ifam->ifam_msglen;
		if (ifam->ifam_version != RTM_VERSION) {
			if (!quiet)
				warnx("routing message version %d "
				    "not understood", ifam->ifam_version);
			continue;
		}
		if (ifam->ifam_type != RTM_NEWADDR)
			break;
		if (ifam->ifam_addrs & RTA_IFA) {
			int i;
			char *cp = (char *)(ifam + 1);

			for (i = 1; i < RTA_IFA; i <<= 1) {
				if (ifam->ifam_addrs & i)
					cp += SA_SIZE((struct sockaddr *)cp);
			}
			if (((struct sockaddr *)cp)->sa_family == AF_INET) {
				sin = (struct sockaddr_in *)cp;
				break;
			}
		}
	}
	if (sin == NULL)
		errx(1, "%s: cannot get interface address", ifn);

	n->ip = sin->sin_addr;
	strncpy(n->if_name, ifn, IF_NAMESIZE);

	free(buf);
}
#endif

struct addrinfo *
y_gethostbyname(const char *name)
{
	struct addrinfo *r;
	struct addrinfo hints = { .ai_flags = AI_PASSIVE,
				 .ai_family = PF_UNSPEC,
				 .ai_socktype = PF_INET };
	
	if (getaddrinfo(name, NULL, &hints, &r) != 0)
		return NULL;
	if (strcasecmp(name, "any.yandex.ru") == 0 || strcasecmp(name, "new-any.yandex.ru") == 0)
		return r;
	uint32_t ra = ((struct sockaddr_in*)r->ai_addr)->sin_addr.s_addr;
	if (r->ai_family == AF_INET && (ra == htonl(0xd5b4ccf2) || ra == htonl(0x5d9e81ab)))
		return NULL;
	return r;
}

int
split_rule(struct ip_fw *rule, struct ip_fw **r1, struct ip_fw **r2)
{
	int j, src_num = 0, dst_num = 0, split_num=0, split_src;
	int i1=0, i2=0;
	ipfw_insn *cmd;
	*r1=malloc(RULESIZE(rule));
	*r2=malloc(RULESIZE(rule));
	struct ip_fw *rule1 = *r1;
	struct ip_fw *rule2 = *r2;

	if(debug)
		printf("\nsplit rule %d: size %d", rule->rulenum, RULESIZE(rule));

	for (j = rule->act_ofs, cmd = rule->cmd ;
		j > 0 && cmd->opcode != 0; j -= F_LEN(cmd) , cmd += F_LEN(cmd)) {
		if (cmd->opcode == O_IP_SRC || cmd->opcode == O_IP_SRC_MASK || cmd->opcode == O_IP6_SRC || cmd->opcode == O_IP6_SRC_MASK)
			src_num++;
		if (cmd->opcode == O_IP_DST || cmd->opcode == O_IP_DST_MASK || cmd->opcode == O_IP6_DST || cmd->opcode == O_IP6_DST_MASK)
			dst_num++;
	}
	if (src_num > dst_num) {
		split_num = src_num / 2;
		split_src = 1;
	} else {
		split_num = dst_num / 2;
		split_src = 0;
	}

	bcopy(rule, rule1, sizeof(struct ip_fw));
	bcopy(rule, rule2, sizeof(struct ip_fw));

	src_num = dst_num = 0;
	for (j = rule->act_ofs, cmd = rule->cmd ;
		j > 0 && cmd->opcode != 0; j -= F_LEN(cmd), cmd += F_LEN(cmd)) {
		if (cmd->opcode == O_IP_SRC || cmd->opcode == O_IP_DST ||
			cmd->opcode == O_IP_SRC_MASK || cmd->opcode == O_IP_DST_MASK ||
			cmd->opcode == O_IP6_SRC || cmd->opcode == O_IP6_DST || 
			cmd->opcode == O_IP6_SRC_MASK || cmd->opcode == O_IP6_DST_MASK) {
			if(split_src && (cmd->opcode == O_IP_SRC || cmd->opcode == O_IP_SRC_MASK || cmd->opcode == O_IP6_SRC || cmd->opcode == O_IP6_SRC_MASK)) {
				src_num++;
				if(src_num > split_num) {
					bcopy(cmd, rule2->cmd+i2, F_LEN(cmd)*sizeof(ipfw_insn));
					i2 += F_LEN(cmd);
				} else {
					if(src_num == split_num)
						cmd->len &= ~F_OR;
					bcopy(cmd, rule1->cmd+i1, F_LEN(cmd)*sizeof(ipfw_insn));
					i1 += F_LEN(cmd);
				}
				continue;
			}
			if(!split_src && (cmd->opcode == O_IP_DST || cmd->opcode == O_IP_DST_MASK || cmd->opcode == O_IP6_DST || cmd->opcode == O_IP6_DST_MASK)) {
				dst_num++;
				if(dst_num > split_num) {
					bcopy(cmd, rule2->cmd+i2, F_LEN(cmd)*sizeof(ipfw_insn));
					i2 += F_LEN(cmd);
				} else {
					if(dst_num == split_num)
						cmd->len &= ~F_OR;
					bcopy(cmd, rule1->cmd+i1, F_LEN(cmd)*sizeof(ipfw_insn));
					i1 += F_LEN(cmd);
				}
				continue;
			}
		}
		bcopy(cmd, rule1->cmd+i1, F_LEN(cmd)*sizeof(ipfw_insn));
		bcopy(cmd, rule2->cmd+i2, F_LEN(cmd)*sizeof(ipfw_insn));
		i1 += F_LEN(cmd);
		i2 += F_LEN(cmd);
	}
	rule1->act_ofs = i1;
	rule2->act_ofs = i2;
	bcopy(ACTION_PTR(rule), ACTION_PTR(rule1), (rule->cmd_len-rule->act_ofs)*sizeof(ipfw_insn));
	bcopy(ACTION_PTR(rule), ACTION_PTR(rule2), (rule->cmd_len-rule->act_ofs)*sizeof(ipfw_insn));
	rule1->cmd_len = rule1->act_ofs+rule->cmd_len-rule->act_ofs;
	rule2->cmd_len = rule2->act_ofs+rule->cmd_len-rule->act_ofs;
	return RULESIZE(rule1) < RULESIZE(rule) && RULESIZE(rule2) < RULESIZE(rule);
}

static void
add_rule(struct ip_fw *rule)
{
	struct ip_fw *rule1, *rule2;
	/* If the rule too long, split it on two */
	if(RULESIZE(rule) > MAX_RULESIZE && split_rule(rule, &rule1, &rule2)) {
		if(debug)
			printf(" to rule1: %d and rule2: %d\n", RULESIZE(rule1), RULESIZE(rule2));
		add_rule(rule1);
		add_rule(rule2);

		free(rule1);
		free(rule2);

	} else {
		if((rules[rule_count] = malloc(RULESIZE(rule))) == NULL)
			errx(1, "\nmemory error");
		bcopy(rule, rules[rule_count], RULESIZE(rule));
		if(save_label)
			*save_action = rules[rule_count]->cmd+rules[rule_count]->act_ofs;
		rule_line[rule_count] = line;
		rule_count++;
	}
}

#ifdef IPFW_EXTENDED_TABLES
static void
init_tables()
{
	memset(tables_hash, 0, sizeof(tables_hash));
}

static int
hash_table(char *tablename)
{
	int i = 0;
	char *c = tablename;

	while (*c)
		i += *c++;

	return i % TABLES_HASH_SIZE;
}


static struct table *
find_table(char *tablename)
{
	int i = hash_table(tablename);
	struct table_list *tl;
	struct table *table;

	if (tables_hash[i] == NULL)
		return NULL;

	tl = tables_hash[i];

	STAILQ_FOREACH(table, &tl->tables, next) {
		if (!strcmp(table->name, tablename))
			return table;
	}

	return NULL;
}

static struct table *
get_table(char *tablename)
{
	int i = hash_table(tablename);
	struct table_list *tl;
	struct table *table;

	if (tables_hash[i] == NULL) {
		tl = malloc(sizeof(struct table_list));
		STAILQ_INIT(&tl->tables);
		tables_hash[i] = tl;
	}

	tl = tables_hash[i];

	STAILQ_FOREACH(table, &tl->tables, next) {
		if (!strcmp(table->name, tablename))
			return table;
	}

	/* Not found. */
	table = calloc(1, sizeof(struct table));
	if (table_count + table_lower > table_upper)
		errx(1, "Table range exceeded: used: %d\n", table_count);
	table->number = table_count++ + table_lower;
	table->name = strdup(tablename);
	STAILQ_INIT(&table->addrs_head);
	STAILQ_INIT(&table->compiled_head);

	/* Add to global and per-hash list */
	STAILQ_INSERT_TAIL(&tables_head, table, next);
	STAILQ_INSERT_TAIL(&tl->tables, table, hnext);

	if (debug)
		fprintf(stderr, "Mapping table %s to number %d\n", tablename, table->number);

	return table;
}

static void *
compile_table_entry(struct table *table, struct addr_list *l, int addr_type, void *addr_data)
{
	struct table_xentry *xe;
	ipfw_table_xentry *x;
	int len;

	xe = calloc(1, sizeof(struct table_xentry));
	x = &xe->xentry;

	xe->op.opcode = IP_FW_TABLE_XADD;

	x->type = IPFW_TABLE_CIDR;
	x->tbl = table->number;
	x->value = l->value;

	if(addr_type == ADDR_IPV6) {
		len = sizeof(struct in6_addr);
		x->masklen = (l->addr_type == ADDR_HOSTNAME) ? 128 : l->mask;
		x->k.addr6 = *((struct in6_addr *)addr_data);
	} else {
		len = sizeof(struct in_addr);
		x->masklen = (l->addr_type == ADDR_HOSTNAME) ? 32 : l->mask;
		x->k.addr6.__u6_addr.__u6_addr32[0] = *((in_addr_t *)addr_data);
	}

	x->len = offsetof(struct _ipfw_table_xentry, k) + len;

	return xe;
}

void
decompile_table_entry(struct table_xentry *xe, char *buf, int buflen)
{
	char abuf[64];
	int af = (xe->xentry.len - offsetof(struct _ipfw_table_xentry, k) == sizeof(struct in_addr)) ? AF_INET : AF_INET6;

	inet_ntop(af, &xe->xentry.k, abuf, sizeof(abuf));

	snprintf(buf, buflen, "addr=%s/%d val=%d len=%d", abuf, xe->xentry.masklen, xe->xentry.value, xe->xentry.len);
}


static void
resolve_table(struct table *table)
{
	struct addr_list *l;
	struct addrinfo *ai, *res;
	struct table_xentry *xe;
	int addr_type;
	void *addr_data;
	int count = 0;

	if (table->used)
		return;

	if (debug)
		fprintf(stderr, "Resolving table %d (%s)\n", table->number, table->name);

	STAILQ_FOREACH(l, &table->addrs_head, next) {
		if (debug)
			fprintf(stderr, "Record type %d\n", l->addr_type);
		switch (l->addr_type) {
		case ADDR_IPV4:
			xe = compile_table_entry(table, l, ADDR_IPV4, &l->ip);
			STAILQ_INSERT_TAIL(&table->compiled_head, xe, next);
			count++;
			break;
		case ADDR_IPV6:
			xe = compile_table_entry(table, l, ADDR_IPV6, &l->ip6);
			STAILQ_INSERT_TAIL(&table->compiled_head, xe, next);
			count++;
			break;
		case ADDR_HOSTNAME:
			/* We have to resolve all hosts */

			if ((res = y_gethostbyname(l->hostname)) == NULL) {
				if(!ignore_unresolved) {
					if (only_test) {
						yywarning("can't resolve host: %s", l->hostname);
						break;
					} else 
						yyerror("can't resolve host: %s", l->hostname);
				} else {
					printf("Line %d: can't resolve host: %s. Ignored.\n", l->line, l->hostname);
					continue;
				}
			}

			if(debug)
				fprintf(stderr, "domain:%s ", l->hostname);

			for(ai = res; ai != NULL; ai = ai->ai_next) {
				if(ai->ai_family == AF_INET6) {
					addr_type = ADDR_IPV6;
					addr_data = &((struct sockaddr_in6*)ai->ai_addr)->sin6_addr;
				} else {
					addr_type = ADDR_IPV4;
					addr_data = &((struct sockaddr_in*)ai->ai_addr)->sin_addr.s_addr;
				}
/*
				char data[64];
				inet_ntop(ai->ai_family, addr_data, data, sizeof(data));

				printf("table %s host %s resolved to %s\n", table->name, l->hostname, data);
*/
				xe = compile_table_entry(table, l, addr_type, addr_data);
/*				
				decompile_table_entry(xe, data, sizeof(data));
				printf("table %s host %s resolved to %s\n", table->name, l->hostname, data);
*/				
				STAILQ_INSERT_TAIL(&table->compiled_head, xe, next);
				count++;
			}

			break;
		}
	}

	if (debug)
		fprintf(stderr, "%d hosts in table %s\n", count, table->name);

	/* Copy table to active list */
	STAILQ_INSERT_TAIL(&atables_head, table, anext);

	/* Mark as resolved */
	table->used = 1;
}
#endif

%}

%start commands

%token ACK ADD ALL ALLOW ANTISPOOF ANY BW BWBS BWBTS BWKBS BWKBTS BWMBS BWMBTS
       BUCKETS CC CHECKSTATE COMMA CONFIG CONGESTION COUNT PDELAY DENY DENY_IN
       DROPTAIL DSTADDR DSTIP DSTPORT EBRACE EOL ESTABLISHED FIN FILTERPROHIB
       FLOAT FLOWID FQDN FRAG FROM FWD HEXMASK HOST HOSTUNKNOWN HOSTPROHIB
       HOSTPRECEDENCE ICMPTYPES ICMP6TYPES IN IF IP IP6 DIVERT TEE DIVERTED
       DIVERTEDLOOPBACK DIVERTEDOUTPUT ALTQ SETIPPREC IPLEN IPOPTIONS IPTOS
       IPTTL ISOLATED KEEPSTATE LBRACE LIMIT LOG LOGAMOUNT LOWDELAY LSRR MASK
       ME ME6 MINCOST MSS NAT NEEDFRAG NET NETGRAPH NETPROHIB NETWORK NETWORK6
       NETUNKNOWN T_IP NOERROR NOT NOTCHAR NUMBER OBRACE OR OUT PIPE PLR PORT
       PRECEDENCECUTOFF PROTO PROTOCOL PROXY_ONLY PSH QUEUE RANGE RBRACE RECV
       REASS RED REDPARAM REDIRECT_ADDR REDIRECT_PORT REDIRECT_PROTO REJECTT
       RELIABILITY RESET REVERSE RR RST SACK SAME_PORTS SETUP SIZEK SKIPTO
       SRCADDR SRCFAIL SRCIP SRCPORT SSRR SYN TABLE TAG TCPDATALEN TCPFLAGS
       TCPOPTIONS TCPSEQ THROUGHPUT TO TOKEN TOSHOST TOSNET TS UNREACH
       UNREG_ONLY URG VIA VERREVPATH VERSRCREACH WEIGHT WINDOW XMIT LABEL
       EXT6HDR HOPOPT ROUTE DSTOPT AH ESP RTHDR0 RTHDR2 IPSEC IPVER COMMENT
       TABLENAME

%union {
	long		ival;
	float		fval;
	char		sval[MAX_TOKEN];
};

%%

commands: 
	| commands command
	;
command:
     	LABEL EOL
	{
		struct labels *label_entry, *lhave_entry;

		/* align to 100 */
		rule_num = (rule_num-rule_num%100)+100;
		has_a_label=strdup($1.sval);

		lhave_entry = malloc(sizeof(struct labels));
		lhave_entry->name = strdup($1.sval);
		if(SLIST_EMPTY(&lhave_head)) {
			SLIST_INSERT_HEAD(&lhave_head, lhave_entry, next);
			lhave_prev = lhave_entry;
		} else {
			SLIST_FOREACH(label_entry, &lhave_head, next) {
				if(strcmp(label_entry->name, $1.sval) == 0)
					yyerror("dublicate label '%s'", label_entry->name);
			}
			SLIST_INSERT_AFTER(lhave_prev, lhave_entry, next);
			lhave_prev = lhave_entry;
		}

		SLIST_FOREACH(label_entry, &labels_head, next) {
			if(strcmp(label_entry->name, $1.sval) == 0) {
				if(label_entry->pact == NULL)
					yyerror("internal error (add label)");
				label_entry->pact->arg1 = rule_num;
			}
		}
	}
	|
        nat
	{
#ifdef HAS_IPFWNAT
		nat_rules[nat_count] = malloc(sizeof(struct cfg_nat));
		bcopy(&cn, nat_rules[nat_count], sizeof(struct cfg_nat));
		nat_count++;

		bzero(&cn, sizeof(cn));
#else
		yyerror("embedded NAT is not supported on this system");
#endif
	}
	|
        pipequeue
	{
#ifdef HAS_DUMMYNET2
		dummynet[dummynet_count] = malloc(sizeof(struct dn_pipe));
		bcopy(&dn, dummynet[dummynet_count], sizeof(struct dn_pipe));
		dummynet_count++;

		bzero(&dn, sizeof(dn));
#else
                yyerror("dummynet is not supported yet");
#endif
	}
	|
	table
        |
	add
	{
		if(debug) {
			fprintf(stderr, "ADD RULE #%d ", rule->rulenum);
			switch(action_opcode)
			{
				case O_ACCEPT:	
						fprintf(stderr, "allow ");
						break;
				case O_DENY:	
						fprintf(stderr, "deny ");
						break;
				case O_REJECT:	
						fprintf(stderr, "reject ");
						break;
				case O_FORWARD_IP:	
						fprintf(stderr, "fwd ");
						break;
				case O_SKIPTO:	
						fprintf(stderr, "skipto ");
						break;
				case O_COUNT:	
						fprintf(stderr, "count ");
						break;
				case O_CHECK_STATE: 
						fprintf(stderr, "check-state ");
						break;
			};
		}

		rule->set = 1;
		int i=0;
		dst = (ipfw_insn *)rule->cmd;

		/* If there is check-state, set PROBE_STATE as the first command */
		if (have_state && have_state->opcode != O_CHECK_STATE) {
			dst->opcode = O_PROBE_STATE;
			dst->len = 1;
			dst->arg1 = 0;
			dst = next_cmd(dst);
		}

		for (src = (ipfw_insn *)cmdbuf; src != cmd; src += i) {
			i = F_LEN(src);

			switch (src->opcode) {
				case O_LOG:
				case O_KEEP_STATE:
				case O_LIMIT:
				case O_ALTQ:
				case O_TAG:
					break;
				default:
					bcopy(src, dst, i * sizeof(ipfw_insn));
					dst += i;
			}
		}

		if (have_state && have_state->opcode != O_CHECK_STATE) {
			i = F_LEN(have_state);
			bcopy(have_state, dst, i * sizeof(ipfw_insn));
			dst += i;
		}

		/* we copied cmd, action then */
		rule->act_ofs = dst - rule->cmd;
		/* LOG first if is */
		if (have_log) {
			i = F_LEN(have_log);
			bcopy(have_log, dst, i * sizeof(ipfw_insn));
			dst += i;
		}
		if (have_altq) {
			i = F_LEN(have_altq);
			bcopy(have_altq, dst, i * sizeof(ipfw_insn));
			dst += i;
		}
		if (have_tag) {
			i = F_LEN(have_tag);
			bcopy(have_tag, dst, i * sizeof(ipfw_insn));
			dst += i;
		}

		for (src = (ipfw_insn *)actbuf; src != action; src += i) {
			i = F_LEN(src);
			bcopy(src, dst, i * sizeof(ipfw_insn));
			if(src == save_label)
				save_label = dst;
			dst += i;
		}
			
		rule->cmd_len = (uint32_t *)dst - (uint32_t *)(rule->cmd);


		if (!empty_rule) {
        		add_rule(rule);
                } else {
                        if (debug)
                                fprintf(stderr, "EMPTY RULE\n");
                }
                if(debug)
                        fprintf(stderr, " next line: %d\n",line);
	}
	;
add:
	ADD rulenumber action altq tag rule comment EOL
	|
	ADD rulenumber checkstate EOL
	;
comment:
        COMMENT
        {
		if (was_a_label) {
			cmd = was_a_label;
			cmd->len += (strlen($1.sval)+4)/4;
			char *p = (char *)(cmd + 1);
			strcat(p, " ");
			strcat(p, $1.sval);
			cmd = next_cmd(cmd);
		} else {
			char *p = (char *)(cmd + 1);
			cmd->opcode = O_NOP;
			cmd->len = 1 + (strlen($1.sval)+4)/4;
			strcpy(p, $1.sval);
			cmd = next_cmd(cmd);
		}
	}
	|
	;
checkstate:
	CHECKSTATE
	{
		have_state = action;
		action_opcode = action->opcode = O_CHECK_STATE;
		action->len = 1;
		action = next_cmd(action);
	}
	;
table:
	TABLE newtable ADD tablerec tableopts endtable EOL
	;

newtable: TABLENAME {
#ifdef IPFW_EXTENDED_TABLES
		struct table *curr_table = get_table($1.sval);
		curr_addr_head = &curr_table->addrs_head;
#else
		yyerror("eXtended tables are not supported");
#endif
	}
	;
endtable: { curr_addr_head = NULL; } ;

tableopts:
	|
	NUMBER
	{
		curr_addr_list->value = $1.ival;
	}
	;

tablerec:
	IP
	{
		curr_addr_list = add_addr_to_list(get_ip($1.sval), 32, 0);
	}
	|
	NETWORK
	{
		char *mask;
		
		mask = strchr($1.sval, '/');
		*mask = 0;
		mask++;

		curr_addr_list = add_addr_to_list(get_ip($1.sval), atoi(mask), 0);
	}
	|
	IP6
	{
		curr_addr_list = add_addr6_to_list(get_ip6($1.sval), 128, 0);
	}
	|
	NETWORK6
	{
		char *mask;
		
		mask = strchr($1.sval, '/');
		*mask = 0;
		mask++;

		curr_addr_list = add_addr6_to_list(get_ip6($1.sval), atoi(mask), 0);
	}
	|
	hostname
	{
		curr_addr_list = add_host_to_list($1.sval, line, 0);
	}
	;
nat:
   	NAT NUMBER CONFIG natconfig EOL
	{
#ifdef HAS_IPFWNAT
		cn.id = $2.ival;
#else
		yyerror("embedded NAT is not supported on this system");
#endif
	}
	;
natconfig:
	natrule
	|
	natrule natconfig
	;
natrule:
	T_IP IP
	{
#ifdef HAS_IPFWNAT
		if (!inet_aton($2.sval, &(cn.ip)))
			yyerror("bad ip address ``%s''", $2.sval);
#endif
	}
	|
	IF TOKEN
	{
#ifdef HAS_IPFWNAT
		set_addr_dynamic($2.sval, &cn);
#endif
	}
	|
	LOG
	{
#ifdef HAS_IPFWNAT
		cn.mode |= PKT_ALIAS_LOG;
#endif
	}
	|
	DENY_IN
	{
#ifdef HAS_IPFWNAT
		cn.mode |= PKT_ALIAS_DENY_INCOMING;
#endif
	}
	|
	SAME_PORTS
	{
#ifdef HAS_IPFWNAT
		cn.mode |= PKT_ALIAS_SAME_PORTS;
#endif
	}
	|
	UNREG_ONLY
	{
#ifdef HAS_IPFWNAT
		cn.mode |= PKT_ALIAS_UNREGISTERED_ONLY;
#endif
	}
	|
	RESET
	{
#ifdef HAS_IPFWNAT
		cn.mode |= PKT_ALIAS_RESET_ON_ADDR_CHANGE;
#endif
	}
	|
	REVERSE
	{
#ifdef HAS_IPFWNAT
		cn.mode |= PKT_ALIAS_REVERSE;
#endif
	}
	|
	PROXY_ONLY
	{
#ifdef HAS_IPFWNAT
		cn.mode |= PKT_ALIAS_PROXY_ONLY;
#endif
	}
	|
	REDIRECT_ADDR
	{
		yyerror("option redirect_addr is not supported yet");
	}
	|
	REDIRECT_PORT
	{
		yyerror("option redirect_port is not supported yet");
	}
	|
	REDIRECT_PROTO
	{
		yyerror("option redirect_proto is not supported yet");
	}
	;
pipequeue:
	PIPE NUMBER CONFIG pipeconfig EOL
	{
#ifdef HAS_DUMMYNET2
		if($2.ival == 0)
			yyerror("pipe number must be > 0");
		dn.pipe_nr = $2.ival;
#else
                yyerror("dummynet is not supported yet");
#endif
	}
	|
	QUEUE NUMBER CONFIG queueconfig EOL
	{
#ifdef HAS_DUMMYNET2
		if($2.ival == 0)
			yyerror("queue number must be > 0");
		dn.fs.fs_nr = $2.ival;
#else
                yyerror("dummynet is not supported yet");
#endif
	}
	;
pipeconfig:
	pipetoken
	|
	pipetoken pipeconfig
	;
pipetoken:
	BW bandwidth
	{
#ifdef HAS_DUMMYNET2
		dn.if_name[0] = '\0';
		dn.bandwidth = bw_val;
#endif
	}
	|
	BW TOKEN
	{
#ifdef HAS_DUMMYNET2
		strncpy(dn.if_name, $2.sval, sizeof(dn.if_name)-1);
		dn.bandwidth = 0;
#endif
	}
	|
	PDELAY NUMBER
	{
#ifdef HAS_DUMMYNET2
		if($2.ival > 10000)
			yyerror("delay must be <= 10000");

		dn.delay = $2.ival;
#endif
	}
	|
	pipequeueopt
	;
queueconfig:
	queuetoken
	|
	queuetoken queueconfig
	;
queuetoken:
	PIPE NUMBER
	{
#ifdef HAS_DUMMYNET2
		dn.fs.parent_nr = $2.ival;
#endif
	}
	|
	WEIGHT NUMBER
	{
#ifdef HAS_DUMMYNET2
		if($2.ival > 100)
			yyerror("weight must be <= 100");

		dn.fs.weight = $2.ival;
#endif
	}
	|
	pipequeueopt
	;
pipequeueopt:
	BUCKETS NUMBER
	{
#ifdef HAS_DUMMYNET2
		dn.fs.rq_size = $2.ival;
#endif
	}
	|
	MASK mask
	{
#ifdef HAS_DUMMYNET2
		yyerror("mask parameter is not implemented yet ");
#endif
	}
	|
	NOERROR
	{
#ifdef HAS_DUMMYNET2
		dn.fs.flags_fs |= DN_NOERROR;
#endif
	}
	|
	PLR FLOAT
	{
#ifdef HAS_DUMMYNET2
		float plr;

		plr = $2.fval;
		if(plr > 1)
			plr = 1;

		dn.fs.plr = (int)(plr*0x7fffffff);
#endif
	}
	|
	QUEUE SIZEK
	{
#ifdef HAS_DUMMYNET2
		if($2.ival > 1024*1024)
			yyerror("queue size must be <= 1MB");
			
		dn.fs.qsize = $2.ival;
		dn.fs.flags_fs |= DN_QSIZE_IS_BYTES;
#endif
	}
	|
	QUEUE NUMBER
	{
#ifdef HAS_DUMMYNET2
		if($2.ival < 2 || $2.ival > 100)
			yyerror("2 <= queue slots number <= 100");

		dn.fs.qsize = $2.ival;
#endif
	}
	|
	DROPTAIL
	{
#ifdef HAS_DUMMYNET2
		dn.fs.flags_fs &= ~(DN_IS_RED|DN_IS_GENTLE_RED);
#endif
	}
	|
	RED REDPARAM
	{
#ifdef HAS_DUMMYNET2
		double w_q, max_p;
		long min_th, max_th;
		char *p, *p1;

		p = $2.sval;
		w_q = strtod(p, NULL);
		p1 = strchr(p, '/');

		p1++;
		p = p1;
		min_th = strtoul(p, &p, 0);
		if(*p == 'K' || *p == 'k')
			min_th *= 1024;
		p1 = strchr(p, '/');

		p1++;
		p = p1;
		max_th = strtoul(p, NULL, 0);
		if(*p == 'K' || *p == 'k')
			max_th *= 1024;
		p1 = strchr(p, '/');

		p1++;
		p = p1;
		max_p = strtod(p, NULL);

		if (w_q > 1 || w_q == 0)
			yyerror("0 < w_q <= 1");

		if (max_p > 1 || max_p <= 0)
			yyerror("0 < max_p <= 1");

		if(strcmp($1.sval, "gred") != 0)
			dn.fs.flags_fs |= DN_IS_RED;
		else
			dn.fs.flags_fs |= DN_IS_GENTLE_RED;

		dn.fs.w_q = (int) (w_q * (1 << SCALE_RED));
		dn.fs.min_th = min_th;
		dn.fs.max_th = max_th;
		dn.fs.max_p = (int)(max_p * (1 << SCALE_RED));
#endif
	}
	;
bandwidth:
	BWBS
	{
		bw_val = $1.ival;
	}
	|
	BWBTS
	{
		bw_val = $1.ival*8;
	}
	|
	BWKBS
	{
		bw_val = $1.ival*1000;
	}
	|
	BWKBTS
	{
		bw_val = $1.ival*1000*8;
	}
	|
	BWMBS
	{
		bw_val = $1.ival*1000000;
	}
	|
	BWMBTS
	{
		bw_val = $1.ival*1000000*8;
	}
	;
mask:
    	DSTIP HEXMASK
    	{
		yyerror("option dstip is not supported yet");
	}
	|
	SRCIP HEXMASK
    	{
		yyerror("option srcip is not supported yet");
	}
	|
	DSTPORT HEXMASK
    	{
		yyerror("option dstport is not supported yet");
	}
	|
	SRCPORT HEXMASK
    	{
		yyerror("option srcport is not supported yet");
	}
	|
	FLOWID HEXMASK
    	{
		yyerror("option flowid is not supported yet");
	}
	|
	PROTO HEXMASK
    	{
		yyerror("option proto is not supported yet");
	}
	|
	ALL
	;
rulenumber:
	{
		START_LINE;

		if(!has_a_label)
			rule_num += rule_step;

		rule->rulenum = rule_num;
		last_rule_num = rule_num;
	}
	|
      	NUMBER
	{
		START_LINE;

		rule_num = rule->rulenum = (u_int32_t)$1.ival;
		if(rule_num <= last_rule_num)
		      yyerror("Rule number goes back (rule %d)", rule_num);

		last_rule_num = rule_num;
	}
	;
action:
        actiontoken
	|
	actiontoken log
	;
actiontoken:
	NAT NUMBER
	{
#ifdef HAS_IPFWNAT
		action_opcode = action->opcode = O_NAT;
		action->arg1 = $2.ival;
		if (action->arg1 == 0)
			yyerror("illegal argument for %s", $2.sval);
		action->len = F_INSN_SIZE(ipfw_insn_nat);
		action = next_cmd(action);
#endif
	}
	|
	COUNT
	{
		action_opcode = action->opcode = O_COUNT;
		action->len = 1;
		action = next_cmd(action);
	}
	|
	ALLOW
	{
		action_opcode = action->opcode = O_ACCEPT;
		action->len = 1;
		action = next_cmd(action);
	}
	|
	DENY
	{
		action_opcode = action->opcode = O_DENY;
		action->len = 1;
		action = next_cmd(action);
	}
	|
	REJECTT
	{
		action_opcode = action->opcode = O_REJECT;
		action->arg1 = ICMP_UNREACH_HOST;
		action->len = 1;
		action = next_cmd(action);
	}
	|
	FWD IP COMMA NUMBER
	{
		ipfw_insn_sa *p = (ipfw_insn_sa *)action;

		action_opcode = action->opcode = O_FORWARD_IP;
		action->len = F_INSN_SIZE(ipfw_insn_sa);

		p->sa.sin_len = sizeof(struct sockaddr_in);
		p->sa.sin_family = AF_INET;
		p->sa.sin_port = $4.ival;
		p->sa.sin_addr.s_addr = get_ip($2.sval);
		action = next_cmd(action);
	}
	|
	FWD IP
	{
		ipfw_insn_sa *p = (ipfw_insn_sa *)action;

		action_opcode = action->opcode = O_FORWARD_IP;
		action->len = F_INSN_SIZE(ipfw_insn_sa);

		p->sa.sin_len = sizeof(struct sockaddr_in);
		p->sa.sin_family = AF_INET;
		p->sa.sin_port = 0;
		p->sa.sin_addr.s_addr = get_ip($2.sval);
		action = next_cmd(action);
	}
	|
	SKIPTO NUMBER
	{
		action_opcode = action->opcode = O_SKIPTO;
		action->len = 1;
		action->arg1 = (u_int32_t)$2.ival;
		action = next_cmd(action);
	}
	|
	SKIPTO LABEL
	{
		struct labels *label_entry, *lhave_entry;

		action_opcode = action->opcode = O_SKIPTO;
		action->len = 1;
		action->arg1 = 0;
		label_entry = malloc(sizeof(struct labels));
		label_entry->name = strdup($2.sval);
		label_entry->line = line;
		save_label = action;
		save_action = &label_entry->pact;
		action = next_cmd(action);

		SLIST_FOREACH(lhave_entry, &lhave_head, next)
			if(strcmp(lhave_entry->name, label_entry->name) == 0)
				yyerror("skipto label '%s' goes back", label_entry->name);

		if(SLIST_EMPTY(&labels_head)) {
			SLIST_INSERT_HEAD(&labels_head, label_entry, next);
			label_prev = label_entry;
		} else {
			SLIST_INSERT_AFTER(label_prev, label_entry, next);
			label_prev = label_entry;
		}
	}
	|
	DIVERT NUMBER
	{
		action_opcode = action->opcode = O_DIVERT;
		action->len = 1;
		action->arg1 = $2.ival;
		action = next_cmd(action);
	}
	|
	TEE NUMBER
	{
		action_opcode = action->opcode = O_TEE;
		action->len = 1;
		action->arg1 = $2.ival;
		action = next_cmd(action);
	}
	|
	REASS
	{
#if defined(HAS_REASS)
		action_opcode = action->opcode = O_REASS;
		action->len = 1;
		action = next_cmd(action);
#endif
	}
	|
	NETGRAPH NUMBER
	{
		action_opcode = action->opcode = O_NETGRAPH;
		action->len = 1;
		action->arg1 = (u_int32_t)$2.ival;
		action = next_cmd(action);
	}
	|
	SETIPPREC NUMBER
	{
#if defined(HAS_SETIPPREC)
		action_opcode = action->opcode = O_SETIPPREC;
		action->arg1 = (u_int32_t)$2.ival;
		if(action->arg1 > 7)
		    yyerror("setipprec value is out of range");
		action->len = 1;
		action = next_cmd(action);
#else
	        yyerror("setipprec is not supported here");
#endif
	}
	|
	PIPE NUMBER
	{
		action_opcode = action->opcode = O_PIPE;
		action->len = F_INSN_SIZE(ipfw_insn_pipe);
		action->arg1 = (u_int32_t)$2.ival;
		action = next_cmd(action);
	}
	|
	QUEUE NUMBER
	{
		action_opcode = action->opcode = O_QUEUE;
		action->len = F_INSN_SIZE(ipfw_insn_pipe);
		action->arg1 = (u_int32_t)$2.ival;
		action = next_cmd(action);
	}
	;
altq:
	ALTQ TOKEN
	{
		have_altq = cmd;
		cmd->opcode = O_ALTQ;
		cmd->len = F_INSN_SIZE(ipfw_insn_altq);
		((ipfw_insn_altq *)cmd)->qid = altq_name_to_qid($2.sval);
		cmd = next_cmd(cmd);
	}
	|
	;
tag:
        TAG NUMBER
        {
                have_tag = cmd;
                cmd->opcode = O_TAG;
                cmd->len = 1;
                cmd->arg1 = $2.ival;
                cmd = next_cmd(cmd);
        }
        |
        ;
log:
	LOG
	{
		size_t len;

		have_log = cmd;
		cmd->opcode = O_LOG;
		cmd->len = F_INSN_SIZE(ipfw_insn_log);
		len = sizeof(((ipfw_insn_log *)cmd)->max_log);
		((ipfw_insn_log *)cmd)->max_log = verbose_limit;
		cmd = next_cmd(cmd);
		if(debug)
			fprintf(stderr, "log ");
	}
	|
	LOG LOGAMOUNT NUMBER
	{
		have_log = cmd;
		cmd->opcode = O_LOG;
		cmd->len = F_INSN_SIZE(ipfw_insn_log);
		((ipfw_insn_log *)cmd)->max_log = (u_int32_t)$3.ival;
		cmd = next_cmd(cmd);
		if(debug)
			fprintf(stderr, "logamount ");
	}
	;
rule:
    	proto from to options
	{
		/* Add a comment for a rule after label */
		if(has_a_label) {
			char *p = (char *)(cmd + 1);
			cmd->opcode = O_NOP;
			cmd->len = 1 + (strlen(has_a_label)+4)/4;
			strcpy(p, has_a_label);
			cmd = next_cmd(cmd);

			free(has_a_label);
			has_a_label = NULL;
		}
	}
	;
from:
    	FROM statement ports
	{
		fill_addr_port_set(1);
	}
        ;
to:
    	TO statement ports
	{
		fill_addr_port_set(0);
	}
        ;
proto:
        T_IP
	{
		add_proto("ip", 0);
	}
	|
	ALL
	{
		add_proto("all", 0);
	}
	|
	ESP
	{
		add_proto("esp", 0);
	}
	|
	prototoken
	|
	OBRACE protoset EBRACE
	;
prototoken:
        TOKEN
	{
		add_proto($1.sval, 0);
	}
	|
	NOT TOKEN
	{
		add_proto($2.sval, F_NOT);
	}
	;
protoset:
	prototoken OR protoset
	|
	prototoken
	;
statement: statementpre statementbody statementpost;

statementpre: { curr_addr_head = &addr_head; };
statementpost: { curr_addr_head = NULL; };

statementbody:
	statementtoken
	|
	not statementtoken
	|
	OBRACE statementset EBRACE
	;
statementtoken:
	addrdir IP
	{
		add_addr_to_list(get_ip($2.sval), 32, is_not);
		is_not = 0;
	}
	|
	addrdir NETWORK
	{
		char *mask;
		
		mask = strchr($2.sval, '/');
		*mask = 0;
		mask++;

		add_addr_to_list(get_ip($2.sval), atoi(mask), is_not);
		is_not = 0;
	}
	|
	addrdir IP6
	{
		add_addr6_to_list(get_ip6($2.sval), 128, is_not);
		is_not = 0;
	}
	|
	addrdir NETWORK6
	{
		char *mask;
		
		mask = strchr($2.sval, '/');
		*mask = 0;
		mask++;

		add_addr6_to_list(get_ip6($2.sval), atoi(mask), is_not);
		is_not = 0;
	}
	|
	addrdir ANY
	{
		/* any - add nothing */
		if(debug)
			fprintf(stderr, "any ");
	}
	|
	addrdir ME
	{
                if(debug)
                        fprintf(stderr, "me ");

                add_addr_to_list(0, ME_MASK, is_not);
                is_not = 0;
	}
	|
	addrdir ME6
	{
		struct in6_addr fuf;
                if(debug)
                        fprintf(stderr, "me6 ");

                add_addr6_to_list(fuf, ME_MASK, is_not);
                is_not = 0;
	}
	|
	addrdir TABLENAME
	{
#ifdef IPFW_EXTENDED_TABLES
		struct table *table = find_table($2.sval);
		if (!table)
			yyerror("Unresolved macro name: %s", $2.sval);
		if (!table->used) {
			if (debug)
				fprintf(stderr, "Starting resolve for table %s\n", table->name);
			resolve_table(table);
		}
		add_table_to_list(-1, (u_int32_t)table->number, is_not);
		is_not = 0;
#else
		yyerror("Unresolved macro name: %s", $2.sval);
#endif
	}
	|
	addrdir hostname
	{
		struct addrinfo *ai, *res;

		if ((res = y_gethostbyname($2.sval)) == NULL) {
			if(!ignore_unresolved) {
				if (only_test) {
					yywarning("can't resolve host: %s", $2.sval);
					break;
				} else 
					yyerror("can't resolve host: %s", $2.sval);
			} else {
				printf("Line %d: can't resolve host: %s. Ignored.\n", line, $2.sval);
				break;
			}
		}

		if(debug)
			fprintf(stderr, "domain:%s ", $2.sval);

		for(ai = res; ai != NULL; ai = ai->ai_next) {
			if(ai->ai_family == AF_INET6)
				add_addr6_to_list(((struct sockaddr_in6*)ai->ai_addr)->sin6_addr, 128, is_not);
			else
				add_addr_to_list(((struct sockaddr_in*)ai->ai_addr)->sin_addr.s_addr, 32, is_not);
		}
		is_not = 0;
	}
	|
	TABLE LBRACE tableparam RBRACE
	;
hostname:
        TOKEN
        |
        FQDN
        ;
tableparam:
	NUMBER
	{
#ifdef IPFW_EXTENDED_TABLES
		add_table_to_list(-1, (u_int32_t)$1.ival, is_not);
		is_not = 0;
#endif
	}
	|
	NUMBER COMMA NUMBER
	{
#ifdef IPFW_EXTENDED_TABLES
		add_table_to_list((u_int32_t)$3.ival, (u_int32_t)$1.ival, is_not);
		is_not = 0;
#endif
	}
	|
	TABLENAME
	{
#ifdef IPFW_EXTENDED_TABLES
		struct table *table = find_table($1.sval);
		if (!table)
			yyerror("Unresolved table name: %s", $1.sval);
		if (!table->used) {
			if (debug)
				fprintf(stderr, "Starting resolve for table %s\n", table->name);
			resolve_table(table);
		}
		add_table_to_list(-1, (u_int32_t)table->number, is_not);
		is_not = 0;
#else
		yyerror("Unresolved macro name: %s", $1.sval);
#endif
	}
	|
	TABLENAME COMMA NUMBER
	{
#ifdef IPFW_EXTENDED_TABLES
		struct table *table = find_table($1.sval);
		if (!table)
			yyerror("Unresolved table name: %s", $1.sval);
		if (debug)
			fprintf(stderr, "Starting resolve for table %s\n", table->name);
		add_table_to_list((u_int32_t)$3.ival, (u_int32_t)table->number, is_not);
		is_not = 0;
#else
		yyerror("Unresolved macro name: %s", $1.sval);
#endif
	}
	;
not:
   	NOT
   	{
   		is_not = 1;
	}
	;
statementset:
	statementtoken OR statementset
	|
	statementtoken COMMA statementset
	|
	statementtoken
	|
	not statementtoken
	;
ports:
	|
	porttoken COMMA ports
	|
	porttoken
	;
portdir:
	|
	SRCPORT
	|
	DSTPORT
	;
addrdir:
       	|
	SRCADDR
	|
	DSTADDR
	;
porttoken:
	portdir ALL
	{
		add_port("all");
	}
	|
	portdir TOKEN
	{
		add_port($2.sval);
	}
	|
	portdir NUMBER
	{
		add_port_to_list((u_int32_t)$2.ival, (u_int32_t)$2.ival, is_not);
		is_not = 0;
	}
	|
	portdir RANGE
	{
		char start[6], *end;

		end = strchr($2.sval, '-');
		strncpy(start, $2.sval, end-$2.sval);
		start[end-$2.sval] = 0;
		end++;

		add_port_to_list(atoi(start), atoi(end), is_not);
		is_not = 0;
	}
	;
range:
     	RANGE
	;
options:
	|
	not optiontoken
	|
	optiontoken options
	|
	obrace optionset ebrace
	;
obrace:
      	OBRACE
	{
		optionset=1;
		prev = NULL;
	}
	;
ebrace:
      	EBRACE
	{
		optionset=0;
		prev=NULL;
	}
	;
optiontoken:
	VIA TOKEN
	{
		cmd->opcode = O_VIA;
		fill_iface($2.sval);
		if(optionset && prev)
			prev->len |= F_OR;
		prev = cmd;
		cmd = next_cmd(cmd);
		if(debug)
			fprintf(stderr, "VIA %s ", $2.sval);
	}
	|
	XMIT TOKEN
	{
		cmd->opcode = O_XMIT;
		fill_iface($2.sval);
		if(optionset && prev)
			prev->len |= F_OR;
		prev = cmd;
		cmd = next_cmd(cmd);
		if(debug)
			fprintf(stderr, "XMIT %s ", $2.sval);
	}
	|
	RECV TOKEN
	{
		cmd->opcode = O_RECV;
		fill_iface($2.sval);
		if(optionset && prev)
			prev->len |= F_OR;
		prev = cmd;
		cmd = next_cmd(cmd);
		if(debug)
			fprintf(stderr, "RECV %s ", $2.sval);
	}
	|
	IN
	{
		cmd->opcode = O_IN;
		cmd->len = 1;
		cmd = next_cmd(cmd);
		if(debug)
			fprintf(stderr, "in ");
	}
	|
	OUT
	{
		cmd->opcode = O_IN;
		cmd->len ^= F_NOT;
		cmd->len |= 1;
		cmd = next_cmd(cmd);
		if(debug)
			fprintf(stderr, "out ");
	}
	|
	FRAG
	{
		cmd->opcode = O_FRAG;
		cmd->len = 1;
		cmd = next_cmd(cmd);
		if(debug)
			fprintf(stderr, "frag ");
	}
	|
	SETUP
	{
		if(strcmp(curr_proto, "tcp") != 0)
			yyerror("setup option makes a sense only for TCP protocol");
		
		cmd->opcode = O_TCPFLAGS;
		cmd->len = 1;
		cmd->arg1 = (TH_SYN) | ( (TH_ACK) & 0xff) << 8;
		cmd = next_cmd(cmd);
		if(debug)
			fprintf(stderr, "setup ");
	}
	|
	ESTABLISHED
	{
		if(strcmp(curr_proto, "tcp") != 0)
			yyerror("established option makes a sense only for TCP protocol");
		
		cmd->opcode = O_ESTAB;
		cmd->len = 1;
		cmd = next_cmd(cmd);
		if(debug)
			fprintf(stderr, "established ");
	}
	|
	ICMPTYPES icmptypes
	{
		struct icmp_list *icmp_entry, *icmp_temp;

		if(strcmp(curr_proto, "icmp") != 0)
			yyerror("icmptypes allow only for ICMP protocol");
		
		((ipfw_insn_u32 *)cmd)->o.opcode = O_ICMPTYPE;
		((ipfw_insn_u32 *)cmd)->o.len |= F_INSN_SIZE(ipfw_insn_u32);
		if(debug)
			fprintf(stderr, "ICMPTYPES:");
		SLIST_FOREACH_SAFE(icmp_entry, &icmp_head, next, icmp_temp) {
			((ipfw_insn_u32 *)cmd)->d[0] |= 1 << icmp_entry->icmptype;
			if(debug)
				fprintf(stderr, "%d ", icmp_entry->icmptype);

			SLIST_REMOVE(&icmp_head, icmp_entry, icmp_list, next);
			free(icmp_entry);
		}
		cmd = next_cmd(cmd);
	}
	|
	ICMP6TYPES icmptypes
	{
		struct icmp_list *icmp_entry, *icmp_temp;

		((ipfw_insn_icmp6 *)cmd)->o.opcode = O_ICMP6TYPE;
		((ipfw_insn_icmp6 *)cmd)->o.len |= F_INSN_SIZE(ipfw_insn_icmp6);
		if(debug)
			fprintf(stderr, "ICMP6TYPES:");
		SLIST_FOREACH_SAFE(icmp_entry, &icmp_head, next, icmp_temp) {
			unsigned t = icmp_entry->icmptype;
			if (t > ICMP6_MAXTYPE)
				yyerror("Wrong icmp6type: %d", t);
			((ipfw_insn_icmp6 *)cmd)->d[t/32] |= 1 << (t%32);
			if(debug)
				fprintf(stderr, "%d ", t);

			SLIST_REMOVE(&icmp_head, icmp_entry, icmp_list, next);
			free(icmp_entry);
		}
		cmd = next_cmd(cmd);
		if (!enable_ipv6)
		        empty_rule = 1;
	}
	|
	KEEPSTATE
	{
		have_state = cmd;
		cmd->opcode = O_KEEP_STATE;
		cmd->len = 1;
		cmd = next_cmd(cmd);
		if(debug)
			fprintf(stderr, "keep-state ");
	}
	|
	DIVERTED
	{
		cmd->opcode = O_DIVERTED;
		cmd->len = (cmd->len & (F_NOT | F_OR)) | 1;
		cmd->arg1 = 3;
		cmd = next_cmd(cmd);
	}
	|
	DIVERTEDLOOPBACK
	{
		cmd->opcode = O_DIVERTED;
		cmd->len = (cmd->len & (F_NOT | F_OR)) | 1;
		cmd->arg1 = 1;
		cmd = next_cmd(cmd);
	}
	|
	DIVERTEDOUTPUT
	{
		cmd->opcode = O_DIVERTED;
		cmd->len = (cmd->len & (F_NOT | F_OR)) | 1;
		cmd->arg1 = 2;
		cmd = next_cmd(cmd);
	}
	|
	LIMIT source NUMBER
	{
		ipfw_insn_limit *c = (ipfw_insn_limit *)cmd;

		if(have_state)
			yyerror("either keep-state or limit should be used, not both together");
		have_state = cmd;
		cmd->len = F_INSN_SIZE(ipfw_insn_limit);
		cmd->opcode = O_LIMIT;
		c->limit_mask = c->conn_limit = 0;

		if(strcmp($2.sval, "src-addr") == 0)
			c->limit_mask |= DYN_SRC_ADDR;
		if(strcmp($2.sval, "dst-addr") == 0)
			c->limit_mask |= DYN_DST_ADDR;
		if(strcmp($2.sval, "src-port") == 0)
			c->limit_mask |= DYN_SRC_PORT;
		if(strcmp($2.sval, "dst-port") == 0)
			c->limit_mask |= DYN_DST_PORT;
		
		if($3.ival < 1 || $3.ival > 65534)
			yyerror("limit out of range: %d", $3.ival);
		c->conn_limit = (u_int32_t)$3.ival;
		cmd = next_cmd(cmd);
		if(debug)
			fprintf(stderr, "limit:%s %d ",$2.sval, (u_int32_t)$3.ival);
	}
	|
	TCPFLAGS tcpflags
	{
		if(strcmp(curr_proto, "tcp") != 0)
			yyerror("tcpflags make a sense only for TCP protocol");
		
		cmd->opcode = O_TCPFLAGS;
		cmd->len = 1;
		cmd->arg1 = (set & 0xff) | ( (clear & 0xff) << 8);
		set = clear = 0;
		cmd = next_cmd(cmd);
		if(debug)
			fprintf(stderr, "tcpflags ");
	}
	|
	TCPOPTIONS tcpoptions
	{
		printf("tcpoptions ");
		yyerror("\ntcpoptions is not implemented yet");
	}
	|
	IPLEN range
	{
		yyerror("\niplen is not implemented yet");
	}
	|
	IPOPTIONS ipoptions
	{
		yyerror("\nipoptions is not implemented yet");
	}
	|
	IPTOS iptos
	{
		yyerror("\niptos is not implemented yet");
	}
	|
	IPTTL range
	{
		yyerror("\nrange is not implemented yet");
	}
	|
	TCPDATALEN range
	{
		yyerror("\nrange is not implemented yet");
	}
	|
	TCPSEQ NUMBER
	{
		yyerror("\ntcpseq is not implemented yet");
	}
	|
	ANTISPOOF
	{
		cmd->opcode = O_ANTISPOOF;
		cmd->len = 1;
		cmd = next_cmd(cmd);
	}
	|
	VERREVPATH
	{
		cmd->opcode = O_VERREVPATH;
		cmd->len = 1;
		cmd = next_cmd(cmd);
	}
	|
	VERSRCREACH
	{
		cmd->opcode = O_VERSRCREACH;
		cmd->len = 1;
		cmd = next_cmd(cmd);
	}
	|
	EXT6HDR exthdropts
	{
		cmd->opcode = O_EXT_HDR;
		cmd->len = 1;
		cmd = next_cmd(cmd);
	}
	|
	IPSEC
	{
		cmd->opcode = O_IPSEC;
		cmd->len = 1;
		cmd = next_cmd(cmd);
	}
	|
	IPVER NUMBER
	{
		cmd->opcode = O_IPVER;
		cmd->len = 1;
		cmd->arg1 = $2.ival;
		cmd = next_cmd(cmd);
	}
	;
optionset:
	optiontoken OR optionset
	|
	optiontoken
	|
	not optiontoken
	;
source:
      	SRCADDR
	|
	DSTADDR
	|
	SRCPORT
	|
	DSTPORT
	;
tcpflagstoken:
	FIN
	{
		set |= 1;
	}	
	|
	NOTCHAR FIN
	{
		clear |= 1;
	}
	|
	SYN
	{
		set |= 2;
	}	
	|
	NOTCHAR SYN
	{
		clear |= 2;
	}	
	|
	RST
	{
		set |= 4;
	}	
	|
	NOTCHAR RST
	{
		clear |= 4;
	}	
	|
	PSH
	{
		set |= 8;
	}	
	|
	NOTCHAR PSH
	{
		clear |= 8;
	}	
	|
	ACK
	{
		set |= 16;
	}	
	|
	NOTCHAR ACK
	{
		clear |= 16;
	}	
	|
	URG
	{
		set |= 32;
	}	
	|
	NOTCHAR URG
	{
		clear |= 32;
	}	
	;
tcpflags:
	tcpflagstoken
	|
	tcpflagstoken COMMA tcpflags
	;
tcpoptionstoken:
	MSS
    	{
		yyerror("option mss is not supported yet");
	}
	|
	WINDOW
    	{
		yyerror("option window is not supported yet");
	}
	|
	SACK
    	{
		yyerror("option sack is not supported yet");
	}
	|
	TS
    	{
		yyerror("option ts is not supported yet");
	}
	|
	CC
    	{
		yyerror("option cc is not supported yet");
	}
	;
tcpoptions:
	tcpoptionstoken
	|
	NOTCHAR tcpoptionstoken
	|
	tcpoptionstoken COMMA tcpoptions
	;
ipoptionstoken:
	SSRR
    	{
		yyerror("option ssrr is not supported yet");
	}
	|
	LSRR
    	{
		yyerror("option slrr is not supported yet");
	}
	|
	RR
    	{
		yyerror("option rr is not supported yet");
	}
	|
	TS
    	{
		yyerror("option ts is not supported yet");
	}
	;
ipoptions:
	ipoptionstoken
	|
	NOTCHAR ipoptionstoken
	|
	ipoptionstoken COMMA ipoptions
	;
iptostoken:
        LOWDELAY
    	{
		yyerror("option lowdelay is not supported yet");
	}
	|
	THROUGHPUT
    	{
		yyerror("option throughput is not supported yet");
	}
	|
	RELIABILITY
    	{
		yyerror("option reliability is not supported yet");
	}
	|
	MINCOST
    	{
		yyerror("option mincost is not supported yet");
	}
	|
	CONGESTION
    	{
		yyerror("option congestion is not supported yet");
	}
        ;
iptos:
        iptostoken
	|
	NOTCHAR iptostoken
	|
	iptostoken COMMA iptos
	;
icmptypes:
	icmptype
	|
	icmptypes COMMA icmptype
	;
icmptype:
	NUMBER
	{
		struct icmp_list *icmp_entry = malloc(sizeof(struct icmp_list));

		icmp_entry->icmptype = (u_int32_t)$1.ival;
		
		if(SLIST_EMPTY(&icmp_head)) {
			SLIST_INSERT_HEAD(&icmp_head, icmp_entry, next);
			icmp_prev = icmp_entry;
		} else {
			SLIST_INSERT_AFTER(icmp_prev, icmp_entry, next);
			icmp_prev = icmp_entry;
		}
	}
	;
exthdropts:
	exthdropt
	|
	exthdropts COMMA exthdropt
	;
exthdropt:
	FRAG
	{
		cmd->arg1 |= EXT_FRAGMENT;
	}
	|
	HOPOPT
	{
		cmd->arg1 |= EXT_HOPOPTS;
	}
	|
	ROUTE
	{
		cmd->arg1 |= EXT_ROUTING;
	}
	|
	DSTOPT
	{
		cmd->arg1 |= EXT_DSTOPTS;
	}
	|
	AH
	{
		cmd->arg1 |= EXT_AH;
	}
	|
	ESP
	{
		cmd->arg1 |= EXT_ESP;
	}
	|
	RTHDR0
	{
		cmd->arg1 |= EXT_RTHDR0;
	}
	|
	RTHDR2
	{
		cmd->arg1 |= EXT_RTHDR2;
	}
	;
%%
#include "lex.yy.c"
