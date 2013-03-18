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

#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <err.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#if !defined(IFNAMSIZ)
#define  IFNAMSIZ     16
#endif
#define  IF_NAMESIZE     16
#include <sys/queue.h>
#define IPFW_INTERNAL   /* Access to protected structures in ip_fw.h. */
#include <netinet/ip_fw.h>
#include <sys/queue.h>
#include <netinet/ip_dummynet.h>
#include <errno.h>
#include <sys/param.h>
#include <sys/sysctl.h>
#include <libutil.h>

/* Check if extended tables are supported */
#ifdef IP_FW_TABLE_XADD
#define IPFW_EXTENDED_TABLES
#endif

#define MAX_RULES	65535

int line=1, rule_step=2, quiet=0, debug=0, ignore_unresolved=0, only_test=0, unclean_test=0, save_binary=0, enable_ipv6=0;
uint32_t rule_num;
int rule_count=0, dummynet_count=0, nat_count=0, table_count=0;
struct ip_fw *rules[MAX_RULES];
struct dn_pipe *dummynet[MAX_RULES];
struct cfg_nat *nat_rules[MAX_RULES];
int rule_line[MAX_RULES];
int table_lower = 1, table_upper = 65534;
int verbose_limit = 0;	/* Default ipfw verbose limit */

extern SLIST_HEAD(, labels) labels_head;
struct labels {
	char		*name;
	ipfw_insn	*pact;
	unsigned int	line;
	SLIST_ENTRY(labels) next;
};

#ifdef IPFW_EXTENDED_TABLES
STAILQ_HEAD(atables_head, table);
STAILQ_HEAD(addr_list_head, addr_list);
extern struct atables_head atables_head;
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

struct table_xentry {
	ip_fw3_opheader		op;
	ipfw_table_xentry	xentry;
	STAILQ_ENTRY(table_xentry)	next;
};

void
decompile_table_entry(struct table_xentry *xe, char *buf, int buflen);
#endif

int yyparse();

void help() {
	fprintf(stderr, "Using: fw-loader [-h] [-d] [-b m] [-s n] [-t] [-q] [-6] [<file_name>]\n"
"-h		Help. This page.\n"
"-b m		Rule number base. Default is 0. First rule will numbered as m+n.\n"
"-d		Debug mode.\n"
"-i		Ignore rules with unresolved FDQN.\n"
"-S file_name	Save binary data for ipfw(8) inside this file.\n"
"-s n		Rule increment step. Default is 2.\n"
"-t		Parse and load rules without install (test mode).\n"
"-T lower:upper Table space to use.\n"
"-M file_name	Save mapping of table names to numbers into this file.\n"
"-q		Be quiet. No output at all.\n"
"-6		Enable IPv6.\n"
"file_name	file with rules for loading. stdin if ommitted.\n");
	exit(0);
}

int
main(int argc, char *argv[])
{
	int i, f, bf, s;
	char ch, *d;
	uint32_t masks[2];
	struct labels *label_entry;
	struct pidfh *pfh;
	char *binary_fname;
	size_t slen;
	pid_t opid;
	char *table_map_fname = NULL;
	int tmap_fd = 0; /* table name map output file descriptor */

	while((ch = getopt(argc, argv, "b:dhiS:s:tT:q6M:")) != -1) {
		switch(ch) {
		case 'b':
			rule_num = atoi(optarg);
			break;
		case 'd':
			debug = 1;
			break;
		case 'h':
		case '?':
		default:
			help();
			/* Never reached */
		case 'i':
			ignore_unresolved = 1;
			break;
		case 'S':
			save_binary = 1;
			binary_fname = optarg;
			break;
		case 's':
			rule_step = atoi(optarg);
			break;
		case 't':
			only_test = 1;
			break;
		case 'T':
#ifdef IPFW_EXTENDED_TABLES
			if ((d = strchr(optarg, ':')))
				table_upper = atoi(d + 1);
			table_lower = atoi(optarg);
			if ((table_lower < 1) || (table_lower >= table_upper) || (table_upper > 65534))
				errx(1, "Invalid table range. Valid rannge is 1...65534");
#else
			errx(1, "eXtended tables not supported by kernel");
#endif
			break;
		case 'q':
			quiet = 1;
			break;
		case '6':
			enable_ipv6 = 1;
			break;
		case 'M':
#ifdef IPFW_EXTENDED_TABLES
			table_map_fname = optarg;
#else
			errx(1, "eXtended tables not supported by kernel");
#endif
			break;
		}
	}
	argc -= optind-1;
	argv += optind-1;

	if(argc > 1) {
		if(debug)
			fprintf(stderr, "using file: %s\n", argv[1]);
		f = open(argv[1], O_RDONLY);
		if(f == -1)
			errx(1, "Can't open file: %s", argv[1]);
		close(0);
		dup(f);
		close(f);
	}

	if(!only_test) {
	    /* Create a PID file and check if we already run */
	    if ((pfh = pidfile_open("/var/run/fw-loader.pid", 0644, &opid)) == NULL) {
		if (errno == EEXIST)
		    errx(1, "Already run with PID %d. Exiting.", opid);
		errx(1, "Can't create PID file");
	    }
	    pidfile_write(pfh);

	    if (save_binary) {
		bf = open(binary_fname, O_WRONLY|O_TRUNC|O_CREAT);
		if(bf == -1)
			errx(1, "Can't open file: %s", binary_fname);
	    }
	}

	/*
	 * Read verbose limit. Fail IFF ipfw is not loaded and we're
	 * not running in bootstrap mode.
	 */
	slen = sizeof(verbose_limit);
	if ((sysctlbyname("net.inet.ip.fw.verbose_limit", &verbose_limit,
	    &slen, NULL, 0) == -1) && (save_binary == 0)) {
		errx(1, "\nsysctlbyname(\"%s\")", "net.inet.ip.fw.verbose_limit");
	}

	if (debug)
		fprintf(stderr, "verbose limit set to %d\n", verbose_limit);

	if(!quiet) {
		fprintf(stderr,"Checking and loading rules");
		fflush(stdout);
	}

	yyparse();
	
	if (unclean_test) {
		yyerror("Some name resolving issues were found, loading rules failed");
	}

	/* Check for unresolved labels */
	SLIST_FOREACH(label_entry, &labels_head, next) {
	    if(label_entry->pact->arg1 == 0) {
		if(!only_test)
		    pidfile_remove(pfh);
		errx(1, "Unresolved label '%s' at line %u", label_entry->name, label_entry->line);
	    }
	}

	if(!quiet)
		printf(" done.\nLines processed: %d\nRules loaded: %d\nDummynet rules loaded: %d\nNAT rules loaded: %d\n", line--, rule_count, dummynet_count, nat_count);

	if(!only_test) {

		/* Сохраняем правила в бинарном формате в файл */
		if (save_binary) {
			/* Проходим по всем правилам и загружаем их */
			for( i = 0; i < rule_count; i++ ) {
				int rule_size = RULESIZE(rules[i]);
				if(debug)
				    printf("rule opcodes len: %d\n", rule_size);
				if (write(bf, rules[i], rule_size) == -1) {
					pidfile_remove(pfh);
					errx(1, "file write error. line: %d (rule #%d)  err=%d (opcode=%d)\n", rule_line[i]-1, i+1, errno, rules[i]->cmd->opcode);
				}
				if(!quiet) {
				    if(i%100 == 0)
					printf(".");
				    if(i > 0 && i%1000 == 0)
					printf("%d", i);
				    fflush(stdout);
				}
			}

			close(bf);
			pidfile_remove(pfh);
			return (0);
		}

		if(geteuid() > 0) {
			pidfile_remove(pfh);
			errx(1, "You're not root. Not enought right to install rules.");
		}

		if((s = socket(AF_INET, SOCK_RAW, IPPROTO_RAW)) < 0) {
			pidfile_remove(pfh);
			errx(1, "socket error");
		}
#ifdef IPFW_EXTENDED_TABLES
		/* Install tables */
		struct table *table;
		struct table_xentry *xe;
		int res;
		/* open table map output file */
		if (table_map_fname) {
			tmap_fd = open (table_map_fname, O_WRONLY|O_TRUNC|O_CREAT);
			if (tmap_fd == -1) {
				warn("open %s", table_map_fname);
				tmap_fd = 0;
			}
		}

		STAILQ_FOREACH(table, &atables_head, anext) {
			if (debug)
				fprintf(stderr, "Installing table number %d (%s)\n", table->number, table->name);

			/* write into table map file */
			if (tmap_fd)
			{
				char buff[BUFSIZ];
				int len = snprintf(buff, sizeof(buff), "%d %s\n", table->number, table->name);
				if (len < 0)
					err(1, "snprintf");
				else if (len < sizeof(buff))
				{
					char *buff_to_write = buff;
					while (len > 0)
					{
						int written = write(tmap_fd, buff_to_write, len);
						if (written == -1) {
							if (errno == EINTR) continue;
							err(1, "write");
						}
						len -= written;
						buff_to_write += written;
					}
				}
			}

			i = 0;
			STAILQ_FOREACH(xe, &table->compiled_head, next) {
				res = setsockopt(s, IPPROTO_IP, IP_FW3, xe, xe->xentry.len + sizeof(ip_fw3_opheader));
				if (res != 0) {
					char buf[64];
					decompile_table_entry(xe, buf, sizeof(buf));
					fprintf(stderr, "Error installing record: %s\n", buf);
					/* Workaround duplicate entries adding */
					if (errno == EEXIST)
						continue;

					errx(1, "Installing rules failed in table %d (%s) err=%d errno=%d\n", table->number, table->name, res, errno);
				}
				i++;
			}
			if (debug)
				fprintf(stderr, "%d rule(s) installed\n", i);
		}
		if (tmap_fd)
			close(tmap_fd);
#endif

		if(rule_count > 0) {
			if(!quiet) {
				printf("Installing rules");
				fflush(stdout);
			}

			/* 
			 * Готовим set #1. Сначала disable it, потом загружаем туда правила,
			 * потом делаем swap 0 1. Наши правила становятся активными.
			 * После этого удаляем set #1, в котором остались старые правила.
			 */

			/* 
			 * Номер set устанавливается на самом деле так: 1<<n.
			 * masks[0] - sets to disable, masks[1] - sets to enable.
			 */
			masks[0] = 1<<1;
			masks[1] = 0;
			if(setsockopt(s, IPPROTO_IP, IP_FW_DEL, masks, sizeof(masks)) < 0)
				err(1, "can't disable set 1");

			/* Удаляем set#1 на всякий случай, если там были правила */
			/* 
			 * error code not checked, since removing an empty set
			 * is an error now. 
			 */
			masks[0] = (1 & 0xffff) | (1<<24);
			setsockopt(s, IPPROTO_IP, IP_FW_DEL, masks, sizeof(uint32_t));

			/* Проходим по всем правилам и загружаем их */
			for( i = 0; i < rule_count; i++ ) {
				int rule_size = RULESIZE(rules[i]);
				if(debug)
				    printf("rule opcodes len: %d\n", rule_size);
				if(getsockopt(s, IPPROTO_IP, IP_FW_ADD,
				    rules[i], (socklen_t *)&rule_size) < 0) {
					pidfile_remove(pfh);
					errx(1, "ipfw install error. line: %d (rule #%d)  err=%d (opcode=%d)\n", rule_line[i]-1, i+1, errno, rules[i]->cmd->opcode);
				}
				if(!quiet) {
				    if(i%100 == 0)
					printf(".");
				    if(i > 0 && i%1000 == 0)
					printf("%d", i);
				    fflush(stdout);
				}
			}

			/* Обмениваем set#0 и set#1. вычисляется так: (4<<24)|(num1<<16)|num2 */
			masks[0] = (4<<24) | (1<<16) | 0;
			if(setsockopt(s, IPPROTO_IP, IP_FW_DEL, masks, sizeof(uint32_t)) < 0)
				err(1, "can't swap sets 0<->1");

			/* Удаляем set#1, где у нас остались старые правила */
			masks[0] = (1 & 0xffff) | (1<<24);
			if(setsockopt(s, IPPROTO_IP, IP_FW_DEL, masks, sizeof(uint32_t)) < 0)
				err(1, "can't delete set1");
		}

		if(rule_count && !quiet)
			printf(".%d\n", rule_count);

		if(dummynet_count > 0) {
#ifdef HAS_DUMMYNET2
			if(!quiet) {
				printf("\ninstall dummynet rules");
				fflush(stdout);
			}
			for( i=0; i < dummynet_count; i++) {
				if(setsockopt(s, IPPROTO_IP, IP_DUMMYNET_CONFIGURE, dummynet[i], sizeof(struct dn_pipe)) < 0)
					errx(1, "can't load dummynet rules");
				if(!quiet) {
				    printf(".");
				    fflush(stdout);
				}
			}
			if(!quiet)
				printf("%d\n", dummynet_count);
#else
			pidfile_remove(pfh);
                        errx(1, "dummynet???");
#endif
		}

#ifdef HAS_IPFWNAT
		if(nat_count > 0) {
		    if(!quiet) {
			    printf("\ninstall nat rules");
			    fflush(stdout);
		    }
		    for( i=0; i < nat_count; i++) {
			    if(setsockopt(s, IPPROTO_IP, IP_FW_NAT_CFG, nat_rules[i], sizeof(struct cfg_nat)) < 0) {
				    pidfile_remove(pfh);
				    errx(1, "can't load nat rules");
			    }
			    if(!quiet) {
				    printf(".");
				    fflush(stdout);
			    }
			    if(!quiet)
				    printf("%d\n", nat_count);
		    }
		}
#endif
		close(s);
	} else
		if(!quiet)
			printf("Rules are OK.\n");

	if(!only_test)
		pidfile_remove(pfh);
	return 0;
}


