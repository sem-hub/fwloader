#!/bin/sh

FLAGS=

gcc -xc - 2>/dev/null << EOF
#include <sys/types.h>
#include <netinet/ip_compat.h>
#include <netinet/in.h>
#include <netinet/ip_fw.h>

int
main()
{
    enum ipfw_opcodes test = O_SETIPPREC;
}
EOF

if [ $? -eq 0 ]; then
	FLAGS="$FLAGS -DHAS_SETIPPREC"
fi

rm -f a.out

gcc -xc - 2>/dev/null << EOF
#include <sys/types.h>
#include <sys/queue.h>
#include <netinet/ip_compat.h>
#include <netinet/in.h>
#define IPFW_INTERNAL
#define IF_NAMESIZE 16
#include <netinet/ip_fw.h>

int
main()
{
    struct cfg_nat nat;
}
EOF

if [ $? -eq 0 ]; then
	FLAGS="$FLAGS -DHAS_IPFWNAT"
fi

rm -f a.out

gcc -xc - 2>/dev/null << EOF
#include <sys/types.h>
#include <sys/queue.h>
#include <netinet/ip_compat.h>
#include <netinet/in.h>
#include <netinet/ip_fw.h>
#include <netinet/ip_fw.h>
#include <netinet/ip_dummynet.h>

int
main()
{
    struct dn_pipe dnpipe;
}
EOF

if [ $? -eq 0 ]; then
	FLAGS="$FLAGS -DHAS_DUMMYNET2"
fi

rm -f a.out

gcc -xc - 2>/dev/null << EOF
#include <sys/types.h>
#include <netinet/ip_compat.h>
#include <netinet/in.h>
#include <netinet/ip_fw.h>

int
main()
{
    enum ipfw_opcodes test = O_REASS;
}
EOF

if [ $? -eq 0 ]; then
	FLAGS="$FLAGS -DHAS_REASS"
fi

rm -f a.out

echo $FLAGS
