
/*

MIT Copyright Notice

Copyright 2003 M.I.T.

Permission is hereby granted, without written agreement or royalty fee, to use, 
copy, modify, and distribute this software and its documentation for any 
purpose, provided that the above copyright notice and the following three 
paragraphs appear in all copies of this software.

IN NO EVENT SHALL M.I.T. BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL, 
INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS SOFTWARE 
AND ITS DOCUMENTATION, EVEN IF M.I.T. HAS BEEN ADVISED OF THE POSSIBILITY OF 
SUCH DAMANGE.

M.I.T. SPECIFICALLY DISCLAIMS ANY WARRANTIES INCLUDING, BUT NOT LIMITED TO 
THE IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, 
AND NON-INFRINGEMENT.

THE SOFTWARE IS PROVIDED ON AN "AS-IS" BASIS AND M.I.T. HAS NO OBLIGATION TO 
PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.

$Author: tleek $
$Date: 2004/02/05 15:18:49 $
$Header: /mnt/leo2/cvs/sabo/hist-040105/bind/b4/ns-lookup-bad.c,v 1.2 2004/02/05 15:18:49 tleek Exp $



*/


/*

BIND Copyright Notice

 Copyright (C) 2000-2002  Internet Software Consortium.

 Permission to use, copy, modify, and distribute this software for any
 purpose with or without fee is hereby granted, provided that the above
 copyright notice and this permission notice appear in all copies.

 THE SOFTWARE IS PROVIDED "AS IS" AND INTERNET SOFTWARE CONSORTIUM
 DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL
 IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL
 INTERNET SOFTWARE CONSORTIUM BE LIABLE FOR ANY SPECIAL, DIRECT,
 INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING
 FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT,
 NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION
 WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.


$Author: tleek $
$Date: 2004/02/05 15:18:49 $
$Header: /mnt/leo2/cvs/sabo/hist-040105/bind/b4/ns-lookup-bad.c,v 1.2 2004/02/05 15:18:49 tleek Exp $



*/


/*

<source>

*/

#include <sys/param.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <arpa/nameser.h>

#include <syslog.h>
#include <resolv.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <assert.h>

#include "my-named.h"

struct zoneinfo	*zones = NULL;

struct in_addr data_inaddr(const u_char *data);
struct namebuf *nlookup(u_char *dname);
struct databuf **create_databuf_list(int num);


/* void
 * nslookupComplain(sysloginfo, queryname, complaint, dname, a_rr)
 *	Issue a complaint about a dangerous situation found by nslookup().
 * params:
 *	sysloginfo is a string identifying the complainant.
 *	queryname is the domain name associated with the problem.
 *	complaint is a string describing what is wrong.
 *	dname and a_rr are the problematic other name server.
 */
static void
nslookupComplain(sysloginfo, queryname, complaint, dname, a_rr, nsdp)
     const char *sysloginfo, *queryname, *complaint, *dname;
     const struct databuf *a_rr, *nsdp;
{
#ifdef STATS
  char nsbuf[20];
  char abuf[20];
#endif
	char *a, *ns;
	
	printf("NS '%s' %s\n", dname, complaint);                 
	
	if (sysloginfo && queryname)
	  {
	  char buf[999];

		a = ns = (char *)NULL;
#ifdef STATS
		if (nsdp) {
		  if (nsdp->d_ns) {
		    strcpy(nsbuf, inet_ntoa(nsdp->d_ns->addr));
		    ns = nsbuf;
		  } else {
		    ns = zones[nsdp->d_zone].z_origin;
		  }
		}
		if (a_rr->d_ns) {
		  strcpy(abuf, inet_ntoa(a_rr->d_ns->addr));
		  a = abuf;
		} else {
		  a = zones[a_rr->d_zone].z_origin;
		}
#endif
		/* syslog only takes 5 params */
		if ( a != NULL || ns != NULL)
		  {
		    printf("Calling sprintf!\n");
                    printf("sprintf args: %s: query(%s) %s (%s:%s)",
                           sysloginfo, queryname,
                           complaint, dname,
                           inet_ntoa(data_inaddr(a_rr->d_data)));
		    
		    /*BAD*/
		    sprintf(buf, "%s: query(%s) %s (%s:%s) learnt (A=%s:NS=%s)",
			    sysloginfo, queryname,
			    complaint, dname,
			    inet_ntoa(data_inaddr(a_rr->d_data)),
			    a ? a : "<Not Available>",
			    ns ? ns : "<Not Available>" );
		  }
		else
                  {
		    printf("Calling sprintf!\n");
                    printf("sprintf args: %s: query(%s) %s (%s:%s)",
                           sysloginfo, queryname,
                           complaint, dname,
                           inet_ntoa(data_inaddr(a_rr->d_data)));
		    
		    /*BAD*/
		    sprintf(buf, "%s: query(%s) %s (%s:%s)",
			    sysloginfo, queryname,
			    complaint, dname,
			    inet_ntoa(data_inaddr(a_rr->d_data)));
		    syslog(LOG_INFO, buf);
		    printf("strlen(buf) = %d\n", strlen(buf));
		  }
	  }
}


/* Misha: MODIFIED NSLOOKUP- this function is somewhat different from
* the original, but has very similar structure.  

* For each hostname, DNS tries to resolve the domain of the
* hostname. If DNS can't resolve the domain name, it reads in from an
* internal database a list of name server (NS) records that are
* responsible for the particular domain name. BIND has some way of
* prioritizing the NS records. It tries to resolve the domain name by
* querying the NS records in some order.  Before being able to query
* the NS records, BIND must obtain the IP addresses of the NS records.
* nslookup takes a list of NS records and creates a list of
* corresponding IP addresses (nsa[]).  If at any point nslookup
* notices an invalid NS record, it will complain by calling
* nslookupComplain, which in turn will print a message to syslog via a
* sprintf call.  If the domain names of the invalid NS server is very
* long, a buffer gets overflowed via the sprintf call.
*/

/*	Lookup the IP address for each nameserver in `nsp' and add it to a list if it meets certain conditions 
 *	Detects the following dangerous operations:
 *		One of the A records for one of the nameservers in nsp
 *		refers to the address of one of our own interfaces;
 *		One of the A records refers to the nameserver port on
 *		the host that asked us this question.
 * returns: the number of addresses looked up,  or -1 if a dangerous operation
 *	is detected.
 * side effects:
 *	if a dangerous situation is detected and (syslogdname && sysloginfo),
 *		calls syslog.
 */

int nslookup(nsp, syslogdname, sysloginfo)
	     struct databuf *nsp[];
	     const char *syslogdname;
	     const char *sysloginfo;
{
	register struct namebuf *np;
	register struct databuf *dp, *nsdp;
	u_char *dname;
	int i, class, found_arr = 0;
	static struct in_addr nsa;           /*misha: IP addresses of name servers we looked up */
	
	printf("syslogdname = %s\n", syslogdname);
        printf("sysloginfo = %s\n", sysloginfo);

	//	while ((nsdp = *nsp++) != NULL) {

	for (i=0; i<2; i++) {
	  printf ("i=%d\n", i);
	  nsdp = *(nsp+i);

	  class = nsdp->d_class;           /*Misha: should be C_IN */

	  printf("Class = %d\n", class);

	  printf("C_IN = %d, class = %d\n", C_IN, class);
	  dname = (u_char *)nsdp->d_data;    
	  
	  np = (struct namebuf *) nlookup(dname); /* my version of nlookup.. returns a pointer to namebuf struct*/
	  
	  /* The namebuf contains a data record containing an IP address of the name server*/
	  
	  /* Look for name server addresses */
	  for (dp = np->n_data;  dp != NULL;  dp = dp->d_next) {
	    printf("We're inside for loop!\n");
  
#ifdef NCACHE
	    if (dp->d_rcode)
	      continue;
#endif
	    printf("T_A = %d, dp->d_type = %d\n", T_A, dp->d_type);

	    if (dp->d_type == T_CNAME && dp->d_class == class)
	      goto finish;
	    if (dp->d_type != T_A || dp->d_class != class)
	      continue;
	    if (data_inaddr(dp->d_data).s_addr == INADDR_ANY) {
	      static char *complaint = "Bogus (0.0.0.0) A RR";
	      printf("Calling nslookupComplain!\n");
	      nslookupComplain(sysloginfo, syslogdname,                     /* This complaint should be triggered */
			       complaint, dname, dp, nsdp);
	      continue;
	    }
#ifdef INADDR_LOOPBACK
	    if (ntohl(data_inaddr(dp->d_data).s_addr) ==
	      INADDR_LOOPBACK) {
	    static char *complaint = "Bogus LOOPBACK A RR";
	    nslookupComplain(sysloginfo, syslogdname,
			     complaint, dname, dp, nsdp);
	    continue;
	  }
#endif
#ifdef INADDR_BROADCAST
	  if (ntohl(data_inaddr(dp->d_data).s_addr) == 
	      INADDR_BROADCAST) {
	    static char *complaint = "Bogus BROADCAST A RR";
	    nslookupComplain(sysloginfo, syslogdname,
			     complaint, dname, dp, nsdp);
	    continue;
	  }
#endif
	  found_arr++;
	  nsa = data_inaddr(dp->d_data);
	  }

	  nsp++;
	}
 finish:
	return found_arr; 
}


/*Misha: This is a stub for nlookup(). */
/* Given a dname of a name server, it returns a pointer to a namebuf. */
/* For simplicity's sake, nlookup always returns a namebuf with the same two databufs*/ 
struct namebuf *nlookup(u_char *dname){
  struct databuf **double_nb;
  struct namebuf *nbuf = (struct namebuf *) calloc(1, sizeof(struct namebuf));
  
  double_nb = (struct databuf **) create_databuf_list(1);
  nbuf->n_data = (struct databuf *) *double_nb++;  /*The  namebuf contains one databuf*/
  
  return nbuf;

}  

/*
 * This is nec'y for systems that croak when deref'ing unaligned pointers.
 * SPARC is an example.  Note that in_addr.s_addr needn't be a 32-bit int,
 * so we want to avoid bcopy and let the compiler do the casting for us.
 */
struct in_addr
data_inaddr(data)
     const u_char *data;
{
  struct in_addr ret;
  u_int32_t tmp;
 
  bcopy((char *)data, (char *)&tmp, INADDRSZ);

  ret.s_addr = tmp;
  // dangling ptr??
  return (ret);
}






/* create an array of num pointers to databuf structs */
struct databuf **create_databuf_list(int num){
  struct databuf **dbl, **temp;
  int i;
  FILE *f;
  
  /* create a list of pointers to databuf structs */
  dbl = (struct databuf **) malloc(num * sizeof(struct databuf *));
  temp = dbl;

  f = fopen("address_file", "r");

  /* create a linked list containing one databuf for each of the num pointers */
  for (i=0; i<num; i++){
    *dbl = (struct databuf *) calloc(1, sizeof(struct databuf));

    (*dbl)->d_data[0] = (u_char) getc(f);
    (*dbl)->d_data[1] = (u_char) getc(f);
    (*dbl)->d_data[2] = (u_char)  getc(f);
    (*dbl)->d_data[3] = (u_char) getc(f);
    (*dbl)->d_class = C_IN;
    (*dbl)->d_type = T_A;          /* make it an address record */
    (*dbl)->d_next = NULL;

    /* (*dbl)->d_ns = (struct nameser *) malloc(sizeof(struct nameser)); */
    /*  (*dbl)->dns->addr.s_addr = (in_addr_t) random(); */

    dbl++;
  }

  fclose(f);

  return temp;

}


int main(int argc, char **argv) {
  struct databuf **nsp;
  char syslogdname[1000],sysloginfo[1000];
  FILE *f;

  assert (argc == 2);
  f = fopen(argv[1], "r");
  assert (f!=NULL);

  fgets(syslogdname, 1000, f);   /* read in a large domain name that the DNS server will attempt to resolve */
  fgets(sysloginfo, 1000, f);    /* read in the name of the dns server that will resolve domain */
  
  fclose(f);

  nsp = (struct databuf **) create_databuf_list(2);            /* create an array of 2 pointers to databufs */ 
  nslookup(nsp, syslogdname, sysloginfo);   

  return 0;
}

/*

</source>

*/

