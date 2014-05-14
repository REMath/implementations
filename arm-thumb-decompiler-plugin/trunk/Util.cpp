#include "default.h"
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <ida.hpp>
#include <idp.hpp>
#include <kernwin.hpp>
#include "fpro.h"

byte *load_file(const char *str, size_t *len)
{
	FILE *in = qfopen(str, "rb");
	size_t size;
	byte *mem;

	if (in == NULL) {
		*len = 0;	
		return NULL;
	}

	qfseek(in, 0, SEEK_END);
	size = qftell(in);
	qfseek(in, 0, SEEK_SET);

	mem = (byte*)malloc(size + 1);
	mem[size] = 0;

	qfread(in,mem, size);
	qfclose(in);

	*len = size;
	return mem;
}

bool save_file(const char *str, byte *mem, size_t size)
{
	FILE *f = qfopen(str, "wb");
	if (!f) return false;
	qfwrite(f, mem, size);
	qfclose(f);
	return true;
}

bool strhcmp(const char *big, const char *small)
{
	while (*small) {
		if (*small++ != *big++)
			return false;
	}
	return true;
}

char * _cdecl str_fmt(const char *str, ...) {
	char buf[8192];
	va_list va;

	va_start(va, str);
	vsprintf(buf, str, va);
	va_end(va);

	return strdup(buf);
}

char *strcpy_e(void *d, const void *s) {
	int len = strlen((char*)s);
	return (char*)memcpy(d, s, len+1) + len;
}

char *strcpy_m(void *a, const void *b, int len)
{
	((char*)a)[len] = 0;
	return (char*)memcpy(a, b, len);
}

char *strduplen(const char *src, int len) {
	char *d = (char*)malloc(len+1);
	if (d==NULL) return NULL;
	d[len] = 0;
	return (char*)memcpy(d, src, len);
}

void *memcpy_e(void *d, const void *s, size_t len)
{
	memcpy(d, s, len);	
	return (byte*)d + len;
}

char *my_strtok(char *s, char c)
{
	if (s != NULL && (s = strchr(s, c)) != NULL)
		*s++ = 0;
	return s;
}

char *my_strchr(const char *s, char c)
{
	while (*s && *s != c) s++;
	return (char*)s;
}

char *str_set(char **str, const char *txt) {
	if (*str)  {
		free(*str);
	}
	if (txt==NULL) txt="";
	return *str = strdup(txt);
}

char *str_setx(char **str, char *txt) {
	if (*str)  {
		free(*str);
	}
	if (txt==NULL) txt=strdup("");
	return *str = txt;
}

void str_free(char **str) {
	if (*str) {
		free(*str);
		*str = NULL;
	}
}

char * _cdecl str_fmt_nf(const char *str, ...) {
	__declspec(thread)  static char *tmp = NULL;

	char buf[4096];
	va_list va;
	va_start(va, str);
	vsprintf(buf, str, va);
	va_end(va);
	
	return str_set(&tmp, buf);
}

void *memdup(void *src, int len) {
	void *d = malloc(len);
	if (d==NULL) return NULL;
	return memcpy(d, src, len);
}

char *strsep(char **string_p, char delim) {
	char *s = *string_p;
	char *start = s, c;

	if (s == NULL)
		return NULL;

	do {
		c = *s++;
		if (c == delim) {
			s[-1] = 0;
			*string_p = s;
			return start;
		}
	} while (c != 0);
	*string_p = NULL;
	return start;
}

	
void strlcpy(char *dst, const char *src, uint maxlen) {
	char c;

	if (maxlen == 0)
		return;

	if (src==NULL) {
		*dst = 0;
		return;
	}

	for(;;) {
		c = *dst++ = *src++;
		if(!--maxlen) {
			dst[-1] = 0;
			break;
		}
		if (!c)
			break;
	}
}

char *get_str(const char *str, int index) {
	do {
		if (--index<0)
			return (char*)str;
		do {
			str++;
		} while (str[-1]);
	} while(1);
}


int CountBits(uint32 v)
{
	int c;
	for (c = 0; v; c++) v &= v - 1;
	return c;
}


uint32 _declspec(naked) rdtsc() {
	_asm {
		rdtsc
		ret
	}
}

void Pool::Init(size_t size)
{
	blksize = size;
	blk = NULL;
}

void *Pool::Alloc(size_t size)
{
	size = (size + 3) & ~3; // align size to 4 boundary

	assert(size + sizeof(PoolBlk) < blksize);
	if (blk == NULL || size > (size_t)(blk->end - blk->head)) {
		PoolBlk *pb = (PoolBlk*)malloc(blksize);
		pb->end = (byte*)pb + blksize;
		pb->head = pb->data;
		pb->next = blk;
		blk = pb;
	}
	byte *r = blk->head;
	blk->head += size;
	assert(blk->head <= blk->end);

	return r;
}

size_t Pool::GetSize()
{
	size_t tot = 0;
	for(PoolBlk *p = blk; p; p=p->next) {
		tot += p->head - p->data;
	}
	return tot;
}


void Pool::Free()
{
	for(PoolBlk *p = blk, *cur; p;) {
		cur = p;
		p = p->next;
		free(cur);
	}
//	msg("Free pool %d\n", tot);
	blk = NULL;
}


