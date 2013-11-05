
#undef min
#undef max
#undef offsetof

#include <malloc.h>
#include <assert.h>

typedef unsigned char byte;
typedef unsigned int uint;
typedef unsigned short uint16;
typedef unsigned long u32;
typedef signed long i32;
typedef unsigned long addr_t;

//extern "C" {
//	void __cdecl _assert(void *, void *, unsigned);
//}

//#ifdef assert
//#undef assert
//#endif
//#define assert(exp) (void)( (exp) || (_assert(#exp, __FILE__, __LINE__), 0) )
#define offsetof(type, n) ((size_t)(&((type*)0)->n))
#define offsetofend(type,n) (offsetof(type,n) + sizeof(((type*)0)->n))

#define assert_compile(expr) void __ct_assert__(int a[1 - 2 * !(expr)]);
#define lengthof(expr) (sizeof(expr)/sizeof(expr[0]))
#define StackAlloc(T,size) ((T*)alloca((size) * sizeof(T)))


// VC 6 for-fix
//Who uses VC6 anymore
//#define for if(0);else for

#undef min
#undef max

template <typename T> T min(T a, T b) { if (a < b) return a; return b; }
template <typename T> T max(T a, T b) { if (a > b) return a; return b; }

template<typename T> T inline exch(T &a, const T b) {
	T t = a; a = b; return t;
}

template<typename T> T inline postinc(T &a, size_t b) {
	T t = a; a += b; return t;
}
template<typename T> void inline swap(T &a, T &b) {
	b = exch(a, b);
}

//The C++ Standard Library forbids macroizing keywords.
//#define inline __forceinline

template <typename T, int minsize = 16> class LList {
	T *mem;
	size_t alloc,count;
public:
	void inline Init() { mem = NULL; alloc = count = 0; }
	void inline Init(size_t init) { Init(); Resize(init); }
	size_t inline GetCount() const { return count; }
	size_t inline GetAlloc() const { return alloc; }
	void inline SetCount(int c) { count = c; }

	inline T& operator[](size_t offset) { /*assert(offset ==0);*/   return mem[offset]; }
	inline const T& operator[](size_t offset) const { assert(offset ==0 || offset<alloc); return mem[offset]; }


	void inline Resize(size_t a) {
		mem = (T*)realloc(mem, (alloc=a) * sizeof(T));
	}

	int inline Append(const T &t) {
		if (count >= alloc) Resize(max<size_t>(minsize, alloc * 2));
		int r=count++;
		mem[r] = t;
		return r;
	}

	T inline &Inject(size_t pos) {
		assert(pos <= count);
		if (count >= alloc) Resize(max<size_t>(minsize, alloc * 2));
		memmove(&mem[pos + 1], &mem[pos], (count++ - pos) * sizeof(T));
		return mem[pos];
	}

	void inline Append(const T *t, size_t n)
	{
		if (count + n > alloc) {
			Resize(max<size_t>(max(count+n, alloc * 2),minsize));
		}
		int r = count;
		count += n;
		memcpy(mem + r, t, sizeof(T) * n);			
	}

	T inline &Append() {
		if (count >= alloc) Resize(max<size_t>(minsize, alloc * 2));
		return mem[count++];
	}

	void inline Compact() {
		Resize(count);
	}

	void inline Free() {
		free(mem);
	}

	bool inline MoveUpLast(size_t index) {
		assert(index < count);
		size_t c = --count;
		if (index != c) {
			mem[index] = mem[c];
			return true;
		}
		return false;
	}

	void inline RemoveElement(size_t i) {
		assert(i < count);
		memcpy(&mem[i], &mem[i+1], sizeof(mem[0]) * (--count - i));
	}

	size_t inline LookupElement(const T &v) const {
		for(size_t i = 0; i != count; i++)
			if (mem[i] == v)
				return i;
		return (size_t) -1;
	}

	size_t inline LookupElementExist(const T &v) const {
		for(size_t i = 0;; i++) {
			assert(i < count);
			if (mem[i] == v)
				return i;
		}
	}

	bool inline HasElement(const T &v) const {
		for(size_t i = 0; i != count; i++)
			if (mem[i] == v)
				return true;
		return false;
	}

	T *StealArray(size_t *len) {
		T *r = mem;
		*len = count;
		Init();
		return r;
	}
};

class Pool {
	size_t blksize;

	struct PoolBlk {
		byte *head;
		byte *end;
		PoolBlk *next;
		byte data[1];
	};
	PoolBlk *blk;
public:
	Pool() {}
	Pool(size_t size) { Init(size); }
	~Pool() { Free(); }

	void Init(size_t blksize = 16384);
	void *Alloc(size_t size);
	
	void Free();

	size_t GetSize();
};

template<typename T, size_t offs>  class TailQueueX {
	T *_first, **_last;
	static T **next(T *a) { return (T**)((byte*)a + offs); }

public:
	inline void unlinknext(T **a) { if (!(*a = (*a)->next)) _last = a;	}
	inline void unlinkhead() { unlinknext(&_first); }

	inline void init() { _first = NULL; _last = &_first; }
	inline void enqueue(T *a) {	*_last = a; _last = next(a); *_last = NULL; }
	inline T *dequeue() { assert(_first); T *f = _first; unlinknext(&_first); return f; }
	inline bool empty() { return _first == NULL; }
	inline T *last() { assert(_first); return (T*)((byte*)_last - offs); }
	inline T *&first() { return _first; }
	inline void enqueue_head(T *a) { if (!(a->next = _first)) _last = &a->next; _first = a; }

	inline void copy_from(TailQueueX<T,offs> *a) {
		*this = *a;
		if (a->_last == &a->_first)
			_last = &_first;
	}

};
#define TailQueue(T,next) TailQueueX<T, offsetof(T, next)>


#define HASBIT(n,i) (((n)>>(i))&1)
#define SETBIT(n,i) (n) |= (1<<(i))
#define CLRBIT(n,i) (n) &= ~(1<<(i))
#define MKBIT(i) (1<<(i))


byte *load_file(const char *str, size_t *len);
bool save_file(const char *str, byte *mem, size_t size);
char * _cdecl str_fmt(const char *str, ...);
char * _cdecl str_fmt_nf(const char *str, ...);
char *strcpy_e(void *d, const void *s);
void *memdup(void *src, int len);
int CountBits(u32 v);
unsigned int rdtsc();
char *my_strchr(const char *s, char c);

