// cycles.h            see license.txt for copyright and terms of use
// read processor cycle count
// interface is portable, implementation is not

#ifdef __cplusplus
extern "C" {
#endif


// read the processor's cycle-count register, and store the count
// into these two 'unsigned' variables; if the count isn't available,
// yields zero in both
void getCycles(unsigned *lowp, unsigned *highp);


#ifdef __GNUC__
// if we're using gcc, so the 'long long' type is available,
// here's a more convenient version
unsigned long long getCycles_ll(void);
#endif


#ifdef __cplusplus
}
#endif

