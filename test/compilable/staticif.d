static if (__WORDSIZE == 64)
    enum __SIZEOF_PTHREAD_BARRIER_T = 32;
else
    enum __SIZEOF_PTHREAD_BARRIER_T = 20;

static if (true) {
    enum __WORDSIZE = 64;
}

struct pthread_barrier_t
{
    byte[__SIZEOF_PTHREAD_BARRIER_T] __size;
}
