
#include <sys/time.h>
#include <stdlib.h>

#ifndef IDRIS_FARRP_TIME_H
#define IDRIS_FARRP_TIME_H

double getTime() {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec + tv.tv_usec / 1e6;
}

#endif /* IDRIS_FARRP_TIME_H */
