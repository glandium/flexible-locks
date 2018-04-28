// Copyright 2018 Mike Hommey
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#include <stdlib.h>

#ifdef _WIN32
#include <windows.h>
struct Mutex {
    CRITICAL_SECTION mutex;
};

void mutex_init(struct Mutex* m) {
    InitializeCriticalSection(&m->mutex);
}

void mutex_lock(struct Mutex* m) {
    EnterCriticalSection(&m->mutex);
}

void mutex_unlock(struct Mutex* m) {
    LeaveCriticalSection(&m->mutex);
}

void mutex_destroy(struct Mutex* m) {
    DeleteCriticalSection(&m->mutex);
}
#else
#include <pthread.h>
struct Mutex {
    pthread_mutex_t mutex;
};

void mutex_init(struct Mutex* m) {
    pthread_mutex_init(&m->mutex, NULL);
}

void mutex_lock(struct Mutex* m) {
    pthread_mutex_lock(&m->mutex);
}

void mutex_unlock(struct Mutex* m) {
    pthread_mutex_unlock(&m->mutex);
}

void mutex_destroy(struct Mutex* m) {
    pthread_mutex_destroy(&m->mutex);
}
#endif

struct Data {
    size_t a;
    size_t b;
    struct Mutex mutex;
};

void data_inc(struct Data* d) {
    mutex_lock(&d->mutex);
    d->a++;
    if (d->a % 9 == 0) {
        d->b++;
    }
    mutex_unlock(&d->mutex);
}

struct Data* data_new() {
    struct Data* d = malloc(sizeof(struct Data));
    d->a = 0;
    d->b = 0;
    mutex_init(&d->mutex);
    return d;
}

void data_free(struct Data* d) {
    mutex_destroy(&d->mutex);
    free(d);
}
