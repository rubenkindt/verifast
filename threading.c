#ifdef WIN32
#include <windows.h>
#else
#include <pthread.h>
#include <time.h>
#endif
#include <stdlib.h> /* abort */

#include "threading.h"

#ifdef WIN32
struct thread {
    HANDLE handle;
};

// The callback function needs to respect a non-standard calling convention.
struct run_closure {
    void (*run)(void *data);
    void *data;
};

DWORD WINAPI run_closure_run(LPVOID argument)
{
    struct run_closure *closure = (struct run_closure *)argument;
    void (*run)(void *data) = closure->run;
    void *data = closure->data;
    free(closure);
    run(data);
    return 0;
}
#else
struct thread {
    pthread_t id;
};
#endif

struct thread *thread_start_joinable(void* run, void *data)
{
#ifdef WIN32
    struct run_closure *closure;
    HANDLE result;
    struct thread *t;
    
    closure = malloc(sizeof(struct run_closure));
    closure->run = run;
    closure->data = data;
    result = CreateThread(0, 0, run_closure_run, closure, 0, 0);
    if (result == NULL)
        abort();
    t = malloc(sizeof(struct thread));
    if (t == 0) abort();
    t->handle = result;
    return t;
#else
    pthread_t id;
    
    int result = pthread_create(&id, 0, (void *(*)(void *))run, data);
    if (result != 0)
        abort();
    struct thread *t = malloc(sizeof(struct thread));
    if (t == 0) abort();
    t->id = id;
    return t;
#endif
}

void thread_join(struct thread *t)
{
#ifdef WIN32
    DWORD result = WaitForSingleObject(t->handle, INFINITE);
    if (result != WAIT_OBJECT_0) abort();
    CloseHandle(t->handle);
#else
    int result = pthread_join(t->id, 0);
    if (result != 0) abort();
#endif
    free(t);
}

void thread_dispose(struct thread* t)
{
#ifdef WIN32
    CloseHandle(t->handle);
#else
    pthread_detach(t->id);
#endif
    free(t);
}

void thread_start(void* run, void *data)
{
    struct thread *t = thread_start_joinable(run, data);
    thread_dispose(t);
}

struct lock {
#ifdef WIN32
    CRITICAL_SECTION criticalSection;
#else
    pthread_mutex_t mutex;
#endif
};

struct lock *create_lock()
{
    struct lock *lock = malloc(sizeof(struct lock));
#ifdef WIN32
    InitializeCriticalSection(&(lock->criticalSection));
#else
    int result = pthread_mutex_init(&(lock->mutex), 0);
    if (result != 0)
        abort();
#endif
    return lock;
}

void lock_acquire(struct lock *lock)
{
#ifdef WIN32
    EnterCriticalSection(&(lock->criticalSection));
#else
    pthread_mutex_lock(&(lock->mutex));
#endif
}

void lock_release(struct lock *lock)
{
#ifdef WIN32
    LeaveCriticalSection(&(lock->criticalSection));
#else
    pthread_mutex_unlock(&(lock->mutex));
#endif
}

void lock_dispose(struct lock *lock)
{
#ifdef WIN32
    DeleteCriticalSection(&(lock->criticalSection));
#else
    pthread_mutex_destroy(&(lock->mutex));
#endif
    free(lock);
}

struct mutex {
#ifdef WIN32
    CRITICAL_SECTION criticalSection;
    DWORD ownerThreadId;
#else
    pthread_mutex_t mutex;
    pthread_t ownerThreadId;
#endif
};

struct mutex *create_mutex()
{
    struct mutex *mutex = malloc(sizeof(struct mutex));
#ifdef WIN32
    InitializeCriticalSection(&(mutex->criticalSection));
#else
    int result = pthread_mutex_init(&(mutex->mutex), 0);
    if (result != 0)
        abort();
#endif
    mutex->ownerThreadId = 0;
    return mutex;
}

void mutex_acquire(struct mutex *mutex)
{
#ifdef WIN32
    EnterCriticalSection(&(mutex->criticalSection));
#else
    pthread_mutex_lock(&(mutex->mutex));
#endif
    if (mutex->ownerThreadId != 0)
        abort();
#ifdef WIN32
    mutex->ownerThreadId = GetCurrentThreadId();
#else
    mutex->ownerThreadId = pthread_self();
#endif
}

void mutex_release(struct mutex *mutex)
{
#ifdef WIN32
    if (mutex->ownerThreadId != GetCurrentThreadId())
        abort();
    mutex->ownerThreadId = 0;
    LeaveCriticalSection(&(mutex->criticalSection));
#else
    if (!pthread_equal(mutex->ownerThreadId, pthread_self()))
        abort();
    mutex->ownerThreadId = 0;
    pthread_mutex_unlock(&(mutex->mutex));
#endif
}

void mutex_dispose(struct mutex *mutex)
{
#ifdef WIN32
    DeleteCriticalSection(&(mutex->criticalSection));
#else
    pthread_mutex_destroy(&(mutex->mutex));
#endif
    free(mutex);
}

struct mutex_cond {
#ifdef WIN32
    CONDITION_VARIABLE cond;
#else
    pthread_cond_t cond;
#endif
};

struct mutex_cond *create_mutex_cond() {
    struct mutex_cond *result = malloc(sizeof(struct mutex_cond));
    if (result == 0) abort();
#ifdef WIN32
    InitializeConditionVariable(&result->cond);
#else
    if (pthread_cond_init(&result->cond, NULL) != 0)
        abort();
#endif
    return result;
}

void mutex_cond_wait(struct mutex_cond *cond, struct mutex *mutex) {
    mutex->ownerThreadId = 0;
#ifdef WIN32
    if (!SleepConditionVariableCS(&cond->cond, &mutex->criticalSection, INFINITE))
        abort();
#else
    if (pthread_cond_wait(&cond->cond, &mutex->mutex) != 0)
        abort();
#endif
#ifdef WIN32
    mutex->ownerThreadId = GetCurrentThreadId();
#else
    mutex->ownerThreadId = pthread_self();
#endif
}

void mutex_cond_signal(struct mutex_cond *cond) {
#ifdef WIN32
    WakeConditionVariable(&cond->cond);
#else
    if (pthread_cond_signal(&cond->cond) != 0)
        abort();
#endif
}

void mutex_cond_signal_all(struct mutex_cond *cond) {
#ifdef WIN32
    WakeAllConditionVariable(&cond->cond);
#else
    if (pthread_cond_broadcast(&cond->cond) != 0)
        abort();
#endif
}

void mutex_cond_dispose(struct mutex_cond *cond) {
#ifdef WIN32
    // Windows CONDITION_VARIABLEs need no cleanup
#else
    if (pthread_cond_destroy(&cond->cond) != 0)
        abort();
#endif
    free(cond);
}

struct leaky_mutex *create_leaky_mutex() {
    return (void *)create_mutex();
}

void leaky_mutex_acquire(struct leaky_mutex *mutex) {
    mutex_acquire((void *)mutex);
}

void leaky_mutex_release(struct leaky_mutex *mutex) {
    mutex_release((void *)mutex);
}

void leaky_mutex_dispose(struct leaky_mutex *mutex) {
    mutex_release((void *)mutex);
    mutex_dispose((void *)mutex);
}

struct leaky_mutex_cond *create_leaky_mutex_cond() {
    return (void *)create_mutex_cond();
}

void leaky_mutex_cond_wait(struct leaky_mutex_cond *cond, struct leaky_mutex *mutex) {
    mutex_cond_wait((void *)cond, (void *)mutex);
}

void leaky_mutex_cond_signal(struct leaky_mutex_cond *cond) {
    mutex_cond_signal((void *)cond);
}

void leaky_mutex_cond_signal_all(struct leaky_mutex_cond *cond) {
    mutex_cond_signal_all((void *)cond);
}

void leaky_mutex_cond_dispose(struct leaky_mutex_cond *cond) {
    mutex_cond_dispose((void *)cond);
}

void thread_sleep(unsigned int millis) {
#ifdef WIN32
    Sleep(millis);
#else
    struct timespec ts = { .tv_sec = millis / 1000, .tv_nsec = (millis % 1000) * 1000000 };
    if (nanosleep(&ts, 0))
        abort();
#endif
}
