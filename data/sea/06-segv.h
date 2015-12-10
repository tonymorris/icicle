#include "05-error.h"

/* this global is pretty nasty, don't know how else we can get
 * information in a signal handler though */
static const size_t segv_user_data_size = 1024*1024;
static char segv_user_data[segv_user_data_size];

static void segv_handler (int sig)
{
    void *frames[50];
    size_t n_frames = backtrace (frames, sizeof(frames));

    fprintf (stderr, "icicle: segmentation fault:\n");
    backtrace_symbols_fd (frames, n_frames, STDERR_FILENO);
    fprintf (stderr, "\n%s\n", segv_user_data);

    exit (1);
}

void segv_install_handler (const char *user_data, size_t user_data_size)
{
    size_t size = MIN (user_data_size, segv_user_data_size-1);
    memcpy (segv_user_data, user_data, size);
    segv_user_data[size] = '\0';

    struct sigaction act;

    sigemptyset (&act.sa_mask);
    act.sa_flags   = 0;
    act.sa_handler = segv_handler;

    sigaction (SIGSEGV, &act, NULL);
}

void segv_remove_handler ()
{
    struct sigaction act;

    sigemptyset (&act.sa_mask);
    act.sa_flags   = 0;
    act.sa_handler = SIG_DFL;

    sigaction (SIGSEGV, &act, NULL);
}
