#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include "threading.h"
#include "sockets.h"
#include "stringBuffers.h"

struct log {
  struct log *next;
  char *name;
  struct mutex *mutex;
  struct mutex_cond *append_cond;
  int size;
};

#ifndef SEEK_END
#define SEEK_END 2
#endif

int get_file_size(char *name)
{
  FILE *f = fopen(name, "rb");
  if (f == 0) {
    printf("Could not open file '%s'\n", name);
    abort();
  }
  fseek(f, 0, SEEK_END);
  long result = ftell(f);
  fclose(f);
  if (result < 0) {
    printf("Could not determine the size of log file '%s'. Terminating the program...\n", name);
    abort();
  }
  if (result > INT_MAX) {
    printf("Log too big. Terminating the program...\n");
    abort();
  }
  return (int)result;
}

struct connection {
  struct log *logs;
  struct socket *socket;
};

struct log *lookup_log(struct log *logs, struct string_buffer *name)
{
  for (;;)
  {
    if (logs == 0)
      return 0;
    if (string_buffer_equals_string(name, logs->name))
      return logs;
    logs = logs->next;
  }
}

void fwrite_string_buffer(FILE *file, struct string_buffer *buffer)
{
  int bufferLength = string_buffer_get_length(buffer);
  char *bufferChars = string_buffer_get_chars(buffer);
  fwrite(bufferChars, 1, bufferLength, file);
}

void append_to_log(struct log *log, struct socket *socket, struct string_buffer *line)
{
  for (;;)
  {
    socket_write_string(socket, "OK\n");
    printf("APPEND: Waiting for next line to append...\n");
    if (socket_read_line(socket, line)) {
      printf("APPEND: Error while reading line. Terminating the connection...\n");
      socket_close(socket);
      string_buffer_dispose(line);
      return;
    }
    printf("APPEND: Appending the line.\n");
    mutex_acquire(log->mutex);
    FILE *f = fopen(log->name, "ab");
    if (f == 0) {
      mutex_release(log->mutex);
      socket_write_string(socket, "Could not open log file\n");
      socket_close(socket);
      string_buffer_dispose(line);
      printf("APPEND: Could not open log file '%s'. Terminating the connection...\n", log->name);
      return;
    }
    fwrite_string_buffer(f, line);
    fputs("\n", f);
    fclose(f);
    int lineLength = string_buffer_get_length(line);
    if (INT_MAX - lineLength - 1 < log->size)
        abort();
    int newSize = log->size + lineLength + 1;
    log->size = newSize;
    mutex_cond_signal(log->append_cond);
    mutex_release(log->mutex);
    printf("APPEND: Appended the line. New size of the log: %d bytes.\n", newSize);
  }
}

bool parse_string_buffer_as_decimal(struct string_buffer *buffer, int *intValue)
//@ requires [?f]string_buffer(buffer, ?cs) &*& *intValue |-> _;
//@ ensures [f]string_buffer(buffer, cs) &*& *intValue |-> ?value &*& result ? 0 <= value : true;
{
  int n = string_buffer_get_length(buffer);
  if (n == 0)
    return false;
  char *p = string_buffer_get_chars(buffer);
  int value = 0;
  bool result = true;
  for (; result && 0 < n; n--, p++)
  //@ requires [f]chars(p, n, ?ccs) &*& 0 <= value;
  //@ ensures [f]chars(old_p, old_n, ccs) &*& 0 <= value;
  {
    //@ chars_limits(p);
    //@ div_rem_nonneg(INT_MAX, 10);
    if (*p < '0' || '9' < *p || INT_MAX / 10 - (*p - '0') < value) {
      result = false;
    } else {
      value = value * 10 + (*p - '0');
    }
  }
  //@ string_buffer_minus_chars_elim();
  *intValue = value;
  return result;
}

int min(int x, int y)
{
  return x < y ? x : y;
}

#ifndef SEEK_SET
#define SEEK_SET 0
#endif

void list_log(struct log *log, struct socket *socket, struct string_buffer *line)
{
  int offset;
  int maxNbBytes;

  mutex_acquire(log->mutex);
  int logSize = log->size;
  mutex_release(log->mutex);

  printf("LIST: Current size of the log: %d bytes.\n", logSize);

  printf("LIST: Waiting to read the offset...\n");
  if (socket_read_line(socket, line)) {
    printf("LIST: An error occurred while reading the offset. Terminating the connection...\n");
    goto clean_up;
  }

  if (!parse_string_buffer_as_decimal(line, &offset)) {
    printf("LIST: The offset is not a valid decimal integer. Terminating the connection...\n");
    goto clean_up;
  }
  if (offset > logSize) {
    printf("LIST: The offset is greater than the size of the log. Terminating the connection...\n");
    goto clean_up;
  }

  printf("LIST: Waiting to read the maximum number of log bytes to transfer...\n");
  if (socket_read_line(socket, line)) {
    printf("LIST: An error occurred while reading the maximum number of bytes to transfer. Terminating the connection...\n");
    goto clean_up;
  }

  if (!parse_string_buffer_as_decimal(line, &maxNbBytes)) {
    printf("LIST: The maximum number of bytes to transfer is not a valid decimal integer. Terminating the connection...\n");
    goto clean_up;
  }

  int nbBytesToRead = min(logSize - offset, maxNbBytes);
  printf("LIST: Transferring %d bytes (= the minimum of %d (the log size %d - offset %d) and the specified maximum number of bytes to transfer %d)...\n", nbBytesToRead, logSize - offset, logSize, offset, maxNbBytes);

  printf("LIST: Opening the log...\n");
  FILE *f = fopen(log->name, "rb");
  if (f == 0) {
    printf("LIST: An error occurred while opening the log file. Terminating the connection...\n");
    goto clean_up;
  }

  fseek(f, offset, SEEK_SET);
  char buffer[1000];
  while (0 < nbBytesToRead)
  {
    int nbBytesToReadNow = min(nbBytesToRead, 1000);
    printf("LIST: Trying to read %d bytes.\n", nbBytesToReadNow);
    int nbBytesRead = fread(buffer, 1, nbBytesToReadNow, f);
    printf("LIST: Read %d bytes.\n", nbBytesRead);
    if (nbBytesRead == 0) {
      printf("LIST: An error occurred while trying to read from the log file. Terminating the connection...\n");
      fclose(f);
      goto clean_up;
    }
    socket_write_chars(socket, buffer, nbBytesRead);
    printf("LIST: Wrote %d bytes.\n", nbBytesRead);
    nbBytesToRead -= nbBytesRead;
  }
  fclose(f);
  printf("LIST: Done; terminating the connection...\n");

clean_up:
  socket_close(socket);
  string_buffer_dispose(line);
}

void follow_log(struct log *log, struct socket *socket, struct string_buffer *line)
{
  mutex_acquire(log->mutex);
  int logSize = log->size;
  mutex_release(log->mutex);
  printf("FOLLOW: Current size of the log file: %d bytes.\n", logSize);

  printf("FOLLOW: Waiting to read the offset...\n");
  if (socket_read_line(socket, line)) {
    printf("FOLLOW: An error occurred while reading the offset. Terminating the connection...\n");
    goto clean_up;
  }

  int offset;
  {
    int offsetVar;
    if (!parse_string_buffer_as_decimal(line, &offsetVar)) {
      printf("FOLLOW: The offset is not a valid decimal integer. Terminating the connection...\n");
      goto clean_up;
    }
    offset = offsetVar;
  }
  if (offset > logSize) {
    printf("FOLLOW: The offset is greater than the current log size. Terminating the connection...\n");
    goto clean_up;
  }

  FILE *f = fopen(log->name, "rb");
  if (f == 0) {
    printf("FOLLOW: Failed to open the log. Terminating the connection...\n");
    goto clean_up;
  }

  fseek(f, offset, SEEK_SET);
  char buffer[1000];
  for (;;)
  {
    if (offset == logSize) {
      mutex_acquire(log->mutex);
      //@ assert mutex_held(?mutex, _, _, ?fm);
      for (;;)
      {
        logSize = log->size;
        if (offset < logSize)
          break;
        printf("FOLLOW: Reached the end of the log. Waiting for new entries to be appended...\n");
        mutex_cond_wait(log->append_cond, log->mutex);
      }
      mutex_release(log->mutex);
      //@ leak [fm]mutex(mutex, _);
    }

    int nbBytesToReadNow = min(logSize - offset, 1000);
    printf("FOLLOW: Trying to read %d bytes...\n", nbBytesToReadNow);
    int nbBytesRead = fread(buffer, 1, nbBytesToReadNow, f);
    printf("FOLLOW: Read %d bytes.\n", nbBytesRead);
    if (nbBytesRead == 0) {
      printf("FOLLOW: Failed to read any bytes. Terminating the connection...\n");
      break;
    }
    socket_write_chars(socket, buffer, nbBytesRead);
    printf("FOLLOW: Transferred %d bytes.\n", nbBytesRead);
    offset += nbBytesRead;
  }
  fclose(f);

clean_up:
  socket_close(socket);
  string_buffer_dispose(line);
}

void handle_connection(struct connection *connection)
{
  struct log *logs = connection->logs;
  struct socket *socket = connection->socket;
  free(connection);

  printf("Accepted a connection. Waiting to receive log filename...\n");

  struct string_buffer *line = create_string_buffer();
  if (socket_read_line(socket, line)) {
    printf("Error while reading the log filename. Terminating the connection...\n");
    socket_close(socket);
    string_buffer_dispose(line);
    return;
  }

  char *logName = string_buffer_get_string(line);
  printf("Received log filename '%s'.\n", logName);
  free(logName);

  struct log *log = lookup_log(logs, line);
  if (log == 0) {
    socket_write_string(socket, "No such log\n");
    printf("No such log. Terminating the connection...\n");
    socket_close(socket);
    string_buffer_dispose(line);
    return;
  } else {
    socket_write_string(socket, "OK\n");
  }

  printf("Waiting to receive the command...\n");

  if (socket_read_line(socket, line)) {
    printf("Error while reading the command. Terminating the connection...\n");
    socket_close(socket);
    string_buffer_dispose(line);
    return;
  }

  if (string_buffer_equals_string(line, "APPEND"))
    append_to_log(log, socket, line);
  else if (string_buffer_equals_string(line, "LIST"))
    list_log(log, socket, line);
  else if (string_buffer_equals_string(line, "FOLLOW"))
    follow_log(log, socket, line);
  else {
    socket_write_string(socket, "No such command\n");
    printf("No such command. Terminating the connection...\n");
    socket_close(socket);
    string_buffer_dispose(line);
  }
}

int main(int argc, char **argv)
//@ requires 0 <= argc &*& [_]argv(argv, argc, _);
//@ ensures true;
{
  struct log *logs = 0;
  //@ open argv(argv, argc, _);
  if (argc > 0) {
    //@ pointer_limits(argv);
    argv++;
    argc--;
    for (; argc > 0; argc--, argv++)
    //@ invariant [_]argv(argv, argc, _); // TODO: Extend this invariant.
    {
      char *name = *argv;
      struct log *newLog = malloc(sizeof(struct log));
      if (newLog == 0) abort();
      newLog->next = logs;
      newLog->name = name;
      int logSize = get_file_size(name);
      newLog->size = logSize;
      struct mutex *mutex = create_mutex();
      newLog->mutex = mutex;
      struct mutex_cond *cond = create_mutex_cond();
      newLog->append_cond = cond;
      logs = newLog;
      printf("Added log '%s' (current size: %d bytes)\n", name, logSize);
      //@ pointer_limits(argv);
    }
  }

  struct server_socket *serverSocket = create_server_socket(1234);
  if (serverSocket == 0) {
    printf("Could not create server socket at port 1234. Terminating the program...\n");
    return 1;
  }

  for (;;)
  {
    struct socket *socket = server_socket_accept(serverSocket);
    if (socket == 0) {
      printf("server_socket_accept failed. Terminating the program.\n");
      abort();
    }
    struct connection *connection = malloc(sizeof(struct connection));
    if (connection == 0) abort();
    connection->logs = logs;
    connection->socket = socket;
    thread_start(handle_connection, connection);
  }
}
