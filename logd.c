// annotated by Ruben Kindt for the module verifast in the course Capita selecta van de software engineering (B-KUL-G0L15B)
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

/*@
predicate_family_instance thread_run_data(handle_connection)(struct connection *conn) =
  conn->logs |-> ?logs &*& conn->socket |-> ?sock &*& malloc_block_connection(conn) &*& 
  socket_input_stream(sock) &*& socket_output_stream(sock) &*& [?l]logs(logs, ?depth);

 predicate_ctor log_mal_pre(struct log *log)() =  log_size(log, ?size) &*& size<= INT_MAX &*& size>=0;

predicate logs(struct log *log, int depth) =
  log == 0 ?
   depth == 0
  :
   log->name |-> ?str &*& [_]string(str,_) &*& log->next |-> ?next
   &*& malloc_block_log(log) &*& logs(next, depth - 1) &*& log!=0
   &*& log->mutex |-> ?mutex &*& log->append_cond |-> ?append_cond
   &*& mutex(mutex,log_mal_pre(log)) &*& mutex_cond(append_cond,mutex);
@*/

#ifndef SEEK_END
#define SEEK_END 2
#endif

int get_file_size(char *name)
//@ requires [?fi]string(name, ?fcs);
//@ ensures [fi]string(name, fcs) &*& !(result > INT_MAX) &*& !(result < 0);
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
//@ requires [?b]string_buffer(name, _) &*& [?l]logs(logs, ?depth);
//@ ensures [b]string_buffer(name, _)   &*& [l]logs(result, _);
{
  for (;;)
  //@ invariant [b]string_buffer(name, _) &*& [l]logs(logs,_);
  {
    if (logs == 0)
      return 0;
    //@ open [l]logs(logs, ?depth2);
    if (string_buffer_equals_string(name, logs->name))
    { //added
      //@ close [l]logs(logs, depth2);
      return logs;
    }
    //@ leak [l]log_mutex(logs, ?mut);
    //@ leak [l]log_append_cond(logs, ?append_cond);  
    //@ leak [l]mutex(mut, _);
    //@ leak [l]mutex_cond(append_cond, mut);
  
    //@ leak [l]log_name(logs,?str);
    //@ leak [_]string(str,_);
    //@ leak [l]log_next(logs, ?next);
    //@ leak [l]malloc_block_log(logs);
    logs = logs->next;
  }
}


void fwrite_string_buffer(FILE *file, struct string_buffer *buffer)
//@ requires [?b]string_buffer(buffer, _) &*& [?fil]file(file);
//@ ensures  [b]string_buffer(buffer, _) &*& [fil]file(file);
{
  int bufferLength = string_buffer_get_length(buffer);
  char *bufferChars = string_buffer_get_chars(buffer);
  fwrite(bufferChars, 1, bufferLength, file);
  //@ string_buffer_minus_chars_elim();
}

void append_to_log(struct log *log, struct socket *socket, struct string_buffer *line)
/*@
 requires socket_input_stream(socket) &*& socket_output_stream(socket) 
   &*& string_buffer(line, _) &*& log!=0 &*& [?l]logs(log, ?depth) ;
@*/
//@ensures true;
{
  for (;;)
  /*@ invariant socket_input_stream(socket) &*& socket_output_stream(socket) 
       &*& string_buffer(line, _) &*& [l]logs(log, depth);
  @*/
  {
    socket_write_string(socket, "OK\n");
    printf("APPEND: Waiting for next line to append...\n");
    if (socket_read_line(socket, line)) {
      printf("APPEND: Error while reading line. Terminating the connection...\n");
      socket_close(socket);
      string_buffer_dispose(line);
      //@ leak [l]logs(log, depth);
      return;
    }
    printf("APPEND: Appending the line.\n");
    
    //@ open [l]logs(log, depth);
    mutex_acquire(log->mutex);
    FILE *f = fopen(log->name, "ab");
    if (f == 0) {
      mutex_release(log->mutex);
      socket_write_string(socket, "Could not open log file\n");
      socket_close(socket);
      string_buffer_dispose(line);
      printf("APPEND: Could not open log file '%s'. Terminating the connection...\n", log->name);
      //@ close [l]logs(log, depth);
      //@ leak [l]logs(log, depth); 
      return;
    }
    //@ open log_mal_pre(log)();
    fwrite_string_buffer(f, line);
    fputs("\n", f);
    fclose(f);
    int lineLength = string_buffer_get_length(line);
    if (INT_MAX - lineLength - 1 < log->size)
        abort();
    
    int newSize = log->size + lineLength + 1;
    log->size = newSize;
    //@ close log_mal_pre(log)();
    mutex_cond_signal(log->append_cond);
    mutex_release(log->mutex);
    printf("APPEND: Appended the line. New size of the log: %d bytes.\n", newSize);
    //@close [l]logs(log, depth);
  }
  //@ leak [l]logs(log, depth);
}

bool parse_string_buffer_as_decimal(struct string_buffer *buffer, int *intValue)
//@ requires [?f]string_buffer(buffer, ?cs) &*& *intValue |-> _;//given
//@ ensures [f]string_buffer(buffer, cs) &*& *intValue |-> ?value &*& result ? 0 <= value : true;//given
{
  int n = string_buffer_get_length(buffer);
  if (n == 0)
    return false;
  char *p = string_buffer_get_chars(buffer);
  int value = 0;
  bool result = true;
  for (; result && 0 < n; n--, p++)
  //@ requires [f]chars(p, n, ?ccs) &*& 0 <= value;//given
  //@ ensures [f]chars(old_p, old_n, ccs) &*& 0 <= value;//given
  {
    //@ chars_limits(p);//given
    //@ div_rem_nonneg(INT_MAX, 10);//given
    if (*p < '0' || '9' < *p || INT_MAX / 10 - (*p - '0') < value) {
      result = false;
    } else {
      value = value * 10 + (*p - '0');
    }
  }
  //@ string_buffer_minus_chars_elim();//given
  *intValue = value;
  return result;
}

int min(int x, int y)
//@ requires true;
//@ ensures x<y? result==x: result==y;
{
  return x < y ? x : y;
}

#ifndef SEEK_SET
#define SEEK_SET 0
#endif

void list_log(struct log *log, struct socket *socket, struct string_buffer *line)
/*@ requires log!=0 &*& socket_input_stream(socket) &*& 
   socket_output_stream(socket) &*& string_buffer(line, _) &*& [?l]logs(log, ?depth);
@*/
//@ ensures true;
{
  int offset;
  int maxNbBytes;
  
  //@ open [l]logs(log, depth);
  mutex_acquire(log->mutex);
  //@ open log_mal_pre(log)(); 
  int logSize = log->size;
  //@ close log_mal_pre(log)();
  mutex_release(log->mutex);
  //@ close [l]logs(log, depth);

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
  //@ open [l]logs(log, depth);
  FILE *f = fopen(log->name, "rb");
  //@ close [l]logs(log,depth);
  if (f == 0) {
    printf("LIST: An error occurred while opening the log file. Terminating the connection...\n");
    goto clean_up;
  }

  fseek(f, offset, SEEK_SET);
  char buffer[1000];
  while (0 < nbBytesToRead)
  //@ invariant chars(buffer, 1000, ?cs) &*& file(f) &*& socket_output_stream(socket);
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
  //@ leak [l]logs(log, depth);
}

void follow_log(struct log *log, struct socket *socket, struct string_buffer *line)
/*@ requires socket_input_stream(socket) &*& [?l]logs(log, ?depth)
      &*& log!=0 &*& socket_output_stream(socket) &*& string_buffer(line, _);
@*/
//@ ensures true;
{
  //@ open [l]logs(log, depth);
  mutex_acquire(log->mutex);
  //@ open log_mal_pre(log)();
  int logSize = log->size;
  //@ close log_mal_pre(log)();
  mutex_release(log->mutex);
  //@ close [l]logs(log, depth);
  printf("FOLLOW: Current size of the log file: %d bytes.\n", logSize);

  printf("FOLLOW: Waiting to read the offset...\n");
  if (socket_read_line(socket, line)) {
    printf("FOLLOW: An error occurred while reading the offset. Terminating the connection...\n");
    //@ leak [l]logs(log, depth);
    goto clean_up;
  }

  int offset;
  {
    int offsetVar;
    if (!parse_string_buffer_as_decimal(line, &offsetVar)) {
      printf("FOLLOW: The offset is not a valid decimal integer. Terminating the connection...\n");
      //@ leak [l]logs(log, depth);
      goto clean_up;
    }
    offset = offsetVar;
  }
  if (offset > logSize) {
    printf("FOLLOW: The offset is greater than the current log size. Terminating the connection...\n");
    //@ leak [l]logs(log, depth);
    goto clean_up;
  }
  //@ open [l]logs(log, depth);
  FILE *f = fopen(log->name, "rb");
  //@close [l]logs(log, depth);
  if (f == 0) {
    printf("FOLLOW: Failed to open the log. Terminating the connection...\n");
    //@ leak [l]logs(log, depth);
    goto clean_up;
  }

  fseek(f, offset, SEEK_SET);
  char buffer[1000];
  for (;;)
  /*@ invariant chars(buffer, 1000, _) &*& file(f) &*& logSize >= offset &*& offset >= 0 
        &*& socket_output_stream(socket) &*& [l]logs(log, depth);
  @*/
  {
    if (offset == logSize) {
      //@ open [l]logs(log, depth);
      mutex_acquire(log->mutex);
      //@ open log_mal_pre(log)();
  
      //@ assert mutex_held(?mutex, _, _, ?fm);//given
      for (;;)
      /*@ invariant log_size(log,?size) &*& mutex_held(mutex, _, _, fm);
      @*/;
      {
        logSize = log->size;
        if (offset < logSize)
          break;
        printf("FOLLOW: Reached the end of the log. Waiting for new entries to be appended...\n");
        mutex_cond_wait(log->append_cond, log->mutex);
      }
      //@ close log_mal_pre(log)();
      mutex_release(log->mutex);
      //@ close logs(log, depth);
      //@ leak [fm]mutex(mutex, _);//given
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
  //@ leak [l]logs(log, depth);
clean_up:
  socket_close(socket);
  string_buffer_dispose(line);

}

void handle_connection(struct connection *connection)//@ : thread_run
//@ requires thread_run_data(handle_connection)(connection);
//@ ensures true;
{
  //@ open thread_run_data(handle_connection)(connection);
  struct log *logs = connection->logs;
  struct socket *socket = connection->socket;
  free(connection);

  printf("Accepted a connection. Waiting to receive log filename...\n");

  struct string_buffer *line = create_string_buffer();
  if (socket_read_line(socket, line)) {
    printf("Error while reading the log filename. Terminating the connection...\n");
    socket_close(socket);
    string_buffer_dispose(line);
    //@leak [_]logs(logs, ?depth);
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
    //@ leak [_]logs(log, ?depth);
    return;
  } else {
    socket_write_string(socket, "OK\n");
  }

  printf("Waiting to receive the command...\n");

  if (socket_read_line(socket, line)) {
    printf("Error while reading the command. Terminating the connection...\n");
    socket_close(socket);
    string_buffer_dispose(line);
    //@ leak [_]logs(log, ?depth);
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
    //@ leak [_]logs(log, _);
  }
}

int main(int argc, char **argv)
//@ requires 0 <= argc &*& [_]argv(argv, argc, _);//given
//@ ensures true;//given
{
  struct log *logs = 0;
  //@ close logs(logs, 0);
  
  //@ open argv(argv, argc, _);//given
  if (argc > 0) {
    //@ pointer_limits(argv);//given
    argv++;
    argc--;
    for (; argc > 0; argc--, argv++)
    /*@ invariant [_]argv(argv, argc, _) &*& logs(logs, ?depth);
    @*/
    {
      char *name = *argv;
      struct log *newLog = malloc(sizeof(struct log));
      if (newLog == 0) abort();
      newLog->next = logs;
      newLog->name = name;
      int logSize = get_file_size(name);
      newLog->size = logSize;

      //@ close log_mal_pre(newLog)(); 
      //@ close create_mutex_ghost_arg(log_mal_pre(newLog));
      struct mutex *mutex = create_mutex();
      newLog->mutex = mutex;
      //@ close create_mutex_cond_ghost_args(newLog->mutex);
      struct mutex_cond *cond = create_mutex_cond();
      newLog->append_cond = cond;    
      logs = newLog;
      printf("Added log '%s' (current size: %d bytes)\n", name, logSize);
      //@ pointer_limits(argv); //given
      //@ close logs(newLog, depth + 1);
    }
  }

  struct server_socket *serverSocket = create_server_socket(1234);
  if (serverSocket == 0) {
    printf("Could not create server socket at port 1234. Terminating the program...\n");
    //@ leak [_]logs(logs, _);
    return 1;
  }

  //@ leak [_]logs(logs,_);
  for (;;)
  //@ invariant server_socket(serverSocket) &*& [_]logs(logs, _);
  {
    //@ leak [_]logs(logs,_);
    struct socket *socket = server_socket_accept(serverSocket);
    if (socket == 0) {
      printf("server_socket_accept failed. Terminating the program.\n");
      abort();
    }
    struct connection *connection = malloc(sizeof(struct connection));
    if (connection == 0) abort();
    connection->logs = logs;
    connection->socket = socket;
    //@ close thread_run_data(handle_connection)(connection);
    thread_start(handle_connection, connection);
  }
}
