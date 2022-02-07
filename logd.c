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
predicate logs_pre(struct log *log, struct log *next) =
  log->name |-> ?n &*& string(n,_) &*& log->next |-> next &*&
   log->mutex |-> ?mutex &*& logs_pre(next, _) &*& log_mutex_pre(log,_);
    // &*& string(n,_) &*& log_name(log, n)
@*/
/*@
 predicate_ctor log_mal_pre(struct log *log)() =
  log->name |-> ?name &*& log->next |-> ?next &*& log->size |-> ?size
  &*& malloc_block_log(log);// &*& log->append_cond |-> ?append_cond &*& log->mutex |-> ?mutex
  
    // &*& string(n,_) &*& log_name(log, n)

@*/

/*@
 predicate_ctor log_con_pre(struct log *log)() =
  log->name |-> ?name &*& log->next |-> ?next &*& log->size |-> ?size
  &*& malloc_block_log(log);// &*& log->append_cond |-> ?append_cond &*& log->mutex |-> ?mutex
  
    // &*& string(n,_) &*& log_name(log, n)

@*/

/*@
predicate logs_pre2(struct log *log, struct string_buffer *name) =
  log->name |-> ?n &*& string(n,_) &*& log->next |-> ?next &*&
   logs_pre2(next, name) &*& log_mutex_pre(log,_); // &*& log_name(log, n)
@*/

#ifndef SEEK_END
#define SEEK_END 2
#endif

int get_file_size(char *name)
//@ requires [?fi]string(name, ?fcs);
//@ ensures [fi]string(name, fcs);
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
//@ requires [?b]string_buffer(name, _) &*& logs->name |-> ?str &*& string(str,_);// &*& [?l]logs_pre(logs,?next);
//@ ensures [b]string_buffer(name, _) ;//&*& [l]logs_pre(result,_);
{
  for (;;)
  /*@ invariant  [b]string_buffer(name, _) &*& logs->name |-> _ &*& string(str,_);//&*& [l]logs_pre(logs,_) ;
         //&*& logs == 0 ? true: logs_pre(logs, name) &*& logs->next |-> ?next &*& logs_pre(next, name);
  @*/
  {
    if (logs == 0){
    //@ leak log_name(logs, _);
    //@ leak string(str,_);
      return 0;}
    
    // @ open logs_pre(logs, ?n);
    if (string_buffer_equals_string(name, logs->name)){ //todo
      //@ close [l]logs_pre(logs, n);
      return logs;}
    //@ close [l]logs_pre(logs, n);
          
    //@ open [_]logs_pre(logs, ?nnext);
    //@ leak [l]log_mutex_pre(logs,_);
    //@ leak [l]log_mutex(logs,_);
    //@ leak [l]log_name(?llogs,?nkl);
    //@ leak [l]string(nkl,_);
    
    logs = logs->next;
    //@ leak [_]log_next(llogs,_);
  }
}


void fwrite_string_buffer(FILE *file, struct string_buffer *buffer)
//@ requires [?b]string_buffer(buffer, _) &*& [?fil]file(file);
//@ ensures  [b]string_buffer(buffer, _) &*& [fil]file(file); //todo check if terug geven of leak beter is, deze zou goed moeten zijn 
{
  int bufferLength = string_buffer_get_length(buffer);
  char *bufferChars = string_buffer_get_chars(buffer);
  fwrite(bufferChars, 1, bufferLength, file);
  //@ string_buffer_minus_chars_elim();
  ///@ leak [1/2]chars(_,_,_);
  ///@ leak [1/2]string_buffer_minus_chars(_,_,_);
}

/*@
predicate log_mutex_pre(struct log *log, struct mutex *mutex) =
  log->mutex |-> ?m &*& mutex(m, ?p) &*& log->name |-> ?n &*& string(n, _) &*& 
  log->size |-> ?size &*& log->append_cond |-> ?append_cond &*& mutex_cond(append_cond, m); // &*& log_name(log, n)
@*/

void append_to_log(struct log *log, struct socket *socket, struct string_buffer *line) //todo mogelijks moeten hier meer[iets of_] bij
/*@
 requires socket_input_stream(socket) &*& socket_output_stream(socket) &*& string_buffer(line, _)
   &*& logs_pre(log,_);// &*& log_mutex_pre(log,_);// &*& log->mutex |-> ?mutex;
@*/
//@ensures logs_pre(log,_);
{
  for (;;)
  /*@ invariant socket_input_stream(socket) &*& socket_output_stream(socket) &*& string_buffer(line, _)
       &*& logs_pre(log,_) ;// &*& log_mutex_pre(log,_);
  @*/
  {
    ///@ close socket_output_stream(socket);
    socket_write_string(socket, "OK\n");
    printf("APPEND: Waiting for next line to append...\n");
    if (socket_read_line(socket, line)) {
      printf("APPEND: Error while reading line. Terminating the connection...\n");
      socket_close(socket);
      string_buffer_dispose(line);
      ///@ leak logs_pre(_, _);
      ///@ leak log_mutex_pre(_,_);
      return;
    }
    printf("APPEND: Appending the line.\n");
    //@ open logs_pre(log,_);
    //@ open log_mutex_pre(log,_);// log->mutex);
    mutex_acquire(log->mutex);
    FILE *f = fopen(log->name, "ab");
    if (f == 0) {
      mutex_release(log->mutex);
      socket_write_string(socket, "Could not open log file\n");
      socket_close(socket);
      string_buffer_dispose(line);
      printf("APPEND: Could not open log file '%s'. Terminating the connection...\n", log->name);
      
      //@ leak logs_pre(_, _);
      //@ leak log_mutex(log,_);
      //@ leak log_name(log,_);
      //@ leak mutex(_,_);
      //@ leak string(_,_);
      //@ leak log_size(log, _);
      //@ leak log_append_cond(log, _);
      //@ leak mutex_cond(_, _);      
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
    //@close log_mutex_pre(log, log->mutex);
  }
  
}

bool parse_string_buffer_as_decimal(struct string_buffer *buffer, int *intValue)
//correct
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
  //correct
  //@ requires [f]chars(p, n, ?ccs) &*& 0 <= value;
  //@ ensures [f]chars(old_p, old_n, ccs) &*& 0 <= value;
  {
    //correct
    //@ chars_limits(p);
    //@ div_rem_nonneg(INT_MAX, 10);
    if (*p < '0' || '9' < *p || INT_MAX / 10 - (*p - '0') < value) {
      result = false;
    } else {
      value = value * 10 + (*p - '0');
    }
  }
  //correct
  //@ string_buffer_minus_chars_elim();
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
/*@ requires [?l]logs_pre(log,?next) &*& socket_input_stream(socket) &*& 
   socket_output_stream(socket) &*& string_buffer(line, _);
@*/
//@ ensures [l]logs_pre(log,next); //todo
{
  int offset;
  int maxNbBytes;
  
  //@ open [?p]logs_pre(log,next);
  //@ open [?m]log_mutex_pre(log,?iets);
  mutex_acquire(log->mutex);
  int logSize = log->size;

  mutex_release(log->mutex);
  //@ close [m]log_mutex_pre(log,iets);
  //@ close [p]logs_pre(log,next);


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
  //@ open [?g]logs_pre(log,next);
  FILE *f = fopen(log->name, "rb");
  //@ close [g]logs_pre(log,next);
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
  ///@ leak [l]logs_pre(log,next);
}

void follow_log(struct log *log, struct socket *socket, struct string_buffer *line)
/*@ requires logs_pre(log, ?next) &*& socket_input_stream(socket) 
      &*& socket_output_stream(socket) &*& string_buffer(line, _);
@*/
//@ ensures logs_pre(log, next);
{
  //@ open logs_pre(log,_);
  //@ open log_mutex_pre(log,_);
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
      //correct
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
      //correct
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

void handle_connection(struct connection *connection)//@ : thread_run
//@ requires thread_run_data(handle_connection)(connection) ;
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
    // @ leak logs_pre(logs,_);
    //@ leak log_name(logs, _);
    return;
  }
  
  char *logName = string_buffer_get_string(line);
  printf("Received log filename '%s'.\n", logName);
  free(logName);

  // leak string_buffer(line,_);
  struct log *log = lookup_log(logs, line);

  if (log == 0) {
    socket_write_string(socket, "No such log\n");
    printf("No such log. Terminating the connection...\n");
    socket_close(socket);
    string_buffer_dispose(line);
    //@ leak logs_pre(_,_);
    return;
  } else {
    socket_write_string(socket, "OK\n");
  }

  printf("Waiting to receive the command...\n");

  if (socket_read_line(socket, line)) {
    printf("Error while reading the command. Terminating the connection...\n");
    socket_close(socket);
    string_buffer_dispose(line);
    //@ leak logs_pre(_,_);
    return;
  }
  
  ///@ open logs_pre(?lg,?test2);
  if (string_buffer_equals_string(line, "APPEND"))
    // test
    append_to_log(log, socket, line);
  else if (string_buffer_equals_string(line, "LIST"))
    list_log(log, socket, line);
    // leak logs_pre(log,_);
  else if (string_buffer_equals_string(line, "FOLLOW"))
    follow_log(log, socket, line);
  else {
    socket_write_string(socket, "No such command\n");
    printf("No such command. Terminating the connection...\n");
    socket_close(socket);
    string_buffer_dispose(line);
  }
  //@ leak logs_pre(log,_);
  ///@ leak socket_input_stream(?sock);
  ///@ leak socket_output_stream(sock);
  
}


/*@
predicate_family_instance thread_run_data(handle_connection)(struct connection *conn) =
  conn->logs |-> ?logs &*& logs->name |-> _ &*& conn->socket |-> ?sock &*& malloc_block_connection(conn) &*& 
  socket_input_stream(sock) &*& socket_output_stream(sock) ;//&*& logs==0 ? logs_pre(0, _) : logs_pre(logs,_);
  // &*& 
  //&*&
  //[1/2]counter->mutex |-> ?mutex &*& [1/3]mutex(mutex, counter(counter));
@*/

int main(int argc, char **argv)
//corect
//@ requires 0 <= argc &*& [_]argv(argv, argc, _);
//@ ensures true;
{
  ///@ assume (1 == argc); //todo rm
  struct log *logs = 0;
  //correct
  //@ open argv(argv, argc, _);
  if (argc > 0) {
    //correct
    //@ pointer_limits(argv);
    argv++;
    argc--;
    for (; argc > 0; argc--, argv++)
    //@ invariant [_]argv(argv, argc, _) ;//&*& pointer_limits(argv); // TODO: Extend this invariant.
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
      //@ leak newLog->mutex |-> mutex &*& mutex(mutex,_);
      //@ close create_mutex_cond_ghost_args(newLog->mutex);
      struct mutex_cond *cond = create_mutex_cond();
      newLog->append_cond = cond;
      //@ leak newLog->append_cond |-> cond &*& mutex_cond(cond,_);
      logs = newLog;
      printf("Added log '%s' (current size: %d bytes)\n", name, logSize);
      //correct
      //@ pointer_limits(argv);
      // prob close log
    }
  }

  struct server_socket *serverSocket = create_server_socket(1234);
  if (serverSocket == 0) {
    printf("Could not create server socket at port 1234. Terminating the program...\n");
    return 1;
  }

  for (;;)
  //@ invariant server_socket(serverSocket);
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
    ///@ open logs_pre(logs,_);
    //@ close thread_run_data(handle_connection)(connection);
    thread_start(handle_connection, connection);
    ///@ leak thread_run_data(handle_connection)(connection);
    
  }
}
