#ifndef SOCKETS_H
#define SOCKETS_H

#include <stdbool.h>
#include <stdlib.h>
#include "stringBuffers.h"

struct server_socket;
struct socket;

/*@
predicate server_socket(struct server_socket *serverSocket;);
predicate socket_input_stream(struct socket *socket;);
predicate socket_output_stream(struct socket *socket;);
@*/

struct server_socket *create_server_socket(int port);
    //@ requires emp;
    //@ ensures result == 0 ? true : server_socket(result);
struct socket *server_socket_accept(struct server_socket *serverSocket);
    //@ requires server_socket(serverSocket);
    //@ ensures server_socket(serverSocket) &*& result == 0 ? true : socket_input_stream(result) &*& socket_output_stream(result);
void server_socket_close(struct server_socket *serverSocket);
    //@ requires server_socket(serverSocket);
    //@ ensures true;

struct socket *create_client_socket(char *host, int port);
    //@ requires true;
    //@ ensures socket_input_stream(result) &*& socket_output_stream(result);

void socket_write_string_buffer(struct socket *socket, struct string_buffer *buffer);
    //@ requires socket_output_stream(socket) &*& [?f]string_buffer(buffer, ?cs);
    //@ ensures socket_output_stream(socket) &*& [f]string_buffer(buffer, cs);

void socket_write_string(struct socket* socket, char* string);
    //@ requires socket_output_stream(socket) &*& [?f]string(string, ?cs);
    //@ ensures socket_output_stream(socket) &*& [f]string(string, cs);

void socket_write_chars(struct socket* socket, char* buffer, int len);
    //@ requires socket_output_stream(socket) &*& [?f]chars(buffer, len, ?cs);
    //@ ensures socket_output_stream(socket) &*& [f]chars(buffer, len, cs);

void socket_write_integer_as_decimal(struct socket *socket, int value);
    //@ requires socket_output_stream(socket);
    //@ ensures socket_output_stream(socket);
bool socket_wait_for_char(struct socket *socket);
    //@ requires socket_input_stream(socket);
    //@ ensures socket_input_stream(socket);
/** Returns `false` on success; `true` on failure. */
bool socket_read_line(struct socket *socket, struct string_buffer *buffer);
    //@ requires socket_input_stream(socket) &*& string_buffer(buffer, _);
    //@ ensures socket_input_stream(socket) &*& string_buffer(buffer, _);
char* socket_read_line_as_string(struct socket* socket);
    //@ requires socket_input_stream(socket);
    //@ ensures socket_input_stream(socket) &*& result == 0 ? true : string(result, ?cs) &*& malloc_block(result, length(cs) + 1);
int socket_read_nonnegative_integer(struct socket *socket);
    //@ requires socket_input_stream(socket);
    //@ ensures socket_input_stream(socket);
void socket_close(struct socket *socket);
    //@ requires socket_input_stream(socket) &*& socket_output_stream(socket);
    //@ ensures emp;

#endif
