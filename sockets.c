#include <stdbool.h>
#include <stdlib.h> /* abort */
#include <string.h> /* memset */
#include <stdio.h> /* printf, perror */
#include <sys/types.h>

#ifdef WIN32

//#include <winsock.h> /* send, recv */
#include <winsock2.h>
#include <ws2tcpip.h>
#include <process.h> /* _exit */
#define snprintf sprintf_s

#else

#include <sys/socket.h>   /* socket(), bind(), listen(), accept() */
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <unistd.h> /* fork, write, close */
#define SOCKET int
#define INVALID_SOCKET (-1)
#define SOCKADDR_IN struct sockaddr_in
#define SOCKADDR struct sockaddr

#endif

#include "stringBuffers.h"
#include "sockets.h"

void print_socket_error_message(char *api)
{
#ifdef WIN32
    int error = WSAGetLastError();
    char *msg = 0;
    FormatMessage(FORMAT_MESSAGE_ALLOCATE_BUFFER | FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS, NULL, error, MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT), (void *)&msg, 0, NULL);
    fprintf(stderr, "Socket API call '%s' failed: error code %d: %s\n", api, error, msg);
    LocalFree(msg);
#else
    perror(api);
#endif
}

SOCKET socket_create_and_listen(int port)
{
    SOCKET serverSocket = 0;
    struct sockaddr_in serverName = { 0 };
    int status = 0;

#ifdef WIN32
    {
        WSADATA windowsSocketsApiData;
        WSAStartup(MAKEWORD(2, 0), &windowsSocketsApiData);
    }
#endif

    serverSocket = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (INVALID_SOCKET == serverSocket)
    {
        //print_socket_error_message("socket()");
        return INVALID_SOCKET;
    }
    
    serverName.sin_addr.s_addr=htonl(INADDR_ANY);
    serverName.sin_family = AF_INET;
    /* network-order */
    serverName.sin_port = htons(port);

    status = bind(serverSocket, (struct sockaddr *) &serverName, sizeof(serverName));
    if (INVALID_SOCKET == status)
    {
        return INVALID_SOCKET;
    }
    
    status = listen(serverSocket, 5);  // Allow 5 pending incoming connection requests
    if (INVALID_SOCKET == status)
    {
        return INVALID_SOCKET;
    }

    return serverSocket;
}

SOCKET socket_accept(SOCKET serverSocket)
{
    struct sockaddr_in clientName = { 0 };
    SOCKET slaveSocket;
    socklen_t clientLength = sizeof(clientName);

    (void) memset(&clientName, 0, sizeof(clientName));

    slaveSocket = accept(serverSocket, (struct sockaddr *) &clientName, &clientLength);
    if (INVALID_SOCKET == slaveSocket)
    {
        return INVALID_SOCKET;
    }
    
    return slaveSocket;
}

SOCKET socket_create(char *host, int port)
{
#ifdef WIN32
    {
        WSADATA windowsSocketsApiData;
        WSAStartup(MAKEWORD(2, 0), &windowsSocketsApiData);
    }
#endif

    struct addrinfo hints;
    struct addrinfo *addresses;
    char portText[12];
    
    {
        int result = snprintf(portText, sizeof(portText), "%d", port);
        if (result < 0 || result >= sizeof(portText))
            abort();
    }

    memset(&hints, 0, sizeof(struct addrinfo));
    hints.ai_family = AF_UNSPEC; // Allow both IPv4 and IPv6
    hints.ai_socktype = SOCK_STREAM;

    {
        int result = getaddrinfo(host, portText, &hints, &addresses);
        if (result != 0) {
#ifdef WIN32
            print_socket_error_message("getaddrinfo()");
#else
            const char *msg = gai_strerror(result);
            fprintf(stderr, "getaddrinfo(): %s\n", msg);
#endif
            abort();
        }
    }

    char *api = 0;

    for (struct addrinfo *address = addresses; address != NULL; address = address->ai_next) {
        api = "socket()";
        SOCKET socketHandle = socket(address->ai_family, address->ai_socktype, address->ai_protocol);
        if (socketHandle == INVALID_SOCKET)
            continue;
        api = "connect()";
        if (connect(socketHandle, address->ai_addr, address->ai_addrlen) == 0)
            return socketHandle;
    #ifdef WIN32
        closesocket(socketHandle);
    #else
        close(socketHandle);
    #endif
    }
    print_socket_error_message(api);
    abort();
}

struct server_socket {
    int handle;
};

struct server_socket *create_server_socket(int port)
{
    int handle;
    struct server_socket *serverSocket = malloc(sizeof(struct server_socket));
    if(serverSocket == 0) return 0;
    handle = socket_create_and_listen(port);
    if(handle == INVALID_SOCKET) {
      free(serverSocket);
      return 0;
    }
    serverSocket->handle = handle;
    return serverSocket;
}

#define READER_BUFFER_SIZE 4096

struct socket {
    int handle;
    struct reader *reader;
    struct writer *writer;
};

struct reader {
    int handle;
    char *bufferStart;
    char *bufferEnd;
    char buffer[READER_BUFFER_SIZE];
};

bool reader_read(struct reader *reader)
{
    reader->bufferStart = reader->buffer;
    {
        ssize_t count = recv(reader->handle, reader->buffer, READER_BUFFER_SIZE, 0);
        if (count < 0) {
            //print_socket_error_message("recv()");
            //abort();
            return true;
        }
        if (count == 0)
            return true;
        reader->bufferEnd = reader->buffer + count;
    }
    return false;
}

bool reader_read_line(struct reader *reader, struct string_buffer *buffer)
{
    string_buffer_clear(buffer);
    for (;;)
    {
        void *newline = memchr(reader->bufferStart, '\n', reader->bufferEnd - reader->bufferStart);
        if (newline != 0) {
            char *end = (char *)newline;
            if (reader->bufferStart < end && *(end - 1) == '\r')
                end--;
            string_buffer_append_chars(buffer, reader->bufferStart, end - reader->bufferStart);
            reader->bufferStart = (char *)newline + 1;
            return false;
        } else {
            string_buffer_append_chars(buffer, reader->bufferStart, reader->bufferEnd - reader->bufferStart);
            if (reader_read(reader))
                return true;
        }
    }
}

bool socket_wait_for_char(struct socket *socket)
{
    if (socket->reader->bufferEnd > socket->reader->bufferStart)
        return false;
    return reader_read(socket->reader);
}

bool socket_read_line(struct socket* socket, struct string_buffer* buffer) 
{
  return reader_read_line(socket->reader, buffer);
}

char *reader_read_line_as_string(struct reader *reader)
{
    struct string_buffer *buffer = create_string_buffer();
    bool eof = reader_read_line(reader, buffer);
    if (eof) {
        string_buffer_dispose(buffer);
        return 0;
    }
    return string_buffer_to_string(buffer);
}

char* socket_read_line_as_string(struct socket *socket)
{
  return reader_read_line_as_string(socket->reader);
}

int reader_read_nonnegative_integer(struct reader *reader)
{
    char *line = reader_read_line_as_string(reader);
    int value;
    if (line == 0) return -1;
    sscanf(line, "%d", &value);
    free(line);
    return value;
}

int socket_read_nonnegative_integer(struct socket* socket)
{
  return reader_read_nonnegative_integer(socket->reader);
}

struct writer {
    int handle;
};

void writer_write_string(struct writer *writer, char *text)
{
    size_t length = strlen(text);
    send(writer->handle, text, length, 0);
}

void socket_write_string(struct socket* socket, char* text)
{
  writer_write_string(socket->writer, text);
}

void writer_write_integer_as_decimal(struct writer *writer, int value)
{
    char buffer[40];
    snprintf(buffer, 40, "%d", value);
    writer_write_string(writer, buffer);
}

void socket_write_integer_as_decimal(struct socket* socket, int value)
{
  writer_write_integer_as_decimal(socket->writer, value);
}

void writer_write_pointer_as_hex(struct writer *writer, void *value)
{
    char buffer[40];
    snprintf(buffer, 40, "%p", value);
    writer_write_string(writer, buffer);
}

void writer_write_string_buffer(struct writer *writer, struct string_buffer *buffer)
{
    send(writer->handle, string_buffer_get_chars(buffer), string_buffer_get_length(buffer), 0);
}

void writer_write_chars(struct writer *writer, char* buffer, int len) {
  send(writer->handle, buffer, len, 0);
}

void socket_write_chars(struct socket* socket, char* buffer, int len) {
  writer_write_chars(socket->writer, buffer, len);
}

void socket_write_string_buffer(struct socket* socket, struct string_buffer* buffer) 
{
  writer_write_string_buffer(socket->writer, buffer);
}

struct socket *server_socket_accept(struct server_socket *serverSocket)
{
    struct reader* reader;
    struct writer* writer;
    struct socket* socket;
    int handle = socket_accept(serverSocket->handle);
    if(handle == INVALID_SOCKET) {
      return 0;
    }
    reader = malloc(sizeof(struct reader));
    writer = malloc(sizeof(struct writer));
    socket = malloc(sizeof(struct socket));
    if(reader == 0 || writer == 0 || socket == 0) {
      if(reader != 0) free(reader);
      if(writer != 0) free(writer);
      if(socket != 0) free(socket);
      return 0;
    }
    reader->handle = handle;
    reader->bufferStart = reader->buffer;
    reader->bufferEnd = reader->buffer;
    writer->handle = handle;
    socket->handle = handle;
    socket->reader = reader;
    socket->writer = writer;
    return socket;
}

struct socket *create_client_socket(char *host, int port)
{
    int handle = socket_create(host, port);
    struct reader *reader = malloc(sizeof(struct reader));
    struct writer *writer = malloc(sizeof(struct writer));
    struct socket *socket = malloc(sizeof(struct socket));
    reader->handle = handle;
    reader->bufferStart = reader->buffer;
    reader->bufferEnd = reader->buffer;
    writer->handle = handle;
    socket->handle = handle;
    socket->reader = reader;
    socket->writer = writer;
    return socket;
}

struct reader *socket_get_reader(struct socket *socket)
{
    return socket->reader;
}

struct writer *socket_get_writer(struct socket *socket)
{
    return socket->writer;
}

void socket_close(struct socket *socket)
{
#ifdef WIN32
    closesocket(socket->handle);
#else
    close(socket->handle);
#endif
    free(socket->reader);
    free(socket->writer);
    free(socket);
}

void server_socket_close(struct server_socket *socket) {
#ifdef WIN32
    closesocket(socket->handle);
#else
    close(socket->handle);
#endif
    free(socket);
}
