#include <stdbool.h>
#include <limits.h>
#include "stringBuffers.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#ifdef WIN32
#define snprintf sprintf_s
#endif

struct string_buffer {
    int length;
    int capacity;
    char *chars;
};

/*@
predicate string_buffer(struct string_buffer *buffer;) =
    buffer->length |-> ?length &*& buffer->capacity |-> ?capacity &*& buffer->chars |-> ?charsArray &*& malloc_block_string_buffer(buffer) &*&
    chars(charsArray, capacity, ?cs) &*& malloc_block(charsArray, capacity) &*& 0 <= length &*& length <= capacity &*& length(cs) == capacity;
@*/

char *string_buffer_to_string(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures string(result, ?cs) &*& malloc_block(result, length(cs) + 1);
{
    char *result;
    char *zero = "";
    //@ string_to_chars(zero);
    string_buffer_append_chars(buffer, zero, 1);
    result = buffer->chars;
    free(buffer);
    return result;
    //@ assume(false);
}

char *string_buffer_get_string(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer) &*& malloced_string(result);
{
    int length = buffer->length;
    if (length == INT_MAX) abort();
    char *result = malloc((size_t)(length + 1));
    if (result == 0) abort();
    memcpy(result, buffer->chars, (size_t)length);
    result[length] = 0;
    //@ assert chars(result + length + 1, 0, ?cs0);
    //@ switch (cs0) { case nil: case cons(h, t): }
    //@ close chars(result + length, 1, {0});
    //@ chars_join(result);
    //@ chars_separate_string(result);
    return result;
}

struct string_buffer *create_string_buffer()
    //@ requires emp;
    //@ ensures result != 0 &*& string_buffer(result);
{
    struct string_buffer *buffer = malloc(sizeof(struct string_buffer));
    if (buffer == 0) {
        abort();
    }
    buffer->length = 0;
    buffer->capacity = 0;
    buffer->chars = 0;
    //@ assume(false);
    //@ close chars(0, nil);
    //@ malloc_block_null();
    //@ close string_buffer(buffer);
    return buffer;
}

char *string_buffer_get_chars(struct string_buffer *buffer)
    //@ requires false; // TODO: Improve this contract.
    //@ ensures true;
{
    return buffer->chars;
}

int string_buffer_get_length(struct string_buffer *buffer)
    //@ requires [?f]string_buffer(buffer);
    //@ ensures [f]string_buffer(buffer) &*& 0 <= result;
{
    //@ open string_buffer(buffer);
    int result = buffer->length;
    //@ close [f]string_buffer(buffer);
    return result;
}

void string_buffer_clear(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer);
{
    //@ open string_buffer(buffer);
    buffer->length = 0;
    //@ close string_buffer(buffer);
}

void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count)
    //@ requires string_buffer(buffer) &*& [?f]chars(chars, count, ?cs);
    //@ ensures string_buffer(buffer) &*& [f]chars(chars, count, cs);
{
    int newLength = 0;
    //@ length_nonnegative(cs);
    //@ open string_buffer(buffer);
    //@ malloc_block_limits(buffer->chars);
    int length = buffer->length;
    if (INT_MAX - buffer->length < count) abort();
    newLength = buffer->length + count;
    if (buffer->capacity < newLength) {
        char *bufferChars = 0;
        char *newChars = malloc((size_t)newLength);
        if (newChars == 0) abort();
        buffer->capacity = newLength;
        bufferChars = buffer->chars;
        //@ chars_split(buffer->chars, buffer->length);
        //@ chars_split(newChars, buffer->length);
        memcpy(newChars, buffer->chars, (size_t)buffer->length);
        //@ chars_join(newChars);
        //@ chars_join(bufferChars);
        free(buffer->chars);
        buffer->chars = newChars;
    }
    //@ chars_split(buffer->chars, buffer->length);
    //@ chars_split(buffer->chars + buffer->length, count);
    //@ malloc_block_limits(buffer->chars);
    memcpy(buffer->chars + buffer->length, chars, (size_t)count);
    //@ chars_join(buffer->chars);
    //@ chars_join(buffer->chars);
    buffer->length = newLength;
    //@ close string_buffer(buffer);
}

void string_buffer_append_char(struct string_buffer *buffer, char c)
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer);
{
    char buf[1] = {c};
    string_buffer_append_chars(buffer, buf, 1);
}

void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer) &*& [?f]string_buffer(buffer0);
    //@ ensures string_buffer(buffer) &*& [f]string_buffer(buffer0);
{
    //@ open string_buffer(buffer0);
    //@ chars_split(buffer0->chars, buffer0->length);
    string_buffer_append_chars(buffer, buffer0->chars, buffer0->length);
    //@ chars_join(buffer0->chars);
    //@ close [f]string_buffer(buffer0);
}

void string_buffer_append_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer) &*& [?f]string(string, ?cs);
    //@ ensures string_buffer(buffer) &*& [f]string(string, cs);
{
    int length = strlen(string);
    //@ chars_split(string, length);
    string_buffer_append_chars(buffer, string, length);
    //@ chars_join(string);
}

void string_buffer_append_integer_as_decimal(struct string_buffer *buffer, int value)
    //@ requires string_buffer(buffer);
    //@ ensures string_buffer(buffer);
{
  char tmp[80];
  snprintf(tmp, 80, "%d", value);
  string_buffer_append_string(buffer, tmp);
}

struct string_buffer *string_buffer_copy(struct string_buffer *buffer)
    //@ requires [?f]string_buffer(buffer);
    //@ ensures [f]string_buffer(buffer) &*& result != 0 &*& string_buffer(result);
{
    //@ open string_buffer(buffer);
    struct string_buffer *copy = malloc(sizeof(struct string_buffer));
    char *chars = malloc(buffer->length);
    if (copy == 0 || chars == 0) abort();
    copy->length = buffer->length;
    copy->capacity = buffer->length;
    //@ chars_split(buffer->chars, buffer->length);
    memcpy(chars, buffer->chars, buffer->length);
    //@ chars_join(buffer->chars);
    copy->chars = chars;
    //@ close [f]string_buffer(buffer);
    //@ close string_buffer(copy);
    return copy;
}

bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires [?f]string_buffer(buffer) &*& [?f0]string_buffer(buffer0);
    //@ ensures [f]string_buffer(buffer) &*& [f0]string_buffer(buffer0);
{
    bool result = false;
    //@ open string_buffer(buffer);
    //@ open string_buffer(buffer0);
    if (buffer->length == buffer0->length) {
        //@ chars_split(buffer->chars, buffer->length);
        //@ chars_split(buffer0->chars, buffer0->length);
        int result0 = memcmp(buffer->chars, buffer0->chars, buffer->length);
        //@ chars_join(buffer->chars);
        //@ chars_join(buffer0->chars);
        result = result0 == 0;
    }
    //@ close [f]string_buffer(buffer);
    //@ close [f0]string_buffer(buffer0);
    return result;
}

bool string_buffer_equals_string(struct string_buffer *buffer, char *string)
    //@ requires [?f1]string_buffer(buffer) &*& [?f2]string(string, ?cs);
    //@ ensures [f1]string_buffer(buffer) &*& [f2]string(string, cs);
{
    bool result = false;
    //@ open string_buffer(buffer);
    int length = strlen(string);
    if (length == buffer->length) {
        //@ chars_split(buffer->chars, length);
        //@ chars_split(string, length);
        int result0 = memcmp(buffer->chars, string, length);
        //@ chars_join(buffer->chars);
        //@ chars_join(string);
        result = result0 == 0;
    }
    //@ close [f1]string_buffer(buffer);
    return result;
}

void string_buffer_dispose(struct string_buffer *buffer)
    //@ requires string_buffer(buffer);
    //@ ensures emp;
{
    //@ open string_buffer(buffer);
    free(buffer->chars);
    free(buffer);
}

int chars_index_of_string(char *chars, int length, char *string)
    //@ requires [?f1]chars(chars, length, ?charsChars) &*& [?f2]string(string, ?stringChars);
    /*@
    ensures
        [f1]chars(chars, length, charsChars) &*& [f2]string(string, stringChars) &*&
        result == -1 ? true : 0 <= result &*& result + index_of('\0', stringChars) <= length(charsChars);
    @*/
{
    int n = strlen(string);
    char *p = chars;
    char *end = 0;
    //@ length_nonnegative(charsChars);
    //@ chars_limits(chars);
    end = chars + length;
    while (true)
        //@ invariant [f1]chars(chars, charsChars) &*& [f2]chars(string, stringChars) &*& chars <= p &*& p <= end;
    {
        if (end - p < n) return -1;
        //@ chars_split(chars, p - chars);
        //@ chars_split(p, n);
        //@ chars_split(string, n);
        {
            int cmp = memcmp(p, string, n);
            //@ chars_join(string);
            //@ chars_join(p);
            //@ chars_join(chars);
            if (cmp == 0) return p - chars;
            //@ take_0(stringChars);
            //@ take_0(drop(p - chars, charsChars));
            //@ assert [_]chars(chars, ?charsChars2);
            //@ assert p + 1 - chars <= length(charsChars);
            //@ assert(charsChars2 == charsChars);
            //@ assert p + 1 - chars <= length(charsChars2);
            p++;
            //@ open chars(string, stringChars);
            //@ chars_split(chars, p - chars);
            //@ assert [_]chars(p, ?pChars) &*& [_]character(string, ?c0);        
            p = memchr(p, *string, end - p);
            //@ chars_join(chars);
            //@ close [f2]chars(string, stringChars);
            if (p == 0) return -1;
        }
    }
}

bool string_buffer_contains_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0)
    //@ requires string_buffer(buffer) &*& [?f]string_buffer(buffer0);
    //@ ensures string_buffer(buffer) &*& [f]string_buffer(buffer0);
{
  struct string_buffer* buffer0_copy = string_buffer_copy(buffer0);
  char* chars0 = string_buffer_to_string(buffer0_copy);
  int index = chars_index_of_string(buffer->chars, buffer->length, chars0);
  free(chars0);
  return index != -1;
}

bool string_buffer_contains_string(struct string_buffer *buffer, char *string)
    //@ requires string_buffer(buffer) &*& [?f2]string(string, ?cs);
    //@ ensures string_buffer(buffer) &*& [f2]string(string, cs);
{
  int index = chars_index_of_string(buffer->chars, buffer->length, string);
  return index != -1;
}

bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after)
    //@ requires [?f1]string_buffer(buffer) &*& [?f2]string(separator, ?cs) &*& string_buffer(before) &*& string_buffer(after);
    //@ ensures [f1]string_buffer(buffer) &*& [f2]string(separator, cs) &*& string_buffer(before) &*& string_buffer(after);
{
    //@ open string_buffer(buffer);
    int n = strlen(separator);
    char *chars = buffer->chars;
    int length = buffer->length;
    //@ chars_split(chars, buffer->length);
    int index = chars_index_of_string(chars, length, separator);
    //@ chars_join(chars);
    if (index == -1) { /*@ close [f1]string_buffer(buffer); @*/ return false; }
    string_buffer_clear(before);
    //@ chars_split(chars, index);
    string_buffer_append_chars(before, chars, index);
    //@ chars_join(chars);
    string_buffer_clear(after);
    //@ chars_limits(chars);
    //@ chars_split(chars, index + n);
    //@ chars_split(chars + index + n, length - index - n);
    string_buffer_append_chars(after, chars + index + n, length - index - n);
    //@ chars_join(chars + index + n);
    //@ chars_join(chars);
    //@ close [f1]string_buffer(buffer);
    return true;
}
