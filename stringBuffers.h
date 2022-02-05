#ifndef STRINGBUFFERS_H
#define STRINGBUFFERS_H

#include <stdbool.h>
#include <stdlib.h>

struct string_buffer;
typedef struct string_buffer *string_buffer;

/*@

predicate malloc_block_string(char *s, list<char> cs;) =
    malloc_block_chars(s, ?size) &*& chars(s + length(cs) + 1, size - length(cs) - 1, _);

predicate malloced_string(char *s;) =
    string(s, ?cs) &*& malloc_block_string(s, cs);

predicate string_buffer(struct string_buffer *buffer; list<char> cs);
predicate string_buffer_minus_chars(struct string_buffer *buffer, char *pcs, list<char> cs);

@*/

struct string_buffer *create_string_buffer();
    //@ requires emp;
    //@ ensures result != 0 &*& string_buffer(result, nil);
int string_buffer_get_length(struct string_buffer *buffer);
    //@ requires [?f]string_buffer(buffer, ?cs);
    //@ ensures [f]string_buffer(buffer, cs) &*& result == length(cs);
char *string_buffer_get_string(struct string_buffer *buffer);
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, cs) &*& malloced_string(result);
char *string_buffer_get_chars(struct string_buffer *buffer);
    //@ requires [?f]string_buffer(buffer, ?cs);
    //@ ensures [f]string_buffer_minus_chars(buffer, result, cs) &*& [f]chars(result, length(cs), cs);
/*@
lemma void string_buffer_minus_chars_elim();
    requires [?f]string_buffer_minus_chars(?buffer, ?pcs, ?cs) &*& [f]chars(pcs, length(cs), cs);
    ensures [f]string_buffer(buffer, cs);
@*/
bool string_buffer_equals(struct string_buffer *buffer, struct string_buffer *buffer0);
    //@ requires [?f]string_buffer(buffer, ?cs) &*& [?f0]string_buffer(buffer0, ?cs0);
    //@ ensures [f]string_buffer(buffer, cs) &*& [f0]string_buffer(buffer0, cs0);
bool string_buffer_equals_string(struct string_buffer *buffer, char *string);
    //@ requires [?f1]string_buffer(buffer, ?cs) &*& [?f2]string(string, ?scs);
    //@ ensures [f1]string_buffer(buffer, cs) &*& [f2]string(string, scs);
void string_buffer_clear(struct string_buffer *buffer);
    //@ requires string_buffer(buffer, _);
    //@ ensures string_buffer(buffer, nil);
void string_buffer_append_chars(struct string_buffer *buffer, char *chars, int count);
    //@ requires string_buffer(buffer, ?cs) &*& [?f]chars(chars, count, ?ccs);
    //@ ensures string_buffer(buffer, append(cs, ccs)) &*& [f]chars(chars, count, ccs);
void string_buffer_append_char(struct string_buffer *buffer, char c);
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, append(cs, {c}));
void string_buffer_append_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0);
    //@ requires string_buffer(buffer, ?cs) &*& [?f]string_buffer(buffer0, ?cs0);
    //@ ensures string_buffer(buffer, append(cs, cs0)) &*& [f]string_buffer(buffer0, cs0);
bool string_buffer_contains_string(struct string_buffer *buffer, char* string);
    //@ requires string_buffer(buffer, ?cs) &*& [?f2]string(string, ?scs);
    //@ ensures string_buffer(buffer, cs) &*& [f2]string(string, scs);
bool string_buffer_contains_string_buffer(struct string_buffer *buffer, struct string_buffer *buffer0);
    //@ requires string_buffer(buffer, ?cs) &*& [?f]string_buffer(buffer0, ?cs0);
    //@ ensures string_buffer(buffer, cs) &*& [f]string_buffer(buffer0, cs0);
void string_buffer_append_string(struct string_buffer *buffer, char *string);
    //@ requires string_buffer(buffer, ?cs) &*& [?f]string(string, ?scs);
    //@ ensures string_buffer(buffer, append(cs, scs)) &*& [f]string(string, scs);
void string_buffer_append_integer_as_decimal(struct string_buffer *buffer, int value);
    //@ requires string_buffer(buffer, _);
    //@ ensures string_buffer(buffer, _);
struct string_buffer *string_buffer_copy(struct string_buffer *buffer);
    //@ requires [?f]string_buffer(buffer, ?cs);
    //@ ensures [f]string_buffer(buffer, cs) &*& result != 0 &*& string_buffer(result, cs);
bool string_buffer_split(struct string_buffer *buffer, char *separator, struct string_buffer *before, struct string_buffer *after);
    //@ requires [?f1]string_buffer(buffer, ?cs) &*& [?f2]string(separator, ?scs) &*& string_buffer(before, _) &*& string_buffer(after, _);
    //@ ensures [f1]string_buffer(buffer, cs) &*& [f2]string(separator, scs) &*& string_buffer(before, _) &*& string_buffer(after, _);
void string_buffer_dispose(struct string_buffer *buffer);
    //@ requires string_buffer(buffer, _);
    //@ ensures emp;
char *string_buffer_to_string(struct string_buffer *buffer);
    //@ requires string_buffer(buffer, _);
    //@ ensures string(result, ?cs) &*& malloc_block(result, length(cs) + 1);

/*@

lemma void string_buffer_distinct(struct string_buffer* buffer1, struct string_buffer* buffer2);
  requires string_buffer(buffer1, ?cs1) &*& string_buffer(buffer2, ?cs2);
  ensures string_buffer(buffer1, cs1) &*& string_buffer(buffer2, cs2) &*& buffer1 != buffer2;

@*/

#endif
