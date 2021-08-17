//
// Created by JerryChen on 2021/5/10.
//

#pragma once

#include <ctype.h>
#include <limits.h>
#include <math.h>
#include <regex.h>
#include <stdarg.h>
#include <stdbool.h> // true false
#include <stddef.h>  // size_t
#include <stdint.h>  // int32_t
#include <stdio.h>   // printf, scanf
#include <stdlib.h>
#include <string.h> // strcmp
#include <time.h>   // clock_t

#define Lambda(l_ret_type, l_arguments, l_body)                                \
  ({                                                                           \
    l_ret_type l_anonymous_functions_name l_arguments                          \
        l_body &l_anonymous_functions_name;                                    \
  }) // fn = lambda ( ret_type, ( argu ), ...; )

#define Malloc(type, p, s)                                                     \
  if (!((p) = malloc(s * sizeof(type))))                                       \
  fprintf(stderr, "Insufficient memory"), exit(EXIT_FAILURE)
// MALLOC ( type, ptr, capacity )

#define Realloc(type, p, s)                                                    \
  if (!((p) = realloc(p, s * sizeof(type))))                                   \
  fprintf(stderr, "Insufficient memory"), exit(EXIT_FAILURE)
// REALLOC ( type, ptr, capacity )

#define Calloc(p, n, s)                                                        \
  if (!((p) = calloc(n, s))) {                                                 \
    fprintf(stderr, "Insufficient memory");                                    \
    exit(EXIT_FAILURE);                                                        \
  }

#define For(i, loopmax, ...)                                                   \
  for (register size_t(i) = 0; (i) < (loopmax); (i)++) {                       \
    __VA_ARGS__                                                                \
  }
#define ForLoop(i, s, loopmax, ...)                                            \
  for (register size_t(i) = (s); (i) <= (loopmax); (i)++) {                    \
    __VA_ARGS__                                                                \
  }

#define Foreach_string(iterator, ...)                                          \
  for (uint8 **iterator = (uint8 *[]){__VA_ARGS__, NULL}; *iterator; iterator++)

#define Foreach_str(iterator, list)                                            \
  for (uint8 **iterator = list; *iterator; iterator++)

#define Forever(...) for (__VA_ARGS__;;) /* infinite loop */
#define Fn_apply(type, fn, ...)                                                \
  {                                                                            \
    void *stopper_for_apply = (int[]){0};                                      \
    type **list_for_apply = (type *[]){__VA_ARGS__, stopper_for_apply};        \
    for (uint32_t i = 0; list_for_apply[i] != stopper_for_apply; i++)          \
      (fn)(list_for_apply[i]);                                                 \
  } // Fn_apply( type, fn, 1, 2, 3 ) IS fn(1), f(2), f(3) ...;

#define Free_all(...)                                                          \
  Fn_apply(                                                                    \
      void, free,                                                              \
      __VA_ARGS__) // Free_all( 1, 2 ,3 ) IS free(1), free(2), free(3)...;

#define Log2(n) (log(n) / log(2))

#define Swap(x, y, t) ((t) = (x), (x) = (y), (y) = (t)) /* switch x, y */
#define Compare(x, y)                                                          \
  ((x) < (y))    ? -1                                                          \
  : ((x) == (y)) ? 0                                                           \
                 : 1 /* compare x, y ; if x < y, -1; equal, 0; bigger 1 */

#define TimeInterval(start, end)                                               \
  (double)((end) - (start)) / CLOCKS_PER_SEC * 1000
#define PrintResult(op, ...) fprintf((op), __VA_ARGS__), printf(__VA_ARGS__)

#define Max(a, b) ((a) > (b) ? (a) : (b))
#define Min(a, b) ((a) < (b) ? (a) : (b))
#define Square(x) (x) * (x)
#define Dprint(expr, expr2) printf(#expr " = " #expr2 "\n", expr)
// exsample: dprint( x/y, %d )

#define StrCpy(dest, src)                                                      \
  while ((*(dest)++ = *(src)++) != '\0')                                       \
    ;

#define Exit(condition, ...)                                                   \
  if ((condition))                                                             \
  printf(__VA_ARGS__), exit(EXIT_FAILURE)

#define PrintfErr(...) fprintf(stderr, __VA_ARGS__), exit(EXIT_FAILURE)

#define Reverse(s, len)                                                        \
  {                                                                            \
    for (register int k = 0, j = (len)-1, c = 0; k < j; k++, j--)              \
      Swap((s)[k], (s)[j], c);                                                 \
  } // reverse

#define Arrlen(a) (sizeof((a)) / sizeof((a[0])))
#define Toupper(c) (((c) >= 'a' && (c) <= 'z') ? ((c)-0x20) : (c))

double sum_array(double in[]);

#define Sum_oneTo(max, out)                                                    \
  {                                                                            \
    int32_t total = 0;                                                         \
    for (int32_t i = 0; i <= max; i++)                                         \
      total += i;                                                              \
    out = total;                                                               \
  } // Sum_oneTo

#define Sum_arr(...) sum_array((double[]){__VA_ARGS__, NAN})

typedef char *string;

#define BIGBUFSIZ 1060308
#define SMALLSIZ 128
#define HASHCAPA 7919

size_t getAllCharFromFile(const char *filename, char **buf);