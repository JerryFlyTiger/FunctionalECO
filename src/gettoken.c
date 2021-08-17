//
// Created by JerryChen on 2021/5/11.
//

#include "../include/tokenize.h"

#define nmatch 5

static string stringBuffer = NULL, charPtr = NULL;

#define REG_LEN 8

// static const char reArr[REG_LEN][SMALLSIZ << 1] = {
static string reArr[REG_LEN];
static const char re_total[] =
    "(/[*](([^*])|([*][^/]))*[*]/)|(//[^\n]*\n)|[ "
    "\f\r\t\v]+|[\n]+|([_a-zA-Z][_a-zA-Z0-9]{0,30})|[0-9]+|[)(,.:#'/"
    "+=*;-]|[][]|.";                                          // total
static const char re_mlc[] = "(/[*](([^*])|([*][^/]))*[*]/)"; // 0, m l comments
static const char re_olc[] = "(//[^\n]*\n)"; // 1, one line comments
static const char re_ws[] = "[ \f\r\t\v]+";  // 2, white space
static const char re_nl[] = "[\n]+";         // 3, new line
static const char re_id[] = "([_a-zA-Z][_a-zA-Z0-9]{0,30})";     // 4, id
static const char re_dig[] = "[0-9]+";                           // 5, digit
static const char re_del[] = "&&|[|][|]|[)(,.:#'/+=*;-|&]|[][]"; // 6, delimiter
static const char re_oth[] = ".";                                // 7, other

static regex_t regexs[REG_LEN];

static void reg_comp(regex_t *regex, const void *re) {
  if (regcomp(regex, re, REG_EXTENDED)) {
    printf("regcomp Error\n");
    exit(EXIT_FAILURE);
  } // if
} // reg_comp

void scanner_init(size_t capacity) {
  if (stringBuffer)
    return;
  reg_comp(regexs, re_total);
  reArr[0] = re_mlc;
  reArr[1] = re_olc;
  reArr[2] = re_ws;
  reArr[3] = re_nl;
  reArr[4] = re_id;
  reArr[5] = re_dig;
  reArr[6] = re_del;
  reArr[7] = re_oth;
  for (size_t i = 1; i < REG_LEN; ++i)
    reg_comp(regexs + i, reArr[i - 1]);
  Malloc(char, stringBuffer, capacity);
  charPtr = stringBuffer;
} // scanner_init

void bufferFree() {
  if (!stringBuffer)
    return;
  free(stringBuffer);
  stringBuffer = NULL;
} // bufferFree

void scanner_free() {
  for (size_t i = 0; i < REG_LEN; ++i)
    regfree(&regexs[i]);
} // regfree

TokenPtr new_token(intmax_t type, void *value, size_t line, size_t column) {
  TokenPtr token = malloc(sizeof(Token));
  *token = (Token){.type = type,
                   .value = value,
                   .line = line,
                   .column = column,
                   .next = NULL};
  return token;
} // new_token

TokenPtr tokenClone(const Token *src) {
  if (!src)
    return NULL;
  TokenPtr temp = malloc(sizeof(Token));
  *temp = (Token){.type = src->type,
                  .value = src->value,
                  .line = src->line,
                  .column = src->column,
                  .next = NULL};
  return temp;
} // treeClone

TokenPtr gettoken(string str, SymbolTable reserveWordsTable,
                  SymbolTable symbolTable) {
  string p = str;
  TokenPtr tokenLL = NULL, tokPtr = NULL, current = NULL;
  regmatch_t pmatch[nmatch];
  regoff_t len, off;
  size_t line = 1, column = 0;

  while (true) {
    if (regexec(regexs, p, nmatch, pmatch, 0))
      break;
    // off = pmatch[0].rm_so + (p - *str);
    len = pmatch[0].rm_eo - pmatch[0].rm_so;
    // printf("#%d:\n", i + 1);
    // printf("offset = %jd; length = %jd\n", (intmax_t)off, (intmax_t)len);
    // printf("substring = \"%.*s\"\n", (int)len, p + pmatch[0].rm_so);

    strncpy(charPtr, p + pmatch[0].rm_so, (size_t)len);
    charPtr[(size_t)len] = '\0';
    intmax_t type;
    void *value = NULL;

    for (size_t j = 1; j < REG_LEN; ++j) {
      if (regexec(regexs + j, charPtr, nmatch, pmatch, 0))
        continue;
      if (j == 1) { // 1 : m l comment
        char *tmp = NULL, *c = charPtr;
        for (; c < charPtr + len; ++c)
          if (*c == '\n') {
            ++line;
            tmp = c;
          } // if

        // column = p - tmp;
        break;
      } else if (j == 2) { // 2 : one line comment
        ++line;
        column = 0;
        break;
      } else if (j == 3) { // 3 : white space
        column += len;
        break;
      } else if (j == 4) { // 4 : new line
        line += len;
        column = 0;
        break;
      } else if (j == 5) { // 5, id
        if (value = symbolTableSearch(reserveWordsTable, charPtr, RWTCAPA)) {
          type = RESERVEWORD;
          value = ((Entry *)value)->key;
        } else {
          type = SYMBOL;
          value = symbolTableInsert(symbolTable, charPtr, NULL, HASHCAPA);
        } // else
      } else if (j == 6) {
        type = DIGIT; // 6, digit
        value = strtol(charPtr, NULL, 10);
      } else if (j == 7) { // 7, delimiter
        type = DELIMITER;
        value = charPtr;
      } else { // 8, other
        fprintf(stderr, "Mismatch Error : %s\n", charPtr);
        exit(EXIT_FAILURE);
      } // else

      tokPtr = new_token(type, value, line, column);
      column += len;
      if (!tokenLL) {
        tokenLL = tokPtr;
        current = tokPtr;
      } else {
        current->next = tokPtr;
        current = tokPtr;
      } // else

      break;
    } // for

    charPtr += ((size_t)len + 1);
    p += pmatch[0].rm_eo;
  } // while

  return tokenLL;
} // gettoken

void tokenFree(TokenPtr tokenPtr) {
  if (!tokenPtr)
    return;
  for (TokenPtr next = NULL; tokenPtr; tokenPtr = next) {
    next = tokenPtr->next;
    free(tokenPtr);
  } // for
} // tokenFree

void printType(intmax_t type) {
  if (type == SYMBOL)
    printf("%s", "symbol");
  else if (type == RESERVEWORD)
    printf("%s", "reserveword");
  else if (type == DIGIT)
    printf("%s", "digit");
  else if (type == DELIMITER)
    printf("%s", "delimiter");
  else {
    fprintf(stderr, "type error : %ld\n", type);
    exit(EXIT_FAILURE);
  } // else
} // printType

void printToken(TokenPtr tokenPtr) {
  if (!tokenPtr) {
    perror("Error! tokenPtr is NULL!!!\n");
    exit(EXIT_FAILURE);
  } // if

  for (TokenPtr tok = tokenPtr; tok; tok = tok->next) {
    printf("type = ");
    printType(tok->type);
    if (tok->type == RESERVEWORD)
      printf(", %s , line = %ld, column = %ld\n", (string)(tok->value), tok->line,
             tok->column);
    else if (tok->type == SYMBOL)
      printf(", %s , line = %ld, column = %ld\n", ((Entry *)(tok->value))->key,
             tok->line, tok->column);
    else if (tok->type == DIGIT)
      printf(", %ld , line = %ld, column = %ld\n", *((intmax_t *)tok->value),
             tok->line, tok->column);
    else if (tok->type == DELIMITER)
      printf(", %s , line = %ld, column = %ld\n", (string)(tok->value), tok->line,
             tok->column);
    else {
      perror("type error");
      exit(EXIT_FAILURE);
    } // else
  }   // for
} // printToken