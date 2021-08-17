//
// Created by JerryChen on 2021/5/20.
//

#ifndef FUNCTIONALECO_TOKENIZE_H
#define FUNCTIONALECO_TOKENIZE_H

#include "../include/myHeader.h"
#include "../include/symbolTable.h"

#define SYMBOL 444
#define RESERVEWORD 555
#define DIGIT 666
#define DELIMITER 777

#define MODULE 0
#define INPUT 1
#define OUPUT 2
#define REG 3
#define WIRE 4
#define ASSIGN 5
#define OR 6
#define NOR 7
#define XOR 8
#define XNOR 9
#define NOT 10
#define AND 11
#define NAND 12
#define BUF 13
#define ENDMODULE 14

#define RESERVEWORDS_LEN 15
extern const char reserveWords[RESERVEWORDS_LEN][15];

typedef struct _token *TokenPtr;
typedef struct _token {
  intmax_t type;
  void *value;
  size_t line;
  size_t column; // head char column
  TokenPtr next;
} Token; // struct Token

TokenPtr new_token(intmax_t type, void *value, size_t line, size_t column);

TokenPtr gettoken(string str, SymbolTable reserveWordsTable,
                  SymbolTable symbolTable);

TokenPtr tokenClone(const Token *src);
void tokenFree(TokenPtr tokenPtr);
void printType(intmax_t type);
void printToken(TokenPtr tokenPtr);
void scanner_init(size_t capacity);
void scanner_free();
void bufferFree();

#endif // FUNCTIONALECO_TOKENIZE_H