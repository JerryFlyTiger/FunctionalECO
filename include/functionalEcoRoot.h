//
// Created by JerryChen on 2021/5/10.
//

#ifndef FUNCTIONALECO_FUNCTIONALECOROOT_H
#define FUNCTIONALECO_FUNCTIONALECOROOT_H
#include "../include/myHeader.h"
#include "symbolTable.h"
#include "tokenize.h"

typedef struct _gate* GatePtr;
typedef struct _gate {
  TokenPtr gateLL;
  size_t count;
  GatePtr next;
} Gate;

typedef struct _module {
  string name;
  TokenPtr head;
  TokenPtr inputs;
  TokenPtr outputs;
  TokenPtr wires;
  GatePtr gates;
  GatePtr gates_tail;
  size_t countOfGates;
} Module; // struct module

void eval(TokenPtr token, Module *module);
void gates_sim(GatePtr gatePtr);
void moduleInput(Module *module, TokenPtr inputVals);
void moduleOutput(Module *module);
void modulePrint(Module *module);
void moduleFree(Module *module);
void patch_output(TokenPtr token, string filename);

#endif // FUNCTIONALECO_FUNCTIONALECOROOT_H
