//
// Created by JerryChen on 2021/5/10.
//

#ifndef FUNCTIONALECO_SYMBOLTABLE_H
#define FUNCTIONALECO_SYMBOLTABLE_H

#include "../include/B_Tree.h"

#define RWTCAPA 277

typedef B_TreeNodePtr *SymbolTable;

B_TreeNodePtr *symbolTableCreate(size_t capacity);

Entry *symbolTableSearch(B_TreeNodePtr *symTab, string key, size_t capacity);
Entry *symbolTableInsert(B_TreeNodePtr *symTab, string key, void *value,
                         size_t capacity);
void symbolTableFree(B_TreeNodePtr *symTab, size_t capacity);

#endif // FUNCTIONALECO_SYMBOLTABLE_H
