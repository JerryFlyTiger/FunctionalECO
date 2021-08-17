//
// Created by JerryChen on 2021/5/10.
//

#include "../include/symbolTable.h"

static size_t hash(string src, size_t capacity) {
  size_t hvalue = 0;
  while (*src) {
    hvalue += *src++;
    if (*src)
      hvalue += (*src++) << 8;
  } // while

  return hvalue % capacity;
} // hash

B_TreeNodePtr *symbolTableCreate(size_t capacity) {
  B_TreeNodePtr *symTab;
  Malloc(B_TreeNodePtr, symTab, capacity);
  return symTab;
} // symbolTableCreate

Entry *symbolTableSearch(B_TreeNodePtr *symTab, string key, size_t capacity) {
  return B_Tree_search(symTab[hash(key, capacity)], key);
} // symbolTableSearch

Entry *symbolTableInsert(B_TreeNodePtr *symTab, string key, void *value,
                         size_t capacity) {
  Entry *eP = symbolTableSearch(symTab, key, capacity);
  if (eP) {
    eP->value = value;
    return eP;
  } // if

  return B_Tree_insert(symTab + hash(key, capacity), key, value);
} // symbolTableInsert

void symbolTableFree(B_TreeNodePtr *symTab, size_t capacity) {
  for (size_t i = 0; i < capacity; ++i)
    B_Tree_free(symTab[i]);
} // symbolTableFree