//
// Created by JerryChen on 2021/5/12.
//

#ifndef BTREE_BTREE_H
#define BTREE_BTREE_H

#include "../include/myHeader.h"

#define M 4

typedef struct _entry {
  string key;
  void *value;
} Entry;

typedef struct _btreenode *B_TreeNodePtr;
typedef struct _btreenode {
  Entry *entrys[M]; // real capa == M-1 !!!
  size_t entryN;
  size_t childN;
  B_TreeNodePtr childs[M + 1]; // real capa == M
  B_TreeNodePtr parent;
} B_TreeNode;

Entry *B_Tree_insert(B_TreeNodePtr *root, const char *key, const void *value);
Entry *B_Tree_search(const B_TreeNode *root, const char *key);
void B_Tree_free(B_TreeNodePtr root);
void printBTree(const B_TreeNode *root, const size_t level);

#endif // BTREE_BTREE_H
