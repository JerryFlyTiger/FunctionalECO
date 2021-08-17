//
// Created by JerryChen on 2021/5/12.
//

#include "../include//B_Tree.h"

static Entry *new_entry(const char *key, const void *value) {
  Entry *eP;
  Malloc(Entry, eP, 1);
  *eP = (Entry){.key = key, .value = value};
  return eP;
} // new_B_TreeNode

static B_TreeNodePtr new_BtreeNode(const char *key, const void *value,
                                   const B_TreeNode *parent) {
  B_TreeNodePtr bP;
  Malloc(B_TreeNode, bP, 1);
  *bP = (B_TreeNode){.entrys[0] = new_entry(key, value),
                     .entryN = 1,
                     .childN = 0,
                     .parent = parent};
  for (int i = 1; i < M; ++i) {
    bP->entrys[i] = NULL;
  } // for

  for (int i = 0; i < M+1; ++i) {
    bP->childs[i] = NULL;
  } // for

  return bP;
} // new_B_TreeNode

Entry *B_Tree_search(const B_TreeNode *root, const char *key) {
  if (!root)
    return NULL;
  Entry **entrys = root->entrys;
  intmax_t low = 0, high = root->entryN - 1, mid = high >> 1;
  while (low <= high && entrys[mid] && strcmp(key, entrys[mid]->key)) {
    if (strcmp(key, entrys[mid]->key) < 0)
      high = mid - 1;
    else
      low = mid + 1;
    mid = (low + high) >> 1;
  } // while

  if (mid < 0)
    mid = 0;

  for (; mid < low && entrys[mid]; ++mid)
    if (strcmp(key, entrys[mid]->key) > 0)
      continue;
    else
      break;

  if (entrys[mid] && !strcmp(key, entrys[mid]->key))
    return entrys[mid];

  return B_Tree_search(root->childs[mid], key);
} // B_Tree_search

static B_TreeNodePtr locateLeaf(const B_TreeNode *root, const char *key,
                                size_t *iP) {

  Entry **entrys = root->entrys;
  intmax_t low = 0, high = root->entryN - 1, mid = high >> 1;
  while (low <= high && strcmp(key, entrys[mid]->key)) {
    if (strcmp(key, entrys[mid]->key) < 0)
      high = mid - 1;
    else
      low = mid + 1;
    mid = (low + high) >> 1;
  } // while

  if (mid < 0)
    mid = 0;

  for (; mid < low; ++mid)
    if (strcmp(key, entrys[mid]->key) > 0)
      continue;
    else
      break;
  *iP = mid;
  if (root->childs[mid])
    return locateLeaf(root->childs[mid], key, iP);
  else
    return root;
} // locateLeaf

static B_TreeNodePtr split(B_TreeNodePtr leaf) {

  B_TreeNodePtr root = NULL, parent = leaf->parent;
  intmax_t mid_i = (leaf->entryN - 1) >> 1;
  string mid = leaf->entrys[mid_i]->key;
  Entry **rnv_arr = leaf->entrys + mid_i + 1;
  size_t rnv_arr_len = leaf->entryN - 1 - mid_i;
  leaf->entryN = mid_i;

  B_TreeNodePtr rNode = new_BtreeNode(rnv_arr[0]->key, rnv_arr[0]->value, NULL);
  for (size_t i = 1; i < rnv_arr_len; ++i) // data to right node
    rNode->entrys[i] = rnv_arr[i];

  rNode->entryN = rnv_arr_len;

  for (size_t i = 0, j = mid_i + 1; j < leaf->childN;
       ++i, ++j) { // childs to right node
    rNode->childs[i] = leaf->childs[j];
    leaf->childs[j]->parent = rNode;
  } // for

  rNode->childN = leaf->childN - mid_i - 1;
  leaf->childN -= rNode->childN;

  if (!parent) {
    root = new_BtreeNode(mid, leaf->entrys[mid_i]->value, NULL);
    root->childs[0] = leaf;
    leaf->parent = root;
    root->childs[1] = rNode;
    rNode->parent = root;
    root->childN = 2;
    return root;
  } // if

  // insertDataToParent
  size_t i = 0, pDataN = parent->entryN, childN = ++(parent->childN);
  for (; i < pDataN; ++i)
    if (strcmp(mid, parent->entrys[i]->key) > 0)
      continue;
    else if (!strcmp(mid, parent->entrys[i]->key)) { // TODO : have problem
      perror("Error!\n");
      exit(EXIT_FAILURE);
    } // elif
    else
      break;

  pDataN = ++(parent->entryN);
  for (size_t j = pDataN - 1; j > i; --j) // data shift to right side
    parent->entrys[j] = parent->entrys[j - 1];
  parent->entrys[i]->key = mid;
  parent->entrys[i]->value = leaf->entrys[mid_i]->value;

  ++i;
  for (size_t j = childN - 1; j > i; --j) // childs shift to right side
    parent->childs[j] = parent->childs[j - 1];
  parent->childs[i] = rNode;
  rNode->parent = parent;

  if (pDataN > M - 1)
    return split(parent);

  for (; parent->parent; parent = parent->parent)
    ;
  return parent;
} // split

Entry *B_Tree_insert(B_TreeNodePtr *root, const char *key, const void *value) {
  if (!*root) {
    *root = new_BtreeNode(key, value, NULL);
    return (*root)->entrys[0];
  } // if

  size_t i = 0;
  B_TreeNodePtr leaf = locateLeaf(*root, key, &i);
  size_t dataN = ++(leaf->entryN);
  for (size_t j = dataN - 1; j > i; --j) // data shift to right side
    leaf->entrys[j] = leaf->entrys[j - 1];
  leaf->entrys[i] = new_entry(key, value);
  if (dataN <= M - 1)
    return leaf->entrys[i];
  *root = split(leaf);
  return leaf->entrys[i];
} // B_Tree_insert

void printBTree(const B_TreeNode *root, const size_t level) {
  if (root == NULL)
    return;
  printf("level = %ld :\n", level);
  for (int i = 0; i < root->entryN; ++i)
    printf("data : %s\n", root->entrys[i]->key);
  printf("\n");
  for (int i = 0; i < root->childN; ++i)
    printBTree(root->childs[i], level + 1);
} // printBTree

void entryFree(Entry *entryPtr) {
  if (!entryPtr)
    return;
  //if (entryPtr->value)
  //  free(entryPtr->value); // TODO: had error
  free(entryPtr);
} // entryFree

void B_Tree_free(B_TreeNodePtr root) {
  if (root == NULL)
    return;

  // for (size_t i = 0; i < root->entryN; ++i) // TODO : had error
  //   entryFree(root->entrys[i]);

  // for (size_t i = 0; i < root->childN; ++i) // TODO : had error
  //  B_Tree_free(root->childs[i]);
  free(root);
} // B_Tree_free