//
// Created by JerryChen on 2021/5/10.
//

#include "../include/myHeader.h"
#include <fcntl.h>
#include <unistd.h>

size_t getAllCharFromFile(const char *filename, char **buf) {

  size_t capacity = BIGBUFSIZ;
  size_t oldCapa = capacity;
  int fd = open(filename, O_RDONLY);
  if (fd == -1) {
    fprintf(stderr, "Cannot open %s. Try again later.\n", filename);
    exit(EXIT_FAILURE);
  } // if

  Malloc(char, *buf, capacity);
  size_t nread = read(fd, *buf, capacity);
  if (!nread) {
    fprintf(stderr, "No char in %s.\n", filename);
    exit(EXIT_FAILURE);
  } // if

  size_t len = nread;
  while (nread == oldCapa) {
    oldCapa = capacity;
    capacity <<= 1; // capacity *= 2
    Realloc(char, *buf, capacity);
    nread = read(fd, *buf + len, oldCapa);
    len += nread;
  } // if

  close(fd);
  (*buf)[len] = 0;
  return len;
} // getAllCharFromFile
