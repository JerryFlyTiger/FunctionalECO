#include "../include/functionalEcoRoot.h"

extern const char reserveWords[RESERVEWORDS_LEN][15] = {
    "module", "input", "output", "reg", "wire", "assign", "or",       "nor",
    "xor",    "xnor",  "not",   "and", "nand", "buf",    "endmodule"};

string R1Buf, R2Buf, G1Buf;
clock_t start;

Module module_R1;
Module module_R2;
Module module_G1;

int main(const int argc, const char *argv[]) { // ./eco R1.v R2.v G1.v patch.v
  start = clock();
  system("pwd");
  system("ls");

  TokenPtr tokenPtr_R1 = NULL, tokenPtr_R2 = NULL, tokenPtr_G1 = NULL;
  SymbolTable reserveWordsTable = symbolTableCreate(RWTCAPA);
  SymbolTable symbolTable_R1 = symbolTableCreate(HASHCAPA);
  SymbolTable symbolTable_R2 = symbolTableCreate(HASHCAPA);
  SymbolTable symbolTable_G1 = symbolTableCreate(HASHCAPA);

  for (size_t i = 0; i < RESERVEWORDS_LEN; ++i)
    symbolTableInsert(reserveWordsTable, reserveWords[i], NULL, RWTCAPA);

//  printf("We have %d arguments:\n", argc);
//  for (int i = 0; i < argc; ++i)
//    printf("[%d] %s\n", i, argv[i]);

  size_t r1_len = getAllCharFromFile(argv[1], &R1Buf); // R1.v
  size_t r2_len = getAllCharFromFile(argv[2], &R2Buf); // R1.v
  size_t g1_len = getAllCharFromFile(argv[3], &G1Buf); // G1.v
  // printf("g1_len = %ld\n%s\n", g1_len, G1Buf);
  // printf("----\n\n");

  scanner_init((r1_len + r2_len + g1_len) << 1);

  tokenPtr_R1 = gettoken(R1Buf, reserveWordsTable, symbolTable_R1);
  tokenPtr_R2 = gettoken(R2Buf, reserveWordsTable, symbolTable_R2);
  tokenPtr_G1 = gettoken(G1Buf, reserveWordsTable, symbolTable_G1);
  // TokenPtr tokenPtr_simR2 = gettoken("0 1 1", reserveWordsTable, symbolTable_R2);
  // TokenPtr tokenPtr_simG1 = gettoken("0 1 1", reserveWordsTable, symbolTable_G1);

  scanner_free();

  patch_output(tokenPtr_R2, argv[4]);

  // printToken(tokenPtr_R1);
  // printToken(tokenPtr_R2);
  // printToken(tokenPtr_G1);


  // eval(tokenPtr_R1, &module_R1);
  // eval(tokenPtr_R2, &module_R2);
  // eval(tokenPtr_G1, &module_G1);

  // printf("R1\n");
  // modulePrint(&module_R1);
  // printf("R2\n");
  // modulePrint(&module_R2);
  // printf("G1\n");
  // modulePrint(&module_G1);

  // moduleInput(&module_R1, tokenPtr_simR2);
  // moduleInput(&module_G1, tokenPtr_simG1);

  // gates_sim(module_R2.gates);
  // gates_sim(module_G1.gates);

  // printf("module's Output\n");
  // moduleOutput(&module_R2);
  // moduleOutput(&module_G1);

  // tokenFree(tokenPtr_simR2);
  // tokenFree(tokenPtr_simG1);


  // tokenFree(tokenPtr_R1), tokenPtr_R1 = NULL;
  tokenFree(tokenPtr_R2), tokenPtr_R2 = NULL;
  // tokenFree(tokenPtr_G1), tokenPtr_G1 = NULL;
  // moduleFree(&module_R1);
  // moduleFree(&module_R2);
  // moduleFree(&module_G1);
  symbolTableFree(symbolTable_R1, HASHCAPA);
  symbolTableFree(symbolTable_R2, HASHCAPA);
  symbolTableFree(symbolTable_G1, HASHCAPA);
  symbolTableFree(reserveWordsTable, RWTCAPA);
  bufferFree();
  Free_all(R1Buf, R2Buf, G1Buf)
  // printf("execution time : %g ms\n", TimeInterval(start, clock()));
} // main