//
// Created by JerryChen on 2021/5/24.
//
#include "../include/functionalEcoRoot.h"

static GatePtr new_gate(TokenPtr gateLL, const size_t count) {
  GatePtr gate = malloc(sizeof(Gate));
  *gate = (Gate){.gateLL = gateLL, .count = count, .next = NULL};
  return gate;
} // new_token

static TokenPtr getVar(Token **token) {
  TokenPtr tmp = tokenClone(*token);
  TokenPtr current = tmp;
  for (*token = (*token)->next; true; *token = (*token)->next)
    if ((*token)->type == DELIMITER && ((string)((*token)->value))[0] == ';')
      return tmp;
    else if ((*token)->type == SYMBOL) {
      // Entry *entryPtr = (*token)->value;
      // entryPtr->value = new_token(DIGIT, 0, 0, 0);
      current->next = tokenClone(*token);
      current = current->next;
    } else
      continue;
} // getVar

static TokenPtr getOneStmt(Token **token) {
  TokenPtr tmp = tokenClone(*token);
  TokenPtr current = tmp;
  for (*token = (*token)->next;; *token = (*token)->next) {
    current->next = tokenClone(*token);
    current = current->next;
    if ((*token)->type == DELIMITER && ((string)((*token)->value))[0] == ';')
      return tmp;
  } // for
} // getOneStmt

void eval(TokenPtr token, Module *module) {
  for (TokenPtr tmp = token; tmp; tmp = tmp->next) {
    if (tmp->type == RESERVEWORD) {
      if (tmp->value == reserveWords[ENDMODULE])
        return;
      else if (tmp->value == reserveWords[MODULE]) {
        tmp = tmp->next;
        module->name = ((Entry *)(tmp->value))->key;
        // ((Entry *)(tmp->value))->value = tmp->next;
        tmp = tmp->next->next;
        module->head = getVar(&tmp);

        //        for (tmp = tmp->next->next;
        //             tmp->type != DELIMITER || ((string)(tmp->value))[0] !=
        //             ';'; tmp = tmp->next)
        //          ;
      } else if (tmp->value == reserveWords[INPUT]) {
        tmp = tmp->next;
        // printf("37:............ %p\n", reserveWords[OUPUT]);
        module->inputs = getVar(&tmp);
        // printf("39:............ %s\n", tmp->value);
      } else if (tmp->value == reserveWords[OUPUT]) {
        tmp = tmp->next;
        // printf("40:............\n");
        // printToken(tmp);
        module->outputs = getVar(&tmp);
      } else if (tmp->value == reserveWords[WIRE]) {
        tmp = tmp->next;
        module->wires = getVar(&tmp);
      } else if (tmp->value == reserveWords[OR] ||
                 tmp->value == reserveWords[NOR] ||
                 tmp->value == reserveWords[XOR] ||
                 tmp->value == reserveWords[NOT] ||
                 tmp->value == reserveWords[AND] ||
                 tmp->value == reserveWords[XNOR] ||
                 tmp->value == reserveWords[NAND]) {

        // printf("1.........................\n");
        if (!module->gates) {
          module->gates = new_gate(getOneStmt(&tmp), 1);
          module->gates_tail = module->gates;
          module->countOfGates = 1;

          // printf("Gates:................................\n");
          // printf("%p\n", module->gates);

          // printToken(module->gates);
          // exit(EXIT_FAILURE);
        } else {
          ++(module->countOfGates);
          module->gates_tail->next =
              new_gate(getOneStmt(&tmp), module->countOfGates);
          module->gates_tail = module->gates_tail->next;

          // printf(" ");
          // printToken(current);
        } // else

        // printf("2.........................\n");

      } // else if
    }   // if
  }     // for
} // eval

static intmax_t getValueFromStmt(Token **stmt) {
  intmax_t value = -1;
  bool isEnd = false;
  for (; !isEnd; *stmt = (*stmt)->next)
    if ((*stmt)->type == DELIMITER && ((string)((*stmt)->value))[0] == ';') {
      value = -1;
      isEnd = true;
    } else if ((*stmt)->type == SYMBOL) {
      TokenPtr tokenPtr = ((TokenPtr)(((Entry *)((*stmt)->value))->value));
      if (!tokenPtr)
        return -2;
      value = (intmax_t)tokenPtr->value;
      isEnd = true;
    } // else if

  return value;
} // getValueFromStmt

void gates_sim(GatePtr gatePtr) {
  intmax_t value, tmp;
  for (; gatePtr; gatePtr = gatePtr->next) {
    void *tokVal = gatePtr->gateLL->value;
    TokenPtr outputTok = gatePtr->gateLL->next->next->next;
    TokenPtr tok = gatePtr->gateLL->next->next->next->next->next;
    value = getValueFromStmt(&tok);

    while (tok)
      if (tokVal == reserveWords[OR]) {
        tmp = getValueFromStmt(&(tok));
        if (tmp == -2)
          return;
        if (tmp != -1)
          value = value || tmp;
      } else if (tokVal == reserveWords[NOR]) {

      } else if (tokVal == reserveWords[XOR]) {

      } else if (tokVal == reserveWords[AND]) {
        tmp = getValueFromStmt(&(tok));
        if (tmp == -2)
          return;
        if (tmp != -1)
          value = value && tmp;
      } else if (tokVal == reserveWords[XNOR]) {

      } else if (tokVal == reserveWords[NAND]) {

      } else if (tokVal == reserveWords[NOT]) {

      } // else if

    void *val = ((Entry *)(outputTok->value))->value;
    if (val)
      tokenFree(val);
    printf("output value = %ld\n", value);
    ((Entry *)(outputTok->value))->value =
        new_token(DIGIT, (void *)value, 0, 0);
  } // for
} // gates_sim

void moduleInput(Module *module, TokenPtr inputVals) {
  TokenPtr tmp = module->inputs;
  for (; tmp; tmp = tmp->next, inputVals = inputVals->next)
    if (((Entry *)(tmp->value))->value)
      tokenFree(((Entry *)(tmp->value))->value);
    else
      ((Entry *)(tmp->value))->value = tokenClone(inputVals);
} // moduleInput

void moduleOutput(Module *module) { // TODO:had error
  printf(
      "key = %s, value = %s\n",
      (string)((Entry *)(module->outputs->value))->key,
      (string)(((TokenPtr)((Entry *)(module->outputs->value))->value)->value));
} // moduleOutput

void modulePrint(Module *module) {
  printf("module %s\n", module->name);
  printf("Head :\n");
  printToken(module->head);
  printf("Inputs :\n");
  printToken(module->inputs);
  printf("Outputs :\n");
  printToken(module->outputs);
  printf("Wires :\n");
  printToken(module->wires);
  printf("Gates :\n");
  GatePtr gatePtr = module->gates;
  for (size_t i = 0; i < module->countOfGates; ++i, gatePtr = gatePtr->next) {
    printf("count : %ld\n", gatePtr->count);
    printToken(gatePtr->gateLL);
  } // for

  printf("---------------\n");
} // modulePrint

void moduleFree(Module *module) {
  tokenFree(module->outputs);
  tokenFree(module->inputs);
  tokenFree(module->head);
  tokenFree(module->wires);
  GatePtr gatePtr = module->gates;
  for (GatePtr next = NULL; gatePtr; gatePtr = next) {
    next = gatePtr->next;
    tokenFree(gatePtr->gateLL);
    free(gatePtr);
  } // for
} // moduleFree

size_t fprintfToken(FILE *fp, TokenPtr tokenPtr) {
  if (!tokenPtr) {
    perror("Error! tokenPtr is NULL!!!\n");
    exit(EXIT_FAILURE);
  } // if

  if (tokenPtr->type == RESERVEWORD) {
    fprintf(fp, "%s", (string)tokenPtr->value);
    return strlen(tokenPtr->value);
  } else if (tokenPtr->type == SYMBOL) {
    fprintf(fp, "%s", (string)(((Entry *)(tokenPtr->value))->key));
    return strlen(((Entry *)(tokenPtr->value))->key);
  } else if (tokenPtr->type == DIGIT) {
    fprintf(fp, "%ld", ((intmax_t)tokenPtr->value));

    char buffer[100];
    sprintf(buffer, "%ld", (intmax_t)tokenPtr->value);
    return strlen(buffer);
  } else if (tokenPtr->type == DELIMITER) {
    fprintf(fp, "%s", (string)(tokenPtr->value));
    return strlen(tokenPtr->value);
  } else {
    perror("type error");
    exit(EXIT_FAILURE);
  } // else
} // fprintToken

void patch_output(TokenPtr token, string filename) {
  size_t line = 1, column = 0;
  bool isGetModule = false;
  bool isGetGate = false;
  bool isEnd = false;
  FILE *fp;
  fp = fopen(filename, "w");
  for (TokenPtr tmp = token; tmp && !isEnd; tmp = tmp->next) {
    for (; line < tmp->line; ++line) {
      fputc('\n', fp);
      column = 0;
    } // if

    for (; column < tmp->column; ++column)
      fputc(' ', fp);

    if (tmp->type == RESERVEWORD) {
      if (tmp->value == reserveWords[ENDMODULE])
        isEnd = true;
      else if (tmp->value == reserveWords[MODULE]) {
        isGetModule = true;
      } // else if
      else if (tmp->value == reserveWords[OR] ||
               tmp->value == reserveWords[NOR] ||
               tmp->value == reserveWords[XOR] ||
               tmp->value == reserveWords[NOT] ||
               tmp->value == reserveWords[AND] ||
               tmp->value == reserveWords[XNOR] ||
               tmp->value == reserveWords[NAND]) {

        isGetGate = true;
      } // else if
    }   // if
    else if (tmp->type == SYMBOL && isGetGate) {
      fputs("eco_", fp);
      isGetGate = false;
    } // else if

    column += fprintfToken(fp, tmp);

    if (tmp->type == SYMBOL && isGetModule) {
      fputs("_eco", fp);
      isGetModule = false;
    } // else if
  }   // for

  fputc('\n', fp);
  fclose(fp);
} // patch_output
