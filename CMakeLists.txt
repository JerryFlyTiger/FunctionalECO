cmake_minimum_required(VERSION 3.20)
project(FunctionalECO C)

set(CMAKE_C_STANDARD 11)

add_executable(FunctionalECO
        src/main.c
        src/B_Tree.c
        src/eval.c
        src/gettoken.c
        src/mylib.c
        src/symbolTable.c
        include/B_Tree.h
        include/myHeader.h
        include/symbolTable.h
        include/tokenize.h
        include/functionalEcoRoot.h
        )
