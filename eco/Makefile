CXX      ?= clang++
CADICAL  := ../tools/cadical
CXXFLAGS := -std=c++17 -O3 -pthread -Wall -Wextra -I$(CADICAL)/src
LDLIBS   := $(CADICAL)/build/libcadical.a
SRC      := src/main.cpp
HDRS     := src/netlist.hpp src/aig.hpp src/sat.hpp src/patch.hpp src/rectify.hpp

all: build/eco

build/eco: $(SRC) $(HDRS)
	@mkdir -p build
	$(CXX) $(CXXFLAGS) $(SRC) $(LDLIBS) -o $@

debug: $(SRC) $(HDRS)
	@mkdir -p build
	$(CXX) -std=c++17 -g -O0 -fsanitize=address,undefined -I$(CADICAL)/src $(SRC) $(LDLIBS) -o build/eco_debug

clean:
	rm -rf build

.PHONY: all debug clean
