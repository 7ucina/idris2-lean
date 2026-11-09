LEAN_HOME ?= $(HOME)/idris2-fast/lean/lean-4.35.0-linux
# Lean's bundled clang (the compiler Lean itself uses); it ships no libc
# headers, so point it at the system's glibc headers
CC = $(LEAN_HOME)/bin/clang
SYSINC = -nostdinc -isystem $(LEAN_HOME)/include/clang -isystem /usr/include/x86_64-linux-gnu -isystem /usr/include
# must match the flags the backend compiles generated code with (IDRIS2_LEAN_CFLAGS)
CFLAGS ?= -O3
FLAGS = $(CFLAGS) -DNDEBUG -w $(SYSINC) -I$(LEAN_HOME)/include

all: libidris_lean.a idris_lean.h.pch ld/ld.lld

libidris_lean.a: idris_lean.c idris_lean.h
	$(CC) $(FLAGS) -c idris_lean.c -o idris_lean.o
	ar rcs $@ idris_lean.o

# precompiled header: saves re-parsing lean.h and libc headers on every build
idris_lean.h.pch: idris_lean.h
	$(CC) $(FLAGS) -x c-header idris_lean.h -o $@

# Lean's bundled lld (much faster than bfd for the large static runtime)
ld/ld.lld:
	mkdir -p ld && ln -sf $(LEAN_HOME)/bin/ld.lld ld/ld.lld

clean:
	rm -rf idris_lean.o libidris_lean.a idris_lean.h.pch ld
