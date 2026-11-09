# idris2-lean

**An Idris2 code generator that compiles to C on top of Lean 4's runtime, and runs as fast as Lean 4.**

`idris2-lean` adds a `--cg lean` backend to the Idris2 compiler. It lowers Idris2's
ANF into a λRC-style IR and ports Lean 4's memory-management optimizations to
Idris. The IR becomes C that links against Lean's own runtime (`lean.h`,
`libleanrt`), so compiled Idris programs get Lean's object layout, small-object
allocator, GMP-backed integers, strings, closures and task manager.

```
$ idris2-lean --cg lean Main.idr -o main && ./build/exec/main
```

## Performance

Six benchmarks, written as equivalent programs in Lean 4 and Idris2. Times are the best of 3
runs; every output is checked against Lean's.

| benchmark | Lean 4.35 | **idris2-lean** | Idris2 (Chez) | Idris2 (RefC) |
|---|---:|---:|---:|---:|
| NFib (n = 38) | 0.20s | **0.20s** | 6.40s | 4.50s |
| BinaryTrees (depth 21) | 2.40s | **2.40s** | 48.2s | 61.3s |
| RBMap (4.2M inserts) | 1.60s | **1.40s** | 3.80s | 15.2s |
| Deriv (symbolic differentiation) | 2.20s | **1.10s** | 4.20s | 4.50s |
| NQueens (n = 13, list-based) | 3.00s | **2.50s** | 22.9s | wrong output |
| ListPipe (map/filter, 50 × 1M) | 0.40s | **0.30s** | 1.10s | 2.50s |

Peak memory is on par with Lean (e.g. RBMap 167 MB vs 168 MB; ListPipe 29 MB vs 46 MB).
On NFib the hot loop compiles to the same machine code as Lean's.

## How it works

The backend runs Lean's pipeline from *Counting Immutable Beans* (Ullrich & de Moura, 2019),
plus a few passes Idris needs:

| pass | module | what it does |
|---|---|---|
| lowering | `Lower.idr` | ANF → first-order IR with join points; rebuilding a matched constructor reuses the scrutinee |
| specialization | `Spec.idr` | clones higher-order functions for known closures (`foldr`, `map`, …); known closure calls become direct calls |
| simplification | `Opt.idr` | dead-let elimination; floating lets into the branch that uses them |
| unboxing | `Types.idr` | `Int`/`IntN`/`BitsN`/`Char`/`Double`/enums as raw C scalars, using declared types (sound under dependent types) |
| constructor layout | `Layout.idr` | Lean layout: boxed fields first, then unboxed scalar fields sorted by size |
| purity and CSE | `CSE.idr` | effect analysis (the world token isn't linear in ANF), CSE of pure expressions, pure constants cached as persistent objects |
| accumulator TRE | `Accum.idr` | `f x = a + f y` becomes a loop with an accumulator |
| reset/reuse | `ResetReuse.idr` | dead constructor cells are reused for new allocations |
| borrow inference | `Borrow.idr` | parameters that don't need ownership skip reference counting |
| explicit RC | `RC.idr` | precise `inc`/`dec` insertion |
| expansion | `Expand.idr` | in-place update fast path (unchanged fields aren't rewritten); `inc`/`dec` cancellation |
| C emission | `EmitC.idr` | C code with self tail calls as loops, boxed wrappers for closures, FFI glue |

The runtime layer (`support/idris_lean.{h,c}`) implements Idris primitive semantics on top of Lean's
runtime: wrapping fixed-width arithmetic, Euclidean `div`/`mod`, UTF-8 character-indexed strings,
`IORef`, `IOArray`, `Buffer`, clocks, string iterators, threads, mutexes, condition variables,
semaphores, barriers, channels, futures, and garbage-collection finalizers.

## Usage

Requirements: Linux x86-64, gcc, an Idris2 0.8 installation that includes the `idris2api`
package (`make install-api` in the Idris2 source tree), and a Lean 4 release toolchain
(tested with 4.35.0).

```sh
make -C support LEAN_HOME=/path/to/lean-4.35.0-linux   # runtime library, precompiled header, lld
idris2 --build idris2-lean.ipkg                         # builds build/exec/idris2-lean
```

`build/exec/idris2-lean` is a complete `idris2` executable with an extra backend:

```sh
idris2-lean --cg lean Main.idr -o main          # native binary in build/exec/main
idris2-lean --cg lean -p contrib Main.idr -o main
idris2-lean --cg lean --exec main Main.idr      # compile and run
IDRIS2_CG=lean idris2-lean --build project.ipkg # or set the default codegen
```

The resulting binaries are self-contained; Lean's runtime is linked statically.
Generated C is compiled with Lean's bundled clang and linked with Lean's `ld.lld`, so a
typical program builds in 1.3–2.2s.

### Configuration

| variable | default | meaning |
|---|---|---|
| `IDRIS2_LEAN_HOME` | `~/idris2-fast/lean/lean-4.35.0-linux` | Lean toolchain |
| `IDRIS2_LEAN_SUPPORT` | `~/idris2-fast/idris2-lean/support` | runtime support directory |
| `IDRIS2_LEAN_IDRIS_LIB` | `~/idris2-fast/prefix/idris2-0.8.0/lib` | location of `libidris2_support` |
| `IDRIS2_LEAN_CC` | Lean's clang | C compiler; `gcc` also works |
| `IDRIS2_LEAN_CFLAGS` | `-O3` | C flags (the precompiled header assumes `-O3`) |
| `IDRIS2_LEAN_DUMP=1` | unset | write the IR after each pass (`*.lower.ir` … `*.final.ir`) |
| `IDRIS2_LEAN_NO_ACCUM=1` | unset | disable the accumulator pass |

## Correctness

The backend passes **132 of 160** tests from Idris2's own suite (`allbackends`, `base`,
`prelude`, `refc`, `chez` and the *Type-Driven Development* book examples). Where RefC's recorded
expected output differs from ours, our output is identical to the Chez backend's. The
remaining failures are tests specific to other backends (Node, Chez's generated Scheme,
REPL behavior, build-tree paths), two tests of Scheme-only FFI, and one Int64→Double
rounding edge case where Chez and C differ.

```sh
IDRIS2_TESTS=/path/to/Idris2/tests tests/runtests.sh refc/strings chez/chez015 base/data_list
```

## Reproducing the benchmarks

```sh
LEAN_HOME=/path/to/lean bench/build.sh    # builds the Lean 4, idris2-lean, Chez and RefC versions
bench/run.sh lean4 lean chez refc
```

## Limitations

- C FFI callbacks (`CFFun`) and `%foreign` structs aren't supported. Scheme-only primitives
  other than the concurrency ones listed above aren't either.
- Garbage-collection finalizers run as soon as the last reference to a `GCPtr` is dropped.
  That's deterministic, but can be earlier than under Chez's tracing GC.
- `Lazy` values are thunks without memoization (as in the RefC backend).
- When a program's `main` returns, other threads are stopped (as in the Chez backend).
- Only tested on Linux x86-64. The default paths assume the layout used during development,
  so you'll usually need to set the variables above.

## Credits

The optimization passes follow Lean 4's compiler (Lean FRO; Apache 2.0) and the paper
*Counting Immutable Beans: Reference Counting Optimized for Purely Functional Programming*
by Sebastian Ullrich and Leonardo de Moura. Built on the Idris2 compiler API.
