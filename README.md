# CORALean-C — CORA-COMP submission

A [CORA-COMP](https://github.com/CORA-COMP/cora-eval-platform) entry that runs
[CORALean](https://gitlab.lrz.de/cps/coralean)'s float layer: set operations proved sound in
Lean 4, rounded outward at every step, and compiled to a native binary through the C that
Lean emits.

Submit it like any other tool: this repository and a commit, plus a Debian- or Ubuntu-based
image (e.g. `ubuntu:24.04`). `install_tool.sh` installs Lean and builds everything. The scalar
is chosen at run time, so the same commit is entered twice with different tool environments:

| Tool environment | Scalar | Trusted base |
| --- | --- | --- |
| `CORALEAN_SCALAR=dyadic` (default) | CORALean's `Dyadic 53`: an integer mantissa rounded to a double's 53 bits, unbounded exponent | Lean, its runtime and GMP |
| `CORALEAN_SCALAR=double` | the hardware double, round-to-nearest and then one representable value outward | additionally, the IEEE-754 axioms in [`CoraleanC/IEEE.lean`](CoraleanC/IEEE.lean) |

**The double scalar.** Lean's `Float` has no model, so the facts the proofs need of it are
axioms, and they state IEEE-754 behaviour of *finite* doubles. Every operation therefore
carries infinities and NaN into its result rather than hiding them — rounding keeps them,
`minimum`/`maximum` propagate NaN, an inexact `half` is NaN — and the binary reports `error`
unless every output is finite. A finite result was computed from finite values only, which is
where the axioms hold.

## What it runs

| | |
| --- | --- |
| Benchmarks | `test`, `interval`, `zonotope`, and both `-batched` twins |
| Devices | `cpu`; every `gpu` instance reports `unsupported` |
| Batched | yes, one set after another |

| Operation | CORALean definition | Guarantee |
| --- | --- | --- |
| `startup` | `Zonotope.materialise` of `(zeros(n), eye(n))` | — |
| `generateRandom` | — (inputs, generated here) | — |
| `randPoint` | — (`c + G·β`, drawn here) | — |
| `supportFunc` | `Zonotope.boundDot`, `Interval.boundDot` | an upper bound of `max dᵀx` |
| `matMul` | `Zonotope.mtimes`, `Interval.mtimes` | encloses `M·S` |
| `minkSum` | `Zonotope.plus`, `Interval.plus` | encloses `S₁ ⊕ S₂` |
| `contains` | interval: `FloatOps.le` per bound | `true` is sound |

Every result carries CORALean's error box, the interval that holds what rounding has cost, so
`supportFunc` and the enclosures are over-approximations of the exact answer rather than
approximations of it.

**Zonotope `contains` is `unsupported`.** Deciding it is a linear program, and CORALean has no
certified way to answer *yes*: its simplex (`Global/LinProg/Simplex.lean`) is deliberately
untrusted, and what gets checked is its dual solution, by weak duality — which certifies
upper bounds and emptiness, i.e. that a point is *not* contained. A proof of containment needs
a primal witness `β` with `‖β‖∞ ≤ 1` checked under outward rounding, and the float layer has
no such check. Every catalog query is contained, so a certified *no* would not help.

## What is measured

`run_instance.sh` execs the binary, which generates the inputs and repeats the operation
`repetition` times. The result file also has the binary's own split:

| Column | |
| --- | --- |
| `time_generate` | generating the inputs |
| `time_operation` | the operation, repeated `repetition` times |
| `dtype` | `dyadic53` or `float64-outward` |

Every set is stored after each operation (`materialise`), as CORALean's own operation
instances do, so a timing covers the numbers rather than a closure that would compute them
later. Starting the binary takes about 60 ms.

## Building

`CORALean/` is the part of CORALean that `Main.lean` reaches — 260 modules, proofs
included, copied unchanged from commit `bbe335f`. Only those are checked, and only their C
and that of the Mathlib modules they import is compiled.

`install_tool.sh` runs:

```bash
lake exe cache get      # Mathlib's prebuilt oleans
lake build coralean-c   # checks CORALean/, compiles the emitted C, links
```

On a 16-core machine, checking `CORALean/` takes about 11 minutes and compiling and linking
about 3.

## Running one instance locally

```bash
P='{"set": "zonotope", "operation": "matMul", "dim": 10, "generators": 20, "device": "cpu", "repetition": 100}'
CORALEAN_SCALAR=double ./run_instance.sh v1 zonotope matMul-10d-cpu "$P" 60 /tmp/result.csv
cat /tmp/result.csv
```

## Layout

| File | |
| --- | --- |
| `Main.lean` | the instance: inputs, the repeated CORALean operation, the verdict |
| `CoraleanC/IEEE.lean` | the hardware double as a `SoundFloatArithmetic` scalar |
| `CORALean/` | the copied CORALean modules |
| `lakefile.lean` | the `coralean-c` executable and the Mathlib version CORALean pins |
| `install_tool.sh` | installs Lean, builds the executable |
| `prepare_instance.sh` | nothing to prepare |
| `run_instance.sh` | the timed script: runs the executable |
