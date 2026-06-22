# sml-proof

[![CI](https://github.com/sjqtentacles/sml-proof/actions/workflows/ci.yml/badge.svg)](https://github.com/sjqtentacles/sml-proof/actions/workflows/ci.yml)

A **natural-deduction proof checker** for classical propositional logic, in pure
Standard ML. The formula type is reused verbatim from the vendored
[`sml-logic`](https://github.com/sjqtentacles/sml-logic) library (`Logic.prop`),
so proofs are stated over exactly the propositions that `sml-logic` parses,
pretty-prints and decides — and any closed theorem can be cross-checked
semantically with `Logic.isTautology`.

A `proof` is a derivation tree built from the standard introduction/elimination
rules plus classical reductio (`RAA`). `infer` walks the tree, validates every
rule application, and returns the derived **sequent** as a pair

```
(open / undischarged assumptions, conclusion)
```

Rules that discharge an assumption (`->I`, `~I`, `vE`, `RAA`) remove every
assumption structurally equal to the discharged formula.

No FFI, no threads, no clock, no randomness: deterministic and byte-identical
under **MLton** and **Poly/ML**. Open assumptions are returned de-duplicated and
ordered by pretty-printed form.

## Rules

| Constructor | Rule |
|---|---|
| `Assume p` | `p ⊢ p` |
| `TrueI` | `⊢ ⊤` |
| `AndI (p, q)` / `AndE1 p` / `AndE2 p` | `∧` intro / elim |
| `OrI1 (p, b)` / `OrI2 (a, p)` / `OrE (p, a, q, b, r)` | `∨` intro / elim (discharging) |
| `ImpI (a, p)` / `ImpE (p, q)` | `→` intro (discharging) / elim (modus ponens) |
| `NotI (a, p)` / `NotE (p, q)` | `¬` intro (discharging) / elim |
| `FalseE (p, φ)` | ex falso quodlibet |
| `RAA (a, p)` | classical reductio (discharges `¬a`) |
| `IffI (p, q)` / `IffE1 p` / `IffE2 p` | `↔` intro / elim |

## API

```sml
structure Proof : sig
  type prop = Logic.prop
  datatype proof = Assume of prop | TrueI
    | AndI of proof * proof | AndE1 of proof | AndE2 of proof
    | OrI1 of proof * prop  | OrI2 of prop * proof
    | OrE of proof * prop * proof * prop * proof
    | ImpI of prop * proof  | ImpE of proof * proof
    | NotI of prop * proof  | NotE of proof * proof
    | FalseE of proof * prop | RAA of prop * proof
    | IffI of proof * proof | IffE1 of proof | IffE2 of proof
  exception Invalid of string

  val infer  : proof -> prop list * prop
  val propEq : prop -> prop -> bool
  val proves : prop list -> proof -> prop -> bool
  val isTheorem : proof -> prop -> bool
  val sequentToString : proof -> string
end
```

## Example

```sml
val A = Logic.Var "A" and B = Logic.Var "B"

(* the K combinator  A -> (B -> A) *)
val k = Proof.ImpI (A, Proof.ImpI (B, Proof.Assume A))
val true = Proof.isTheorem k (Logic.Imp (A, Logic.Imp (B, A)))
val true = Logic.isTautology (Logic.Imp (A, Logic.Imp (B, A)))   (* cross-check *)
```

Running [`examples/demo.sml`](examples/demo.sml) with `make example` prints
(note `sml-logic`'s pretty-printer renders negation as `!`):

```
Natural-deduction proofs checked by sml-proof:

Implication (K combinator):
  A -> (B -> A)
    |- A -> B -> A   [tautology: true]

Conjunction commutativity:
  A & B -> B & A
    |- A & B -> B & A   [tautology: true]

Law of excluded middle (classical reductio):
  A | ~A
    |- A | !A   [tautology: true]

Double-negation elimination:
  ~~A -> A
    |- !!A -> A   [tautology: true]

The checker rejects an invalid step:
  AndE1 applied to a non-conjunction A:  proves = false

Goal parsed by sml-logic, then proved here:
  parsed goal     : A -> B -> A
  proof is a theorem of it : true
```

## Build & test

Requires [MLton](http://mlton.org/) and/or [Poly/ML](https://polyml.org/).

```sh
make test        # build + run the suite under MLton
make test-poly   # run the suite under Poly/ML
make all-tests   # both
make example     # build + run the demo
make clean
```

## Installing with smlpkg

```sh
smlpkg add github.com/sjqtentacles/sml-proof
smlpkg sync
```

`sml-proof` vendors `sml-logic` under `lib/github.com/sjqtentacles/sml-logic/`
(a byte-identical copy of the upstream library). Reference
`lib/github.com/sjqtentacles/sml-proof/proof.mlb` from your own `.mlb`
(MLton / MLKit), or feed `sources.mlb` to `tools/polybuild` (Poly/ML).

## Layout

```
sml.pkg                                      smlpkg manifest (requires sml-logic)
Makefile                                     MLton + Poly/ML targets
.github/workflows/ci.yml                     CI: MLton + Poly/ML
lib/github.com/sjqtentacles/
  sml-proof/  proof.sig proof.sml sources.mlb proof.mlb
  sml-logic/  vendored propositional-logic library (byte-identical copy)
examples/
  demo.sml      proof checking + sml-logic cross-checks
test/
  harness.sml / test.sml                     28 reference checks
  entry.sml / main.sml
tools/polybuild                              Poly/ML build wrapper
```

## Tests

28 deterministic checks: classic propositional theorems with explicit
derivation trees — identity, conjunction commutativity, modus ponens, the K
combinator `A → (B → A)`, hypothetical syllogism, ex falso, the **law of
excluded middle** and **double-negation elimination** via classical reductio, a
**De Morgan** law, disjunction-elimination commutativity, and biconditional
intro/elim — each closed theorem cross-checked against `sml-logic`'s semantic
tautology test, plus several invalid proofs that the checker correctly rejects.
Run `make all-tests` to verify identical output under both compilers.

## License

MIT. See [LICENSE](LICENSE).
