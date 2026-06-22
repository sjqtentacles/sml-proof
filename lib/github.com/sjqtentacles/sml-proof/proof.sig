(* proof.sig

   A natural-deduction proof checker for classical propositional logic, in pure
   Standard ML.  The formula type is reused verbatim from the vendored
   `sml-logic` library (`Logic.prop`), so proofs are stated over exactly the
   propositions that `sml-logic` parses, pretty-prints and decides.

   A `proof` is a derivation tree built from the standard introduction and
   elimination rules (plus classical reductio).  `infer` walks the tree, checks
   every rule application, and returns the derived sequent as a pair of
     (open / undischarged assumptions, conclusion).
   Rules that discharge an assumption (->I, ~I, vE, RAA) remove every assumption
   structurally equal to the discharged formula.

   The checker is purely syntactic; soundness can be cross-checked semantically
   with `sml-logic` (every closed theorem's conclusion is a tautology).

   No FFI, threads, clock or randomness: deterministic and byte-identical under
   MLton and Poly/ML.  Open assumptions are returned de-duplicated and ordered
   by their pretty-printed form. *)

signature PROOF =
sig
  type prop = Logic.prop

  datatype proof =
      Assume of prop                              (* phi |- phi *)
    | TrueI                                       (* |- 1 *)
    | AndI  of proof * proof                      (* A, B  => A & B *)
    | AndE1 of proof                              (* A & B => A *)
    | AndE2 of proof                              (* A & B => B *)
    | OrI1  of proof * prop                       (* A     => A | B  (B supplied) *)
    | OrI2  of prop * proof                       (* B     => A | B  (A supplied) *)
    | OrE   of proof * prop * proof * prop * proof
                                                  (* A|B, [A]..C, [B]..C => C *)
    | ImpI  of prop * proof                       (* discharge A in (..B) => A -> B *)
    | ImpE  of proof * proof                      (* A -> B, A => B  (modus ponens) *)
    | NotI  of prop * proof                       (* discharge A in (..0) => ~A *)
    | NotE  of proof * proof                      (* ~A, A => 0 *)
    | FalseE of proof * prop                      (* 0 => phi  (ex falso) *)
    | RAA   of prop * proof                       (* classical: discharge ~A in (..0) => A *)
    | IffI  of proof * proof                      (* A -> B, B -> A => A <-> B *)
    | IffE1 of proof                              (* A <-> B => A -> B *)
    | IffE2 of proof                              (* A <-> B => B -> A *)

  exception Invalid of string

  (* the derived sequent: (open assumptions, conclusion).  Raises Invalid with
     a description if any rule is misapplied. *)
  val infer : proof -> prop list * prop

  (* structural equality of propositions *)
  val propEq : prop -> prop -> bool

  (* does the proof derive `goal` using only assumptions drawn from `ctx`? *)
  val proves : prop list -> proof -> prop -> bool

  (* a closed theorem: the proof has no open assumptions and concludes `goal`. *)
  val isTheorem : proof -> prop -> bool

  (* render the derived sequent, e.g. "A, B |- A & B" (or "|- ..." if closed). *)
  val sequentToString : proof -> string
end
