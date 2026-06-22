(* Tests for sml-proof: natural-deduction checker over sml-logic propositions.

   Reference vectors: classic propositional theorems with explicit derivation
   trees (identity, conjunction commutativity, modus ponens, K combinator,
   hypothetical syllogism, ex falso, the law of excluded middle and double-
   negation elimination via classical reductio, a De Morgan law, biconditional
   intro/elim).  Each closed theorem is cross-checked against sml-logic's
   semantic tautology test, and several invalid proofs are rejected. *)

structure Tests =
struct
  open Harness
  structure P = Proof
  structure L = Logic

  val A = L.Var "A" and B = L.Var "B" and C = L.Var "C"
  infix 4 -->
  infix 5 ||
  infix 6 &
  fun a & b = L.And (a, b)
  fun a || b = L.Or (a, b)
  fun a --> b = L.Imp (a, b)
  val nt = L.Not

  fun thm name pf goal =
    ( checkBool (name ^ " (derives goal)") (true, P.isTheorem pf goal)
    ; checkBool (name ^ " (goal is a tautology)") (true, L.isTautology goal) )

  fun runAll () =
    let
      val () = section "identity and conjunction"
      val () = thm "A -> A" (P.ImpI (A, P.Assume A)) (A --> A)
      val pAndComm =
        P.ImpI (A & B,
          P.AndI (P.AndE2 (P.Assume (A & B)), P.AndE1 (P.Assume (A & B))))
      val () = thm "A&B -> B&A" pAndComm ((A & B) --> (B & A))

      val () = section "implication"
      val () = thm "A -> (B -> A)" (P.ImpI (A, P.ImpI (B, P.Assume A))) (A --> (B --> A))
      val syll =
        P.ImpI (A --> B,
          P.ImpI (B --> C,
            P.ImpI (A,
              P.ImpE (P.Assume (B --> C), P.ImpE (P.Assume (A --> B), P.Assume A)))))
      val () = thm "hypothetical syllogism"
                 syll ((A --> B) --> ((B --> C) --> (A --> C)))

      val () = section "modus ponens as a sequent"
      val mp = P.ImpE (P.Assume (A --> B), P.Assume A)
      val () = checkBool "[A->B, A] |- B" (true, P.proves [A --> B, A] mp B)
      val () = checkBool "open assumption not in ctx -> not proved"
                 (false, P.proves [A] mp B)

      val () = section "negation / ex falso"
      val exfalso = P.FalseE (P.NotE (P.Assume (nt A), P.Assume A), B)
      val () = checkBool "[A, ~A] |- B (ex falso)" (true, P.proves [A, nt A] exfalso B)

      val () = section "classical: excluded middle"
      val h = nt (A || nt A)
      val notA = P.NotI (A, P.NotE (P.Assume h, P.OrI1 (P.Assume A, nt A)))
      val lemFalse = P.NotE (P.Assume h, P.OrI2 (A, notA))
      val lem = P.RAA (A || nt A, lemFalse)
      val () = thm "A | ~A" lem (A || nt A)
      val () = checkString "lem sequent is closed"
                 ("|- " ^ L.pretty (A || nt A), P.sequentToString lem)

      val () = section "classical: double-negation elimination"
      val dne =
        P.ImpI (nt (nt A),
          P.RAA (A, P.NotE (P.Assume (nt (nt A)), P.Assume (nt A))))
      val () = thm "~~A -> A" dne (nt (nt A) --> A)

      val () = section "De Morgan"
      val ndis = nt (A || B)
      val dmNotA = P.NotI (A, P.NotE (P.Assume ndis, P.OrI1 (P.Assume A, B)))
      val dmNotB = P.NotI (B, P.NotE (P.Assume ndis, P.OrI2 (A, P.Assume B)))
      val deMorgan = P.ImpI (ndis, P.AndI (dmNotA, dmNotB))
      val () = thm "~(A|B) -> (~A & ~B)" deMorgan (nt (A || B) --> (nt A & nt B))

      val () = section "disjunction elimination"
      (* from A|B, with A->C and B->C as assumptions discharged, derive C; here
         take C = B|A to show commutativity of disjunction *)
      val orComm =
        P.ImpI (A || B,
          P.OrE (P.Assume (A || B),
                 A, P.OrI2 (B, P.Assume A),
                 B, P.OrI1 (P.Assume B, A)))
      val () = thm "A|B -> B|A" orComm ((A || B) --> (B || A))

      val () = section "biconditional"
      val iffRefl = P.IffI (P.ImpI (A, P.Assume A), P.ImpI (A, P.Assume A))
      val () = thm "A <-> A" iffRefl (L.Iff (A, A))
      val () = checkBool "IffE1 extracts A->B"
                 (true, P.proves [L.Iff (A, B)] (P.IffE1 (P.Assume (L.Iff (A, B)))) (A --> B))

      val () = section "the checker rejects invalid proofs"
      val () = checkBool "AndE1 on a non-conjunction fails"
                 (false, P.proves [A] (P.AndE1 (P.Assume A)) A)
      val () = checkBool "undischarged assumption is not a theorem"
                 (false, P.isTheorem (P.Assume A) A)
      val () = checkBool "ImpE with wrong argument fails"
                 (false, P.proves [A --> B, C] (P.ImpE (P.Assume (A --> B), P.Assume C)) B)
      val () = checkBool "A -> B is NOT a theorem (and not a tautology)"
                 (false, L.isTautology (A --> B))
      val () = checkBool "OrE with mismatched case formula fails"
                 (false, P.proves [A || B]
                    (P.OrE (P.Assume (A || B), A, P.Assume A, C, P.Assume C)) A)
    in
      Harness.run ()
    end

  val run = runAll
end
