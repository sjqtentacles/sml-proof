(* demo.sml - check a few natural-deduction proofs and confirm, via sml-logic,
   that each closed theorem's conclusion is a tautology.  Deterministic:
   identical output on every run and both compilers. *)

structure P = Proof
structure L = Logic

val A = L.Var "A" and B = L.Var "B" and C = L.Var "C"
fun imp a b = L.Imp (a, b)
fun conj a b = L.And (a, b)
fun disj a b = L.Or (a, b)
val nt = L.Not

fun report name pf =
  let
    val (opens, _) = P.infer pf
    val seq = P.sequentToString pf
    val taut = if null opens then L.isTautology (#2 (P.infer pf)) else true
  in
    print ("  " ^ name ^ "\n    " ^ seq
           ^ (if null opens then "   [tautology: " ^ Bool.toString taut ^ "]" else "   [open]")
           ^ "\n")
  end

val () = print "Natural-deduction proofs checked by sml-proof:\n\n"

val () = print "Implication (K combinator):\n"
val () = report "A -> (B -> A)" (P.ImpI (A, P.ImpI (B, P.Assume A)))

val () = print "\nConjunction commutativity:\n"
val () = report "A & B -> B & A"
  (P.ImpI (conj A B, P.AndI (P.AndE2 (P.Assume (conj A B)), P.AndE1 (P.Assume (conj A B)))))

val () = print "\nLaw of excluded middle (classical reductio):\n"
val h = nt (disj A (nt A))
val notA = P.NotI (A, P.NotE (P.Assume h, P.OrI1 (P.Assume A, nt A)))
val lem = P.RAA (disj A (nt A), P.NotE (P.Assume h, P.OrI2 (A, notA)))
val () = report "A | ~A" lem

val () = print "\nDouble-negation elimination:\n"
val dne = P.ImpI (nt (nt A), P.RAA (A, P.NotE (P.Assume (nt (nt A)), P.Assume (nt A))))
val () = report "~~A -> A" dne

val () = print "\nThe checker rejects an invalid step:\n"
val () = print ("  AndE1 applied to a non-conjunction A:  proves = "
                ^ Bool.toString (P.proves [A] (P.AndE1 (P.Assume A)) A) ^ "\n")

(* the formula type is shared with sml-logic, so we can also parse a goal *)
val () = print "\nGoal parsed by sml-logic, then proved here:\n"
val goal = L.parse "A -> (B -> A)"
val () = print ("  parsed goal     : " ^ L.pretty goal ^ "\n")
val () = print ("  proof is a theorem of it : "
                ^ Bool.toString (P.isTheorem (P.ImpI (A, P.ImpI (B, P.Assume A))) goal) ^ "\n")
