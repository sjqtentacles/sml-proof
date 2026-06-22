(* proof.sml - implementation of the PROOF signature. *)

structure Proof :> PROOF =
struct
  type prop = Logic.prop

  datatype proof =
      Assume of prop
    | TrueI
    | AndI  of proof * proof
    | AndE1 of proof
    | AndE2 of proof
    | OrI1  of proof * prop
    | OrI2  of prop * proof
    | OrE   of proof * prop * proof * prop * proof
    | ImpI  of prop * proof
    | ImpE  of proof * proof
    | NotI  of prop * proof
    | NotE  of proof * proof
    | FalseE of proof * prop
    | RAA   of prop * proof
    | IffI  of proof * proof
    | IffE1 of proof
    | IffE2 of proof

  exception Invalid of string

  open Logic

  fun propEq (Var a) (Var b) = a = b
    | propEq TrueP TrueP = true
    | propEq FalseP FalseP = true
    | propEq (Not a) (Not b) = propEq a b
    | propEq (And (a, b)) (And (c, d)) = propEq a c andalso propEq b d
    | propEq (Or (a, b)) (Or (c, d)) = propEq a c andalso propEq b d
    | propEq (Imp (a, b)) (Imp (c, d)) = propEq a c andalso propEq b d
    | propEq (Iff (a, b)) (Iff (c, d)) = propEq a c andalso propEq b d
    | propEq _ _ = false

  (* assumption sets: de-duplicated, ordered by pretty form *)
  fun insA (p, []) = [p]
    | insA (p, q :: qs) =
        if propEq p q then q :: qs
        else case String.compare (Logic.pretty p, Logic.pretty q) of
               LESS => p :: q :: qs
             | EQUAL => if propEq p q then q :: qs else p :: q :: qs
             | GREATER => q :: insA (p, qs)
  fun unionA (xs, ys) = List.foldl insA ys xs
  fun removeA (a, xs) = List.filter (fn x => not (propEq a x)) xs

  (* infer returns (open assumptions, conclusion) *)
  fun infer pf =
    case pf of
      Assume p => ([p], p)
    | TrueI => ([], TrueP)
    | AndI (p, q) =>
        let val (ap, cp) = infer p val (aq, cq) = infer q
        in (unionA (ap, aq), And (cp, cq)) end
    | AndE1 p =>
        let val (ap, cp) = infer p
        in case cp of And (a, _) => (ap, a)
                    | _ => raise Invalid "AndE1: premise is not a conjunction" end
    | AndE2 p =>
        let val (ap, cp) = infer p
        in case cp of And (_, b) => (ap, b)
                    | _ => raise Invalid "AndE2: premise is not a conjunction" end
    | OrI1 (p, b) =>
        let val (ap, cp) = infer p in (ap, Or (cp, b)) end
    | OrI2 (a, p) =>
        let val (ap, cp) = infer p in (ap, Or (a, cp)) end
    | OrE (p, a, q, b, r) =>
        let
          val (ap, cp) = infer p
          val (aq, cq) = infer q
          val (ar, cr) = infer r
        in
          case cp of
            Or (x, y) =>
              if not (propEq x a andalso propEq y b)
              then raise Invalid "OrE: case formulas do not match the disjunction"
              else if not (propEq cq cr)
              then raise Invalid "OrE: the two branches reach different conclusions"
              else (unionA (ap, unionA (removeA (a, aq), removeA (b, ar))), cq)
          | _ => raise Invalid "OrE: first premise is not a disjunction"
        end
    | ImpI (a, p) =>
        let val (ap, cp) = infer p in (removeA (a, ap), Imp (a, cp)) end
    | ImpE (p, q) =>
        let
          val (ap, cp) = infer p val (aq, cq) = infer q
        in
          case cp of
            Imp (a, b) =>
              if propEq a cq then (unionA (ap, aq), b)
              else raise Invalid "ImpE: argument does not match the antecedent"
          | _ => raise Invalid "ImpE: first premise is not an implication"
        end
    | NotI (a, p) =>
        let val (ap, cp) = infer p
        in if propEq cp FalseP then (removeA (a, ap), Not a)
           else raise Invalid "NotI: body does not derive falsehood" end
    | NotE (p, q) =>
        let val (ap, cp) = infer p val (aq, cq) = infer q
        in case cp of
             Not a => if propEq a cq then (unionA (ap, aq), FalseP)
                      else raise Invalid "NotE: ~A and A do not match"
           | _ => raise Invalid "NotE: first premise is not a negation" end
    | FalseE (p, phi) =>
        let val (ap, cp) = infer p
        in if propEq cp FalseP then (ap, phi)
           else raise Invalid "FalseE: premise is not falsehood" end
    | RAA (a, p) =>
        let val (ap, cp) = infer p
        in if propEq cp FalseP then (removeA (Not a, ap), a)
           else raise Invalid "RAA: body does not derive falsehood" end
    | IffI (p, q) =>
        let val (ap, cp) = infer p val (aq, cq) = infer q
        in case (cp, cq) of
             (Imp (a, b), Imp (b', a')) =>
               if propEq a a' andalso propEq b b'
               then (unionA (ap, aq), Iff (a, b))
               else raise Invalid "IffI: the two implications are not converses"
           | _ => raise Invalid "IffI: premises are not implications" end
    | IffE1 p =>
        let val (ap, cp) = infer p
        in case cp of Iff (a, b) => (ap, Imp (a, b))
                    | _ => raise Invalid "IffE1: premise is not a biconditional" end
    | IffE2 p =>
        let val (ap, cp) = infer p
        in case cp of Iff (a, b) => (ap, Imp (b, a))
                    | _ => raise Invalid "IffE2: premise is not a biconditional" end

  fun subsetCtx (opens, ctx) =
    List.all (fn a => List.exists (fn c => propEq a c) ctx) opens

  fun proves ctx pf goal =
    let val (opens, concl) = infer pf
    in propEq concl goal andalso subsetCtx (opens, ctx) end
    handle Invalid _ => false

  fun isTheorem pf goal =
    let val (opens, concl) = infer pf
    in null opens andalso propEq concl goal end
    handle Invalid _ => false

  fun sequentToString pf =
    let
      val (opens, concl) = infer pf
      val lhs = String.concatWith ", " (List.map Logic.pretty opens)
    in
      (if lhs = "" then "" else lhs ^ " ") ^ "|- " ^ Logic.pretty concl
    end
end
