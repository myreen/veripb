open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory finite_mapTheory;

val _ = new_theory "pb_constraint_int";

(* abstract syntax *)

Datatype:
  pb_constaint = PBC (num |-> int) int
End

(*

Datatype:
  pb_constaint = PBC (num |-> num # bool) num
End

Definition b2i_def[simp]:
  b2i T = 1:int ∧
  b2i F = 0:int
End

  4 * (1-i) + 3 * i + 2 * j >= 4
  1 * (1-i) + 2 * j >= 1

  ~i either 0 or 1

We need:
 - addition of constraints
 - division (same factor in each)
 - division (round up coeficients, follows from above version)
 - saturation
 - substitution (either literal or zero, one)
 - drat-like rule
 - implication (do not remove sat assignments)
 - dominance (more complicated than above)

*)

(* semantics *)

Definition b2i_def[simp]:
  b2i T = 1:int ∧
  b2i F = 0:int
End

Definition pb_sum_acc_def[simp]:
  pb_sum_acc l k v acc = v * b2i (l k) + acc
End

Definition pb_sum_def:
  pb_sum l (a: num |-> int) = ITFMAP (pb_sum_acc l) a (0:int)
End

Definition pb_val_def[simp]:
  pb_val l (PBC a i) ⇔ pb_sum l a ≥ i
End

(* lemmas about pb_sum *)

Definition pb_sum_to_def:
  pb_sum_to 0 l a = 0:int ∧
  pb_sum_to (SUC n) l a =
    case FLOOKUP a n of
    | NONE => pb_sum_to n l a
    | SOME v => v * b2i (l n) + pb_sum_to n l a
End

(*
  EVAL “pb_sum_to 4 l (FEMPTY |++ [(1,2);(3,4)])”
*)

Theorem pb_sum_to_intro:
  ∀a l. ∃k. ∀n. pb_sum l a = pb_sum_to (k+n) l a
Proof
  cheat
QED

(* addition *)

Definition add_def:
  add (PBC a1 i1) (PBC a2 i2) = PBC (FMERGE (+) a1 a2) (i1 + i2)
End

Theorem pb_sum_add:
  pb_sum l (FMERGE $+ f f') = pb_sum l f + pb_sum l f'
Proof
  qspecl_then [‘f’,‘l’] strip_assume_tac pb_sum_to_intro
  \\ qspecl_then [‘f'’,‘l’] strip_assume_tac pb_sum_to_intro
  \\ qspecl_then [‘FMERGE $+ f f'’,‘l’] strip_assume_tac pb_sum_to_intro
  \\ pop_assum (qspec_then ‘k+k'’ mp_tac)
  \\ pop_assum (qspec_then ‘k+k''’ mp_tac)
  \\ pop_assum (qspec_then ‘k'+k''’ mp_tac)
  \\ rw [] \\ rename [‘pb_sum_to n’]
  \\ rpt (pop_assum kall_tac)
  \\ Induct_on ‘n’
  \\ fs [pb_sum_to_def]
  \\ fs [FLOOKUP_FMERGE]
  \\ rpt CASE_TAC \\ fs []
  \\ intLib.COOPER_TAC
QED

Theorem add_thm:
  pb_val l c1 ∧ pb_val l c2 ⇒ pb_val l (add c1 c2)
Proof
  Cases_on ‘c1’ \\ Cases_on ‘c2’
  \\ fs [add_def,pb_sum_add]
  \\ intLib.COOPER_TAC
QED

val _ = export_theory();
