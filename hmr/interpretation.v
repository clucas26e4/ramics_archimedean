(** Interpretation of a hypersequent as a term in NNF *)
Require Import Rpos.
Require Import RL.hmr.term.
Require Import RL.hmr.hseq.
Require Import RL.hmr.semantic.

Require Import List.
Require Import Lra.

Require Import RL.OLlibs.Permutation_Type_more.

Local Open Scope R_scope.

(** ** Interpretation of a sequent *)
Fixpoint sem_seq (T1 : sequent) :=
  match T1 with
  | nil => MRS_zero
  | ((r , A) :: T1) => (r *S A) +S (sem_seq T1)
  end.

(** *** Properties of this interpretation *)
Lemma sem_seq_plus : forall T1 T2, sem_seq (T1 ++ T2) === sem_seq T1 +S sem_seq T2.
Proof.
  induction T1; intros T2.
  - etransitivity ; [ | apply commu_plus]; symmetry; apply neutral_plus.
  - specialize (IHT1 T2).
    destruct a as (r , A).
    simpl.
    etransitivity ; [ | apply asso_plus].
    apply (@ctxt (MRS_plusC (MRS_TC (r *S A)) MRS_hole)).
    apply IHT1.
Qed.

Lemma sem_seq_mul : forall T r, sem_seq (seq_mul r T) === r *S sem_seq T.
Proof.
  induction T; intros r.
  - symmetry; apply mul_0.
  - destruct a as [a Ha]; simpl.
    etransitivity ; [ apply (@ctxt (MRS_plusC (MRS_TC (time_pos r a *S Ha)) MRS_hole)); apply IHT | ]; simpl.
    etransitivity ; [ apply (@ctxt (MRS_plusC MRS_hole (MRS_TC (r *S sem_seq T)))) | ].
    { symmetry ; apply mul_assoc. }
    simpl; auto with MGA_solver.
Qed.

Lemma sem_seq_vec : forall r A (Hnnil : r <> nil), sem_seq (vec r A) === (existT _ (sum_vec r) (sum_vec_non_nil _ Hnnil)) *S A.
Proof.
  induction r; intros A Hnnil.
  { exfalso; auto. }
  destruct r as [ | b r].
  - simpl in *.
    replace (existT (fun r : R => (0 <? r) = true) (projT1 a + 0) (sum_vec_non_nil _ Hnnil)) with a by (apply Rpos_eq; simpl; nra).
    auto.
  - assert (b :: r <> nil) as H by now auto.
    specialize (IHr A H).
    change (sem_seq (vec (a :: b :: r) A)) with (a *S A +S (sem_seq (vec (b :: r) A))).
    replace (existT (fun r0 : R => (0 <? r0) = true) (sum_vec (a :: b :: r)) (sum_vec_non_nil _ Hnnil)) with (plus_pos a (existT _ (sum_vec (b :: r)) (sum_vec_non_nil _ H))) by (destruct a; destruct  b; apply Rpos_eq; simpl; nra).
    etransitivity ; [ | symmetry; apply mul_distri_coeff].
    auto with MGA_solver.
Qed.

Lemma sem_seq_permutation : forall T1 T2, Permutation_Type T1 T2 -> sem_seq T1 === sem_seq T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; try destruct x; try destruct y; simpl; try auto with MGA_solver.
  - etransitivity ; [ apply asso_plus | ].
    etransitivity; [ apply plus_left; apply commu_plus | ].
    auto.
  - transitivity (sem_seq l'); assumption.
Qed.

Lemma sem_seq_diamond : forall T, sem_seq (seq_diamond T) === <S> (sem_seq T).
Proof.
  induction T; try (symmetry; apply diamond_zero).
  destruct a as [r A].
  simpl.
  etransitivity ; [ | symmetry; apply diamond_linear].
  etransitivity ; [ | apply plus_left; symmetry; apply diamond_mul].
  auto.
Qed.

Lemma mul_vec_eq : forall A l r, sem_seq (vec (mul_vec r l) A) === r *S sem_seq (vec l A).
Proof.
  intros A.
  induction l; intros r.
  - simpl; symmetry; apply mul_0.
  - simpl.
    etransitivity; [ apply plus_right; apply IHl | ].
    etransitivity; [ apply plus_left; symmetry; apply mul_assoc | ].
    auto with MGA_solver.
Qed.

(** ** Interpretation of a hypersequent *)
Fixpoint sem_hseq G :=
  match G with
  | nil => MRS_zero (* should not happen *)
  | T1 :: nil => sem_seq T1
  | T1 :: G => (sem_seq T1) \/S (sem_hseq G)
  end.

(** *** Properties of this interpretation *)
Lemma sem_hseq_permutation : forall G1 G2, Permutation_Type G1 G2 -> sem_hseq G1 === sem_hseq G2.
Proof.
  intros G1 G2 Hperm; induction Hperm.
  - reflexivity.
  - destruct l; destruct l'.
    + reflexivity.
    + exfalso; apply (Permutation_Type_nil_cons Hperm).
    + apply Permutation_Type_sym in Hperm.
      exfalso; apply (Permutation_Type_nil_cons Hperm).
    + unfold sem_hseq; fold (sem_hseq (s :: l)); fold (sem_hseq (s0 :: l')).
      auto with MGA_solver.
  - destruct l.
    + simpl; apply commu_max.
    + unfold sem_hseq; fold (sem_hseq (s :: l)).
      etransitivity; [ apply asso_max | ].
      etransitivity; [ | symmetry; apply asso_max ].
      apply max_left; apply commu_max.
  - transitivity (sem_hseq l'); assumption.
Qed.
