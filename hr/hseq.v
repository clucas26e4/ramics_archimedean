(** * Definition of hypersquents and sequents *)
Require Import Rpos.
Require Import RL.Utilities.riesz_logic_Nat_more.
Require Import RL.hr.term.
Require Import RL.hr.semantic.

Require Import Lra.
Require Import Lia.
Require Import CMorphisms.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.
Require Import RL.OLlibs.wf_prod.

Local Open Scope R_scope.


(** * Definitions *)
                                                
Definition sequent : Type := list (Rpos * term).

Definition hypersequent : Type := list sequent.

(** ** Property stating whether or not a (hyper)sequent is atomic or basic *)

Definition seq_is_atomic (T : sequent) := Forall_inf (fun x => match x with (a , A) => is_atom A end) T.

Definition hseq_is_atomic G := Forall_inf seq_is_atomic G.



(** ** Complexity *)
Fixpoint HR_outer_complexity_seq (T : sequent) :=
  match T with
  | nil => 0%nat
  | (a, A) :: T => ((RS_outer_complexity_term A) + (HR_outer_complexity_seq T))%nat
  end.

(** return a couple (a,b) where a is the maximum outer complexity of a sequent of G and b is the number of sequents in G with outer complexity equal to a *)
Fixpoint HR_outer_complexity_hseq G :=
  match G with
  | nil => (0%nat, 0%nat)
  | T :: G => if HR_outer_complexity_seq T =? fst (HR_outer_complexity_hseq G) then (fst (HR_outer_complexity_hseq G), S (snd (HR_outer_complexity_hseq G)))
              else if (HR_outer_complexity_seq T <? fst (HR_outer_complexity_hseq G))%nat then (fst (HR_outer_complexity_hseq G) , snd (HR_outer_complexity_hseq G))
                   else (HR_outer_complexity_seq T, 1%nat)
  end.

(** ** Max variable appearing in a hypersequent *)
(* Fixpoint max_var_term A :=
  match A with
  | HR_var n => n
  | HR_covar n => n
  | HR_zero => 0%nat
  | A +S B => Nat.max (max_var_term A) (max_var_term B)
  | r *S A => max_var_term A
  | A /\S B => Nat.max (max_var_term A) (max_var_term B)
  | A \/S B => Nat.max (max_var_term A) (max_var_term B)
  | HR_one => 0%nat
  | HR_coone => 0%nat
  | <S> A => max_var_term A
  end. 

Fixpoint max_var_seq (T : sequent) :=
  match T with
  | nil => 0%nat
  | (r, A) :: T => Nat.max (max_var_term A) (max_var_seq T)
  end.

Fixpoint max_var_hseq G :=
  match G with
  | nil => 0%nat
  | T :: G => Nat.max (max_var_seq T) (max_var_hseq G)
  end. *)

(** ** Substitution *)
Fixpoint subs_seq (D : sequent) n t :=
  match D with
  | nil => nil
  | (r, A) :: D => (r , subs A n t) :: (subs_seq D n t)
  end.

(** ** Definitions \vec{r}.A and HR_variants *)
(** return the list \vec{l}.A *)
Fixpoint vec (l : list Rpos) (A : term) :=
  match l with
  | nil => nil
  | r :: l => (r , A) :: (vec l A)
  end.

(** return \sum\vec{l} *)
Fixpoint sum_vec (l : list Rpos) :=
  match l with
  | nil => 0%R
  | r :: l => Rplus (projT1 r) (sum_vec l)
  end.

(** return the list T,...,T n-times *)
Fixpoint copy_seq n (T : sequent) :=
  match n with
  | 0 => nil
  | S n => (copy_seq n T) ++ T
  end.

(** return the vector (r\vec{l]) *)
Fixpoint mul_vec r (l : list Rpos) :=
  match l with
  | nil => nil
  | r0 :: l => (time_pos r r0) :: (mul_vec r l)
  end.

(** return the vector (\vec{l1}\vec{l2}) *)
Fixpoint vec_mul_vec l1 l2 :=
  match l1 with
  | nil => nil
  | r :: l1 => (mul_vec r l2) ++ (vec_mul_vec l1 l2)
  end.

(** return the list r.T *)
Fixpoint seq_mul (r : Rpos) (T : sequent) :=
  match T with
  | nil => nil
  | ((a , A) :: T) => (time_pos r a, A) :: (seq_mul r T)
  end.

(** return the list \vec{vr}.T *)
Fixpoint seq_mul_vec vr T :=
  match vr with
  | nil => nil
  | r :: vr => (seq_mul r T) ++ (seq_mul_vec vr T)
  end.

(** ** Sum of the weights of the atoms *)
(** sum_weight_seq_var n T return the sum of the weights of the formula (HR_var n) and (HR_covar n) that appears in the sequent T. *)
Fixpoint sum_weight_var_seq n (T : sequent) :=
  match T with
  | nil => 0
  | ((r , RS_var n0) :: T) => if term.V_eq n n0 then (projT1 r) + sum_weight_var_seq n T else sum_weight_var_seq n T
  | ((r , RS_covar n0) :: T) => if term.V_eq n n0 then (- projT1 r) + sum_weight_var_seq n T else sum_weight_var_seq n T
  | ( _ :: T) => sum_weight_var_seq n T
  end.

(** sum_weight_var n G return the sum of the weights of the formula (RS_var n) that appears in the hypersequent G. *)
Fixpoint sum_weight_var n G :=
  match G with
  | nil => 0
  | T :: G => sum_weight_var_seq n T + sum_weight_var n G
  end.

(** * Lemmas *)
(** ** vec *)
Lemma sum_vec_le_0 : forall r, (0 <= sum_vec r)%R.
  induction r; [ | destruct a as [a Ha]; simpl;  apply (R_blt_lt 0 a) in Ha]; simpl; try nra.
Qed.
    
Lemma sum_vec_non_nil : forall r, r <> nil -> (0 <? sum_vec r)%R = true.
  induction r; intros Hnnil; [auto | ].
  simpl.
  apply R_blt_lt.
  destruct a as [a Ha].
  clear Hnnil; simpl.
  apply R_blt_lt in Ha.
  assert (Hle := (sum_vec_le_0 r)).
  nra.
Qed.

Lemma vec_app : forall vr1 vr2 A, vec (vr1 ++ vr2) A = vec vr1 A ++ vec vr2 A.
Proof.
  induction vr1; intros vr2 A; simpl; try rewrite IHvr1; try reflexivity.
Qed.

Lemma sum_vec_app : forall vr1 vr2, sum_vec (vr1 ++ vr2) = (sum_vec vr1) + (sum_vec vr2).
Proof.
  induction vr1; intros vr2.
  - rewrite app_nil_l; simpl; nra.
  - simpl.
    rewrite IHvr1.
    destruct a; simpl; nra.
Qed.

Lemma mul_vec_sum_vec : forall r vr, sum_vec (mul_vec r vr) = (projT1 r) * (sum_vec vr).
Proof.
  intro r; induction vr.
  - simpl; nra.
  - simpl.
    rewrite IHvr.
    destruct r; destruct a; simpl; nra.
Qed.

Lemma sum_vec_vec_mul_vec : forall vr vs, sum_vec (vec_mul_vec vr vs) = (sum_vec vr) * (sum_vec vs).
Proof.
  induction vr; intro vs.
  - simpl; nra.
  - unfold vec_mul_vec; fold vec_mul_vec.
    unfold sum_vec; fold sum_vec.
    rewrite sum_vec_app.
    rewrite mul_vec_sum_vec.
    rewrite IHvr.
    destruct a;  simpl; nra.
Qed.

Lemma vec_mul_vec_nil_r : forall vr, vec_mul_vec vr nil = nil.
Proof with try reflexivity.
  induction vr...
  simpl; rewrite IHvr...
Qed.

Lemma vec_mul_vec_cons_r : forall vr1 vr2 r, Permutation_Type (vec_mul_vec vr1 (r :: vr2)) (mul_vec r vr1 ++ vec_mul_vec vr1 vr2).
Proof.
  induction vr1; intros vr2 r; simpl; try reflexivity.
  replace (time_pos a r) with (time_pos r a) by (clear; destruct r; destruct a; apply Rpos_eq; simpl; nra).
  apply Permutation_Type_skip.
  rewrite app_assoc.
  etransitivity ; [ | apply Permutation_Type_app ; [ apply Permutation_Type_app_comm | reflexivity ] ].
  rewrite <- app_assoc; apply Permutation_Type_app; try reflexivity.
  apply IHvr1.
Qed.

Lemma vec_mul_vec_comm : forall vr1 vr2, Permutation_Type (vec_mul_vec vr1 vr2) (vec_mul_vec vr2 vr1).
Proof.
  induction vr1; intros vr2.
  - simpl; rewrite vec_mul_vec_nil_r; reflexivity.
  - simpl.
    etransitivity ; [ | symmetry; apply vec_mul_vec_cons_r ].
    apply Permutation_Type_app; try reflexivity.
    apply IHvr1.
Qed.

Lemma mul_vec_app : forall vr vs r, mul_vec r (vr ++ vs) = mul_vec r vr ++ mul_vec r vs.
Proof.
  induction vr; intros vs r; simpl; try rewrite IHvr; try reflexivity.
Qed.

Lemma mul_vec_perm : forall vr vs r, Permutation_Type vr vs ->  Permutation_Type (mul_vec r vr) (mul_vec r vs).
Proof.
  intros vr vs r Hperm; induction Hperm; try now constructor.
  transitivity (mul_vec r l'); try assumption.
Qed.

Lemma mul_vec_mul_vec_comm : forall vr r s, mul_vec r (mul_vec s vr) = mul_vec s (mul_vec r vr).
Proof.
  induction vr; intros r s; simpl; try rewrite IHvr; try reflexivity.
  replace (time_pos r (time_pos s a)) with (time_pos s (time_pos r a)); try reflexivity.
  destruct s; destruct r; destruct a; apply Rpos_eq; simpl; nra.
Qed.

Lemma vec_mul_vec_mul_vec_comm : forall vr vs r, vec_mul_vec vr (mul_vec r vs) =  mul_vec r (vec_mul_vec vr vs).
Proof.
  induction vr; intros vs r; try reflexivity.
  simpl.
  rewrite mul_vec_app.
  rewrite IHvr.
  rewrite mul_vec_mul_vec_comm.
  reflexivity.
Qed.

Lemma vec_perm : forall vr1 vr2 A,
    Permutation_Type vr1 vr2 -> Permutation_Type (vec vr1 A) (vec vr2 A).
Proof.
  intros vr1 vr2 A Hperm; induction Hperm; try now constructor.
  transitivity (vec l' A); try assumption.
Qed.

Lemma sum_mul_vec : forall l r, sum_vec (mul_vec r l) =  Rmult (projT1 r) (sum_vec l).
Proof.
  induction l; intros [r Hr].
  - simpl; nra.
  - remember (existT (fun r0 : R => (0 <? r0)%R = true) r Hr) as t.
    unfold mul_vec; fold (mul_vec t l).
    unfold sum_vec; fold (sum_vec (mul_vec t l)); fold (sum_vec l).
    rewrite IHl.
    rewrite Heqt.
    destruct a.
    simpl.
    nra.
Qed.

Lemma sum_vec_perm : forall vr vs,
    Permutation_Type vr vs ->
    sum_vec vr = sum_vec vs.
Proof.
  intros vr vs Hperm; induction Hperm; simpl; nra.
Qed.

Lemma mul_vec_length : forall r vr,
    length (mul_vec r vr) = length vr.
Proof.
  intros r; induction vr; simpl; try rewrite IHvr; reflexivity.
Qed.

Lemma perm_decomp_vec_eq_2 : forall T D r s r' s' A B,
    A <> B ->
    Permutation_Type (vec s' B ++ vec r' A ++ T) (vec s B ++ vec r A ++ D) ->
    {' (a1 , b1 , c1, a2 , b2, c2, T', D') : _ &
                     prod (Permutation_Type r  (a1 ++ b1))
                          ((Permutation_Type r'  (b1 ++ c1)) *
                           (Permutation_Type s  (a2 ++ b2)) *
                           (Permutation_Type s'  (b2 ++ c2)) *
                           (Permutation_Type T (vec a2 B ++ vec a1 A ++ T')) *
                           (Permutation_Type D (vec c2 B ++ vec c1 A ++ D')) *
                           (Permutation_Type T' D')) }.
Proof.
  intros T D r s r' s' A B Hneq Hperm.
  revert s r' r T D A B Hneq Hperm.
  induction s'; [ intros s ; induction s ; [ intros r'; induction r'; [ intros r; induction r | ] | ] | ].
  - intros T D A B Hneq Hperm.
    split with (nil, nil,nil,nil,nil,nil , T , D).
    repeat split; try Permutation_Type_solve.
  - intros T D A B Hneq Hperm.
    simpl in *.
    destruct (in_inf_split (a , A) T) as [[T1 T2] HeqT].
    { apply Permutation_Type_in_inf with ((a , A) :: vec r A ++ D); try Permutation_Type_solve.
      left; reflexivity. }
    subst.
    destruct (IHr (T1 ++ T2) D A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
    { apply Permutation_Type_cons_inv with (a , A).
      Permutation_Type_solve. }
    split with ((a :: a1), b1,c1,a2,b2,c2, T' , D').
    repeat split; try Permutation_Type_solve.
  - intros r T D A B Hneq Hperm; simpl in *.
    case (in_inf_app_or (vec r A) D (a , A)).
    { apply Permutation_Type_in_inf with ((a , A) :: vec r' A ++ T); try Permutation_Type_solve.
      left; reflexivity. }
    + intros Hin.
      assert { r' & Permutation_Type r (a :: r')}.
      { clear - Hin.
        induction r.
        - inversion Hin.
        - simpl in Hin.
          destruct Hin as [Heq | Hin].
          + inversion Heq; split with r; simpl; reflexivity.
          + specialize (IHr Hin) as [r' Hperm].
            split with (a0 :: r').
            Permutation_Type_solve. }
      destruct X as [vr Hperm'].
      destruct (IHr' vr T D A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
      { apply Permutation_Type_cons_inv with (a , A).
        change ((a , A) :: vec vr A ++ D) with (vec (a :: vr) A ++ D).
        etransitivity ; [ apply Hperm | ].
        apply Permutation_Type_app; [ apply vec_perm | ]; Permutation_Type_solve. }
      split with (a1, a :: b1, c1, a2, b2, c2, T', D').
      repeat split; simpl; try Permutation_Type_solve.
    + intros Hin.
      apply in_inf_split in Hin as [[D1 D2] HeqD]; subst.
      destruct (IHr' r T (D1 ++ D2) A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
      { apply Permutation_Type_cons_inv with (a,  A).
        Permutation_Type_solve. }
      split with (a1, b1, a :: c1 , a2, b2, c2, T', D').
      simpl; repeat split; try Permutation_Type_solve.
  - intros r' r T D A B Hneq Hperm; simpl in *.
    assert (In_inf (a , B) T).
    { case (in_inf_app_or (vec r' A) T (a , B)); try (intro H; assumption).
      { apply Permutation_Type_in_inf with ((a, B) :: vec s B ++ vec r A ++ D); try Permutation_Type_solve.
        left; reflexivity. }
      intro H; exfalso; clear - H Hneq.
      induction r'; simpl in H; inversion H.
      + inversion H0; subst; now apply Hneq.
      + apply IHr'; try assumption. }
    apply in_inf_split in X as [[T1 T2] Heq]; subst.
    destruct (IHs r' r (T1 ++ T2) D A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
    { apply Permutation_Type_cons_inv with (a , B).
      Permutation_Type_solve. }
    split with (a1, b1,c1,a :: a2,b2,c2, T' , D').
    repeat split; try Permutation_Type_solve.
  - intros s r' r T D A B Hneq Hperm; simpl in *.
    case (in_inf_app_or (vec s B) (vec r A ++ D) (a , B)).
    { apply Permutation_Type_in_inf with ((a, B) :: vec s' B ++ vec r' A ++ T); try Permutation_Type_solve.
      left; reflexivity. }
    + intros Hin.
      assert { s' & Permutation_Type s (a :: s')}.
      { clear - Hin.
        induction s.
        - inversion Hin.
        - simpl in Hin.
          destruct Hin as [Heq | Hin].
          + inversion Heq; split with s; simpl; reflexivity.
          + specialize (IHs Hin) as [s' Hperm].
            split with (a0 :: s').
            Permutation_Type_solve. }
      destruct X as [vs Hperm'].
      destruct (IHs' vs r' r T D A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
      { apply Permutation_Type_cons_inv with (a , B).
        change ((a , B) :: vec vs B ++ vec r A ++  D) with (vec (a :: vs) B ++ vec r A ++ D).
        etransitivity ; [ apply Hperm | ].
        apply Permutation_Type_app; [ apply vec_perm | ]; Permutation_Type_solve. }
      split with (a1, b1, c1, a2, a::b2, c2, T', D').
      repeat split; simpl; try Permutation_Type_solve.
    + intros H.
      assert (In_inf (a , B) D) as Hin; [ | clear H].
      { case (in_inf_app_or (vec r A) D (a , B)); [ apply H | | ]; try (intros H0; assumption).
        intro H0; exfalso; clear - H0 Hneq.
        induction r; simpl in H0; inversion H0.
        - inversion H; subst; now apply Hneq.
        - apply IHr; try assumption. }
      apply in_inf_split in Hin as [[D1 D2] HeqD]; subst.
      destruct (IHs' s r' r T (D1 ++ D2) A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
      { apply Permutation_Type_cons_inv with (a,  B).
        Permutation_Type_solve. }
      split with (a1, b1, c1 , a2, b2, a :: c2, T', D').
      simpl; repeat split; try Permutation_Type_solve.
Qed.

Lemma perm_decomp_vec_neq_2 : forall T D r s r' s' n1 n2,
    n1 <> n2 ->
    Permutation_Type (vec s (RS_covar n1) ++ vec r (RS_var n1) ++ T) (vec s' (RS_covar n2) ++ vec r' (RS_var n2) ++ D) ->
    {' (T', D') : _ &
                          prod (Permutation_Type T (vec s' (RS_covar n2) ++ vec r' (RS_var n2) ++ T'))
                               ((Permutation_Type D (vec s (RS_covar n1) ++ vec r (RS_var n1) ++ D')) *
                                (Permutation_Type T' D'))}.
Proof.
  intros T D r s r' s'.
  revert s r' r T D.
  induction s'; [ intros s ; induction s ; [ intros r' ; induction r' ; [ intros r; induction r | ] | ] | ].
  - intros T D n1 n2 Hneq Hperm.
    split with (T , D).
    simpl in *; repeat split; Permutation_Type_solve.
  - intros T D n1 n2 Hneq Hperm.
    simpl in *.
    destruct (in_inf_split (a , RS_var n1) D) as [[D1 D2] Heq].
    { apply Permutation_Type_in_inf with ((a, RS_var n1) :: vec r (RS_var n1) ++ T); try Permutation_Type_solve.
      left; reflexivity. }
    subst.
    destruct (IHr T (D1 ++ D2) n1 n2 Hneq) as [[T' D'] [H1' [H2' H3']]].
    { apply Permutation_Type_cons_inv with (a , RS_var n1).
      Permutation_Type_solve. }
    split with (T', D').
    repeat split; try Permutation_Type_solve.
  - intros r T D n1 n2 Hneq Hperm.
    simpl in *.
    destruct (in_inf_split (a , RS_var n2) T) as [[T1 T2] Heq].
    { case (in_inf_app_or (vec r (RS_var n1)) T (a , RS_var n2)) ; [ apply Permutation_Type_in_inf with ((a, RS_var n2) :: vec r' (RS_var n2) ++ D); [ Permutation_Type_solve | left; reflexivity ] | | auto ].
      intros H; clear - H Hneq.
      exfalso.
      induction r; simpl in H; inversion H.
      - inversion H0.
        apply Hneq; apply H3.
      - apply IHr; apply X. }
    subst.
    destruct (IHr' r (T1 ++ T2) D n1 n2 Hneq) as [[T' D'] [H1' [H2' H3']]].
    { apply Permutation_Type_cons_inv with (a , RS_var n2); Permutation_Type_solve. }
    split with (T', D').
    repeat split; try Permutation_Type_solve.
  - intros r' r T D n1 n2 Hneq Hperm.
    simpl in *.
    destruct (in_inf_split (a , RS_covar n1) D) as [[D1 D2] Heq].
    { case (in_inf_app_or (vec r' (RS_var n2)) D (a , RS_covar n1)) ; [ apply Permutation_Type_in_inf with ((a, RS_covar n1) :: vec s (RS_covar n1) ++ vec r (RS_var n1) ++ T); [ Permutation_Type_solve | left; reflexivity ] | | auto ].
      intros H; clear - H Hneq.
      exfalso.
      induction r'; simpl in H; inversion H.
      - inversion H0.
      - apply IHr'; apply X. }
    subst.
    destruct (IHs r' r T (D1 ++ D2) n1 n2 Hneq) as [[T' D'] [H1' [H2' H3']]].
    { apply Permutation_Type_cons_inv with (a , RS_covar n1); Permutation_Type_solve. }
    split with (T', D').
    repeat split; try Permutation_Type_solve.
  - intros s r' r T D n1 n2 Hneq Hperm.
    simpl in *.
    destruct (in_inf_split (a , RS_covar n2) T) as [[T1 T2] Heq].
    { case (in_inf_app_or (vec s (RS_covar n1)) (vec r (RS_var n1) ++ T) (a , RS_covar n2)) ; [ apply Permutation_Type_in_inf with ((a, RS_covar n2) :: vec s' (RS_covar n2) ++ vec r' (RS_var n2) ++ D); [ Permutation_Type_solve | left; reflexivity ] | | ].
      - intros H; clear - H Hneq.
        exfalso.
        induction s; simpl in H; inversion H.
        + inversion H0.
          apply Hneq; apply H3.
        + apply IHs; apply X.
      - intro H0 ;case (in_inf_app_or (vec r (RS_var n1)) T (a , RS_covar n2)) ; [ apply H0 | | auto ].
        intros H; clear - H Hneq.
        exfalso.
        induction r; simpl in H; inversion H.
        + inversion H0.
        + apply IHr; apply X. }
    subst.
    destruct (IHs' s r' r (T1 ++ T2) D n1 n2 Hneq) as [[T' D'] [H1' [H2' H3']]].
    { apply Permutation_Type_cons_inv with (a , RS_covar n2); Permutation_Type_solve. }
    split with (T', D').
    repeat split; try Permutation_Type_solve.
Qed.

(** ** Sequent *)

Lemma seq_mul_One : forall T, seq_mul One T = T.
  induction T; try reflexivity.
  destruct a as (a , A).
  unfold seq_mul; fold seq_mul.
  replace (time_pos One a) with a by (apply Rpos_eq; destruct a; simpl; nra).
  rewrite IHT; reflexivity.
Qed.
  
Lemma seq_mul_app : forall T1 T2 r, seq_mul r (T1 ++ T2) = seq_mul r T1 ++ seq_mul r T2.
Proof.
  induction T1; intros T2 r; try reflexivity.
  destruct a as (a , A).
  simpl; rewrite IHT1.
  reflexivity.
Qed.

Lemma seq_mul_twice : forall T r1 r2,
    seq_mul r1 (seq_mul r2 T) = seq_mul (time_pos r1 r2) T.
Proof.
  induction T as [ | [a A] T]; intros r1 r2; simpl; try reflexivity.
  rewrite IHT.
  replace (time_pos r1 (time_pos r2 a)) with (time_pos (time_pos r1 r2) a) by (apply Rpos_eq;destruct r1; destruct r2; destruct a; simpl; nra).
  reflexivity.
Qed.

Lemma seq_mul_vec_nil_r : forall vr,
    seq_mul_vec vr nil = nil.
Proof.
  induction vr; simpl; try rewrite IHvr; reflexivity.
Qed.

Lemma seq_mul_vec_app_l : forall T vr1 vr2,
    seq_mul_vec (vr1 ++ vr2) T = seq_mul_vec vr1 T ++ seq_mul_vec vr2 T.
Proof.
  intros T; induction vr1; intros vr2; try reflexivity.
  simpl.
  rewrite IHvr1.
  rewrite app_assoc; reflexivity.
Qed.

Lemma seq_mul_vec_app_r : forall T1 T2 vr,
    Permutation_Type (seq_mul_vec vr (T1 ++ T2)) (seq_mul_vec vr T1 ++ seq_mul_vec vr T2).
Proof.
  intros T1 T2; induction vr; try reflexivity.
  simpl.
  rewrite seq_mul_app.
  Permutation_Type_solve.
Qed.


Lemma seq_mul_vec_perm_r : forall vr T1 T2,
    Permutation_Type T1 T2 ->
    Permutation_Type (seq_mul_vec vr T1) (seq_mul_vec vr T2).
Proof.
  intros vr T1 T2 Hperm; induction Hperm; try Permutation_Type_solve.
  - rewrite cons_is_app.
    etransitivity ; [ apply seq_mul_vec_app_r | ].
    rewrite (cons_is_app _ l').
    etransitivity ; [ | symmetry; apply seq_mul_vec_app_r].
    Permutation_Type_solve.
  - rewrite (cons_is_app _ (x :: l)).
    etransitivity ; [ apply seq_mul_vec_app_r | ].
    rewrite (cons_is_app _ l).
    etransitivity ; [ apply Permutation_Type_app; try apply seq_mul_vec_app_r; reflexivity | ].
    rewrite (cons_is_app _ (y :: l)).
    etransitivity ; [ | symmetry ; apply seq_mul_vec_app_r ].
    rewrite (cons_is_app _ l).
    etransitivity ; [ | symmetry; apply Permutation_Type_app; try apply seq_mul_vec_app_r; reflexivity ].
    Permutation_Type_solve.
Qed.

Lemma seq_mul_vec_perm_l : forall vr1 vr2 T,
    Permutation_Type vr1 vr2 ->
    Permutation_Type (seq_mul_vec vr1 T) (seq_mul_vec vr2 T).
Proof.
  intros vr1 vr2 T Hperm; induction Hperm; try Permutation_Type_solve.
Qed.
    
Lemma seq_mul_seq_mul_vec: forall T vr r,
    seq_mul r (seq_mul_vec vr T) = seq_mul_vec vr (seq_mul r T).
Proof.
  intros T vr; revert T; induction vr; intros T r; try reflexivity.
  simpl. rewrite seq_mul_app; rewrite IHvr; rewrite 2 seq_mul_twice.
  replace (time_pos r a) with (time_pos a r) by (apply Rpos_eq; destruct r; destruct a; simpl; nra).
  reflexivity.
Qed.

Lemma seq_mul_seq_mul_vec_2: forall T vr r,
    seq_mul r (seq_mul_vec vr T) = seq_mul_vec (mul_vec r vr) T.
Proof.
  intros T vr; revert T; induction vr; intros T r; try reflexivity.
  simpl. rewrite seq_mul_app; rewrite IHvr; rewrite seq_mul_twice.
  reflexivity.
Qed.
  
Lemma seq_mul_vec_twice : forall T vr1 vr2,
    Permutation_Type (seq_mul_vec vr1 (seq_mul_vec vr2 T)) (seq_mul_vec (vec_mul_vec vr1 vr2) T).
Proof.
  intros T vr1; revert T; induction vr1; intros T vr2; try reflexivity.
  simpl.
  rewrite seq_mul_seq_mul_vec_2; rewrite seq_mul_vec_app_l.
  specialize (IHvr1 T vr2).
  Permutation_Type_solve.
Qed.

Lemma seq_mul_vec_twice_comm : forall T vr1 vr2,
    Permutation_Type (seq_mul_vec vr1 (seq_mul_vec vr2 T)) (seq_mul_vec vr2 (seq_mul_vec vr1 T)).
Proof.
  intros T vr1; revert T; induction vr1; intros T vr2.
  - simpl; rewrite seq_mul_vec_nil_r.
    reflexivity.
  -  simpl.
     etransitivity ; [ | symmetry; apply seq_mul_vec_app_r].
     apply Permutation_Type_app.
     + rewrite seq_mul_seq_mul_vec.
       reflexivity.
     + apply IHvr1.
Qed.

Lemma seq_mul_vec_vec : forall A vr1 vr2,
    Permutation_Type (seq_mul_vec vr1 (vec vr2 A)) (seq_mul_vec vr2 (vec vr1 A)).
Proof.
  intros A vr1; revert A; induction vr1; intros A vr2.
  - simpl; rewrite seq_mul_vec_nil_r.
    reflexivity.
  -  simpl.
     change ((a, A) :: vec vr1 A) with ((vec (a :: nil) A) ++ vec vr1 A).
     etransitivity ; [ | symmetry; apply seq_mul_vec_app_r].
     apply Permutation_Type_app.
     + clear.
       induction vr2; simpl; try reflexivity.
       replace (time_pos a a0) with (time_pos a0 a) by (apply Rpos_eq; destruct a; destruct a0; simpl; nra).
       apply Permutation_Type_skip.
       apply IHvr2.
     + apply IHvr1.
Qed.

Lemma seq_mul_vec_mul_vec : forall A r vr,
    seq_mul r (vec vr A) = vec (mul_vec r vr) A.
Proof.
  intros A r vr; induction vr; simpl; try rewrite IHvr; try reflexivity.
Qed.

Lemma seq_mul_vec_vec_mul_vec : forall vr vs A,
    seq_mul_vec vr (vec vs A) = vec (vec_mul_vec vr vs) A.
Proof.
  induction vr; intros vs A.
  - reflexivity.
  - simpl.
    rewrite vec_app.
    rewrite IHvr.
    rewrite seq_mul_vec_mul_vec.
    reflexivity.
Qed.
    
Lemma seq_mul_perm : forall T1 T2 r,
    Permutation_Type T1 T2 ->
    Permutation_Type (seq_mul r T1) (seq_mul r T2).
Proof.
  intros T1 T2 r Hperm; induction Hperm; try destruct x; try destruct y; try now constructor.
  transitivity (seq_mul r l'); assumption.
Qed.

Lemma copy_seq_plus : forall T n1 n2, copy_seq (n1 + n2) T = copy_seq n1 T ++ copy_seq n2 T.
Proof.
  intros T; intros n1; induction n2; simpl.
  - rewrite app_nil_r; rewrite Nat.add_0_r; reflexivity.
  - rewrite Nat.add_succ_r; simpl.
    rewrite IHn2.
    rewrite app_assoc; reflexivity.
Qed.

Lemma copy_seq_perm : forall T1 T2 n,
    Permutation_Type T1 T2 ->
    Permutation_Type (copy_seq n T1) (copy_seq n T2).
Proof.
  intros T1 T2; induction n; try reflexivity.
  intros Hperm.
  simpl; specialize (IHn Hperm).
  apply Permutation_Type_app; assumption.
Qed.

Lemma copy_seq_app : forall T1 T2 n,
    Permutation_Type (copy_seq n (T1 ++ T2)) (copy_seq n T1 ++ copy_seq n T2).
Proof.
  intros T1 T2; induction n; simpl; Permutation_Type_solve.
Qed.

Lemma copy_seq_nil : forall n, copy_seq n nil = nil.
Proof.
  induction n; simpl; try rewrite IHn; reflexivity.
Qed.

Lemma copy_seq_twice : forall T n1 n2, copy_seq n1 (copy_seq n2 T) = copy_seq (n1 * n2) T.
Proof.
  intros T; induction n1; intros n2; try reflexivity.
  simpl.
  rewrite IHn1; rewrite <- copy_seq_plus.
  rewrite Nat.add_comm.
  reflexivity.
Qed.

(** ** Substitution *)

Lemma subs_seq_app : forall D D' n t, subs_seq (D ++ D') n t = subs_seq D n t ++ subs_seq D' n t.
Proof.
  induction D; intros D' n t; simpl; try rewrite IHD; try destruct a; try reflexivity.
Qed.

Lemma subs_seq_vec : forall D n t A r, subs_seq ((vec r A) ++ D) n t = vec r (subs A n t) ++ subs_seq D n t.
Proof.
  intros D n t A; induction r;simpl; try rewrite IHr; try reflexivity.
Qed.

Lemma subs_seq_ex : forall T1 T2 n t, Permutation_Type T1 T2 -> Permutation_Type (subs_seq T1 n t) (subs_seq T2 n t).
Proof.
  intros T1 T2 n t Hperm; induction Hperm; try destruct x; try destruct y; simpl; try now constructor.
  transitivity (subs_seq l' n t); assumption.
Qed.

Fixpoint subs_hseq (G : hypersequent) n t :=
  match G with
  | nil => nil
  | D :: G => (subs_seq D n t) :: (subs_hseq G n t)
  end.

Lemma subs_hseq_ex : forall G1 G2 n t, Permutation_Type G1 G2 -> Permutation_Type (subs_hseq G1 n t) (subs_hseq G2 n t).
Proof.
  intros G1 G2 n t Hperm; induction Hperm; try destruct x; try destruct y; simpl; try now constructor.
  transitivity (subs_hseq l' n t); assumption.
Qed.

(** ** sum_weight_seq_(co)var *)
(*
Lemma sum_weight_var_seq_lt_max_var : forall n T1,
    (max_var_seq T1 < n)%nat ->
    sum_weight_var_seq n T1 = 0.
Proof.
  intros n; induction T1; intros Hlt; auto.
  destruct a as [a A].
  destruct A; simpl in *; try (apply IHT1 ; lia);
    replace (n =? n0) with false by (symmetry; apply Nat.eqb_neq; lia);
    apply IHT1;
    lia.
Qed. *)

Lemma sum_weight_var_seq_app : forall n T1 T2,
    sum_weight_var_seq n (T1 ++ T2) = sum_weight_var_seq n T1 + sum_weight_var_seq n T2.
Proof.
  intros n T1; induction T1; intros T2; simpl; try nra.
  destruct a as [a A]; simpl.
  specialize (IHT1 T2).
  destruct A; try case (term.V_eq n v); simpl; try nra.
Qed.

Lemma sum_weight_var_seq_mul : forall n T r,
    sum_weight_var_seq n (seq_mul r T) = (projT1 r) * sum_weight_var_seq n T.
Proof.
  intros n T r; induction T; simpl; try nra.
  destruct a as [a A]; simpl.
  destruct A; try case (term.V_eq n v); destruct a; destruct r; simpl in *; try nra.
Qed.

Lemma sum_weight_var_seq_copy : forall n T r,
    sum_weight_var_seq n (copy_seq r T) = (INR r) * sum_weight_var_seq n T.
Proof.
  intros n T r; induction r; simpl in *; try nra.
  rewrite sum_weight_var_seq_app; rewrite IHr.
  change (match r with
          | 0%nat => 1
          | S _ => INR r + 1
          end) with (INR (S r)).
  rewrite S_INR; nra.
Qed.

Lemma sum_weight_var_seq_vec_var_eq : forall n r,
    sum_weight_var_seq n (vec r (RS_var n)) = sum_vec r.
Proof.
  intros n; induction r; simpl; try reflexivity.
  case (term.V_eq n n); intros H; [ rewrite IHr; reflexivity | ].
  exfalso; apply H; reflexivity.
Qed.

Lemma sum_weight_var_seq_vec_covar_eq : forall n r,
    sum_weight_var_seq n (vec r (RS_covar n)) = - sum_vec r.
Proof.
  intros n; induction r; simpl; try lra.
  case (term.V_eq n n); intros H; [ rewrite IHr; lra | ].
  exfalso; apply H; reflexivity.
Qed.

Lemma sum_weight_var_seq_vec_neq : forall n A r,
    RS_var n <> A ->
    RS_covar n <> A ->
    sum_weight_var_seq n (vec r A) = 0.
Proof.
  intros n A; induction r; intros Hneqv Hneqcv; simpl; try reflexivity.
  destruct A; try (case (term.V_eq n v) ; [ intros H; exfalso; now subst | ]); auto.
Qed.

Lemma sum_weight_var_seq_perm : forall n T1 T2,
    Permutation_Type T1 T2 ->
    sum_weight_var_seq n T1 = sum_weight_var_seq n T2.
Proof.
  intros n T1 T2 Hperm; induction Hperm; simpl; try destruct x as [a A]; try destruct y as [b B]; try destruct A; try destruct B; try case (term.V_eq n v); try case (term.V_eq n v0); try nra.
Qed.

(*
Lemma sum_weight_var_lt_max_var : forall n G,
    (max_var_hseq G < n)%nat ->
    sum_weight_var n G = 0.
Proof.
  intros n; induction G; intros Hlt; auto.
  simpl in *.
  rewrite IHG; try lia.
  rewrite sum_weight_var_seq_lt_max_var; try lia.
  lra.
Qed. *)

Lemma sum_weight_var_perm : forall n G H,
    Permutation_Type G H ->
    sum_weight_var n G = sum_weight_var n H.
Proof.
  intros n G H Hperm; induction Hperm; simpl; nra.
Qed.

Lemma seq_decomp_atomic :
  forall T n,
    {' (r,s,D) : _ &
                    prod (sum_vec r - sum_vec s = sum_weight_var_seq n T)
                         (Permutation_Type T (vec s (RS_covar n) ++ vec r (RS_var n) ++ D)) }.
Proof.
  induction T; intros n.
  - split with (nil, nil, nil).
    repeat split; simpl; try reflexivity + lra.
  - destruct (IHT n) as [[[r s] D] [Hsum Hperm]].
    destruct a as [a A].
    destruct A; try (esplit with (r , s, (a , _) :: D); repeat split; try assumption;
                     rewrite ? app_assoc; etransitivity ; [ | apply Permutation_Type_middle]; apply Permutation_Type_skip; rewrite <- app_assoc; now apply Hperm).
    + case_eq (term.V_eq n v); intros Heq He.
      * split with (a :: r, s, D).
        repeat split.
        -- simpl; rewrite <- Hsum.
           rewrite He; lra.
        -- simpl; subst.
           Permutation_Type_solve.
      * split with (r , s , (a, RS_var v) :: D).
        repeat split.
        -- simpl; rewrite Hsum.
           rewrite He; lra.
        -- simpl; Permutation_Type_solve.
    + case_eq (term.V_eq n v); intros Heq He.
      * split with (r, a :: s, D).
        repeat split.
        -- simpl; rewrite <- Hsum.
           rewrite He; lra.
        -- simpl; subst.
           Permutation_Type_solve.
      * split with (r , s , (a, RS_covar v) :: D).
        repeat split.
        -- simpl; rewrite Hsum.
           rewrite He; reflexivity.
        -- simpl; Permutation_Type_solve.
Qed.

Lemma sum_weight_var_seq_no_atom : forall T n,
    ((In_inf (RS_var n) (map snd T) + In_inf (RS_covar n) (map snd T)) -> False) ->
    sum_weight_var_seq n T = 0.
Proof.
  induction T; intros n H; [reflexivity | ].
  destruct a as [r A]; simpl.
  assert ((In_inf (RS_var n) (map snd T) + In_inf (RS_covar n) (map snd T)) -> False).
  { intros H'; apply H.
    inversion H'; [left; right | right; right]; assumption. }
  specialize (IHT n H0).
  rewrite IHT.
  destruct A; simpl; try reflexivity;
    case_eq (term.V_eq n v); intros Heq He; try reflexivity;
      exfalso; subst;
        apply H; [left | right];
          left; reflexivity.
Qed.
           
Lemma seq_atomic_decomp_decr :
  forall T,
    seq_is_atomic T ->
    {' (n, r,s,D) : _ &
                    prod (sum_vec r - sum_vec s = sum_weight_var_seq n T)
                         ((Permutation_Type T (vec s (RS_covar n) ++ vec r (RS_var n) ++ D)) *
                          ((length D < length T)%nat)) } + { forall n, (In_inf (RS_var n) (map snd T) + In_inf (RS_covar n) (map snd T)) -> False }.
Proof.
  induction T; intros Hat.
  - right.
    intros n.
    intros [Hin | Hin]; inversion Hin.
  - inversion Hat; subst.
    specialize (IHT X0).
    destruct a as [a A].
    destruct A; (try now inversion X); 
      destruct IHT as [[[[[nv r] s] D] H] | H].
    + left.
      clear r s D H.
      destruct (seq_decomp_atomic T v) as [[[r s] D] [Hr Hperm]].
      split with (v, a :: r, s , D).
      repeat split.
      * simpl.
        case (term.V_eq v ); intros Heq; [ | contradiction].
        rewrite<- Hr; lra.
      * Permutation_Type_solve.
      * simpl.
        apply Permutation_Type_length in Hperm.
        rewrite Hperm.
        rewrite ? app_length.
        lia.
    + left.
      split with (v, a :: nil, nil, T); specialize (H v).
      repeat split.
      * simpl.
        case (term.V_eq v v); intros Heq; [ | contradiction].
        rewrite sum_weight_var_seq_no_atom; try assumption.
        lra.
      * auto.
      * simpl; lia.
    + left.
      clear r s D H.
      destruct (seq_decomp_atomic T v) as [[[r s] D] [Hr Hperm]].
      split with (v, r, a :: s , D).
      repeat split.
      * simpl.
        case (term.V_eq v v); intros Heq; [ | contradiction].
        rewrite <- Hr; lra.
      * Permutation_Type_solve.
      * simpl.
        apply Permutation_Type_length in Hperm.
        rewrite Hperm.
        rewrite ? app_length.
        lia.
    + left.
      split with (v, nil , a :: nil, T); specialize (H v).
      repeat split.
      * simpl.
        case (term.V_eq v v); intros Heq; [ | contradiction].
        rewrite sum_weight_var_seq_no_atom; try assumption.
        lra.
      * auto.
      * simpl; lia.
Qed.

(** ** atomic *)
Lemma copy_seq_atomic : forall n T, seq_is_atomic T -> seq_is_atomic (copy_seq n T).
Proof.
  induction n; intros T Hat; simpl; [ apply Forall_inf_nil | ].
  apply Forall_inf_app; auto.
  apply IHn; assumption.
Qed.

Lemma seq_atomic_app : forall T1 T2,
    seq_is_atomic T1 ->
    seq_is_atomic T2 ->
    seq_is_atomic (T1 ++ T2).
Proof.  
  intros T1 T2 Hat1.
  induction Hat1; intros Hat2.
  - apply Hat2.
  - simpl; apply Forall_inf_cons; try assumption.
    apply IHHat1.
    apply Hat2.
Qed.

Lemma seq_atomic_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    seq_is_atomic T1 ->
    seq_is_atomic T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; intro Hat.
  - apply Forall_inf_nil.
  - inversion Hat; subst; apply Forall_inf_cons; [ | apply IHHperm]; assumption.
  - inversion Hat; inversion X0; subst.
    apply Forall_inf_cons ; [ | apply Forall_inf_cons ]; assumption.
  - apply IHHperm2; apply IHHperm1; apply Hat.
Qed.

Lemma hseq_atomic_perm : forall G H,
    Permutation_Type G H ->
    hseq_is_atomic G ->
    hseq_is_atomic H.
Proof.
  intros G H Hperm; induction Hperm; intro Hat.
  - apply Forall_inf_nil.
  - inversion Hat; subst; apply Forall_inf_cons; [ | apply IHHperm]; assumption.
  - inversion Hat; inversion X0; subst.
    apply Forall_inf_cons ; [ | apply Forall_inf_cons ]; assumption.
  - apply IHHperm2; apply IHHperm1; apply Hat.
Qed.

Lemma seq_atomic_app_inv_l : forall T1 T2,
    seq_is_atomic (T1 ++ T2) ->
    seq_is_atomic T1.
Proof.
  intros T1; induction T1; intros T2 Hat; try now constructor.
  simpl in Hat; inversion Hat; subst.
  apply Forall_inf_cons; try assumption.
  apply IHT1 with T2; apply X0.
Qed.

Lemma seq_atomic_app_inv_r : forall T1 T2,
    seq_is_atomic (T1 ++ T2) ->
    seq_is_atomic T2.
Proof.
  intros T1; induction T1; intros T2 Hat; try assumption.
  simpl in Hat; inversion Hat; subst.
  apply IHT1; assumption.
Qed.

Lemma seq_atomic_mul : forall T r,
    seq_is_atomic T ->
    seq_is_atomic (seq_mul r T).
Proof.
  intros T r Hat; induction Hat; try destruct x; simpl; try now constructor.
Qed.

(** ** Complexity *)

Lemma complexity_seq_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    HR_outer_complexity_seq T1 = HR_outer_complexity_seq T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; try destruct x; try destruct y; simpl; lia.
Qed.

Lemma complexity_hseq_perm : forall G1 G2,
    Permutation_Type G1 G2 ->
    HR_outer_complexity_hseq G1 = HR_outer_complexity_hseq G2.
Proof.
  intros G1 G2 Hperm; induction Hperm.
  - reflexivity.
  - simpl.
    rewrite IHHperm.
    case (HR_outer_complexity_seq x =? fst (HR_outer_complexity_hseq l'));
      case (HR_outer_complexity_seq x <? fst (HR_outer_complexity_hseq l'))%nat; reflexivity.
  - simpl.
    case_eq (HR_outer_complexity_seq x =? fst (HR_outer_complexity_hseq l)); intros H1;
      case_eq (HR_outer_complexity_seq y =? fst (HR_outer_complexity_hseq l)); intros H2;
        case_eq (HR_outer_complexity_seq x <? fst (HR_outer_complexity_hseq l))%nat; intros H3;
          case_eq (HR_outer_complexity_seq y <? fst (HR_outer_complexity_hseq l))%nat; intros H4;
            case_eq (HR_outer_complexity_seq x =? HR_outer_complexity_seq y); intros H5;
              case_eq (HR_outer_complexity_seq x <? HR_outer_complexity_seq y)%nat; intros H6;
                case_eq (HR_outer_complexity_seq y <? HR_outer_complexity_seq x)%nat; intros H7;
                  repeat (simpl; try rewrite H1; try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5; try (rewrite Nat.eqb_sym in H5; rewrite H5); try rewrite H6; try rewrite H7);
                  try reflexivity;
                  (apply Nat.eqb_eq in H1 + apply Nat.eqb_neq in H1);
                  (apply Nat.eqb_eq in H2 + apply Nat.eqb_neq in H2);
                  (apply Nat.ltb_lt in H3 + apply Nat.ltb_nlt in H3);
                  (apply Nat.ltb_lt in H4 + apply Nat.ltb_nlt in H4);
                  (apply Nat.eqb_eq in H5 + apply Nat.eqb_neq in H5);
                  (apply Nat.ltb_lt in H6 + apply Nat.ltb_nlt in H6);
                  (apply Nat.ltb_lt in H7 + apply Nat.ltb_nlt in H7);
                  try lia.
    rewrite H5; reflexivity.
  - transitivity (HR_outer_complexity_hseq l'); assumption.
Qed.

Lemma complexity_hseq_perm_fst : forall G,
    G <> nil ->
    {' (T, H) : _ &
                Permutation_Type G (T :: H) &
                HR_outer_complexity_seq T = fst (HR_outer_complexity_hseq G) }.
  induction G; intros H; [ exfalso; apply H; reflexivity | clear H ].
  simpl.
  case_eq (HR_outer_complexity_seq a =? fst (HR_outer_complexity_hseq G)); intros H1.
  - split with (a, G); try reflexivity.
    apply Nat.eqb_eq in H1; rewrite H1; reflexivity.
  - case_eq (HR_outer_complexity_seq a <? fst (HR_outer_complexity_hseq G))%nat; intros H2.
    + destruct G; [ inversion H2 | ].
      destruct IHG as [[T H] Hperm Heq].
      { intros H; inversion H. }
      split with (T, (a :: H)).
      * transitivity (a :: T :: H); Permutation_Type_solve.
      * rewrite (complexity_hseq_perm _ _ Hperm).
        rewrite (complexity_hseq_perm _ _ Hperm) in Heq.
        rewrite Heq; reflexivity.
    + split with (a, G); reflexivity.
Qed.

Lemma complexity_hseq_perm_fst_seq : forall T1 T2 G,
    Permutation_Type T1 T2 ->
    HR_outer_complexity_hseq (T1 :: G) = HR_outer_complexity_hseq (T2 :: G).
Proof.
  intros T1 T2 G Hperm.
  simpl.
  rewrite (complexity_seq_perm _ _ Hperm).
  reflexivity.
Qed.

Lemma complexity_seq_app : forall T1 T2,
    HR_outer_complexity_seq (T1 ++ T2) = (HR_outer_complexity_seq T1 + HR_outer_complexity_seq T2)%nat.
Proof.
  induction T1; intros T2; simpl; try rewrite IHT1; try destruct a; lia.
Qed.

Lemma complexity_seq_vec : forall r A,
    HR_outer_complexity_seq (vec r A) = (length r * RS_outer_complexity_term A)%nat.
Proof.
  induction r; intros A; simpl; try rewrite IHr; lia.
Qed.

Lemma seq_is_atomic_complexity_0 :
  forall T,
    seq_is_atomic T ->
    HR_outer_complexity_seq T = 0%nat.
Proof.
  induction T; intros Hat;
    inversion Hat; simpl; try destruct a; try rewrite IHT; try rewrite is_atom_outer_complexity_0;
      auto.
Qed.

Lemma seq_is_atomic_complexity_0_inv :
  forall T,
    HR_outer_complexity_seq T = 0%nat ->
    seq_is_atomic T.
Proof.
  induction T; intros Heq; [ apply Forall_inf_nil |] .
  destruct a as [a A]; simpl in *.
  apply Forall_inf_cons ; [ apply is_atom_outer_complexity_0_inv  | apply IHT]; lia.
Qed.

Lemma hseq_is_atomic_complexity_0 :
  forall G,
    hseq_is_atomic G ->
    fst (HR_outer_complexity_hseq G) = 0%nat.
Proof.
  induction G; intros Hat; [ reflexivity | ].
  inversion Hat; subst; specialize (IHG X0).
  simpl.
  rewrite seq_is_atomic_complexity_0 ; [ | apply X].
  rewrite IHG; reflexivity.
Qed.

Lemma hseq_is_atomic_complexity_0_inv :
  forall G,
    fst (HR_outer_complexity_hseq G) = 0%nat ->
    hseq_is_atomic G.
Proof.
  induction G; intros Heq; [ apply Forall_inf_nil | ].
  simpl in *.
  case_eq (HR_outer_complexity_seq a =? fst (HR_outer_complexity_hseq G)); intros H; rewrite H in Heq; simpl in Heq ; [ apply Nat.eqb_eq in H | apply Nat.eqb_neq in H ].
  { apply Forall_inf_cons; [ apply seq_is_atomic_complexity_0_inv | apply IHG ]; lia. }
  exfalso.
  case_eq (HR_outer_complexity_seq a <? fst (HR_outer_complexity_hseq G))%nat; intros H2; rewrite H2 in Heq; [apply Nat.ltb_lt in H2 | apply Nat.ltb_nlt in H2]; simpl in *; lia.
Qed.

Lemma complexity_seq_mul : forall T r,
    HR_outer_complexity_seq (seq_mul r T) = HR_outer_complexity_seq T.
Proof.
  induction T; intros r; simpl; try specialize (IHT r); try destruct a as [a A];simpl; try lia.
Qed.

Lemma complexity_seq_mul_nth :
  forall G v r,
    HR_outer_complexity_seq (flat_map (fun i : nat => seq_mul r (nth i G nil)) v) = HR_outer_complexity_seq (flat_map (fun i : nat => nth i G nil) v).
Proof.
  intros G; induction v; intros k; auto.
  simpl in *.
  rewrite ? complexity_seq_app; rewrite IHv.
  rewrite complexity_seq_mul.
  reflexivity.
Qed.

Lemma hrr_Z_decrease_complexity : forall G T r,
    r <> nil ->
    HR_outer_complexity_seq (vec r RS_zero ++ T) = fst (HR_outer_complexity_hseq ((vec r RS_zero ++ T) :: G)) ->
    HR_outer_complexity_hseq (T :: G) <2 HR_outer_complexity_hseq ((vec r RS_zero ++ T) :: G).
Proof.
  intros G T r Hnnil Heq.
  simpl.
  case_eq (HR_outer_complexity_seq T =? fst (HR_outer_complexity_hseq G)); intros H1; case_eq (HR_outer_complexity_seq (vec r RS_zero ++ T) =? fst (HR_outer_complexity_hseq G)); intros H2.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H2.
    rewrite complexity_seq_app in H2.
    lia.
  - case_eq (HR_outer_complexity_seq (vec r RS_zero ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_seq_app in H2; rewrite complexity_seq_app in H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_outer_complexity_seq T <? fst (HR_outer_complexity_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite complexity_seq_app in H2; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_outer_complexity_seq T <? fst (HR_outer_complexity_hseq G))%nat; intros H3;
      case_eq (HR_outer_complexity_seq (vec r RS_zero ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite complexity_seq_app in H4; lia.
    + apply fst_lt2.
      rewrite complexity_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      simpl; lia.
Qed.
    
Lemma hrr_plus_decrease_complexity : forall G T A B r,
    r <> nil ->
    HR_outer_complexity_seq (vec r (A +S B) ++ T) = fst (HR_outer_complexity_hseq ((vec r (A +S B) ++ T) :: G)) ->
    HR_outer_complexity_hseq ((vec r A ++ vec r B ++ T) :: G) <2 HR_outer_complexity_hseq ((vec r (A +S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_outer_complexity_seq (vec r A ++ vec r B ++ T) =? fst (HR_outer_complexity_hseq G)); intros H1; case_eq (HR_outer_complexity_seq (vec r (A +S B) ++ T) =? fst (HR_outer_complexity_hseq G)); intros H2; rewrite 2 complexity_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_seq_app in H2.
    rewrite ? complexity_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_outer_complexity_seq (vec r (A +S B) ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_seq_app in H2; rewrite complexity_seq_app in H3.
      rewrite ? complexity_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_outer_complexity_seq (vec r A ++ vec r B ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_outer_complexity_seq (vec r A ++ vec r B ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H3;
      case_eq (HR_outer_complexity_seq (vec r (A +S B) ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite ? complexity_seq_app in *; rewrite ? complexity_seq_vec in *; lia.
    + apply fst_lt2.
      rewrite ? complexity_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      rewrite ? complexity_seq_vec; simpl; lia.
Qed.

Lemma hrr_mul_decrease_complexity : forall G T A r0 r,
    r <> nil ->
    HR_outer_complexity_seq (vec r (r0 *S A) ++ T) = fst (HR_outer_complexity_hseq ((vec r (r0 *S A) ++ T) :: G)) ->
    HR_outer_complexity_hseq ((vec (mul_vec r0 r) A ++ T) :: G) <2 HR_outer_complexity_hseq ((vec r (r0 *S A) ++ T) :: G).
Proof.
  intros G T A r0 r Hnnil Heq.
  simpl.
  case_eq (HR_outer_complexity_seq (vec (mul_vec r0 r) A ++ T) =? fst (HR_outer_complexity_hseq G)); intros H1; case_eq (HR_outer_complexity_seq (vec r (r0 *S A) ++ T) =? fst (HR_outer_complexity_hseq G)); intros H2; rewrite complexity_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_seq_app in H2.
    rewrite ? complexity_seq_vec in *.
    simpl in H2.
    rewrite mul_vec_length in H1.
    lia.
  - case_eq (HR_outer_complexity_seq (vec r (r0 *S A) ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_seq_app in H2; rewrite complexity_seq_app in H3.
      rewrite ? complexity_seq_vec in *; simpl in H1,H2,H3.
      rewrite mul_vec_length in H1.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_outer_complexity_seq (vec (mul_vec r0 r) A ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_seq_vec in *; simpl in H1,H2,H3.
      rewrite mul_vec_length in *; lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_outer_complexity_seq (vec (mul_vec r0 r) A ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H3;
      case_eq (HR_outer_complexity_seq (vec r (r0 *S A) ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite ? complexity_seq_app in *; rewrite ? complexity_seq_vec in *; lia.
    + apply fst_lt2.
      rewrite ? complexity_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      rewrite ? complexity_seq_vec; rewrite mul_vec_length in *; simpl; lia.
Qed.

Lemma hrr_min_r_decrease_complexity : forall G T A B r,
    r <> nil ->
    HR_outer_complexity_seq (vec r (A /\S B) ++ T) = fst (HR_outer_complexity_hseq ((vec r (A /\S B) ++ T) :: G)) ->
    HR_outer_complexity_hseq ((vec r A ++ T) :: G) <2 HR_outer_complexity_hseq ((vec r (A /\S B) ++ T) :: G).
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_outer_complexity_seq (vec r A ++ T) =? fst (HR_outer_complexity_hseq G)); intros H1; case_eq (HR_outer_complexity_seq (vec r (A /\S B) ++ T) =? fst (HR_outer_complexity_hseq G)); intros H2; rewrite ? complexity_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_seq_app in H2.
    rewrite ? complexity_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_outer_complexity_seq (vec r (A /\S B) ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_seq_app in H2; rewrite complexity_seq_app in H3.
      rewrite ? complexity_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_outer_complexity_seq (vec r A ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_outer_complexity_seq (vec r A ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H3;
      case_eq (HR_outer_complexity_seq (vec r (A /\S B) ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite ? complexity_seq_app in *; rewrite ? complexity_seq_vec in *; lia.
    + apply fst_lt2.
      rewrite ? complexity_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      rewrite ? complexity_seq_vec; simpl; lia.
Qed.

Lemma hrr_min_l_decrease_complexity : forall G T A B r,
    r <> nil ->
    HR_outer_complexity_seq (vec r (A /\S B) ++ T) = fst (HR_outer_complexity_hseq ((vec r (A /\S B) ++ T) :: G)) ->
    HR_outer_complexity_hseq ((vec r B ++ T) :: G) <2 HR_outer_complexity_hseq ((vec r (A /\S B) ++ T) :: G).
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_outer_complexity_seq (vec r B ++ T) =? fst (HR_outer_complexity_hseq G)); intros H1; case_eq (HR_outer_complexity_seq (vec r (A /\S B) ++ T) =? fst (HR_outer_complexity_hseq G)); intros H2; rewrite complexity_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_seq_app in H2.
    rewrite ? complexity_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_outer_complexity_seq (vec r (A /\S B) ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_seq_app in H2; rewrite complexity_seq_app in H3.
      rewrite ? complexity_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_outer_complexity_seq (vec r B ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_outer_complexity_seq (vec r B ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H3;
      case_eq (HR_outer_complexity_seq (vec r (A /\S B) ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite ? complexity_seq_app in *; rewrite ? complexity_seq_vec in *; lia.
    + apply fst_lt2.
      rewrite ? complexity_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      rewrite ? complexity_seq_vec; simpl; lia.
Qed.

Lemma hrr_max_decrease_complexity : forall G T A B r,
    r <> nil ->
    HR_outer_complexity_seq (vec r (A \/S B) ++ T) = fst (HR_outer_complexity_hseq ((vec r (A \/S B) ++ T) :: G)) ->
    HR_outer_complexity_hseq ((vec r B ++ T) :: (vec r A ++ T) :: G) <2 HR_outer_complexity_hseq ((vec r (A \/S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_outer_complexity_seq (vec r A ++ T) =? fst (HR_outer_complexity_hseq G)); intros H1; case_eq (HR_outer_complexity_seq (vec r (A \/S B) ++ T) =? fst (HR_outer_complexity_hseq G)); intros H2; rewrite complexity_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_seq_app in H2.
    rewrite ? complexity_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_outer_complexity_seq (vec r (A \/S B) ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_seq_app in H2; rewrite complexity_seq_app in H3.
      rewrite ? complexity_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + simpl.
      case_eq (HR_outer_complexity_seq (vec r B ++ T) =? fst (HR_outer_complexity_hseq G)); intros H4.
      * apply fst_lt2.
        apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
        lia.
      * case_eq (HR_outer_complexity_seq (vec r B ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H5.
        -- apply fst_lt2.
           apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
           lia.
        -- apply fst_lt2.
           rewrite ? complexity_seq_app; rewrite ? complexity_seq_vec; destruct r; [ exfalso; apply Hnnil; reflexivity | ]; simpl; lia.        
  - replace (HR_outer_complexity_seq (vec r A ++ T) <? fst (HR_outer_complexity_hseq G))%nat with true.
    2:{ symmetry.
        apply Nat.ltb_lt; apply Nat.eqb_neq in H1; apply Nat.eqb_eq in H2.
        rewrite ? complexity_seq_app in *; rewrite ? complexity_seq_vec in *; simpl in *; lia. }
    simpl.
    replace (HR_outer_complexity_seq (vec r B ++ T) =? fst (HR_outer_complexity_hseq G)) with false.
    2:{ symmetry.
        apply Nat.eqb_neq; apply Nat.eqb_eq in H2.
        destruct r; [ exfalso; apply Hnnil; reflexivity | ].
        rewrite ? complexity_seq_app in *; rewrite ? complexity_seq_vec in *; simpl in *; lia. }
    replace (HR_outer_complexity_seq (vec r B ++ T) <? fst (HR_outer_complexity_hseq G))%nat with true.
    2:{ symmetry.
        apply Nat.ltb_lt; apply Nat.eqb_eq in H2.
        destruct r; [ exfalso; apply Hnnil; reflexivity | ].
        rewrite ? complexity_seq_app in *; rewrite ? complexity_seq_vec in *; simpl in *; lia. }
    apply snd_lt2; lia.
  - simpl in Heq.
    rewrite H2 in Heq.
    assert ((HR_outer_complexity_seq (vec r (A \/S B) ++ T) <? fst (HR_outer_complexity_hseq G))%nat = false) as H3.
    { apply Nat.ltb_nlt; apply Nat.eqb_neq in H2.
      intros H; apply Nat.ltb_lt in H.
      rewrite H in Heq.
      simpl in Heq.
      apply H2; apply Heq. }
    rewrite H3; clear Heq.
    case_eq (HR_outer_complexity_seq (vec r A ++ T) <? fst (HR_outer_complexity_hseq G))%nat; intros H4; simpl.
    + case (HR_outer_complexity_seq (vec r B ++ T) =? fst (HR_outer_complexity_hseq G));
        [ | case (HR_outer_complexity_seq (vec r B ++ T) <? fst (HR_outer_complexity_hseq G))%nat];
        apply fst_lt2; apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4;
          rewrite ? complexity_seq_app in *; rewrite ? complexity_seq_vec in *;
            (destruct r; [ exfalso; apply Hnnil; reflexivity | ]); simpl in *; lia.
    + case (HR_outer_complexity_seq (vec r B ++ T) =? HR_outer_complexity_seq (vec r A ++ T));
        [ | case (HR_outer_complexity_seq (vec r B ++ T) <? HR_outer_complexity_seq (vec r A ++ T))%nat];
      apply fst_lt2;
        rewrite ? complexity_seq_app in *; rewrite ? complexity_seq_vec in *;
          (destruct r; [ exfalso; apply Hnnil; reflexivity | ]); simpl in *; lia.
Qed.
