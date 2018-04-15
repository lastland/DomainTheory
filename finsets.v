(* Copyright (c) 2014, Robert Dockins *)

Require Import Relations.
Require Import List.
Require Import Setoid.
Require Import Arith.

Require Import Domains.basics.
Require Import Domains.preord.
Require Import Domains.categories.
Require Import Domains.sets.

(** * The theory of finite sets.

      Here we define the theory of finite sets.  Concretely,
      finite sets are represetned by the standard list type,
      with list membership.  Singleton sets are given
      by one-element lists, union is defined by list
      concatination and image is the stadard list map function.
  *)

Definition concat (A:Type) (l:list (list A)) : list A :=
  List.fold_right (@app A) (@nil A) l.

Module finset.
Section finset.
  Definition fset (A:preord) := list A.
  Definition fsingle (A:preord) (a:A) := a::nil.
  Definition fmember (A:preord) (a:A) (P:fset A) := exists a', In a' P /\ a ≈ a'.
  Definition fimage (A B:preord) (f:A → B) (P:fset A) : fset B :=
    List.map (Preord.map A B f) P.
  Definition funion (A:preord) (XS:fset (set.set_preord fset fmember A)) : fset A :=
    fold_right (@app A) (@nil A) XS.

  Program Definition mixin : set.mixin_of fset fmember fsingle fimage funion :=
    set.Mixin fset fmember fsingle fimage funion _ _ _ _ _ _.
  Next Obligation.
    unfold fmember.
    intros. induction X; simpl in *; intuition.
    destruct H0 as [a' [??]]. elim H0.
    destruct H0 as [a' [??]]. destruct H0; subst.
    exists a'. split; eauto.
    destruct IHX as [q [??]]; eauto.
  Qed.
  Next Obligation.
    unfold fmember, fsingle; intros.
    firstorder; subst; auto.
  Qed.
  Next Obligation.
    unfold fmember. simpl; intros.
    induction XS; simpl; intuition.
    destruct H as [?[??]]. elim H.
    destruct H as [?[??]]. 
    destruct H as [?[??]]. elim H.
    
    destruct H1 as [a' [??]].
    apply in_app_or in H1.
    destruct H1.
    exists a0. split; eauto.
    destruct H as [X [??]]; eauto.
    exists X; split; eauto.
    destruct H as [q [??]].
    exists q; split; auto.
    destruct H1 as [X [??]].
    destruct H1 as [Y [??]].
    destruct H1; subst.
    destruct H2 as [a' [??]].
    destruct H3.
    destruct (H3 a') as [a'' [??]]; eauto.
    exists a'. split; auto.
    exists a''. split; auto.
    apply in_or_app. auto.
    eauto.
    destruct H0 as [q [??]]; eauto.
    destruct H2 as [a' [??]].
    exists q; split; auto.
    apply in_or_app; auto.
  Qed.
  Next Obligation.
    unfold fmember, fimage. simpl; intros.
    intuition.
    destruct H as [a' [??]].
    exists a'; split; auto.
    rewrite map_map. auto.
    destruct H as [a' [??]].
    exists a'; split; auto.
    rewrite map_map in H; auto.
  Qed.
  Next Obligation.
    unfold fmember, fimage; simpl; intros.
    destruct H as [a' [??]].
    induction P; simpl in *; intuition; subst.
    exists (Preord.map A B f a').
    split; auto.
    destruct H as [b [??]].
    exists b. split; auto.
  Qed.
  Next Obligation.
    unfold fmember, fimage; simpl; intros.
    destruct H as [a' [??]].
    induction P; simpl in *; intuition; subst.
    exists a. split; auto. exists a; split; auto.
    destruct H as [y [??]].
    exists y. split; auto.
    destruct H as [b [??]].
    exists b; split; auto.
  Qed.
End finset.
End finset.

Canonical Structure finset_theory : set.theory :=
  set.Theory
    finset.fset
    finset.fmember
    finset.fsingle
    finset.fimage
    finset.funion
    finset.mixin.

Notation finset := (set_preord finset_theory).

Definition cl_finset_theory (CL:color) : set.theory 
  := cset_theory finset_theory CL.
Notation cl_finset CL := (set_preord (cl_finset_theory CL)).



Program Definition finset_dec (A:preord) (Adec : ord_dec A) : set_dec finset_theory A
  := Setdec finset_theory A _.
Next Obligation.
  intros A Adec x X.
  induction X. right. red; simpl; intros. 
  destruct H as [x' [??]]. apply H.
  destruct IHX.
  left.
  destruct m as [x' [??]].
  exists x'. split; simpl; auto.
  destruct (PREORD_EQ_DEC A Adec x a).
  left.
  exists a. split; simpl; auto.
  right.
  intros [x' [??]].
  simpl in H; intuition; subst; auto.
  apply n.
  exists x'. split; auto.
Qed.

Canonical Structure finset_dec.


(**  Some useful lemmas relating list formation operations to
     finite set membership.
  *)
Lemma nil_elem : forall (A:preord) (x:A),
  x ∈ (nil : finset A) -> False.
Proof.
  intros. destruct H as [?[??]]. elim H.
Qed.

Lemma cons_elem : forall (A:preord) (a:A) (P:finset A) (x:A),
  x ∈ (a::P : finset A) <-> x ≈ a \/ x ∈ P.
Proof.
  intros; split; intros.
  destruct H as [q [??]].
  destruct H. subst. auto.
  right. exists q; split; auto.
  destruct H.
  exists a; split; simpl; auto.
  destruct H as [q [??]]. exists q; split; simpl; auto.
Qed.

Lemma app_elem :  forall (A:preord) (P Q:finset A) (x:A),
  x ∈ (P++Q : finset A) <-> x ∈ P \/ x ∈ Q.
Proof.
  intro A. induction P; split; intros; auto.
  destruct H; auto.
  apply nil_elem in H. elim H.
  simpl in H.
  apply cons_elem in H.
  destruct H.
  left. apply cons_elem; auto.
  apply IHP in H. destruct H.
  left. apply cons_elem; auto.
  auto.
  simpl. apply cons_elem.
  destruct H.
  apply cons_elem in H.
  destruct H; auto.
  right. apply IHP; auto.
  right. apply IHP; auto.
Qed.

Lemma nil_subset X (Q:finset X) :
  (nil : finset X) ⊆ Q.
Proof.
  repeat intro. apply nil_elem in H. elim H.
Qed.

Lemma ub_nil : forall (X:preord) (a:X),
  upper_bound a (nil : finset X).
Proof.
  repeat intro. apply nil_elem in H. elim H.
Qed.

Lemma ub_cons (X:preord) (x:X) (xs:finset X) (a:X) :
  x ≤ a ->
  upper_bound a xs ->
  upper_bound a (x::xs : finset X).
Proof.
  repeat intro.
  apply cons_elem in H1. destruct H1.
  rewrite H1. auto. apply H0; auto.
Qed.

Lemma cons_subset (X:preord) (x:X) (xs ys:finset X) :
  x ∈ ys -> xs ⊆ ys -> (x::xs : finset X) ⊆ ys.
Proof.
  repeat intro.
  apply cons_elem in H1. destruct H1.
  rewrite H1; auto. apply H0; auto.
Qed.

Lemma cons_morphism (X:preord) (x x':X) (xs xs':finset X) :
  x ≈ x' -> xs ≈ xs' -> (x :: xs:finset X) ≈ x' :: xs'.
Proof.
  intros.
  split.
  apply cons_subset. apply cons_elem. auto.
  red; intros. apply cons_elem; auto.
  right. rewrite <- H0; auto.
  apply cons_subset. apply cons_elem. auto.
  red; intros. apply cons_elem; auto.
  right. rewrite H0; auto.
Qed.

Lemma dec_conj (P Q : Prop) :
  {P}+{~P} -> {Q}+{~Q} -> {P/\Q}+{~(P/\Q)}.
Proof.
  intros. destruct H. destruct H0.
  left; auto.
  right; intros [??]; contradiction.
  right; intros [??]; contradiction.
Qed.

(**  The cartesian product of finite sets.
  *)
Fixpoint finprod {A B:preord} (P:finset A) (Q:finset B) : finset (A×B) :=
  match P with
  | nil => nil
  | x::P' => map (fun y => (x,y)) Q ++ finprod P' Q
  end.

Lemma finprod_elem : forall A B (P:finset A) (Q:finset B) a b, 
  (a,b) ∈ finprod P Q <-> (a ∈ P /\ b ∈ Q).
Proof.
  intros A B. induction P; simpl; split; intros.
  apply nil_elem in H. elim H.
  destruct H. apply nil_elem in H. elim H.
  apply app_elem in H.
  destruct H.
  destruct H as [?[??]].
  apply in_map_iff in H.
  destruct H as [q [??]].
  subst x.
  split.
  apply cons_elem. left.
  destruct H0 as [[??][??]]; split; auto.
  exists q; split; auto.
  destruct H0 as [[??][??]]; split; auto.
  apply IHP in H.
  destruct H; split; auto.
  apply cons_elem; auto.
  destruct H.
  apply cons_elem in H.
  destruct H.
  apply app_elem.
  left.
  destruct H0 as [q [??]].
  exists (a,q).
  split.
  apply in_map_iff.
  exists q. split; auto.
  destruct H; destruct H1.
  split; split; auto.
  apply app_elem. right.
  apply IHP. split; auto.
Qed.  

(**  Disjoint union of finite sets.
  *)

Fixpoint left_finset (A B:preord) (X:finset (sum_preord A B)) : finset A :=
  match X with
  | nil => nil
  | inl l :: X' => l :: left_finset A B X'
  | inr _ :: X' => left_finset A B X'
  end.

Fixpoint right_finset (A B:preord) (X:finset (sum_preord A B)) : finset B :=
  match X with
  | nil => nil
  | inl _ :: X' => right_finset A B X'
  | inr r :: X' => r :: right_finset A B X'
  end.

Lemma left_finset_elem A B X a :
  a ∈ left_finset A B X <-> inl a ∈ X.
Proof.
  induction X; simpl.
  split; intros.
  apply nil_elem in H. elim H.
  apply nil_elem in H. elim H.
  destruct a0; simpl.
  split; intros.
  apply cons_elem in H. destruct H.
  apply cons_elem. left. auto.
  rewrite IHX in H.
  apply cons_elem. right. auto.
  apply cons_elem in H. destruct H.
  apply cons_elem. left. auto.
  apply cons_elem. right. rewrite IHX. auto.
  split; intros.
  rewrite IHX in H.
  apply cons_elem. right. auto.
  apply cons_elem in H. destruct H.
  destruct H. elim H.
  rewrite IHX. auto.
Qed.  

Lemma right_finset_elem A B X b :
  b ∈ right_finset A B X <-> inr b ∈ X.
Proof.
  induction X; simpl.
  split; intros.
  apply nil_elem in H. elim H.
  apply nil_elem in H. elim H.
  destruct a; simpl.
  split; intros.
  rewrite IHX in H.
  apply cons_elem. right. auto.
  apply cons_elem in H. destruct H.
  destruct H. elim H.
  rewrite IHX. auto.

  split; intros.
  apply cons_elem in H. destruct H.
  apply cons_elem. left. auto.
  rewrite IHX in H.
  apply cons_elem. right. auto.
  apply cons_elem in H. destruct H.
  apply cons_elem. left. auto.
  apply cons_elem. right. rewrite IHX. auto.
Qed.  


Definition finsum {A B:preord} (P:finset A) (Q:finset B) : finset (sum_preord A B) :=
  map inl P ++ map inr Q.

Lemma finsum_left_elem : forall A B (P:finset A) (Q:finset B) a, 
  inl a ∈ finsum P Q <-> a ∈ P.
Proof.
  split; intro.
  destruct H as [q [??]].
  unfold finsum in H.
  apply in_app_or in H.
  destruct H.
  apply in_map_iff in H.
  destruct H as [x [??]].
  subst q.
  exists x. split; auto.
  apply in_map_iff in H.
  destruct H as [x [??]].
  subst q.
  destruct H0. elim H.
  destruct H as [x [??]].
  exists (inl x).
  split; auto.
  unfold finsum.
  apply in_or_app.
  left.
  apply in_map. auto.
Qed.
  

Lemma finsum_right_elem : forall A B (P:finset A) (Q:finset B) b, 
  inr b ∈ finsum P Q <-> b ∈ Q.
Proof.
  split; intro.
  destruct H as [q [??]].
  unfold finsum in H.
  apply in_app_or in H.
  destruct H.
  apply in_map_iff in H.
  destruct H as [x [??]].
  subst q.
  destruct H0. elim H.
  apply in_map_iff in H.
  destruct H as [x [??]].
  subst q.
  exists x; split; auto.
  destruct H as [x [??]].
  exists (inr x).
  split; auto.
  unfold finsum.
  apply in_or_app.
  right.
  apply in_map. auto.
Qed.

Lemma left_right_finset_finsum A B X :
  X ≈ finsum (left_finset A B X) (right_finset A B X).
Proof.
  split; hnf; intros.
  destruct a.
  apply finsum_left_elem.
  apply left_finset_elem. auto.
  apply finsum_right_elem.
  apply right_finset_elem. auto.
  destruct a.
  apply left_finset_elem. 
  eapply finsum_left_elem; eauto.
  apply right_finset_elem.
  eapply finsum_right_elem; eauto.
Qed.


(**  We can take the subset of a finite set if the
     predicate we wish to use to take the subset is decidable.
  *)
Section finsubset.
  Variable A:preord.
  Variable P : A -> Prop.
  Variable HP : forall x y, x ≈ y -> P x -> P y.
  Variable Hdec : forall x, { P x } + { ~P x }.

  Fixpoint finsubset (l:finset A) : finset A :=
    match l with
    | nil => nil 
    | x::xs => if Hdec x then x :: finsubset xs else finsubset xs
    end.

  Lemma finsubset_elem : forall X x,
    x ∈ finsubset X <-> (x ∈ X /\ P x).
  Proof.
    induction X; simpl; split; simpl; intros.
    destruct H as [?[??]]. elim H.
    destruct H.
    destruct H as [?[??]]. elim H.
    destruct (Hdec a).
    destruct H as [q [??]].
    simpl in H; destruct H; subst.
    split.
    exists q. split; simpl; auto.
    apply HP with q; auto.
    assert (x ∈ finsubset X).
    exists q; split; simpl; auto.
    apply IHX in H1.
    destruct H1.
    destruct H1 as [q' [??]].
    split; auto.
    exists q'; split; simpl; auto.
    apply IHX in H.
    destruct H.
    split; auto.
    destruct H as [q' [??]].
    exists q'; split; simpl; auto.

    destruct H.
    destruct H as [q [??]].
    simpl in H; destruct H; subst.
    destruct (Hdec q).
    exists q; split; simpl; auto.
    elim n.
    apply HP with x; auto.
    assert (x ∈ finsubset X).
    apply IHX. split; auto.
    exists q; split; auto.
    destruct (Hdec a); auto.
    destruct H2 as [q' [??]].
    exists q'; split; simpl; auto.
  Qed.
End finsubset.
    

(**  We can take the intersection of finite sets if the elements
     have decidable equality.
  *)
Definition fin_intersect (A:preord) (Hdec:ord_dec A) (X Y:finset A) : finset A
 := finsubset A (fun x => x ∈ X) (fun x => finset_dec A Hdec x X) Y.

Lemma fin_intersect_elem : forall A Hdec X Y x,
  x ∈ fin_intersect A Hdec X Y <-> (x ∈ X /\ x ∈ Y).
Proof.
  intros.
  split; intros.
  unfold fin_intersect in H.
  apply finsubset_elem in H.
  intuition.
  intros. rewrite <- H1; auto.
  unfold fin_intersect.
  apply finsubset_elem.
  intros. rewrite <- H0; auto.
  destruct H; split; auto.
Qed.

Definition fin_list_intersect 
  A Hdec (l:finset (finset A)) (Z:finset A) : finset A :=
  List.fold_right (fin_intersect A Hdec) Z l.

Lemma fin_list_intersect_elem : forall A Hdec l Z x,
  x ∈ fin_list_intersect A Hdec l Z <-> (x ∈ Z /\ forall X, X ∈ l -> x ∈ X).
Proof.
  induction l; simpl; intros.
  intuition.
  destruct H0 as [?[??]]. elim H0.
  split; intros.
  apply fin_intersect_elem in H.
  destruct H.
  apply IHl in H0.
  intuition.
  destruct H0 as [q [??]].
  destruct H0. subst q.
  rewrite H3; auto.
  apply H2.
  exists q; split; simpl; auto.
  apply fin_intersect_elem.
  split.
  destruct H.
  apply H0.
  exists a; split; simpl; auto.
  destruct H.
  apply IHl. split; auto.
  intros. apply H0.
  destruct H1 as [q [??]]. exists q; split; simpl; auto.
Qed.


(**  We can remove an element from a finite set if the elements have
     decidable equality.
  *)
Fixpoint finset_remove {A:preord} (Hdec : ord_dec A) (X:finset A) (a:A) : finset A :=
  match X with
  | nil => nil
  | List.cons x xs => if PREORD_EQ_DEC A Hdec x a 
                  then finset_remove Hdec xs a
                  else List.cons x (finset_remove Hdec xs a)
  end.

Lemma finset_remove_elem : forall A (Hdec:ord_dec A) X a x,
  x ∈ finset_remove Hdec X a <-> (x ∈ X /\ x ≉ a).
Proof.  
  intros. induction X.
  split; intros.
  destruct H as [?[??]]. elim H.
  destruct H. auto.
  unfold finset_remove. fold (@finset_remove A).
  destruct (PREORD_EQ_DEC A Hdec a0 a).
  rewrite IHX.
  split; intros.
  destruct H.
  split; auto.
  destruct H as [q [??]]. exists q; split; simpl; auto.
  destruct H. split; auto.
  destruct H as [q [??]].
  simpl in H. destruct H; subst.
  elim H0. eauto.
  exists q; split; auto.
  split; intros.
  destruct H as [q[??]].
  simpl in H. destruct H; subst.
  split. 2: rewrite H0; auto.
  exists q. split; simpl; auto.
  assert (x ∈ (X:finset A) /\ x ≉ a).
  apply IHX.
  exists q; split; auto.
  destruct H1; split; auto.
  destruct H1 as [q' [??]].
  exists q'; split; simpl; auto.
  destruct H.
  destruct H as [q[??]].
  simpl in H. destruct H; subst.
  exists q. split; simpl; auto.
  assert (x ∈ finset_remove Hdec X a).
  apply IHX.
  split; auto.
  exists q; split; auto.
  destruct H2 as [q' [??]].
  exists q'; split; simpl; auto.
Qed.

Lemma finset_remove_length1 A Hdec (X:finset A) (a:A) :
  length (finset_remove Hdec X a) <= length X.
Proof.
  induction X; simpl; auto.
  destruct (Hdec a0 a).
  destruct (Hdec a a0).
  transitivity (length X); auto with arith.
  simpl. auto with arith.
  simpl. auto with arith.
Qed.

Lemma finset_remove_length2 A Hdec (X:finset A) (a:A) :
  a ∈ X -> length (finset_remove Hdec X a) < length X.
Proof.
  intros [q [??]].
  induction X; simpl; intros.
  destruct H.
  destruct H. subst a0.
  destruct (Hdec q a).
  destruct (Hdec a q).
  red. 
  apply Le.le_n_S. apply finset_remove_length1.
  elim n; destruct H0; auto.
  elim n; destruct H0; auto.
  destruct (Hdec a0 a).
  destruct (Hdec a a0).
  transitivity (length X); auto.
  simpl. apply Lt.lt_n_S. apply IHX; auto.
  simpl. apply Lt.lt_n_S. apply IHX; auto.
Qed.  

(**  We can take the powerset of a finite set; that is, all finite
     subsets of a finite set.
  *)
Fixpoint list_finsubsets {A:preord} (M:finset A) : finset (finset A) :=
  match M with
  | nil => List.cons nil nil
  | List.cons x xs => 
       let subs := list_finsubsets xs in
           List.app (subs) (List.map (List.cons x) subs)
  end.

Lemma list_finsubsets_correct A : forall (M X:finset A),
  X ∈ list_finsubsets M -> X ⊆ M.
Proof.
  induction M; simpl; intros.
  destruct H as [?[??]]. elim H.
  simpl in H. intuition subst.
  rewrite H0. red; auto.
  intros. elim H1.
  destruct H as [q [??]].
  apply List.in_app_or in H.
  destruct H.
  red. intros.
  apply (IHM X) in H1.
  destruct H1 as [q' [??]].
  exists q'; split; simpl; auto.
  exists q; split; auto.
  apply List.in_map_iff in H.
  destruct H as [x [??]].
  assert ((x:finset A) ⊆ (M:finset A)).
  apply IHM.
  exists x. split; auto.
  red; intros.
  rewrite H0 in H3.
  rewrite <- H in H3.
  destruct H3 as [q' [??]].
  simpl in H3; intuition subst.
  exists q'. split; simpl; auto.
  destruct (H2 a0) as [q'' [??]].
  exists q'. split; auto.
  exists q''. split; simpl; auto.
Qed.

Lemma list_finsubsets_complete A (Hdec : ord_dec A) : forall (M X:finset A),
  X ⊆ M -> X ∈ list_finsubsets M.
Proof.
  induction M; intros.
  simpl. exists nil. split; simpl; auto.
  split; auto.
  red; simpl; intros. destruct H0 as [?[??]]. elim H0.
  simpl.
  assert (finset_remove Hdec X a ⊆ (M:finset A)).
  red; intros.
  apply finset_remove_elem in H0.
  destruct H0.
  apply H in H0.
  destruct H0 as [q[??]].
  simpl in H0; destruct H0; subst.
  elim H1; auto.
  exists q; split; auto.
  destruct (finset_dec _ Hdec a X).
  generalize H0; intro.
  apply IHM in H0.
  destruct H0 as [Q[??]].
  exists (List.cons a Q).
  split.
  apply List.in_or_app. right.
  apply List.in_map. auto.
  split; red; simpl; intros.
  generalize H3; intros.
  apply H in H3.
  destruct H3 as [q [??]].
  simpl in H3; destruct H3; subst.
  exists q. split; simpl; auto.
  destruct (PREORD_EQ_DEC A Hdec a0 a).
  exists a. split; simpl; auto.
  assert (a0 ∈ finset_remove Hdec X a).
  apply finset_remove_elem. split; auto.
  rewrite H2 in H6.
  destruct H6 as [q' [??]].
  exists q'; split; simpl; auto.
  destruct H3 as [q [??]].
  simpl in H3. destruct H3; subst.
  rewrite H4. auto.
  assert (a0 ∈ Q).
  exists q; split; auto.
  rewrite <- H2 in H5.
  apply finset_remove_elem in H5.
  destruct H5; auto.
  
  assert (finset_remove Hdec X a ∈ list_finsubsets M).
  apply IHM. auto.
  destruct H1 as [Q [??]].
  exists Q. split; auto.
  apply List.in_or_app. auto.
  rewrite <- H2.  
  split; red; simpl; intros.
  apply finset_remove_elem. split; auto.
  intro. apply n. rewrite <- H4; auto.
  apply finset_remove_elem in H3.
  destruct H3; auto.
Qed.


(**  Decidability facts of various kinds can be pushed into finite sets.
  *)
Lemma finset_find_dec (A:preord)
  (P:A -> Prop)
  (HP : forall x y:A, x ≈ y -> P x -> P y)
  (Hdec : forall x:A, {P x}+{~P x}) :
  forall M:finset A, { z | z ∈ M /\ P z } + { forall z, z ∈ M -> ~P z }.
Proof.
  induction M.
  right. intros. destruct H as [?[??]]. elim H.
  destruct IHM.
  destruct s as [z [??]].
  left. exists z. split; auto.
  destruct H as [q [??]]. exists q; split; simpl; auto.
  destruct (Hdec a).
  left. exists a. split; auto.
  exists a. split; simpl; auto.
  right.
  intros. destruct H as [q [??]].
  simpl in H; intuition subst.
  apply n0. apply HP with z; auto.
  apply (n z); auto.
  exists q; split; auto.
Qed.

Lemma finset_find_dec' (A:preord)
  (P:A -> Prop)
  (HP : forall x y:A, x ≈ y -> P x -> P y)
  (Hdec : forall x:A, {P x}+{~P x}) :
  forall M:finset A, { z | z ∈ M /\ ~P z } + { forall z, z ∈ M -> P z }.
Proof.
  induction M.
  right. intros. destruct H as [?[??]]. elim H.
  destruct IHM.
  destruct s as [z [??]].
  left. exists z. split; auto.
  destruct H as [q [??]]. exists q; split; simpl; auto.
  destruct (Hdec a).
  right. intros.
  destruct H as [q [??]].
  simpl in H; intuition subst.
  apply HP with q; auto.
  apply p. exists q; split; auto.
  left. exists a. split; auto.
  exists a; split; simpl; auto.
Qed.

Lemma finsubset_dec (A:preord)
  (HAdec : ord_dec A)
  (P:finset A -> Prop)
  (HP : forall x y:finset A, x ≈ y -> P x -> P y)
  (Hdec : forall x:finset A, {P x}+{~P x}) :
  forall (M:finset A),
    { exists X:finset A, X ⊆ M /\ P X } +
    { forall X:finset A, X ⊆ M -> ~P X }.
Proof.
  intro M.
  destruct (finset_find_dec (finset A) P) with  (list_finsubsets M); auto.
  destruct s as [?[??]].
  left. exists x.
  split; auto.
  apply list_finsubsets_correct. auto.
  right; intros. apply n.
  apply list_finsubsets_complete; auto.
Qed.


Lemma finsubset_dec' (A:preord)
  (HAdec : ord_dec A)
  (P:finset A -> Prop)
  (HP : forall x y:finset A, x ≈ y -> P x -> P y)
  (Hdec : forall x:finset A, {P x}+{~P x}) :
  forall (M:finset A),
    { forall X:finset A, X ⊆ M -> P X } +
    { exists X:finset A, X ⊆ M /\ ~P X }.
Proof.
  intro M.
  destruct (finset_find_dec' (finset A) P) with  (list_finsubsets M); auto.
  destruct s as [?[??]].
  right. exists x.
  split; auto.
  apply list_finsubsets_correct. auto.
  left; intros. apply p.
  apply list_finsubsets_complete; auto.
Qed.

Lemma finset_in_dec (A:preord) (Hdec : ord_dec A) : forall (M:finset A) (x:A),
  { x ∈ M } + { x ∉ M }.
Proof.
  induction M.
  right. intro. destruct H as [?[??]]. elim H.
  intro x.
  destruct (IHM x).
  left.
  destruct m as [q [??]].
  exists q. split; simpl; auto.
  destruct (Hdec x a).
  destruct (Hdec a x).
  left. exists a. split; simpl; auto.
  right.
  intro. destruct H as [q [??]].
  simpl in H; intuition subst.
  apply n0; destruct H0; auto.
  apply n.
  exists q. split; auto.
  right.
  intro. destruct H as [q [??]].
  simpl in H; intuition subst.
  apply n0; destruct H0; auto.
  apply n.
  exists q. split; auto.
Qed.    

Lemma finset_cons_eq (A:preord) (x y:A) (l1 l2:finset A) :
  x ≈ y -> l1 ≈ l2 -> 
  (x::l1 : finset A) ≈ (y::l2).
Proof.
  intros. split.
  hnf; intros.
  apply cons_elem in H1.
  destruct H1. rewrite H1.
  apply cons_elem; auto.
  apply cons_elem; right. rewrite <- H0; auto.
  hnf; intros.
  apply cons_elem in H1.
  destruct H1. rewrite H1.
  apply cons_elem; auto.
  apply cons_elem; right. rewrite H0; auto.
Qed.  

(** ** Swelling

    This lemma is used to construct certain finite sets.
    It works by starting with some small set and adding new
    elements to it until it satisfies some completeness property
    of interest.  We know that the process must halt because
    every new element added is drawn from a finite set [M].

    Swelling is used to construct sets that are hard to get other
    ways, such as when the defining predicate is not decidable.
    
    The swelling techinque is essentially unique to constructive
    settings; in a classical setting one would simply use a set
    comprehension principle to define the desired finite subset.
  *)
Lemma swelling_lemma (A:preord) (HA:ord_dec A)
  (M:finset A)
  (INV : finset A -> Prop)
  (P : finset A -> Prop) 

  (HP : forall z, z ⊆ M -> INV z -> 
    P z \/ exists q, q ∈ M /\ q ∉ z /\ INV (q::z)) :

  (exists z0, z0 ⊆ M /\ INV z0) ->
  exists z, z ⊆ M /\ INV z /\ P z.
Proof.
  intros [z [??]].
  assert (exists M0:finset A,
    (forall q, q ∈ M0 <-> q ∈ M /\ q ∉ z)).
  assert (forall q, {q ∉ z}+{~q ∉ z}).
  intros. 
  destruct (finset_in_dec A HA z q); auto.
  set (M0 := finsubset A (fun q => q ∉ z) X M).
  exists M0. intro q.
  unfold M0. rewrite finsubset_elem. split; auto.
  repeat intro. apply H2. rewrite H1; auto.
  destruct H1 as [M0 ?].
  revert z H H0 H1.  

  induction M0 using 
    (well_founded_induction (Wf_nat.well_founded_ltof _ (@length _))); intros.

  destruct (HP z); eauto.
  destruct H3 as [q [?[??]]].
  set (x' := @finset_remove A HA x q).
  apply (H x') with (q::z).
  red; simpl. unfold x'.
  apply finset_remove_length2.
  apply H2. split; auto.
  apply cons_subset; auto.
  auto.
  intros. split; intros.
  apply finset_remove_elem in H6.
  destruct H6.
  apply H2 in H6.
  destruct H6; split; auto.
  intro.
  apply cons_elem in H9. destruct H9.
  apply H7; auto.
  apply H8; auto.
  apply finset_remove_elem.
  destruct H6. split.
  apply H2.
  split; auto.
  intro. apply H7. apply cons_elem; auto.
  intro. apply H7. apply cons_elem; auto.
Qed.
