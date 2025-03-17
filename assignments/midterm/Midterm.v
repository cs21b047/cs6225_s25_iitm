(** CS6225 Spring 2025: Programs and proofs -- Mid Term *)

(***************************************
 ** Instructions
 ***************************************

   This is a take home exam, with 24 hours for the exam. Strictly no late
   submissions allowed. Submit your solutions through course moodle.

   Completed solutions should not have any [Abort]ed proofs. If there are, they
   will get [0] points. There are a few lemmas and theorems for which the proof
   ends with [Admitted]. For example, see [fib_succ_add] and
   [fib_fib_tail_rec']. Those are the only ones for which you may leave the
   proof as admitted and use it in the subsequent theorems ([fib_ok] for
   example). Your solution will not have any other [Admitted] proofs. Any other
   use of [Admitted] proofs will get [0] points. *)

Require Import Frap MidtermSig.

(***************************************
 ** Swivel
 ***************************************)

Inductive tree :=
  | Leaf
  | Node (v : nat) (lt rt : tree).
  
Fixpoint rightmost (tr: tree) : option nat :=
  match tr with
  | Leaf => None
  | Node v _ rt =>
    match rt with
    | Leaf => Some v
    | _ => rightmost rt
    end
  end.
  
Fixpoint leftmost (tr : tree) : option nat := 
  match tr with
  | Leaf => None
  | Node v lt _ => 
    match lt with 
    | Leaf => Some v
    | _ => leftmost lt
    end
  end.
(* 3 points *)
  
Fixpoint swivel tr :=
  match tr with
  | Leaf => Leaf
  | Node v lt rt => Node v (swivel rt) (swivel lt)
  end.
  
Theorem swivel_ok : forall tr, 
  leftmost tr = rightmost (swivel tr).
(* 5 points *)
Proof.
intros.
induction tr.
trivial.
simpl swivel. destruct tr1. simpl swivel. simpl rightmost. simpl leftmost. trivial.
destruct leftmost. destruct rightmost. assumption. assumption. destruct rightmost. assumption. assumption.
Qed.

(***************************************
 ** Fibonacci Sequence
 ***************************************)

Fixpoint fib n :=
  match n with
  | 0 => 1
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n'' + fib n'
            end
  end.

Fixpoint fib_tail_rec' n a b :=
  match n with
  | 0 => a
  | S n' => fib_tail_rec' n' b (a+b)
  end.

Definition fib_tail_rec n := fib_tail_rec' n 1 1.
(* Remove [n + 0] and fill in correct definition *)
(* 2 points *)

Example ex1: fib 10 = 89.
Proof.
  auto.
Qed.

Example ex2: fib_tail_rec 10 = 89.
Proof.
  auto.
Abort.

Lemma fib_succ_add: forall n,
  fib n + fib (n+1) = fib(n+2).
(* 5 points *)
Proof.
  (* FILL IN *)
  intros.
  assert(fib (S(S n)) = fib(n) + fib(S n)) as H.
  - simpl. trivial.
  - assert (S n = n + 1) as H1.
  induct n. trivial.
  simpl. rewrite IHn. trivial. simpl. trivial. 
  assert(S(S n)+1=S(S(S n))) as H0.
  simpl. rewrite <- H1. trivial.
  assert (S (S n) = n + 2).
  assert (n+2=n+1+1) as H2. linear_arithmetic.
  rewrite H2. rewrite <- H1. simpl. rewrite <- H1. trivial.
  rewrite <- H1. rewrite <- H2. rewrite H. trivial.
Qed.

Lemma fib_fib_tail_rec': forall n k,
  fib_tail_rec' n (fib k) (fib (k+1)) = fib (k+n).
(* 5 points *)
Proof.
  (* FILL IN *)
  induction n as [|n' IH]; intros k.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl.
    rewrite fib_succ_add with (n:=k).
    assert(k+2 = k+1+1). linear_arithmetic. 
    assert (forall l,S l= l + 1) as H1.
    intros l. induct l. simpl. trivial. simpl. rewrite <- IHl. trivial.
    rewrite (H1 n').
    assert(k+(n'+1)=k+1+n'). ring.
    rewrite H0.
    rewrite H.
    rewrite IH with (k := k + 1).
    trivial.
Qed.

Theorem fib_ok : forall n, fib n = fib_tail_rec n.
(* 5 points *)
Proof.
  (* FILL IN *)
  intros.
  assert(fib_tail_rec' n 1 1 = fib n).
  rewrite fib_fib_tail_rec' with (k:=0).
  assert(0+n=n). linear_arithmetic.
  rewrite H. trivial.
  assert(fib_tail_rec n = fib_tail_rec' n 1 1).
  trivial. rewrite H0. rewrite H. trivial.
Qed.

(***************************************
 ** List.rev is involutive
 **************************************)

Require Import List.
Import ListNotations.

Theorem rev_involutive : forall (A:Type) (l : list A), rev (rev l) = l.
(* 5 points *)
Proof.
induct l.
trivial.
simpl. 
assert(rev (rev l ++ [a]) = [a] ++ rev(rev(l))).
rewrite rev_app_distr. trivial.
rewrite H. rewrite IHl. trivial.
Qed.

(***************************************
 ** Insertion sort
 ***************************************
 
 
  We will define insertion sort and prove it right. Consider the following 
  idea. Given the input list l = [4;5;1;3], sorting proceeds like this:

  Using an auxilliary list [sorted]:

  l=[4;5;1;3] aux=[]
  l=[5;1;3]   aux=[4]
  l=[1;3]     aux=[4;5]
  l=[3]       aux=[1;4;5]
  l=[]        aux=[1;3;4;5]
  
  Observe that [aux] is always sorted. The idea is that, at each step, 
  we take one element from [l] and insert into [aux] at the right position 
  so that [aux] remains sorted. When [l] is empty, [aux] is the sorted version 
  of the input list [l].
  
  In a typical insertion sort, you can do binary search on [aux] list and 
  insert, leading to O(n log(n)) running time. We will just do a linear search
  through [aux] to find the correct position.

  We will use the comparison function [compare] that you have seen in the
  assignment. *)

Require Import OrdersFacts.

Check compare.
Print comparison.

(* In order to prove facts, you will need the definitions from the following. *)

Include (OrderedTypeFacts MidtermSig).
Include (OrderedTypeTest MidtermSig).

(* Print OrderedTypeFacts. *)
(* Print OrderedTypeTest. *)

(* FYI, our solution only uses the following three facts, but you may use other 
   facts. *)

Check compare_gt_iff.
Check compare_lt_iff.
Check compare_eq_iff.

(* You will need to define a function [sort] that returns a sorted version 
   of the input list based on the insertion sorting algorithm above: *)
  
Fixpoint insert (x : t) (l : list t) : list t :=
  match l with
  | [] => [x]
  | y :: ys =>
      match compare x y with
      | Lt => x :: y :: ys
      | Eq => x :: y :: ys
      | Gt => y :: insert x ys
      end
  end.

Fixpoint sort_aux (l aux : list t) : list t :=
  match l with
  | [] => aux
  | x :: xs => sort_aux xs (insert x aux)
  end.

Definition sort (l : list t) : list t := sort_aux l [].

(* Remove [l] and fill in correct defintion. *)
(* 5 points *)

(* In order to do the proof, we will define an inductive type called [sorted] 
   that captures that 
  
    (1) An empty list is sorted.
    (2) A singleton list is sorted.
    (3) Given a list [l = x::y::t], in order for [l] to be sorted, it better 
        be the case that [lt x y \/ eq x y] and [sorted (y::t)].
  
   Check the definition of [lt] and [eq] below:
*)

Check lt.
Check eq.

Inductive sorted : list t -> Prop := 
    (* FILL IN *)
  | sorted_nil : sorted []
  | sorted_singleton : forall x, sorted [x]
  | sorted_cons : forall x y l,
      (lt x y \/ eq x y) ->
      sorted (y :: l) ->
      sorted (x :: y :: l).
(* 5 points *)

(* Prove the following theorem: the result of the [sort] function 
   returns a [sorted] list. *)

Lemma insert_sorted : forall x l,
  sorted l -> sorted (insert x l).
Proof.
  induction l as [|y ys IH]; intros Hsorted; simpl.
  - apply sorted_singleton.
  - destruct (compare x y) eqn:Hcomp.
    + apply sorted_cons. right. apply compare_eq_iff. assumption. assumption.
    + apply sorted_cons. left. apply compare_lt_iff. assumption. assumption.
    + inversion Hsorted; subst.
      * apply sorted_cons. left. apply compare_gt_iff. assumption. apply sorted_singleton.
      * apply IH in H2 as H3. destruct (insert x (y0::l)) eqn:Heq_inserted_list.
       apply sorted_singleton. apply sorted_cons. 
       simpl in Heq_inserted_list. destruct (compare x y0) eqn:Hcomp'.
       inversion Heq_inserted_list; subst.
       left. apply compare_gt_iff in Hcomp. assumption.
       inversion Heq_inserted_list; subst.
       left. apply compare_gt_iff in Hcomp. assumption.
       inversion Heq_inserted_list; subst.
      assumption.
      assumption.
Qed.

Lemma sort_aux_sorted : forall l acc,
  sorted acc -> sorted (sort_aux l acc).
Proof.
  induction l as [| x xs IH]; intros acc Hsorted_acc; simpl.
  - assumption.
  - apply IH.
    apply insert_sorted.
    assumption.
Qed.

Theorem sort_ok : forall l, sorted (sort l).
(* 10 points *)
Proof.
  intros l.
  unfold sort.
  apply sort_aux_sorted.
  apply sorted_nil.
Abort.

(* Of course, one also needs to prove that the sorted list is a permutation of 
   the original list. For this, we need to talk about list membership. In Coq, 
   we use `In` construct to describe list membership. For example, *)

Theorem in_list : In 3 [1;2;3].
Proof.
  simplify; equality.
Qed.

Theorem not_in_list : In 4 [1;2;3] -> False.
Proof.
  simplify; equality.
Qed.

Lemma insert_In : forall x l e, In e l \/ e = x -> In e (insert x l).
Proof.
  intros x l e H.
  induction l as [|y ys IH]; simpl in *.
  - destruct H as [HIn | Heq]; subst; auto.
  - destruct H as [HIn | Heq].
    + destruct (compare x y) eqn:Hcomp; simpl; auto. 
      destruct HIn. 
      * left. assumption.
      * right. apply IH. left. assumption.
    + subst. destruct (compare x y) eqn:Hcomp; simpl; auto.
Qed.

Lemma sort_aux_perm : forall l acc e,
  In e l \/ In e acc -> In e (sort_aux l acc).
Proof.
  induction l as [|x xs IH]; intros acc e HIn; simpl.
  - destruct HIn as [HIn_l | HIn_acc].
    + contradiction.
    + assumption.
  - apply IH.
    simpl in HIn.
    destruct HIn as [HIn_l | HIn_acc].
    + destruct HIn_l as [Heq_x | Hin_xs].
      * right. subst. apply insert_In. right. reflexivity.
      * left. assumption.
    + right. apply insert_In. left. assumption.
Qed.

(* Now to the theorem *)
Theorem sort_is_permutation : forall l e, In e l -> In e (sort l).
(* 20 points *)
Proof.
  intros l e HIn.
  unfold sort. apply sort_aux_perm. left. assumption.
Qed.

(* You may need some intermediate lemmas based on the intermediate functions 
   that you may have written down. *)