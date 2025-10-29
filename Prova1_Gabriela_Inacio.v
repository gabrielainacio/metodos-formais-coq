(* Primeira Prova de Métodos Formais 13/10/2025 
   Nome: Gabriela da Silva Inácio                                       *)

(* Deve ser postado um unico arquivo, todas as declarações devem ser feitas nesse arquivo,
   não deve ser importado nenhum módulo adicional. *)

Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(** Questão 1 Prove que todo número natural multiplicado por 2 é par.*)

Search mult PeanoNat.Nat.even.
(*PeanoNat.Nat.even_mul:
  forall n m : nat,
  PeanoNat.Nat.even (n * m) = (PeanoNat.Nat.even n || PeanoNat.Nat.even m)%bool*)


Theorem evenb_2 : forall n:nat,
  evenb (2 * n) = true.
Proof.
  intros n. 
  induction n as [ | n' IHn']. 
  - simpl. 
  reflexivity.
  - rewrite PeanoNat.Nat.even_mul.
    reflexivity.
Qed.

(** Questão 2 Prove que se um número é par seu sucessor é impar.*)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Search S PeanoNat.Nat.even.
(*PeanoNat.Nat.even_succ_succ: forall n : nat, PeanoNat.Nat.even (S (S n)) = PeanoNat.Nat.even n
PeanoNat.Nat.even_succ: forall n : nat, PeanoNat.Nat.even (S n) = PeanoNat.Nat.odd n*)

Theorem even_S_odd : forall n, 
  evenb n = oddb (S n).
Proof.
  intros n.
  unfold oddb.
  induction n as [ | n' IHn'].
  - simpl. 
  reflexivity.
  - rewrite PeanoNat.Nat.even_succ. 
  rewrite PeanoNat.Nat.even_succ_succ.
  reflexivity.
Qed.

(** Questão 3 Prove que a função reverso é distributiva em ralação a concatenação.*)

Search (_ ++ []).

(* lemas auxi *)
Lemma app_nil_end : forall (X:Type) (l:list X),
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [|h t IH].
  - reflexivity.
  - simpl. 
  rewrite IH. 
  reflexivity.
Qed.

Lemma app_ass : forall (X:Type) (l1 l2 l3:list X),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros X l1 l2 l3.
  induction l1 as [|h t IH].
  - reflexivity.
  - simpl. 
  rewrite IH. 
  reflexivity.
Qed.


Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1 as [|x xs IH].
  - simpl. 
    rewrite app_nil_end.
    reflexivity.
  - simpl. 
    rewrite IH.
    rewrite app_ass.
    reflexivity.
Qed.

(** Questão 4 - Prove que se uma função f é involutiva aplicar a composição de f em
uma lista resulta na própria lista. *)

Definition compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Notation "g (.) f" := (compose g f)
                     (at level 5, left associativity).
Definition involutive {A : Type} (f : A -> A) :=
  forall x: A, f (f x) = x.

(* -------------------------------------------*)

(* lema auxiliar:*)

Lemma f_f_a_involutive: forall (A: Type) (f : A -> A) (a : A),
  involutive f -> f (.) f a = a.
Proof.
  intros. 
  unfold compose. 
  rewrite H. 
  reflexivity.
Qed.


Theorem involutive_f_map : forall (A : Type) (f : A -> A) (l:list A), 
  involutive f -> map f (.) f l = l.
Proof.
  intros X f l H. 
  induction l.
  - simpl. reflexivity.
  - simpl. 
  rewrite IHl. 
  rewrite f_f_a_involutive. 
  reflexivity.
    + apply H. 
Qed.