(** ** Exercício 1 - Números Binários 
 Nome: Gabriela Inácio*)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia. 


(** É possível representar números naturais de forma binária como uma listas de zeros 
    (representado por B0) e uns (representado por B1). O contrutor de dados Z representa 
    a lista vázia. Por exemplo:

    
        decimal               binário                          unário
           0                       Z                              O
           1                    B1 Z                            S O
           2                B0 (B1 Z)                        S (S O)
           3                B1 (B1 Z)                     S (S (S O))
           4            B0 (B0 (B1 Z))                 S (S (S (S O)))
           5            B1 (B0 (B1 Z))              S (S (S (S (S O))))
           6            B0 (B1 (B1 Z))           S (S (S (S (S (S O)))))
           7            B1 (B1 (B1 Z))        S (S (S (S (S (S (S O))))))
           8        B0 (B0 (B0 (B1 Z)))    S (S (S (S (S (S (S (S O)))))))

  Note que para facilitar as operações a lista é definida com os bits mais significativos
  à direita. *)    


Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).
  
(** //////////////// 1.Implemente uma função que incrementa um valor binário: *)

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 n => B1 n
  | B1 n => B0 (incr n)
  end.
  
(** //////////////// 2.Implemente uma função que converta um número binário para natural: *)

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with 
  | Z => O
  | B0 n => 2 * (bin_to_nat n) 
  | B1 n => S (2 * (bin_to_nat n))
  end.


(* //////////////// 3.Faça os seguintes testes unitários: *)

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof.
  simpl.
  reflexivity.
Qed.

(** //////////////// 4.Prove as transformações definidas no seguinte diagrama:

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S


*)


Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b. induction b.
  simpl. reflexivity.
  simpl. lia. 
  simpl.
  rewrite IHb.
  lia. 
Qed.


(** Declare uma função que converta números naturais em binários: *)
Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.


(** Prove que as conversões podem ser revertidas: *)

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n.
  simpl. reflexivity.
  simpl. rewrite bin_to_nat_pres_incr.
  rewrite IHn. simpl. reflexivity.
  Qed.


Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z => Z
  | B1 n => B1 (normalize n)
  | B0 n => match normalize n with
            | Z => Z 
            | n' => B0 n'
            end
  end.
  
Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  induction b; simpl.
  - reflexivity.
  - rewrite <- (nat_bin_nat (bin_to_nat b')).
    rewrite IHb'.
    destruct (normalize b'); reflexivity.
  - rewrite <- (nat_bin_nat (bin_to_nat b')).
    rewrite bin_to_nat_normalize.
    rewrite IHb'.
    reflexivity.
Qed.
(* Pesquise sobre a necessidade da função normalize no capítulo Induction. *) 


