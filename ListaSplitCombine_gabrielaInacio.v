Require Export Coq.Lists.List.
Import ListNotations.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Lemma eq_cons : forall (X:Type) (l1 l2: list X) (x: X),
  l1 = l2 -> x :: l1 = x :: l2.
  intros X l1 l2 x.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Theorem split_combine : forall (X : Type) (Y : Type) (l1: list X) (l2: list Y),
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).
Proof.
  intros X Y l1.
  induction l1 as [| x l1' IH].
    simpl. intros l2.
    induction l2 as [| y l2'].
    reflexivity.
    intros contra.
    inversion contra. 
  destruct l2 as [| y l2'].
    simpl. intros contra.
    inversion contra.
    simpl. intros eq.
    inversion eq as [H0].
    apply IH in H0.
    rewrite H0.
    reflexivity.
Qed.

