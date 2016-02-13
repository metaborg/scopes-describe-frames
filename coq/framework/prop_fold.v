Require Import List.
Import ListNotations.

(* Propositional folding over two lists *)

Inductive ForallFold2 {X Y Z : Type} (R : X -> Y -> Z -> Z -> Prop)
            : list X -> list Y -> Z -> Z -> Prop :=
  ForallFold2_nil : forall z, ForallFold2 R [] [] z z
| ForallFold2_cons : forall
    (x : X) (y : Y)
    (z z' z'' : Z)
    (xs : list X) (ys : list Y)
    (REL: R x y z z')
    (REST: ForallFold2 R xs ys z' z''),
    ForallFold2 R (x :: xs) (y :: ys) z z''.
