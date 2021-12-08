Set Implicit Arguments.
Require Import List.
Import ListNotations.

(* zad_01 *)
Lemma zad_1a x y: orb (orb (negb (andb x y)) (andb (negb x) y )) (andb (negb x) (negb y) ) = negb(andb x y).
Proof.
induction x, y. 
- simpl. reflexivity.
- simpl. reflexivity.
- simpl.  reflexivity.
- simpl.  reflexivity.
Qed. 


Lemma zad_1b x y z: andb (andb (negb( andb (andb (negb x) (y)) (negb z))) 
(negb(andb (andb(x) (y)) (z))) )  ( andb (andb (x) (negb y)) (negb z) ) = andb (andb (x) (negb y)) (negb z). 
Proof. 
induction x, y ,z. 
- simpl.  reflexivity.
- simpl.  reflexivity.
- simpl.  reflexivity.
- simpl.  reflexivity.
- simpl.  reflexivity.
- simpl.  reflexivity.
- simpl.  reflexivity.
- simpl.  reflexivity.
Qed.





