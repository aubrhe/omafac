(** This module contains a set of basic definitions
    that will be of use but do not depend upon the  
    specifics of the problem at hand.               *)
(** ---- *)


Require Import List Arith.
Require Import FSets FSetAVL FSetFacts FSetEqProperties FSetProperties.

(** * Tactics *)
Ltac blast := solve [ auto |  discriminate | contradiction ].
Ltac cauto := try blast.

(** * Sets *)

Module Nat <: OrderedType.
  Definition t := nat.
  Definition eq (a b : t) := a=b.
  Definition lt (a b : t) := a<b.

  Lemma eq_refl : forall x : t, eq x x.
  Proof.
    intro; unfold eq; auto.
  Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    intro;unfold eq;auto.
  Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    intros x y z h h';unfold eq in *; rewrite h in *;auto.
  Qed.

  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z :=
    lt_trans.

  Definition lt_not_eq : forall x y : t, lt x y -> ~ eq x y :=
    NPeano.Nat.lt_neq.
  
  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    SearchAbout ({ _ } +  { _ } + { _ } ).
    intros x y; case (lt_eq_lt_dec x y) as [[h|h]|h];
    [apply LT
    |apply EQ
    |apply GT];auto.
  Qed.
  Definition eq_dec := eq_nat_dec.
End Nat.

Module NSet := FSetAVL.Make(Nat).
Module NF := FSetFacts.Facts NSet.
Module NP := FSetProperties.Properties NSet.

Lemma Equal_add : forall x s s', NSet.eq s s' ->
                                 NSet.eq (NSet.add x s) (NSet.add x s').
Proof.
  intros x s s' he.
  apply NP.Add_Equal;simpl; intro y;
  case (eq_nat_dec x y) as [->|h];split;intro h';
  [left
  |apply NSet.add_1
  |right;apply he;apply NSet.add_3 in h'
  |case h' as [->|h'];
    [absurd (y = y)
    |apply NSet.add_2;apply he]
  ]; auto.
Qed.

(** * Lists *)
Lemma strong_induction :
  forall n P,
    P 0 -> (forall n, (forall m, m<n -> P m) -> P n)
    -> P n.
Proof.
  cut (forall n P, (forall k, k <= 0 -> P k) ->
                   (forall n, (forall m, m <= n -> P m)
                              -> (forall m, m<= S n -> P m))
                ->  (forall m, m<= n -> P m)).
  intros h n P p0 hind.
  apply (h n);auto.
  intros k hk;apply le_n_0_eq in hk as <-;auto.
  intros m hind2 k hk.
  apply hind;intros l hl.
  apply hind2;
  apply lt_n_Sm_le;apply (lt_le_trans _ k);auto.
  
  intros n P p0 hind.
  induction n.
  intros;auto.
  apply hind;auto.
Qed.

Lemma strong_induction_list {A}  :
  forall f (P : A -> Prop), (forall l, f l = 0 -> P l) ->
            (forall l, (forall m, f m < f l -> P m) -> P l)
            -> forall l, P l.
Proof.
  intros f P h0 hind l; set (ln := f l);
  assert (f l = ln) as hln; auto.
  cut (forall l, f l = ln -> P l).
  intros h1;auto.
  apply (strong_induction ln).
  apply h0.
  intros n hi m hm.
  apply hind.
  intros k hk; apply (hi (f k)).
  rewrite <- hm;auto.
  auto.
Qed.

Lemma app_prop_dec {A} :
  forall (u : list A) P,
  (forall u1 u2, Decidable.decidable (P u1 u2)) ->
    Decidable.decidable (exists u1 u2, u = u1 ++ u2 /\ P u1 u2).
Proof. 
  induction u;intros P hd.
  case (hd nil nil) as [h|h].
  left;exists nil;exists nil;auto.
  right;intros (u1 & u2 & hu & hp).
  destruct u1;destruct u2; cauto.
  case (IHu (fun u1 u2 => P (a::u1) u2)) as [(u1 & u2 & hu & hp)|h].  
  intros u1 u2;apply hd.
  left;exists (a::u1); exists u2;split.
  simpl;f_equal;auto.
  auto.
  case (hd nil (a::u)) as [hnil|hnil].
  left;exists nil;exists (a::u);split;auto.
  right;intros (u1 & u2 & hu & hp).
  destruct u1;simpl in *.
  rewrite hu in *;cauto.
  apply h;exists u1;exists u2.
  inversion hu;auto.
Qed.

(** A mesure is just a list homomorphism. *)
Definition mesure {A} mes :=
  (forall u1 u2 : list A, mes (u1 ++ u2) = mes u1 + mes u2).

(** Usefull thing *)
Lemma inv_rev {A} (u1 u2 : list A) (o1 o2 : A) :
  u1++o1::nil = u2++o2::nil -> u1 = u2 /\ o1 = o2.
Proof.
  intro h.
  assert (rev (u1++o1::nil) = rev (u2++o2::nil)) as hr.
  rewrite h;auto.
  repeat rewrite rev_unit in hr;inversion hr.
  rewrite <- (rev_involutive u1);
  rewrite <- (rev_involutive u2);rewrite H1;auto.
Qed.

Lemma decomposition {A} : forall u1 u2 u3 u4 : list A, u1++u2 = u3++u4 -> 
exists u5, (u1=u3++u5 /\ u4=u5++u2) \/ (u3=u1++u5 /\ u2=u5++u4).
Proof.
induction u1.
intros; exists u3; right;split; simpl; auto.
destruct u3.
intros; exists (a::u1); left;split; simpl; auto.
intros.
repeat rewrite<- app_comm_cons in *.
inversion H.
rewrite<- H1 in *.
apply IHu1 in H2.
destruct H2.
exists x; case H0;intros;destruct H2;
[left|right]; rewrite H2;rewrite H3; auto.
Qed.

Ltac decomp h :=
let x := fresh "u" in
let h0 :=fresh "h" in
let h1 := fresh "h" in
let h2 := fresh "h" in
case (decomposition _ _ _ _ h); intros x h0; case h0; clear h0; intro h1;
destruct h1 as (h1,h2); rewrite h1 in *;rewrite h2 in *;
simpl in *;clear h.
