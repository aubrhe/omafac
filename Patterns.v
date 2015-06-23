(** This module implements a general framework for 
    specifying patterns. Its also provides usefull
    lemmas to prove that some of those may be safely
    removed.
*)

Require Import List Arith.
Require Import FSets FSetAVL FSetFacts FSetEqProperties FSetProperties.
Require Import Tools Model.

(** A pattern is defined by a property up to context. *)
Definition pattern P (u : schedule) :=
  exists u1 u2 u3, u = u1 ++ u2 ++ u3 /\ P u2.

(** If the property defining the pattern is decidable,
    so is the pattern. *)
Lemma destruct_pattern P :
  (forall u, Decidable.decidable (P u)) ->
  forall u, Decidable.decidable (pattern P u).
Proof.
  intros h u.
  case
    (app_prop_dec u
                  (fun u1 u2 =>
                     exists u3 u4, u2=u3++u4 /\ P u3))
    as [(u1 & u2 & h1 & u3 & u4 & -> & h3)| h1].
  intros;apply app_prop_dec;auto.
  left;exists u1;exists u3;exists u4;auto.
  right;intros (u1 & u2 & u3 & h2 & h3);apply h1; exists u1;
  exists (u2++u3);split;auto.
  exists u2;exists u3;split;auto.
Qed.

(** A reducing function with regard to [P] and [K] is a function that
    given a schedule satisfying [P], will produce a schedule of
    strictly smaller mesure, while preserving [K], evaluation and
    validity, and without increasing the cost.  *)

Definition reducing_function
           (P K : schedule -> Prop)
           (f : schedule -> schedule)
  := exists m,
       mesure m
       /\ (forall u2 u1 u3 : schedule,
             P u2 ->
             (m (f u2) < m u2)
             /\ (u2 ⊲ (f u2))
             /\ (K (u1++u2++u3) -> K (u1++(f u2)++u3))).

(** If there is a reducing function for [P] and [K], then it's possible
    to remove pattern [P] while preserving [K].
    *)
Lemma fun_no_pattern
      (P K : schedule -> Prop) :
  forall f : schedule -> schedule,
    (forall u, Decidable.decidable (P u)) ->
    reducing_function P K f ->
    forall (u : schedule),
       exists v,
         ~ pattern P v
         /\ u ⊲ v
         /\ (K u -> K v).
Proof.
  intros f hdec (mes & hmes & h).
  apply (strong_induction_list mes);
    intros.
  case (destruct_pattern P hdec l) as [(u1 & u2 & u3 & hl & hp )|mot].
  apply (h _ u1 u3) in hp as (hm & hb & hd).  
  exfalso.
  apply (lt_n_0 (mes (f u2))).
  apply (lt_le_trans _ (mes u2));auto.
  rewrite <- H;rewrite hl;repeat rewrite hmes.
  rewrite plus_comm;rewrite <- plus_assoc;
  auto with arith.
  exists l;repeat (split ;auto).  
  case (destruct_pattern P hdec l) as [(u1 & u2 & u3 & hl & hp )|mot].
  apply (h _ u1 u3) in hp as (hm & (hc & hb) & hd).
  assert (mes (u1++ f u2 ++ u3) < mes l).
  rewrite hl;repeat rewrite hmes.
  apply plus_lt_compat_l; apply plus_lt_compat_r;auto.
  apply H in H0 as (v & hmot & (hcost & hbet) & hdej).
  rewrite hl in *;
    exists v; split;[|split;[|]];intros; auto.
  apply (better_trans (u1 ++ f u2 ++ u3));auto;split;auto.
  repeat rewrite cost_app.
  apply plus_le_compat_l.
  apply plus_le_compat_r.
  auto.
  intros e hval.
  rewrite valid_app in hval;destruct hval as (hval & h1).
  rewrite valid_app in hval;destruct hval as (h3 & h2).
  apply hb in h2 as (h2 & hs).
  repeat rewrite valid_app;rewrite eval_app in * ;split.
  repeat split;auto.
  eapply is_smaller_valid;[apply hs|auto].
  repeat rewrite eval_app;  apply is_smaller_eval;auto.  
  exists l; split;[|split;[|]];auto.
Qed.

Lemma pat_app_l P u v :
  pattern P u -> pattern P (v++u).
Proof.
  intros (u1 & u2 & u3 & -> & hu2).
  exists (v++u1); exists u2; exists u3;split;repeat rewrite app_ass;auto.
Qed.
Lemma pat_app_r P u v :
  pattern P u -> pattern P (u++v).
Proof.
  intros (u1 & u2 & u3 & -> & hu2).
  exists u1; exists u2; exists (u3++v);split;repeat rewrite app_ass;auto.
Qed.

Lemma f_preserve_pat (P Q : schedule -> Prop) f :
  (forall u v1 v2 u1,
     Q u ->
     f u = v1 ++ v2 ->
     P (u1++v1) ->
     exists u2 u3,
       u = u2 ++ u3/\
       P(u1++u2))
  ->
  (forall u v1 v2 u1,
     Q u ->
     f u = v1 ++ v2 ->
     P (v2++u1) ->
     exists u2 u3,
       u = u2 ++ u3/\
       P(u3++u1))
  ->
  (forall u v1 v2 v3,
     Q u ->
     f u = v1 ++ v2 ++ v3 ->
     P v2 ->
     exists u1 u2 u3,
       u = u1 ++ u2 ++ u3/\
       P u2)
  ->
  (forall u u1 u3,
     Q u ->
     P (u1++(f u)++u3) ->
     u3 <> nil ->
     u1 <> nil ->
     P (u1 ++ u ++ u3))
  ->
  forall u1 u2 u3, Q u2 ->
                   ~ pattern P (u1++u2++u3) -> ~ pattern P (u1++ f u2 ++ u3). 
Proof.
  intros h1 h2 h3 h4 u1 u2 u3 hq hp (v1 & v2 & v3 & hv & hpf).
  apply hp.
  decomp hv;
    [decomp h5;
      [decomp h7;
        [apply (h1 _ _ _ u) in h5;auto;destruct h5 as (u5 & u6 & -> & h)
        |destruct u4;
          [simpl in *;rewrite<- app_nil_end in *;
           apply (h1 u2 _ nil) in hpf;try rewrite <- app_nil_end;auto;
           destruct hpf as (u5 & u6 & -> & h)
          |destruct u;
            [rewrite app_ass in *;  simpl in *;apply (h2 u2 nil) in hpf;
             cauto;destruct hpf as (u5 & u6 & -> & h)
            |apply h4 in hpf;cauto]]]
      |
      ]
    |decomp h5;
      [decomp h7;
        [apply (h2 _ _ _ u4) in h6;auto;destruct h6 as (u5 & u6 & -> & h)
        |apply h3 in h6;auto; destruct h6 as (u5 & u6 & u7 & -> & h)]
      |
      ]
    ].
  exists v1;exists (u++u5);exists (u6++u3);
  split;repeat rewrite app_ass;auto.
  exists v1; exists (u++u5);exists (u6++v3);
  split;repeat rewrite app_ass;auto.
  exists (v1++u5); exists (u6++o::u4);exists v3;
  split;repeat rewrite app_ass;auto.   
  exists v1;exists (o0::u++u2++o::u4);exists v3;
  split;simpl;repeat rewrite app_ass;auto.
  exists v1;exists v2;exists (u0++u2++u3);
  split;repeat rewrite app_ass;auto.
  exists (u1++u5);exists (u6++u4);exists v3;
  split;repeat rewrite app_ass;auto.
  exists (u1++u5);exists u6;exists (u7++u3);
  split;repeat rewrite app_ass;auto.
  exists (u1++u2++u0);exists v2;exists v3;
  split;repeat rewrite app_ass;auto.
Qed.

Lemma f_preserve_pat_tail  (P Q : schedule -> Prop) f :
  (forall a b, f(a::b) = b) ->
  f nil = nil ->
  (forall a u v w, Q (a::u++v) -> P (w++u) -> u <> nil -> P (w++a::u)) ->
  (forall a u v w, Q (a::u) -> P (v++u++w) -> u++w <> nil -> v <> nil -> P (v++a::u++w)) ->
  forall u1 u2 u3, Q u2 ->
                   ~ pattern P (u1++u2++u3) -> ~ pattern P (u1++ f u2 ++ u3).
Proof.
  intros hcons hnil h1 h2.
  apply f_preserve_pat;intros.

  destruct u.
  exists nil;exists nil;split;simpl;auto;
  rewrite hnil in *;symmetry in H0;apply app_eq_nil in H0;destruct H0 as (-> & ->);auto.

  rewrite hcons in *;
    rewrite H0 in *.
  destruct v1.
  exists nil; exists (o::v2);split;auto.
  apply (h1 _ _ _ u1) in H;cauto.
  exists (o::o0::v1);exists v2;split;auto.
  
  destruct u.
  exists nil;exists nil;split;simpl;auto;
  rewrite hnil in *;symmetry in H0;apply app_eq_nil in H0;destruct H0 as (-> & ->);auto.

  rewrite hcons in *;rewrite H0 in *.
  exists (o::v1);exists v2;split;auto.

  destruct u.
  exists nil;exists nil;exists nil;split;simpl;auto;
  rewrite hnil in *;symmetry in H0;apply app_eq_nil in H0;destruct H0 as (-> & H0);
  apply app_eq_nil in H0;destruct H0 as (-> & ->);auto.

  rewrite hcons in *;rewrite H0 in *.
  exists (o::v1);exists v2;exists v3;split;auto.  

  destruct u.
  rewrite hnil in *;simpl in *;auto.
  rewrite hcons in *;simpl in *.
  destruct u;[destruct u3|];cauto.
  apply h2;cauto.
  
Qed.