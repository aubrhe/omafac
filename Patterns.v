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

(** A reducing function with regard to [P] and [K] is a 
    function that makes some mesure strictly decrease, 
    that preserves [K], evaluation and validity, does
    not increase the cost, and converts a schedule 
    verifying [P] into one not verifying [P].
*)
Definition reducing_function
           (P K : schedule -> Prop)
           (f : schedule -> schedule) :=
  exists m,
    mesure m 
    /\ (forall u2 u1 u3 : schedule,
          P u2 ->
          (~ P (f u2))
          /\ (m (f u2) < m u2)
          /\ ((f u2) <$ u2)
          /\ (((f u2) ++ u3) ⋈ (u2++u3))
          /\ ((u2 ++ u3)≤ ((f u2)++u3))
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
         /\ v <$ u
         /\ u⋈v
         /\ u≤v
         /\ (K u -> K v).
Proof.
  intros f hdec (mes & hmes & h).
  apply (strong_induction_list mes);
    intros.
  case (destruct_pattern P hdec l) as [(u1 & u2 & u3 & hl & hp )|mot].
  apply (h _ u1 u3) in hp as (hp & hm & hc & he & hv & hd).  
  exfalso.
  apply (lt_n_0 (mes (f u2))).
  apply (lt_le_trans _ (mes u2));auto.
  rewrite <- H;rewrite hl;repeat rewrite hmes.
  rewrite plus_comm;rewrite <- plus_assoc;
  auto with arith.
  exists l;repeat split;auto.
  case (destruct_pattern P hdec l) as [(u1 & u2 & u3 & hl & hp )|mot].
  apply (h _ u1 u3) in hp as (hp & hm & hc & he & hv & hd).
  assert (mes (u1++ f u2 ++ u3) < mes l).
  rewrite hl;repeat rewrite hmes.
  apply plus_lt_compat_l; apply plus_lt_compat_r;auto.
  apply H in H0 as (v & hmot & hcost & hev & hval & hdej).
  rewrite hl in *;
    exists v; split;[|split;[|split;[|split]]];intros; auto.
  apply (le_trans _ (cost_schedule (u1 ++ f u2 ++ u3))).
  auto.
  repeat rewrite cost_app.
  apply plus_le_compat_l.
  apply plus_le_compat_r.
  auto.
  apply (eq_eval_trans (u1 ++ f u2 ++ u3));auto.
  apply eq_eval_app;auto.
  apply (le_valid_trans (u1 ++ f u2 ++ u3));auto.
  apply le_valid_app;auto.
  exists l; split;[|split;[|split]];auto.
Qed.
