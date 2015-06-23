Require Import List Arith.
Require Import FSets FSetAVL FSetFacts FSetEqProperties FSetProperties.
Require Import Tools Model Patterns.

Definition P00 (u2 : schedule) :=
  exists i v, u2 = (Wm,i)::v++(Wm,i)::nil /\ ~ In (Dm,i) v.

Definition f00 (u2 :schedule) :=
  match u2 with
    | nil => nil
    | a::v => v
  end.

Lemma red_fun_f00 :
  reducing_function P00 (fun _ => True) f00.
Proof.
  exists (length % list op);split.
  unfold mesure; apply app_length.
  intros u2 _ u3 (i & v & hu2 & hv).
  destruct u2;cauto.
  split;[|split;[split|split]];unfold f00;
  try rewrite cost_unit; auto with arith;
  inversion hu2.
  intros e h;simpl.
  split;auto.
  inversion h;cauto.
  repeat split;
  simpl;auto;try apply NP.subset_refl;
  intro h1;try (apply NP.Dec.F.add_iff;right;auto).
  rewrite NP.Dec.F.add_iff in h1; destruct h1 as [->|ha];auto.
  cut (forall i v e w, ~ In (Dm,i) v ->
                   NSet.MSet.In i (get_memory (e ⇒ (v ++ (Wm,i)::w)))).
  intros hh;apply hh;auto.
  clear o u2 u3 v hu2 hv H0 H1 e h a.
  induction v;intros e w h;simpl.
  rewrite NP.Dec.F.add_iff in *;auto.
  destruct a as (o,k);destruct o; simpl;  
  try (apply IHv;intro h';apply h;simpl;right;assumption);
  case (eq_nat_dec k i) as [->|hk].
  rewrite NP.Dec.F.add_iff in *;auto.
  rewrite NP.Dec.F.add_iff in *;right;
  apply IHv;intro h';apply h;simpl;right;assumption.
  exfalso;apply h;left;auto.
  rewrite NP.Dec.F.remove_iff in *;split;auto.
  apply IHv;intro h';apply h;simpl;right;assumption.
Qed.

Lemma dec_P00 : forall u, Decidable.decidable (P00 u).
Proof.
  intro u.
  unfold P00.
  cut (Decidable.decidable
         (exists v w,
            u=v++w
            /\ (exists v1 v2,
                  v=v1++v2
                  /\
                  (exists i,
                     v1=(Wm,i)::nil
                     /\ ~ In (Dm,i) v2
                     /\ w=(Wm,i)::nil)))).
  intros [(v & w & -> & v1 & v2 & -> & i & -> & hv2 & -> )|h].
  left;exists i; exists v2;repeat split;simpl;auto.
  right; intros (i & v & -> & hv).
  apply h; exists ((Wm,i)::v); exists ((Wm,i)::nil);
  split;auto;exists ((Wm,i)::nil);exists v;split;auto;
  exists i;repeat split;auto.

  apply app_prop_dec.
  intros v w;apply app_prop_dec.
  intros v1 v2.
  destruct v1 as [|(o & i) v1].
  right;intros (i & h1 & h2 & h3);cauto.
  destruct o;
    try (right;intros (k & h1 & h2 & h3);blast).
  destruct w as [|(o & j) w];
    try (right;intros (k & h1 & h2 & h3);blast).
  destruct o;
    try (right;intros (k & h1 & h2 & h3);blast).
  case (eq_nat_dec i j) as [->|hij];
    [|right;intros (k & h1 & h2 & h3);
      inversion h1;inversion h3;rewrite H0 in *;
      rewrite H2 in *;cauto].
  destruct v1 as [|a v1];
    try (right;intros (k & h1 & h2 & h3);blast).
  destruct w as [|b w];
    try (right;intros (k & h1 & h2 & h3);blast).
  case (in_dec eq_op_dec (Dm,j) v2) as [h|h].
  right;intros (k & h1 & h2 & h3);
      inversion h1;rewrite H0 in *;cauto.
  left;exists j;repeat split;auto.
Qed.
  
Definition K00 u := ~ pattern P00 u.

Lemma lem00 :
  (exists u : schedule, good u) ->
  exists v, good v /\ K00 v.
Proof.
  intros (u & hu).
  assert (reducing_function P00 (fun _ => True) f00) as h.
  apply red_fun_f00.
  eapply (fun_no_pattern P00 _ f00) in h.
  destruct h as (v & hp & hb & _).
  exists v; split;auto.
  eapply better_good;eauto.
  apply dec_P00.
Qed.

Definition P01 (u : schedule) := exists i, u=(Dd,i)::nil.

Definition f01 : schedule -> schedule := f00.

Definition K01 u := ~ pattern P01 u /\ K00 u.

Lemma red_fun_f01 :
  reducing_function P01 K00 f01.
Proof.
  exists (length % list op).
  split.
  unfold mesure;apply app_length.
  intros u1 u2 u3 (i & ->). 
  repeat split;auto.
  simpl.
  apply NP.subset_remove_3;apply NP.subset_refl.
  unfold K00.
  apply (f_preserve_pat_tail _ P01);intros;simpl;auto;
  [| |exists i;auto].
  destruct H as (j & h).
  inversion h.
  apply app_eq_nil in H3;destruct H3 as ( -> & ->);cauto.
  contradict H1;auto.
  destruct H as (j,h);inversion h.
  destruct H0 as (k & s & hs1 & hs2).
  rewrite H4 in *;simpl in *.
  rewrite app_comm_cons in hs1.
  apply app_inv_tail in hs1;auto.
  destruct hs1 as (z & h1 & ->).
  destruct v;[contradict H2;auto|].
  simpl in h1;inversion h1.
  exists k;exists (v++(Dd,j)::z);split;auto.
  rewrite<- app_assoc;auto.
  intro hi;apply in_app_or in hi;case hi as [hi|[hi|hi]];cauto;
  apply hs2;rewrite H5;apply in_or_app;[left|right];auto.
Qed.