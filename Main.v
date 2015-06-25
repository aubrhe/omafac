Require Import List Arith.
Require Import FSets FSetAVL FSetFacts FSetEqProperties FSetProperties.
Require Import Tools Model Patterns.

Definition P00 (u2 : schedule) :=
  exists i v, u2 = (Wm,i)::v++(Wm,i)::nil /\ ~ In (Dm,i) v.

Definition f00 (u2 :schedule) := tl u2.
 
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

Lemma preserve00_tl (P : schedule -> Prop) f :
  (forall u, f u = tl u) ->
  (forall o i u, P ((o,i)::u) -> o<>Wm /\ o<> Dm) ->
  forall u2 u1 u3 : schedule,
    P u2 ->
    K00 (u1 ++ u2 ++ u3) -> K00 (u1 ++ f u2 ++ u3).
Proof.
  intros hf hP u2 u1 u3 hu2 hk00.
  apply (f_preserve_pat_tail _ P);auto;
  [intros a b
  |
  |intros a u v w h1 (i & v' & h3 & h4) h5 h6
  |intros a u v w h1 (i & v' & h3 & h4) h5 h6];
  try rewrite hf in *; simpl in *;auto;
  clear u1 u2 u3 hk00 hu2.
 
  destruct a; apply hP in h1;destruct h1 as (h1 & h2);
  destruct w;[contradict h6;auto|]; inversion h3 as ( (ho & h7) ).
  apply app_inv_tail in h7 as (u' & -> & ->);auto.
  exists i;exists (w++(o,n)::u');split;
  [rewrite app_ass ;auto|].

  intro h;apply in_app_or in h; case h as [h|[h|h]];cauto;
  [|inversion h;auto|];
  apply h4;apply in_or_app;[left|right];auto.

  destruct a; apply hP in h1;destruct h1 as (h1 & h2);
  destruct v;[contradict h6;auto|]; inversion h3 as ( (ho & h7) ).
  apply app_inv_tail in h7 as (u' & -> & ->);auto.
  exists i;exists (v++(o,n)::u');split;
  [rewrite app_ass ;auto|].
  
  intro h;apply in_app_or in h; case h as [h|[h|h]];cauto;
  [|inversion h;auto|];
  apply h4;apply in_or_app;[left|right];auto.
Qed.
  
Definition P01 (u : schedule) := exists i, u=(Dd,i)::nil.

Definition f01 (u : schedule) : schedule := tl u.

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
  apply (preserve00_tl P01);intros;auto.
  destruct H as (j & h );inversion h;split;intro;cauto.
  exists i;auto.
Qed.

Lemma P01_equiv_In u :
  pattern P01 u <-> exists i, In (Dd,i) u.
Proof.
  split;[intros (u1 & u2 & u3 & -> & i & ->)|intros (i&h)].
  exists i;apply in_or_app; right;apply in_or_app;left;left;auto. 
  apply in_split in h as (u1 & u3 & ->) ;exists u1;
  exists ((Dd,i)::nil);exists u3;split;auto;exists i;auto.
Qed.

Lemma preserve_01 P f :
  (forall u i, P u -> In (Dd,i) (f u) -> In (Dd,i) u)
  -> forall u1 u2 u3, P u2 ->
                      ~pattern P01 (u1++u2++u3) ->
                      ~pattern P01 (u1++f u2++u3).
Proof.
  intros hf u1 u2 u3 hp hk hu.
  rewrite P01_equiv_In in *.
  destruct hu as (i & h);apply in_app_or in h as [h|h].
  apply hk;exists i;apply in_or_app;left;auto.
  apply in_app_or in h as [h|h].
  apply hk;exists i;apply in_or_app;right;apply in_or_app;left;auto.
  apply hk;exists i;apply in_or_app;right;apply in_or_app;right;auto.
Qed.