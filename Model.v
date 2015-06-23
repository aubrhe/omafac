(** Here we define the computationnal model used 
    in the proof. We also prove some basic lemmas
    about this model. *)

Require Import List Arith.
Require Import FSets FSetAVL FSetFacts FSetEqProperties FSetProperties.
Require Import Tools.

(** * Constants *)
Variable L : nat.

Variable wd : nat.
Variable uf : nat.
Variable ub : nat.
Variable rd : nat.

Variable cmem :nat.

(** * Operations *)
Inductive op_type : Set :=
| F : op_type
| Fb : op_type
| Wm  : op_type
| Wd  : op_type
| Rm  : op_type
| Rd  : op_type
| Dm  : op_type
| Dd  : op_type.

Definition op := (op_type * nat)%type.

Definition type (oi : op) :=
  match oi with
    | (o,i) => o
  end.
Definition index (oi : op) :=
  match oi with
    | (o,i) => i
  end.

(** The equality of operations is decidable. *)
Lemma eq_op_dec : forall x y : op, {x = y} + {x <> y}.
Proof.
  destruct x as (x,i);destruct x; destruct y as (y,j); destruct y;
  try (right;intro; blast);
  case (eq_nat_dec i j) as [ -> | h ];
    try (left;blast);
  right;intro h';inversion h';blast.
Qed.

(** * Schedules *)
Definition schedule := list op.

(** Cost of a single operation. *)
Definition cost (o : op) : nat :=
  match type o with
    | F => uf
    | Fb => ub
    | Wd => wd
    | Rd => rd
    | _ => 0
  end.

(** Cost of a complete schedule. *)
Definition cost_schedule (s : schedule) :=
  fold_left (fun c o => c + cost o) s 0.

Notation "o $" := (cost o) (at level 20).
Notation "| s |" := (cost_schedule s) (at level 20).

(** We may define a preorder over schedules based on their cost. *)
Notation "u <$ v" := (|u| <= |v|) (at level 60).

Lemma le_cost_refl u :
  u <$ u.
Proof.
  auto.
Qed.

Lemma le_cost_trans v u w :
  u <$ v -> v <$ w -> u <$ w.
Proof.
  intros h1 h2;apply (le_trans _ (|v|));auto.
Qed.

Hint Resolve le_cost_refl le_cost_trans.

(** The cost of the empty schedule is 0. *)
Lemma cost_nil : |nil| = 0.
Proof.
  unfold cost_schedule;simpl;auto.
Qed.

(** Specification of the cost function. *)
Lemma cost_unit : forall u op , |op::u| = op$ + | u |.
Proof.
  assert (forall u k l,
            fold_left (fun (c : nat) (o : op) => c + o $) u (k + l)
            = k + fold_left plus (map cost u) l).
  induction u;auto.
  unfold cost_schedule in *;simpl.
  intros k l;rewrite IHu;auto.
  rewrite<- plus_assoc;f_equal;auto.
  rewrite<- IHu.
  apply eq_trans with (0+fold_left plus (map cost u) (l + a $));
    auto;rewrite<- IHu;auto.
  
  intros u op; unfold cost_schedule;simpl.
  replace (op$) with (op$+0);repeat rewrite H;auto.
  rewrite<- plus_assoc;f_equal;auto.
  simpl;replace (0) with (0+0);auto;rewrite H;auto.
Qed.

(** [cost_schedule] is a list homomorphism. *)
Lemma cost_app :
  mesure cost_schedule.
Proof.
  intros u v.
  induction u.
  auto.
  simpl;repeat rewrite cost_unit; rewrite<- plus_assoc;f_equal;auto.
Qed.

(** The cost of a schedule does not depend upon evaluation order. *)
Lemma cost_rev : forall u, |u| = |rev u|.
Proof.
  induction u;simpl;auto.
  rewrite cost_app.
  repeat rewrite cost_unit.
  rewrite cost_nil;rewrite IHu;auto with arith.
  rewrite plus_comm;f_equal;auto.
Qed.

(** An optimal schedule is one that is less costly that any other. *)
Definition optimal s := forall s', s <$ s'.

(** To prove the optimality of a schedule, one may simply prove 
    that it is less costly than another optimal schedule. *)  
Lemma opt_leq s1 s2 : optimal s1 -> s2 <$ s1 -> optimal s2.
Proof.
  intros h1 h2 s; apply (le_trans _ (cost_schedule s1)); cauto.
Qed.

(** * Machine states. *)
Definition storage := NSet.t.
Definition buffer := nat.
Definition state := (buffer * buffer * storage * storage) %type.
Definition get_top (e : state) :=
  match e with (t,b,m,d) => t end.
Definition get_bottom (e : state) :=
  match e with (t,b,m,d) => b end.
Definition get_memory (e : state) :=
  match e with (t,b,m,d) => m end.
Definition get_disk (e : state) :=
  match e with (t,b,m,d) => d end.

(** The equivalence of machine states. *)
Definition equiv e f :=
  get_top e = get_top f
  /\ get_bottom e = get_bottom f
  /\ NSet.eq (get_memory e) (get_memory f)
  /\ NSet.eq (get_disk e) (get_disk f).

Notation "e ≡ f" := (equiv e f) (at level 60).

(** [equiv] is reflexive. *)
Lemma equiv_refl e :
  e ≡ e.
Proof.
repeat split; auto.
Qed.

(** [equiv] is symmetric. *)
Lemma equiv_sym e f :
  e ≡ f -> f ≡ e.
Proof.
intro H. destruct H as (h0 & h1 & h2 & h3).
unfold equiv; rewrite h1 in *.
split ; [|split;[|split]];auto;apply NSet.eq_sym; auto.
Qed.

(** [equiv] is transitive. *)
Lemma equiv_trans f e g :
  e ≡ f -> f ≡ g -> e ≡ g .
Proof.
intros (h0 & h1 & h2 & h3) (hh0 & hh1 & hh2 & hh3).
unfold equiv; rewrite h0 in *.
rewrite h1 in *; rewrite h2 in *; rewrite h3 in *; rewrite hh1 in *.
split ; [|split;[|split]];auto;apply NSet.eq_sym; auto.
Qed.

Hint Resolve opt_leq equiv_refl equiv_trans equiv_sym.

(** The size of the memory of a state is the number of elements
    stored in its memory. *)
Definition size_memory e := NSet.cardinal (get_memory e).

Notation "# e" := (size_memory e) (at level 20).

(** A state has a bounded memory if the size of its memory is
    smaller than the capacity of the memory. *)
Definition bound_memory e :=
  # e <= cmem.

(** Equivalent machine states have the same size of memory. *)
Lemma same_size_mem e f :
  e ≡ f -> # e = # f.
Proof.
  intros (h1 & h2 & h3 & h4).
  apply NP.Equal_cardinal;cauto.
Qed.

(** A machine state is bigger than another if it contains all of the
    data the other has, but maybe more on disk. *)
Definition is_smaller e f :=
  get_top e = get_top f
  /\ get_bottom e = get_bottom f
  /\ NSet.eq (get_memory e) (get_memory f)
  /\ NSet.Subset (get_disk e) (get_disk f).

(** This relation is an order. *)
Lemma is_smaller_refl e f :
  e ≡ f -> is_smaller e f.
Proof.
  intros (h1 & h2 & h3 & h4).
  repeat split;auto;intros.
  apply h3;auto.
  apply h3;auto.
  intro x;apply h4.
Qed.

Lemma is_smaller_trans f e g :
  is_smaller e f -> is_smaller f g -> is_smaller e g.
Proof.
  intros (h1 & h2 & h3 & h4) (h5 & h6 & h7 & h8); repeat split;
  try rewrite h1;try rewrite h2;auto.
  intro;  rewrite<- h7;rewrite <- h3;auto.
  intro;  rewrite h3;rewrite  h7;auto.
  eapply (NP.subset_trans);[apply h4|apply h8]. 
Qed.

Lemma is_smaller_antisym e f :
  is_smaller e f -> is_smaller f e -> e ≡ f.
Proof.
  intros (h1 & h2 & h3 & h4) (h5 & h6 & h7 & h8); repeat split;auto.
  apply h3.
  apply h7.
  apply h4.
  apply h8.
Qed.

(** Related machine states have the same size of memory. *)
Lemma same_size_mem_smaller e f :
  is_smaller e f -> # e = # f.
Proof.
  intros (h1 & h2 & h3 & h4).
  apply NP.Equal_cardinal;cauto.
Qed.
  
Hint Resolve is_smaller_refl is_smaller_trans is_smaller_antisym.

(** * Evaluation of a schedule. *)
Definition rmv := remove (eq_nat_dec).

(** [eval_op o e] computes the result of executing the operation [o] 
    from the state [e]. *)
Definition eval_op o e : state :=
  let i := index o in
  match type o with
    | F => (i+1,get_bottom e,get_memory e,get_disk e)
    | Fb => (get_top e,i,get_memory e, get_disk e)
    | Wm => (get_top e,get_bottom e,
             NSet.add i (get_memory e),get_disk e)
    | Wd => (get_top e,get_bottom e,get_memory e,
             NSet.add i (get_disk e))
    | Rm => (i,get_bottom e,get_memory e,get_disk e)
    | Rd => (i,get_bottom e,get_memory e,get_disk e)
    | Dm => (get_top e,get_bottom e,
             NSet.remove i (get_memory e),get_disk e)
    | Dd => (get_top e,get_bottom e,get_memory e,
             NSet.remove i (get_disk e))
  end.

Notation "e → o" := (eval_op o e) (at level 40).

(** A schedule can be evaluated from a machine state by 
    evaluating successively each of its operations, starting 
    from the last one (right to left evaluation).*)
Definition eval_schedule e s :=
  fold_right eval_op e s.

Notation "e ⇒ s" := (eval_schedule e s) (at level 50).

(** From a state [e] the operation [o] is useless if its evaluation 
    does not modify [e]. *)
Definition useless e o :=
  e → o ≡ e.

(** Evaluating an operation from two equivalent states yields two 
    equivalent states. *)
Lemma equiv_eval_op e f :
  e ≡ f -> (forall o, e→o ≡ f→o ).
Proof.
  intros (h0 & h1& h2 & h3) (o & i); unfold eval_op; destruct o;simpl.
  repeat (split;auto).  
  repeat (split;auto).
  split;[|split;[|split]];auto;apply Equal_add; auto. 
  split;[|split;[|split]];auto;apply Equal_add; auto. 
  repeat (split;auto).
  repeat (split;auto).
  split;[|split;[|split]];auto;apply NP.Equal_remove;auto. 
  split;[|split;[|split]];auto;apply NP.Equal_remove;auto. 
Qed.

(** Evaluating a schedule from two equivalent states yields two 
    equivalent states. *)
Lemma equiv_eval e f :
  e ≡ f -> (forall s, e⇒s ≡ f⇒s ).
Proof.
  cut (forall s e f, e ≡ f -> e⇒ s ≡ f⇒ s);
  [intros h1 h2 s;apply (h1 _ e)
  |induction s; intros e' f' h1;  unfold eval_schedule in * ; simpl;
   [|apply equiv_eval_op;apply IHs]]; assumption.
Qed.

(** The evaluation can be split along a concatenation. *)
Lemma eval_app s1 s2 :
  forall e,
    e ⇒ (s1 ++ s2) = e ⇒ s2 ⇒ s1.
Proof.
  intros;unfold eval_schedule;rewrite fold_right_app;auto.
Qed.

(** Evaluation from a bigger state will yield a bigger state. *)
Lemma is_smaller_eval e f u :
  is_smaller e f -> is_smaller (e ⇒ u) (f ⇒ u).
Proof.
  intro h;
  induction u;
  simpl;auto.
  destruct IHu as (ht & hb & hm & hd).
  simpl;destruct a as (o&i);destruct o;simpl;
  repeat split;simpl;auto;
  try (intros a ha; try (rewrite NP.Dec.F.add_iff in *;
                          case ha);
       try (rewrite NP.Dec.F.remove_iff in *;
             destruct ha as (h1 & h2);split));
  auto;
  try rewrite hm;auto.
Qed.

  
(** We can define an equivalence relation over schedules based on
    the result of their evaluation from any state. *)
Definition eq_eval s1 s2 :=forall e, e ⇒ s1 ≡ e⇒s2.
Notation "s1 ⋈ s2" := (eq_eval s1 s2) (at level 60).

Lemma eq_eval_refl s : s ⋈ s.
Proof.
  intro e;apply equiv_refl.
Qed.
Lemma eq_eval_sym u v : u ⋈ v -> v ⋈ u.
Proof.
  intros h e; apply equiv_sym;auto.
Qed.
Lemma eq_eval_trans v u w : u ⋈ v -> v ⋈ w -> u ⋈ w.
Proof.
  intros h1 h2 e;apply (equiv_trans (e ⇒ v));auto.
Qed.

Hint Resolve eq_eval_refl eq_eval_sym eq_eval_trans.

Lemma eq_eval_app u v v' : v ⋈ v' -> (u++v) ⋈ (u++v').
Proof.
  intros h e.
  repeat rewrite eval_app.  
  apply (equiv_eval);auto.
Qed.  
(** * Validity of a schedule for with respect to some machine state. *)

(** Validity of a single operation from a state. *)
Definition valid_op e o : Prop :=
  let i := index o in
  match type o with
    | F => get_top e = i
    | Fb => get_top e = i /\ get_bottom e = i+1
    | Wm => get_top e = i /\ size_memory e < cmem
    | Wd => get_top e = i
    | Rm => NSet.In i (get_memory e)
    | Rd => NSet.In i (get_disk e)
    | Dm => NSet.In i (get_memory e)
    | Dd => NSet.In i (get_disk e)
  end.

Notation "e ⊩ o" := (valid_op e o) (at level 40).

(** Validity of a schedule from a state. *)
Inductive valid_schedule : state -> schedule -> Prop :=
| vempty e s : s = nil -> valid_schedule e s
| vcons e o s : (e ⇒ s) ⊩ o -> valid_schedule e s ->
                valid_schedule e (o::s).

Notation "e ⊨ s" := (valid_schedule e s) (at level 50).
Hint Constructors valid_schedule.

(** State equivalence preserves the validity of operations. *)
Lemma equiv_valid_op e f :
  e ≡ f -> (forall o, e ⊩ o -> f ⊩ o ).
Proof.
intros (h0 & h1 & h2 & h3) o h. unfold valid_op in *. 
destruct o as (o & i); destruct o; simpl in *;
try rewrite <- h0;try rewrite <- h1;try apply h2;try apply h3;auto.
destruct h as (h4 & h5c);
  split;
  [|replace (size_memory f) with (size_memory e);
     [|apply same_size_mem;split;[|split;[|split]]]];auto.
Qed.

(** State equivalence preserves the validity of schedules. *)
Lemma equiv_valid e f :
  e ≡ f -> (forall s, e ⊨ s -> f ⊨ s ).
Proof.
  cut (forall s e f, e ≡ f -> valid_schedule e s -> valid_schedule f s);
  [ intros h1 h2 s;apply (h1 _ e)
   |induction s;
     [|intros e' f' h1 h2;inversion h2;
       [|apply vcons;
          [apply (equiv_valid_op (eval_schedule e' s));[apply equiv_eval|]|]]]];cauto.
  apply (IHs e');cauto.
Qed.


(** Validity can be split along a concatenation. *)
Lemma valid_app s1 s2 : forall e,
  e ⊨ (s1 ++ s2) <->
  e ⊨ s2 /\ (e ⇒ s2) ⊨ s1.
Proof.
  induction s1;split; intro Hvs.
  rewrite app_nil_l in *;split;[|apply vempty]; cauto.
  rewrite app_nil_l; destruct Hvs; simpl in *; cauto.

  inversion Hvs;cauto;
  apply IHs1 in H3 as (h1&h2);split;
  [|apply vcons;
     [unfold eval_schedule in *;rewrite<- fold_right_app|]];cauto.
  destruct Hvs as (h1 & h2);simpl;inversion h2;cauto;apply vcons.
  unfold eval_schedule in *;rewrite fold_right_app;cauto.
  apply IHs1;auto.

Qed.

Lemma is_smaller_valid_op e f o :
  is_smaller e f -> (e ⊩ o) -> (f ⊩ o).
Proof.
  intros h1 he.
  destruct o as (o,i);destruct o;simpl in *;
  inversion he;cauto;
  unfold valid_op;simpl in *;
  destruct h1 as (h1 & h2 & h3 & h4);
  try rewrite h1 in *;
  try rewrite h2 in *;
  try rewrite <- h3 in *;
  auto.
  split;auto.
  rewrite <- (same_size_mem_smaller e _);auto.
  repeat (split;auto).
Qed.

Lemma is_smaller_valid u :
  forall e f, is_smaller e f -> (e ⊨ u) -> (f ⊨ u).
Proof.
  induction u;intros e f h1 he;auto.
  inversion he;auto.
  apply vcons.
  apply (is_smaller_valid_op (e ⇒ u));auto. 
  apply is_smaller_eval;auto.
  apply (IHu e);auto.
Qed.

(** We can build an preorder relation over schedules from their 
    validity from any state. *)
Definition le_valid u v := forall e, e⊨u -> e⊨v.
Notation "u ≤ v" := (le_valid u v) (at level 60).

Lemma le_valid_refl u : u ≤ u.
Proof.
  intros e h;auto.
Qed.

Lemma le_valid_trans v u w : u ≤ v -> v ≤ w -> u ≤ w.
Proof.
  intros h1 h2 e h3;apply h2;auto.
Qed.

Hint Resolve le_valid_refl le_valid_trans.

Lemma le_valid_app u v v' :
  v ⋈ v' -> v ≤ v' -> (u++v) ≤ (u++v').
Proof.
  intros he h e.
  repeat rewrite valid_app.
  intros (hv & hu);split;auto.
  apply (equiv_valid (e ⇒ v));auto.
Qed.  

(** A good schedule is optimal and total. *)
Definition good u :=
  optimal u
  /\ (0,L+1,NSet.empty,NSet.empty) ⊨ u
  /\ get_bottom ((0,L+1,NSet.empty,NSet.empty) ⇒ u) = 0.


(** A schedule is better than antoher if it perserves all of its good
    properties while being less costly. *)
Definition better u v :=
  v <$ u /\ (forall e, e ⊨ u ->
                       (e ⊨ v /\ is_smaller (e ⇒ u) (e ⇒ v))).
Notation "u ⊲ v" := (better u v) (at level 60).

(** Better is a preorder relation. *)
Lemma better_refl u : u ⊲ u.
Proof.
  repeat split;auto;apply NP.subset_refl.
Qed.

Lemma better_trans v u w :
  u ⊲ v -> v ⊲ w -> u ⊲ w.
Proof.
  intros (hc1 & h1) (hc2 & h2);split;eauto.
  intros e h;apply h1 in h as (h & h3);apply h2 in h as (h & h4);split;eauto.
Qed.

Lemma better_good u v :
  good u -> u ⊲ v -> good v.
Proof.
  intros (ho & hv & he) (hc & h).
  apply h in hv as (hv & (_ & h2 & _)).
  repeat split;eauto.
  rewrite <- h2;auto.
Qed.

Lemma better_valid u v :
  u ⊲ v -> u ≤ v.
Proof.
  intros (_ & h1) e h2.
  apply h1 in h2;auto;destruct h2;auto.
Qed.

Hint Resolve better_refl better_trans better_good better_valid.

