Require Import List Arith.
Require Import FSets FSetAVL FSetFacts FSetEqProperties FSetProperties.

Ltac blast := solve [ auto |  discriminate | contradiction ].
Ltac cauto := try blast.
Lemma discr_rev {A} u (o : A) : ~ u = u++o::nil.
Proof.
  induction u.
  apply app_cons_not_nil.
  intro h;inversion h;cauto.
Qed.

Module Nat <: OrderedType.
  Definition t := nat.
  Definition eq (a b : t) := a=b.
  Definition lt (a b : t) := a<b.

  Lemma eq_refl : forall x : t, eq x x.
  Proof.
    intro;unfold eq;auto.
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

Inductive Sousmot : list nat -> list nat -> Prop :=
| sempty v : Sousmot nil v
| scons1 x u v : Sousmot u v -> Sousmot u (x::v)
| scons2 x u v : Sousmot u v -> Sousmot (x::u) (x::v).



Variable L : nat.

Variable wd : nat.
Variable uf : nat.
Variable ub : nat.
Variable rd : nat.

Variable cmem :nat.

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


Lemma eq_op_dec : forall x y : op, {x = y} + {x <> y}.
Proof.
  destruct x as (x,i);destruct x; destruct y as (y,j); destruct y;
  try (right;intro; blast);
  case (eq_nat_dec i j) as [ -> | h ];
    try (left;blast);
  right;intro h';inversion h';blast.
Qed.

Definition schedule := list op.

Definition cost (o : op) : nat :=
  match type o with
    | F => uf
    | Fb => ub
    | Wd => wd
    | Rd => rd
    | _ => 0
  end.

Definition cost_schedule (s : schedule) :=
  fold_left (fun c o => c + cost o) s 0.

Definition optimal s := forall s', cost_schedule s <= cost_schedule s'.

Lemma opt_leq s1 s2 : optimal s1 -> cost_schedule s2 <= cost_schedule s1 ->
                      optimal s2.
Proof.
  intros h1 h2 s; apply (le_trans _ (cost_schedule s1)); cauto.
Qed.


Lemma cost_unit : forall u op , cost_schedule (op::u) = cost op + cost_schedule u.
Proof.
  assert (forall u k l, fold_left (fun (c : nat) (o : op) => c + cost o) u (k + l)=
                      k + fold_left plus (map cost u) l).
  induction u;auto.
  unfold cost_schedule in *;simpl.
  intros k l;rewrite IHu;auto.
  rewrite<- plus_assoc;f_equal;auto.
  rewrite<- IHu.
  apply eq_trans with (0+fold_left plus (map cost u) (l + cost a));auto;rewrite<- IHu;auto.
  
  intros u op; unfold cost_schedule;simpl.
  replace (cost op) with (cost op+0);repeat rewrite H;auto.
  rewrite<- plus_assoc;f_equal;auto.
  simpl;replace (0) with (0+0);auto;rewrite H;auto.
Qed.

Lemma cost_rev : forall u, cost_schedule u = cost_schedule (rev u).
Proof.
  assert (forall u k, fold_left (fun (c : nat) (o : op) => c + cost o) u k=
                     fold_left plus (map cost u) k).
  induction u;auto.
  unfold cost_schedule in *;simpl.
  intros k;rewrite IHu;auto.

  assert (forall u k, fold_right (fun y x : nat => x + y) k u =
                      fold_right plus k u).
  induction u;intro;simpl;try rewrite IHu;auto with arith.
  
  intro u; unfold cost_schedule;repeat rewrite H.
  rewrite<- fold_left_rev_right.
  rewrite map_rev.
  rewrite fold_symmetric;auto with arith.
Qed.

Definition memory := NSet.t.
Definition disk := NSet.t.
Definition buffer := nat.
Definition state := (buffer * buffer * memory * disk) %type.
Definition get_top (e : state) :=
  match e with (t,b,m,d) => t end.
Definition get_bottom (e : state) :=
  match e with (t,b,m,d) => b end.
Definition get_memory (e : state) :=
  match e with (t,b,m,d) => m end.
Definition get_disk (e : state) :=
  match e with (t,b,m,d) => d end.

(*
Definition same_elts {A} l m :=
  forall a : A, In a l <-> In a m.
*)

(** It has become useless
Definition same_elts_upto i l m :=
  forall a, a < i -> (In a l <-> In a m).
*)

Definition equiv e f :=
  get_top e = get_top f
  /\ get_bottom e = get_bottom f
  /\ NSet.eq (get_memory e) (get_memory f)
  /\ NSet.eq (get_disk e) (get_disk f).

(**
Definition equiv_upto e f :=
  get_top e = get_top f
  /\ get_bottom e = get_bottom f
  /\ same_elts_upto (get_bottom e) (get_memory e) (get_memory f)
  /\ same_elts_upto (get_bottom e) (get_disk e) (get_disk f).
*)

Notation "e ≡ f" := (equiv e f) (at level 20).

Lemma equiv_refl e :
  e ≡ e.
Proof.
repeat split; auto.
Qed.

Lemma equiv_sym e f :
  e ≡ f -> f ≡ e.
Proof.
intro H. destruct H as (h0 & h1 & h2 & h3).
unfold equiv; rewrite h1 in *.
split ; [|split;[|split]];auto;apply NSet.eq_sym; auto.
Qed.

Lemma equiv_trans f e g :
  e ≡ f -> f ≡ g -> e ≡ g .
Proof.
intros (h0 & h1 & h2 & h3) (hh0 & hh1 & hh2 & hh3).
unfold equiv; rewrite h0 in *.
rewrite h1 in *; rewrite h2 in *; rewrite h3 in *; rewrite hh1 in *.
split ; [|split;[|split]];auto;apply NSet.eq_sym; auto.
Qed.


Definition size_memory e := NSet.cardinal (get_memory e).

Definition bound_memory e :=
  size_memory e <= cmem.

Definition rmv := remove (eq_nat_dec).

Definition eval_op o e : state :=
  let i := index o in
  match type o with
    | F => (i+1,get_bottom e,get_memory e,get_disk e)
    | Fb => (i,i,get_memory e, get_disk e)
    | Wm => (i,get_bottom e,NSet.add i (get_memory e),get_disk e)
    | Wd => (i,get_bottom e,get_memory e,NSet.add i (get_disk e))
    | Rm => (i,get_bottom e,get_memory e,get_disk e)
    | Rd => (i,get_bottom e,get_memory e,get_disk e)
    | Dm => (get_top e,get_bottom e,NSet.remove i (get_memory e),get_disk e)
    | Dd => (get_top e,get_bottom e,get_memory e,NSet.remove i (get_disk e))
  end.
  
Definition eval_schedule e s :=
  fold_right eval_op e s.

Definition useless e o :=
  eval_op o e ≡ e.

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

Inductive valid_schedule : state -> schedule -> Prop :=
| vempty e s : s = nil -> valid_schedule e s
| vcons e o s : valid_op (eval_schedule e s) o -> valid_schedule e s ->
                valid_schedule e (o::s).

Hint Constructors valid_schedule.

(**
We need to correct the memory thing: 
we need to have a correct size function, either 
  (i) we use sets for memory, or
  (ii) we keep using lists but we need to make sure they do not have duplicated elements.
*)

Lemma same_size_mem e f :
  e ≡ f -> size_memory e = size_memory f.
Proof.
  intros (h1 & h2 & h3 & h4).
  apply NP.Equal_cardinal;cauto.
Qed.

Lemma equiv_valid_op e f :
  e ≡ f -> (forall o, valid_op e o -> valid_op f o ).
Proof.
intros (h0 & h1 & h2 & h3) o h. unfold valid_op in *. 
destruct o as (o & i); destruct o; simpl in *;
try rewrite <- h0;try rewrite <- h1;try apply h2;try apply h3;auto.
destruct h as (h4 & h5c);
  split;
  [|replace (size_memory f) with (size_memory e);
     [|apply same_size_mem;split;[|split;[|split]]]];auto.
Qed.

Lemma equiv_eval_op e f :
  e ≡ f -> (forall o, eval_op o e ≡ eval_op o f ).
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

(*Lemma valid_prefix e :
  forall a s, valid_schedule e (a::s) -> 
     (valid_op e a /\ valid_schedule (eval_op e a) s).
Proof.
Admitted.*)


Lemma equiv_eval e f :
  e ≡ f -> (forall s, eval_schedule e s ≡ eval_schedule f s ).
Proof.
  cut (forall s e f, e ≡ f -> eval_schedule e s ≡ eval_schedule f s);
  [intros h1 h2 s;apply (h1 _ e)
  |induction s; intros e' f' h1;  unfold eval_schedule in * ; simpl;
   [|apply equiv_eval_op;apply IHs]]; assumption.
Qed.
Lemma equiv_valid e f :
  e ≡ f -> (forall s, valid_schedule e s -> valid_schedule f s ).
Proof.
  cut (forall s e f, e ≡ f -> valid_schedule e s -> valid_schedule f s);
  [ intros h1 h2 s;apply (h1 _ e)
   |induction s;
     [|intros e' f' h1 h2;inversion h2;
       [|apply vcons;
          [apply (equiv_valid_op (eval_schedule e' s));[apply equiv_eval|]|]]]];cauto.
  apply (IHs e');cauto.
Qed.

Lemma valid_app s1 s2 : forall e,
  valid_schedule e (s1 ++ s2) <->
  valid_schedule e s2 /\ valid_schedule (eval_schedule e s2) s1.
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

(*induction s1; intro e; split; intro Hvs; auto. 
SearchAbout (nil ++ _). rewrite app_nil_l. destruct Hvs. simpl in *. assumption.
rewrite <- app_comm_cons in *. inversion Hvs. 
discriminate.
apply IHs1 in H3. destruct H3.
split.
SearchAbout ((_::_)++_). 
apply vcons; auto.
unfold eval_schedule in *.
simpl. assumption.


rewrite <- app_comm_cons in *. 
destruct Hvs as (hvs1 & hvs2). inversion hvs1; auto. discriminate. apply vcons. 
assumption.
rewrite IHs1. split; auto.

 *)
Qed.

Notation "[ a , b ]" := ((a,b)::nil) (at level 50).

Inductive effacement (P : list op -> op -> Prop) :
  list op -> list op -> Prop :=
| effnil : effacement P nil nil
| effcons1 u v x : effacement P u v -> P u x ->
                   effacement P (x::u) v
| effcons2 u v x : effacement P u v -> ~ P u x ->
                   effacement P (x::u) (x::v).

Lemma invert_eff P u v :
  effacement P u v ->
  (u = nil /\ v = nil)
  \/ (exists x u1, u = x::u1 /\ effacement P u1 v /\ P u1 x)
  \/ (exists x u1 v1, u = x::u1 /\ v=x::v1 /\ effacement P u1 v1 /\ ~P u1 x).
Proof.
  intro h; induction h.
  left;auto.
  right;left;exists x;exists u;auto.
  right;right;exists x;exists u;exists v;auto.
Qed.
  
Lemma eff_cost P u v : effacement P u v -> cost_schedule v <= cost_schedule u.
Proof.
  intro h;induction h;simpl in *;auto;
  repeat rewrite cost_unit;auto with arith.
  rewrite plus_comm; apply le_plus_trans;auto.
Qed.

Lemma eff_opt P u v : effacement P u v -> optimal u -> optimal v.
Proof.
  intros h1 h2;apply eff_cost in h1;apply (opt_leq u);auto.
Qed.                                   

Lemma eff_eval (P : list op -> op -> Prop) :
  (forall u x, P u x -> forall e, useless (eval_schedule e u) x) ->
  forall u v, effacement P u v ->
              forall e, (eval_schedule e u) ≡ (eval_schedule e v).
Proof.
  intros h.
  induction u;intros;auto.
  destruct v;auto.
  simpl;repeat split;auto.
  apply invert_eff in H as [(h1 & h2)|[(x & u & h1 & h2 & h3)|(x & u & v1 & h1 & h2 & h3 & h4)]];
  simpl in *;cauto. 
  apply invert_eff in H as [(h1 & h2)|[(o & u1 & h1 & h2 & h3)|(o & u1 & v1 & h1 & h2 & h3 & h4)]];
    simpl in *;cauto.
  inversion h1.
  apply (equiv_trans ( eval_schedule e u1 )).
  unfold useless  in h;  apply (h _ _ );cauto.
  rewrite <- H1 in *;apply IHu;auto.
  rewrite  h2 in *;inversion h1;rewrite <- H1 in *;  simpl;apply equiv_eval_op;
  apply IHu;auto.
Qed.                          

Lemma eff_valid (P : list op -> op -> Prop) :
  (forall u x, P u x -> forall e, useless (eval_schedule e u) x) ->
  forall u v, effacement P u v -> 
              forall e, (valid_schedule e u) -> (valid_schedule e v).
Proof.
  intros h.
  induction u;intros;auto.
  destruct v;auto.
  simpl;repeat split;auto.
  apply invert_eff in H as [(h1 & h2)|[(x & u & h1 & h2 & h3)|(x & u & v1 & h1 & h2 & h3 & h4)]];
  simpl in *;cauto. 
  apply invert_eff in H as [(h1 & h2)|[(o & u1 & h1 & h2 & h3)|(o & u1 & v1 & h1 & h2 & h3 & h4)]];
    simpl in *;cauto.
  inversion h1;  apply IHu; rewrite H2;auto.
  rewrite H2 in *;inversion H0;cauto.

  inversion H0;cauto.
  inversion h1; rewrite <- H7 in *;rewrite H6 in *; clear H H1 H6 H7 H2; rewrite h2 in *;apply vcons.
  apply (equiv_valid_op (eval_schedule e u));cauto.
  apply (eff_eval P);cauto.

  apply IHu;cauto.
Qed.

(*
Definition no_double_write_mem_i s (i : nat) :=
  ~ (exists s1 s2 s3, s = s1 ++ [Wm,i] ++ s2 ++ [Wm,i] ++ s3
                      /\ ~ In (Dm,i) s2).

Fixpoint remove_write_mem_i s (i : nat) :=
  match s with
    | nil => nil
    | (Dm,j)::s => if beq_nat i j
                   then (Dm,j)::s
                   else (Dm,j)::(remove_write_mem_i s i)
    | (Wm,j)::s => if beq_nat i j
                   then remove_write_mem_i s i
                   else (Wm,j)::(remove_write_mem_i s i)
    | oi::s => oi::(remove_write_mem_i s i)
  end.*)


  
Lemma ndw_eff_ex :
   forall s : list op, exists s',
                         effacement
                           (fun u x => exists i, x = (Wm,i)
                                                   /\ exists u1 u2, u = u1 ++ [Wm,i] ++ u2
                                                                      /\ ~ In (Dm,i) u1) 
                           s s'.
Proof.
  induction s.
  exists nil;apply effnil.
  destruct IHs as (s' & IHs).
  set (op:=a);assert (op=a) as hop;auto.
  destruct a as (o,k); destruct o; simpl;
  try (exists (op::s');rewrite hop in *;
              apply effcons2;
              try intros (i & hx & hu);blast).
  assert  (forall u0,
             (exists u1 u2, u0 = u1 ++ (Wm, k) :: u2 /\ ~ In (Dm, k) u1)\/
             ~(exists u1 u2, u0 = u1 ++ (Wm, k) :: u2 /\ ~ In (Dm, k) u1)).
  induction u0.
  right;intros (u1 & u2 & h1 & h2); apply app_cons_not_nil in h1;auto.
  destruct IHu0 as [(u1 & u2 & h1 & h2)| h].
  case (eq_op_dec (Dm,k) a) as [<-|h].
  right;intros (u3 & u4 & h3 & h4).
  destruct u3;simpl in *;cauto.
  inversion h3.
  contradict h4;left;auto.
  left;exists (a::u1);exists u2;split;simpl.
  f_equal;auto.
  intros [ha|hu];[symmetry in ha|];cauto.
  case (eq_op_dec (Wm,k) a) as [<-|ha].
  left;exists nil;exists u0;split;auto.
  right;intros (u3 & u4 & h3 & h4).
  apply h.
  destruct u3.
  contradict ha;simpl in *;inversion h3;auto.
  exists u3; exists u4.
  inversion h3;split;[|intro;apply h4;right];auto.
  
  case (eq_op_dec (Wm,k) op) as [<-|h];
    [case (H s) as [(u1 & u2 & h1 & h2)|hp]|];
    [exists s'|exists ((Wm,k)::s')  |exists (op::s')];
  [apply effcons1;[|exists k;split];auto;
   exists u1;exists u2;auto| |];
  apply effcons2;auto.
  intros (i & h & hp');inversion h.
  rewrite H1 in *;cauto.
Qed. 
  
(*Fixpoint remove_double_write_mem s :=
  match s with
    | nil => nil
    | (Wm,i)::s =>
      (Wm,i)::(remove_write_mem_i (remove_double_write_mem s) i)
    | oi::s => oi::(remove_double_write_mem s)
  end.*)


Lemma correct_rdwm s e :
  eval_schedule e s ≡ eval_schedule e (remove_double_write_mem s).
Admitted.
Lemma valid_rdwm s e :
  valid_schedule e s ->
  valid_schedule e (remove_double_write_mem s).
Admitted.
Lemma optimal_rdwm s e :
  optimal_schedule e s ->
  optimal_schedule e (remove_double_write_mem s).
Admitted.
