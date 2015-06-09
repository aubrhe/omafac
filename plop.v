Require Import List Arith.
Require Import FSets FSetAVL FSetFacts FSetEqProperties FSetProperties.
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
  intros h1 h2 s; apply (le_trans _ (cost_schedule s1));
  [ assumption
  | apply h1].
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

Definition eval_op e o : state :=
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
  fold_left eval_op s e.

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
| vcons e o s : valid_op e o -> valid_schedule (eval_op e o) s ->
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
  apply NP.Equal_cardinal;assumption.
Qed.

Lemma equiv_valid_op e f :
  e ≡ f -> (forall o, valid_op e o -> valid_op f o ).
Proof.
intros (h0 & h1 & h2 & h3) o h. unfold valid_op in *. 
destruct o as (o & i); destruct o; simpl in *.

rewrite <- h0; auto.
rewrite <- h0; rewrite <- h1; auto.
destruct h as (h4 & h5c);
  rewrite <- h0; split;
  [|replace (size_memory f) with (size_memory e);
     [|apply same_size_mem;split;[|split;[|split]]]];assumption.
rewrite <- h0;auto.
apply h2;auto.
apply h3;auto.
apply h2;auto.
apply h3;auto.
Qed.

Lemma equiv_eval_op e f :
  e ≡ f -> (forall o, eval_op e o ≡ eval_op f o ).
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

Lemma equiv_valid e f :
  e ≡ f -> (forall s, valid_schedule e s -> valid_schedule f s ).
Proof.
  cut (forall s e f, e ≡ f -> valid_schedule e s -> valid_schedule f s);
  [ intros h1 h2 s;apply (h1 _ e);assumption
  | induction s; intros e' f' h1 h2; 
    [ apply vempty;reflexivity
    | inversion h2;
      [ discriminate
      | apply vcons;
        [ apply (equiv_valid_op e')
        | apply (IHs (eval_op e' a));
          [ apply equiv_eval_op
          |
          ]
        ]
      ];assumption
    ]
  ].
(**
cut (forall s e f, e ≡ f -> valid_schedule e s -> valid_schedule f s).
intros; auto.
apply (H _ e); auto.
induction s; intros; auto.
apply vcons. 
cut (valid_op e0 a). 
apply equiv_valid_op.
exact H.
apply valid_prefix in H0; destruct H0; auto.
apply valid_prefix in H0; destruct H0; auto.
cut (eval_op e0 a ≡ eval_op f0 a). 
intro; apply IHs with (eval_op e0 a); auto.

destruct a as (o & i); destruct o; unfold eval_op in *; simpl in *.

destruct H as (h0 & h1 & h2 & h3).
try rewrite <- h0; try rewrite <- h1.
repeat split; try simpl; auto. apply h2. apply h2. apply h3. apply h3.

destruct H as (h0 & h1 & h2 & h3).
try rewrite <- h0; try rewrite <- h1.
repeat split; try simpl; auto. apply h2. apply h2. apply h3. apply h3.

destruct H as (h0 & h1 & h2 & h3).
try rewrite <- h0; try rewrite <- h1.
split. auto. split. auto. split. simpl.
absurd (exists j: nat, (In j (i::get_memory e0))/\~(In j (i::get_memory f0))).
intro.
destruct H. inversion H. inversion H2. subst.
exfalso; apply H3; constructor. auto. 
apply H4 in h2.

absurd (same_elts (i :: get_memory e0) (i :: get_memory f0)).
exists j

*)
Qed.
Lemma equiv_eval e f :
  e ≡ f -> (forall s, eval_schedule e s ≡ eval_schedule f s ).
Proof.
  cut (forall s e f, e ≡ f -> eval_schedule e s ≡ eval_schedule f s);
  [intros h1 h2 s;apply (h1 _ e)
  |induction s; intros e' f' h1;  unfold eval_schedule in * ; simpl;
   [|apply IHs;apply equiv_eval_op]]; assumption.
Qed.

Lemma valid_app s1 s2 : forall e,
  valid_schedule e (s1 ++ s2) <->
  valid_schedule e s1 /\ valid_schedule (eval_schedule e s1) s2.
Proof.
  induction s1; intro e; split; intro Hvs.
  simpl in *;split;[apply vempty;reflexivity|]; assumption.
  
  rewrite app_nil_l; destruct Hvs; simpl in *; assumption.

  rewrite <- app_comm_cons in *; inversion Hvs;
  [ discriminate
  | apply IHs1 in H3; destruct H3;split;
    [ apply vcons
    | unfold eval_schedule in *;simpl]]; assumption.

  rewrite <- app_comm_cons in *;destruct Hvs as (hvs1 & hvs2);
  inversion hvs1; auto;[discriminate|];apply vcons;
  [|rewrite IHs1; split];assumption.


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
  end.
    
Fixpoint remove_double_write_mem s :=
  match s with
    | nil => nil
    | (Wm,i)::s =>
      (Wm,i)::(remove_write_mem_i (remove_double_write_mem s) i)
    | oi::s => oi::(remove_double_write_mem s)
  end.

Lemma invert_rwmi s :
  forall s1 s2 i,
    remove_write_mem_i s i = s1 ++ s2 ->
    (*~ In (Dm,i) s1 ->*)
    (exists s3 s4, s=s3++s4 /\
                     remove_write_mem_i s3 i = s1 /\
                     remove_write_mem_i s4 i = s2)
    \/ exists s3, s=s3++s2 /\
                     remove_write_mem_i s3 i = s1.
Proof.
  induction s; intros s1 s2 i h; simpl in * .
  destruct s1;destruct s2;
  [simpl in *;left;exists nil; exists nil; repeat split;simpl
  |contradict h;apply app_cons_not_nil
  |simpl in h;discriminate
  |simpl in h;discriminate].
  set (x:=a);assert (x=a) as hx; [auto|rewrite hx in *].
  destruct a as (o,k); destruct o; simpl in h;
  try
    (destruct s1;simpl in h;
     [destruct s2;[discriminate
                  |inversion h;left;exists nil; exists (x::s);
                   repeat split;simpl]
     |inversion h;
       apply IHs in H1 as [(s3 & s4 & hs & hs3 & hs4)|(s3 & hs & hs3)]];
     [left;exists (x::s3); exists s4;repeat split;simpl;
      [f_equal|f_equal|]
     |right;exists (x::s3); split;simpl;
      [f_equal|f_equal]];assumption).
  case (eq_nat_dec i k) as [-> |].
  rewrite <- beq_nat_refl in h;
    apply IHs in h as [(s3 & s4 & hs & hs3 & hs4)|(s3 & hs & hs3)];
    [left;exists (x::s3); exists s4;repeat split;simpl;
     [f_equal|rewrite <- beq_nat_refl|]
    |right;exists (x::s3); split;simpl;
     [f_equal|rewrite <- beq_nat_refl]];assumption.

  replace (beq_nat i k) with false in h;
    [|symmetry;apply beq_nat_false_iff;assumption].
  destruct s1;simpl in h.
  destruct s2;[discriminate
                    |inversion h;left;exists nil; exists (x::s);
                     repeat split;simpl];
  replace (beq_nat i k) with false;
    [|symmetry;apply beq_nat_false_iff;assumption];reflexivity.
  inversion h.
  apply IHs in H1 as [(s3 & s4 & hs & hs3 & hs4)|(s3 & hs & hs3)];
    [left|right].
  exists (x::s3);exists s4;repeat split;simpl;
  [f_equal
  |replace (beq_nat i k) with false;
    [f_equal
    |symmetry;apply beq_nat_false_iff]|];
  assumption.
  exists (x::s3); split;simpl;
  [f_equal
  |replace (beq_nat i k) with false;
    [f_equal
    |symmetry;apply beq_nat_false_iff]];
  assumption.
  case (eq_nat_dec i k) as [-> |].
  rewrite <- beq_nat_refl in h.
  destruct s1.
  right; exists nil;split;[assumption|reflexivity].
  right; exists (x::s1); split;[|rewrite hx; simpl;rewrite <- beq_nat_refl]; simpl in *;inversion h;f_equal.
  replace (beq_nat i k) with false in h;
    [|symmetry;apply beq_nat_false_iff;assumption].
  destruct s1;simpl in h.
  destruct s2;[discriminate
                    |inversion h;left;exists nil; exists (x::s);
                     repeat split;simpl];
  replace (beq_nat i k) with false;
    [|symmetry;apply beq_nat_false_iff;assumption];reflexivity.
  inversion h.
  apply IHs in H1 as [(s3 & s4 & hs & hs3 & hs4)|(s3 & hs & hs3)];
    [left|right].
  exists (x::s3);exists s4;repeat split;simpl;
  [f_equal
  |replace (beq_nat i k) with false;
    [f_equal
    |symmetry;apply beq_nat_false_iff]|];
  assumption.
  exists (x::s3); split;simpl;
  [f_equal
  |replace (beq_nat i k) with false;
    [f_equal
    |symmetry;apply beq_nat_false_iff]];
  assumption.

Qed.

Lemma no_dwm_rdwmi s :
  forall i j,
    no_double_write_mem_i s i ->
    no_double_write_mem_i (remove_write_mem_i s j) i.
Proof.
  assert (forall i s1 s2,remove_write_mem_i s1 i <> (Wm,i)::s2) as lem1.
  induction s1 ;intros s2 h.
  simpl in h; discriminate.
  destruct a as (o,k); destruct o; simpl in h; try
                                                   discriminate.
  case (eq_nat_dec i k) as [ -> | ];
  [rewrite <- beq_nat_refl in *
  |replace (beq_nat i k) with false in *;
    [|symmetry;apply beq_nat_false_iff;assumption]];
  inversion h;[apply (IHs1 s2);assumption
              |symmetry in H0;contradiction].  
  case (eq_nat_dec i k) as [ -> | ];
  [rewrite <- beq_nat_refl in *
  |replace (beq_nat i k) with false in *;
    [|symmetry;apply beq_nat_false_iff;assumption]];
  discriminate.

  assert (forall op k s1,
           (remove_write_mem_i s1 k)= ->
            In op s1) 
    as lem2.
  assert (forall op k s1,
            In op (remove_write_mem_i s1 k) ->
            In op s1) 
    as lem2.
  intros op i;induction s1;intro h;auto;
  destruct a as (o,l); destruct o; simpl in *;
  try (simpl;case (eq_nat_dec i l) as [ -> | ];
    try (rewrite <- beq_nat_refl in *);
    try (replace (beq_nat i l) with false in *);
    try (symmetry;apply beq_nat_false_iff;assumption));
  try case h as [<-|h];
  try (left;reflexivity);
  try (right;assumption);
  try (right;apply IHs1;assumption).

(*  assert (forall i k s1,
             In (Dm,i) s1 ->
             In (Dm,i)(remove_write_mem_i s1 k))
    as lem3.*)
  intros i j hs (s1 & s2 & s3 & h1 & h3).
  apply invert_rwmi in h1 
    as [(s4 & s5 & hs' & hs4 & hs5) | (s4 & hs' & hs4)].
  apply invert_rwmi in hs5
    as [(s6 & s7 & -> & hs6 & hs7) | (s6 & -> & hs6)].
  apply invert_rwmi in hs7
    as [(s8 & s9 & -> & hs8 & hs9) | (s8 & -> & hs8)].
  apply invert_rwmi in hs9
    as [(s10 & s11 & -> & hs10 & hs11) | (s10 & -> & hs10)].
  
  replace s6 with ([Wm,i]) in *.
  replace s10 with ([Wm,i]) in *.

  apply hs;exists s4; exists s8; exists s11.
  split;[assumption|rewrite (lem2 _ j); rewrite hs8;assumption].
  destruct s10.
  simpl in hs10;discriminate.
  
  destruct s6;try (simpl in *;discriminate).
  
  
  destruct s5;try (simpl in *;discriminate).
  destruct p as (o,k); destruct o; simpl in hs5; try
                                                   discriminate.
  case (eq_nat_dec j k) as [-> | ]; 
  [rewrite <- beq_nat_refl in *
  |replace (beq_nat j k) with false in *;
    [inversion hs5|symmetry;apply beq_nat_false_iff;assumption]].
  replace ((Wm, i) :: s2 ++ (Wm, i) :: s3) with
  (((Wm, i) :: s2) ++ (Wm, i) :: s3) in hs5;[|simpl;reflexivity]. 
  apply invert_rwmi in hs5 
    as [(s6 & s7 & -> & hs6 & hs7) | (s6 & -> & hs6)];
  destruct s6;try (simpl in *;discriminate).
  destruct p as (o,l); destruct o; simpl in hs6; try
                                                   discriminate.
  case (eq_nat_dec k l) as [ -> | h];
  [rewrite <- beq_nat_refl in *
  |replace (beq_nat k l) with false in *;
    [inversion hs6|symmetry;apply beq_nat_false_iff;assumption]].

  apply hs; exists s4;exists nil; exists (s6 ++ s7).
split;simpl in *;[|].

(*  induction s;
  intros i j h  (s1 & s2 & s3 & h1 & h3).
  apply (app_cons_not_nil s1 (s2 ++ (Wm, i) :: s3) (Wm,i));
    simpl in h1;assumption.
 apply invert_rwmi in h1 as [(s4 & s5 & hs & hs1 & hs2)
                            | (s4 & hs & hs1)].*)
  
  intros i j h(*  (s1 & s2 & s3 & h1 & h3).
  apply h*) .
  induction s; intros (s1 & s2 & s3 & h1 & h3).
  apply (app_cons_not_nil s1 (s2 ++ (Wm, i) :: s3) (Wm,i));
    unfold no_double_write_mem_i in *; simpl in h1; auto.
  assert (no_double_write_mem_i s i) as hs;
    [intros (ss1 & ss2 & ss3 & hh1 & hh3);apply h;
     exists (a::ss1);exists ss2;exists ss3;split;
     [simpl;f_equal|];assumption| ].
  
  destruct a as (o,k); destruct o; simpl in h1;
  try (apply IHs in hs;destruct s1 as [|(o & l)];
       [discriminate|];
       simpl in h1;inversion h1;apply hs;
       exists s1;exists s2;exists s3;split;assumption).
  case (eq_nat_dec j k) as [-> |].
  rewrite <- beq_nat_refl in h1.
  apply IHs in hs; apply hs; exists s1;exists s2;exists s3;split;
  assumption.
  replace (beq_nat j k) with false in h1;
    [|symmetry;apply beq_nat_false_iff;assumption].
  destruct s1 as [|(o & l)].
  simpl in h1.
  inversion h1.
  apply invert_rwmi in H1 as [(s4 & s5 & hss & hs1 & hs2)
                            | (s4 & hss & hs1)].
  apply hs; exists nil;exists (remove_write_mem_i s2 j);exists (remove_write_mem_i s3 j).
  split; [simpl|].
  apply hs; exists nil;exists s2;exists s3.

  [discriminate|];
       simpl in h1;inversion h1;apply hs;
       exists s1;exists s2;exists s3;split;assumption.
Qed.
  
Lemma no_dwm_rdwm s :
  forall i,
    no_double_write_mem_i (remove_double_write_mem s) i.
Proof.
  induction s; unfold no_double_write_mem_i in *.
  intros i (s1 & s2 & s3 & h1 & h3);simpl in h1.
  apply (app_cons_not_nil s1 (s2 ++ (Wm, i) :: s3) (Wm,i)); auto.
  intros i (s1 & s2 & s3 & h1 & h3).
  destruct a as (o,j); destruct o; simpl in h1;
  try 
    (destruct s1 as [|(o & k)];
     [discriminate|destruct o;simpl in h1;try discriminate;inversion h1];
     apply (IHs i);exists s1; exists s2; exists s3;split;auto).
  case (eq_nat_dec i j) as [<-| h].
  Focus 2.
  destruct s1 as [|(o & k)];  simpl in h1; inversion h1.
  apply h; symmetry;assumption.
  apply (IHs i);exists s1; exists s2; exists s3;split;auto.

  [ 
       |destruct o;simpl in h1;try discriminate;inversion h1];
       apply (IHs i);exists s1; exists s2; exists s3;split;auto.

  [|destruct s1 as [|(o & k)];  
       [simpl in h1; inversion h1; apply h; symmetry;assumption
       |destruct o;simpl in h1;try discriminate;inversion h1];
       apply (IHs i);exists s1; exists s2; exists s3;split;auto].

Qed.


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
