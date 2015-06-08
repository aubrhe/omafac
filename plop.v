Require Import List Arith.

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

Definition memory := (list nat) %type.
Definition disk := list nat.
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

Definition same_elts {A} l m :=
  forall a : A, In a l <-> In a m.


(** It has become useless
Definition same_elts_upto i l m :=
  forall a, a < i -> (In a l <-> In a m).
*)

Definition equiv e f :=
  get_top e = get_top f
  /\ get_bottom e = get_bottom f
  /\ same_elts (get_memory e) (get_memory f)
  /\ same_elts (get_disk e) (get_disk f).

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
 repeat split; intros; auto;
 [ apply h2
 | apply h2
 | apply h3
 | apply h3]; auto.
Qed.

Lemma equiv_trans f e g :
  e ≡ f -> f ≡ g -> e ≡ g .
Proof.
intros (h0 & h1 & h2 & h3) (hh0 & hh1 & hh2 & hh3).
unfold equiv; rewrite h0 in *.
rewrite h1 in *; rewrite hh1 in *.
repeat split; auto; intros. 
apply hh2; auto; apply h2; auto.
apply h2; auto; apply hh2; auto.
apply hh3; auto; apply h3; auto.
apply h3; auto; apply hh3; auto.
Qed.


Definition size_memory e := length (get_memory e).

Definition rmv := remove (eq_nat_dec).

Definition eval_op e o : state :=
  let i := index o in
  match type o with
    | F => (i+1,get_bottom e,get_memory e,get_disk e)
    | Fb => (i,i,get_memory e, get_disk e)
    | Wm => (i,get_bottom e,i::(get_memory e),get_disk e)
    | Wd => (i,get_bottom e,get_memory e,i::(get_disk e))
    | Rm => (i,get_bottom e,get_memory e,get_disk e)
    | Rd => (i,get_bottom e,get_memory e,get_disk e)
    | Dm => (get_top e,get_bottom e,rmv i (get_memory e),get_disk e)
    | Dd => (get_top e,get_bottom e,get_memory e,rmv i (get_disk e))
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
    | Rm => In i (get_memory e)
    | Rd => In i (get_disk e)
    | Dm => In i (get_memory e)
    | Dd => In i (get_disk e)
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
  same_elts (get_memory e) (get_memory f) -> size_memory e = size_memory f.
Proof.
Admitted.

Lemma equiv_valid_op e f :
  e ≡ f -> (forall o, valid_op e o -> valid_op f o ).
Proof.
intros (h0 & h1 & h2 & h3) o h. unfold valid_op in *. 
destruct o as (o & i); destruct o; simpl in *.

rewrite <- h0; auto.
rewrite <- h0; rewrite <- h1; auto.
rewrite <- h0. 
cut (size_memory e = size_memory f). intro. rewrite <- H. exact h. 
apply same_size_mem; exact h2.
rewrite <- h0; auto.
apply h2; auto.
apply h3; auto.
apply h2; auto.
apply h3; auto.
Qed.

Lemma valid_prefix e :
  forall a s, valid_schedule e (a::s) -> 
     (valid_op e a /\ valid_schedule (eval_op e a) s).
Proof.
Admitted.

Lemma equiv_valid e f :
  e ≡ f -> (forall s, valid_schedule e s -> valid_schedule f s ).
Proof.
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
cut (e0 ≡ f0 -> eval_op e0 a = eval_op f0 a).
intros. apply H2 in H. rewrite <- H; auto.

clear.
intro H; destruct H as (h0 & h1 & h2 & h3).
destruct a as (o & i); destruct o; unfold eval_op; simpl in *.
try rewrite h0; try rewrite h1; try rewrite h2; try rewrite h3; auto.

Qed.

Lemma equiv_eval e f :
  e ≡ f -> (forall s, eval_schedule e s ≡ eval_schedule f s ).
Proof.
Admitted.


Lemma valid_app s1 s2 : forall e,
  valid_schedule e (s1 ++ s2) <->
  valid_schedule e s1 /\ valid_schedule (eval_schedule e s1) s2.
Proof.
induction s1; intro e; split; intro Hvs; auto. 
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
Lemma no_dwm_rdwm s :
  forall i,
    no_double_write_mem_i (remove_double_write_mem s) i. 
Admitted.
