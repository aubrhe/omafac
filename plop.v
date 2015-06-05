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

Definition equiv e f :=
  get_top e = get_top f
  /\ get_bottom e = get_bottom f
  /\ same_elts (get_memory e) (get_memory f)
  /\ same_elts (get_disk e) (get_disk f).

Notation "e ≡ f" := (equiv e f) (at level 20). 

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


Lemma valid_app e s1 s2 :
  valid_schedule e (s1 ++ s2) <->
  valid_schedule e s1 /\ valid_schedule (eval_schedule e s1) s2.
Proof.
Admitted.

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
  valid_schedule e s ->
  valid_schedule e (remove_double_write_mem s).
Admitted.
Lemma no_dwm_rdwm s :
  forall i,
    no_double_write_mem_i (remove_double_write_mem s) i. 
Admitted.
