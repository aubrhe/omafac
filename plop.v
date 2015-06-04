Require Import List Arith.

Variable L : nat.

Variable wd : nat.
Variable uf : nat.
Variable ub : nat.
Variable rd : nat.

Variable cmem :nat.

Inductive op : Set :=
| F : op
| Fb : op
| Wm  : op
| Wd  : op
| Rm  : op
| Rd  : op
| Dm  : op
| Dd  : op.

Definition schedule := list (op * nat).

Definition cost (o : op * nat) : nat :=
  match o with
    | (F,_) => uf
    | (Fb,_) => ub
    | (Wd,_) => wd
    | (Rd,_) => rd
    | _ => 0
  end.

SearchAbout fold_left.

Definition cost_schedule (s : schedule) :=
  fold_left (fun c o => c + cost o) s 0.

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

Definition size_memory e := length (get_memory e).

Definition rmv := remove (eq_nat_dec).

Definition eval e o i: state :=
  match o with
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
  fold_left (fun e' opi => match opi with (o,i) => eval e' o i end) s e.

Inductive valid : state -> schedule -> Prop :=
| vempty e s : s = nil -> valid e s
| vf e i s : get_top e = i ->
             valid (eval e F i) s ->
             valid e ((F,i)::s)
| vfb e i s : get_top e = i -> get_bottom e = i+1 ->
              valid (eval e Fb i) s ->
              valid e ((Fb,i)::s)
| vwm e i s : get_top e = i -> size_memory e < cmem (* \/ In i (get_memory e) *) ->
              valid (eval e Wm i) s ->
              valid e ((Wm,i)::s)
| vwd e i s : get_top e = i ->
              valid (eval e Wd i) s ->
              valid e ((Wd,i)::s)
| vrm e i s : In i (get_memory e) ->
              valid (eval e Rm i) s ->
              valid e ((Rm,i)::s)
| vrd e i s : In i (get_disk e) ->
              valid (eval e Rd i) s ->
              valid e ((Rd,i)::s)
| vdm e i s : In i (get_memory e)->
              valid (eval e Dm i) s ->
              valid e ((Dm,i)::s)
| vdd e i s : In i (get_disk e) ->
              valid (eval e Dd i) s ->
              valid e ((Dd,i)::s).

Hint Constructors valid.

Definition optimal s := forall s', cost_schedule s <= cost_schedule s'.

Lemma opt_leq s1 s2 : optimal s1 -> cost_schedule s2 <= cost_schedule s1 ->
                      optimal s2.
Proof.
  intros h1 h2 s; apply (le_trans _ (cost_schedule s1));
  [ assumption
  | apply h1].
Qed.

Lemma valid_app e s1 s2 : valid e (s1 ++ s2) <-> valid e s1 /\ valid (eval_schedule e s1) s2.
Proof.
  split;intro h.
  induction s1.
  split; auto.
  inversion h.
  rewrite<- app_comm_cons in H; inversion H.
  SearchAbout (_::(_++_) = (_ ::_) ++ _).
  destruct h.

  
Lemma no_double_write_mem e s i :
  forall s1 s2 s3,
  s = s1 ++ ((Wm,i)::nil) ++ s2 ++ ((Wm,i)::nil) ++ s3 ->
  valid e s -> optimal s ->
  ~ In (Dm,i) s2  ->
  exists s', s' = s1 ++ ((Wm,i)::nil) ++ s2 ++ s3
             /\ valid e s'
             /\ optimal s'.
Proof.
intros s1 s2 s3 h1 h2 h3 h4.
exists (s1 ++ ((Wm, i) :: nil) ++ s2 ++ s3); repeat split; auto.


Lemma no_super_write_mem e s i :
  valid e s -> optimal s -> In i (get_memory e) ->
  exists s1 s2, s = s1 ++ ((Wm,i)::nil) ++ s2 ->
                   exists s', s' = s1 ++ s2
                              /\ valid e s'
                              /\ optimal s'.
