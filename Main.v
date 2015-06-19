Require Import List Arith.
Require Import FSets FSetAVL FSetFacts FSetEqProperties FSetProperties.
Require Import Tools Model Patterns.

Definition ppt1 (u2 : schedule) :=
  exists i v, u2 = (Wm,i)::v++(Wm,i)::nil /\ ~ In (Dm,i) v.

Definition pat1 := pattern ppt1.

Definition f1 (u2 :schedule) :=
  match u2 with
    | nil => nil
    | a::v => v
  end.
