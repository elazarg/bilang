Require Import Common.

Definition var := nat.

Module ClientSyntax.

Inductive Client :=
  | await (lval: var) (i: nat)
  | send (lval: var)

  | hash (lval: var) (rval: var)

  | input (lval: var)
  | print (lval: var)
.

(* example: Monty Hall *)

Definition var_car := 0.
Definition var_door1 := 1.
Definition var_goat := 2.
Definition var_door2 := 3.
Definition var_winner := 4.
Definition var_hcar := 5.


Definition Host := [
  input var_car;
  hash  var_car var_hcar;
  send  var_hcar;
  await var_door1 1;
  print var_door1;
  input var_goat;
  send  var_goat;
  await var_door2 3;
  print var_door2;
  send  var_car;
  await var_winner 4;
  print var_winner
].

Definition Guest := [
  await var_hcar 0;
  input var_door1;
  send var_door1;
  await var_goat 2;
  input var_door2;
  send var_door2;
  await var_winner 4;
  print var_winner
].


End ClientSyntax.
