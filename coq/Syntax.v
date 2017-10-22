Require Import List.
Import ListNotations.

Definition id := nat.

Module ClientSyntax.

Inductive Client :=
  | await (lval: id) (i: nat)
  | send (lval: id)

  | hash (lval: id) (rval: id)

  | input (lval: id)
  | print (lval: id)
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
  hash var_car var_hcar;
  send var_hcar;
  await var_door1 1;
  print var_door1;
  input var_goat;
  send var_goat;
  await var_door2 3;
  print var_door2;
  send var_car;
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

Module ServerSyntax.

Inductive Server :=
  | receive (i: nat) (lval: id)
  | emit (lval: id)

  | require_hash (var1 var2: id)
  | call (var1 var2: id)
.

Definition var_car := 0.
Definition var_door1 := 1.
Definition var_goat := 2.
Definition var_door2 := 3.
Definition var_winner := 4.
Definition var_hcar := 5.
Definition var_compute_winner := 6.

Definition rec_emit role var :=  [receive role var;  emit var].

Definition host := 0.
Definition guest := 1.

Definition Monty := []
++ rec_emit host  var_hcar
++ rec_emit guest var_door1
++ rec_emit host  var_goat
++ rec_emit guest var_door2
++ [
   receive host var_car;
   require_hash var_car var_hcar;
   emit var_hcar
]
++ [
  call var_compute_winner var_winner;
  emit var_winner
].

End ServerSyntax.
