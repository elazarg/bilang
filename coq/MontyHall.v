Require Import Common.
Require Import NetSem.
Require Import ServerLang.


Definition var_car := 0.
Definition var_door1 := 1.
Definition var_goat := 2.
Definition var_door2 := 3.
Definition var_winner := 4.
Definition var_hcar := 5.
Definition var_compute_winner := 6.


Definition host := 0.
Definition guest := 1.

Section S.

Definition guest_winner (env: Server.Env) : nat :=
  let eq := fun (v1 v2: nat) => Nat.eqb (env v1) (env v2) in
  let orall := List.existsb (fun x => x) in
  if orall [negb (eq var_hcar var_car); 
            eq var_car  var_goat;
            eq var_goat var_door1;
            eq var_car  var_door2]
    then 1 else 0
.

Definition receive_emit role var :=  Server.proc role var [] var.

Definition prog := [
  receive_emit host  var_hcar;
  receive_emit guest var_door1;
  receive_emit host  var_goat;
  receive_emit guest var_door2;
  receive_emit host  var_car;
  Server.proc guest 0 [Server.call_coq var_compute_winner guest_winner] var_winner
].

End S.

Section C.

Require Import ClientLang.
Import Client.
Definition mh_host : Prog := [
  input var_car;
  hash var_car var_hcar;
  send var_hcar;
  drop;
  receive var_door1;
  print var_door1;
  input var_goat;
  send var_goat;
  drop;
  receive var_door2;
  print var_door2;
  send var_car;
  receive var_winner;
  print var_winner
].

Definition mh_guest : Prog := [
  receive var_hcar;
  input var_door1;
  send var_door1;
  drop;
  receive var_goat;
  input var_door2;
  send var_door2;
  drop;
  receive var_winner;
  print var_winner
].

End C.
