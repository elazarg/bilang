Require Import Common.


Definition var := nat.

Module ServerSyntax.

Inductive Receive :=
  | receive (i: nat) (lval: var)
.

Inductive Emit :=
  | emit (lval: var)
.

Inductive Cmd :=
  | call (nat var2: var)
.

Inductive Method :=
  | proc (r: Receive) (cmds: list Cmd) (e: Emit)
.

Definition Prog := list Method.

Definition var_car := 0.
Definition var_door1 := 1.
Definition var_goat := 2.
Definition var_door2 := 3.
Definition var_winner := 4.
Definition var_hcar := 5.
Definition var_compute_winner := 6.

Definition rec_emit role var :=  proc (receive role var) [] (emit var).

Definition host := 0.
Definition guest := 1.

Definition Monty := [
  rec_emit host  var_hcar;
  rec_emit guest var_door1;
  rec_emit host  var_goat;
  rec_emit guest var_door2;
  proc (receive host var_car) [] (emit var_hcar);
  proc (receive guest 0) [call var_compute_winner var_winner]  (emit var_winner)
].

Definition ServState := var -> nat.


Definition guest_winner (hcar door1 goat door2 car : nat) : bool :=
  negb (Nat.eqb hcar car)
  || Nat.eqb car goat
  || Nat.eqb goat door1
  || Nat.eqb car door2
  .

Definition server_eval_cmd (st: ServState) (cmd: Cmd) : ServState :=
  match cmd with
  | call var_compute_winner v1 =>
    let winner := 
      if guest_winner (st var_hcar) (st var_door1) (st var_goat) (st var_door2) (st var_car) then
        1
      else
        0
    in (update st v1 winner)
  end
.

Fixpoint server_eval_cmds (st: ServState) (cmds: list Cmd) : ServState :=
  match cmds with
  | [] => st
  | cmd::cmds => server_eval_cmds (server_eval_cmd st cmd) cmds
  end.

Definition server_eval (st: ServState) (p: Packet) (m: Method)  : (ServState * option Event) :=
  match (m, p) with 
  | (proc (receive expected v1) cmds (emit v2), (actual, NAT m)) =>
      if Nat.eqb expected actual then
        let st' := update st v1 m in
        let st'' := server_eval_cmds st' cmds in
        (st'', Some (NAT (st'' v2)))
      else
        (st, None)
  end
.

End ServerSyntax.



