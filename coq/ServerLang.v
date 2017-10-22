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

Definition Env := var -> nat.
Definition ServState: Set := Env * Prog.


Definition guest_winner (hcar door1 goat door2 car : nat) : bool :=
  negb (Nat.eqb hcar car)
  || Nat.eqb car goat
  || Nat.eqb goat door1
  || Nat.eqb car door2
  .

Definition server_eval_cmd (env: var -> nat) (cmd: Cmd) : Env :=
  match cmd with
  | call var_compute_winner v1 =>
    let winner := 
      if guest_winner (env var_hcar) (env var_door1) (env var_goat) (env var_door2) (env var_car) then
        1
      else
        0
    in (update env v1 winner)
  end
.

Fixpoint server_eval_cmds (env: Env) (cmds: list Cmd) : Env :=
  match cmds with
  | [] => env
  | cmd::cmds => server_eval_cmds (server_eval_cmd env cmd) cmds
  end.

Definition server_eval (st: ServState) (p: Packet) : (ServState * option Event) :=
  let '(env, prog) := st in
  match (prog, p) with 
  | (proc (receive expected v1) cmds (emit v2)::ms, (actual, NAT m)) =>
      if Nat.eqb expected actual then
        let env' := update env v1 m in
        let env'' := server_eval_cmds env' cmds in
        ((env'', ms), Some (NAT (env'' v2)))
      else
        (st, None)
  | ([], _) => 
        (st, None)
  end
.

End ServerSyntax.



