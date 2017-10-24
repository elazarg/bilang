Require Import Common.

Definition var := nat.


Inductive ClientCmd :=
  | drop
  | receive (lval: var)
  | send (lval: var)

  | hash (lval: var) (rval: var)

  | input (lval: var)
  | print (lval: var)
.

Definition Prog := list ClientCmd.

(* example: Monty Hall *)

Definition var_car := 0.
Definition var_door1 := 1.
Definition var_goat := 2.
Definition var_door2 := 3.
Definition var_winner := 4.
Definition var_hcar := 5.


Definition Host: Prog := [
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

Definition Guest: Prog := [
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


(* Semantics *)
Definition Env := var -> nat.
Record ClState : Set := mkSt {
  Cenv: Env;
  Cprog: Prog;
  Clog_index: nat
}.

Definition client_cmd_step (env: Env) (cmd: ClientCmd) (logindex: nat) (log: option Event)
                           (env': Env) (m: option Msg) (logindex': nat)  : Prop :=
  let nop := env = env' /\ m = None in
  let assign := fun lval x => env' = update env lval x in
  let assign_arbitrary := fun lval => exists x, assign lval x in
  let deque := logindex' = 1 + logindex in
  let nodeque := logindex' = logindex in
  match cmd with
  | drop => nop /\ deque
  | receive lval => match log with
                    | Some (M_nat x) => assign lval x  /\ deque
                    | Some Empty => nop
                    | None => nop
                    end
  | send lval => env = env' /\ m = Some (M_nat (env lval)) /\ nodeque
  | input lval => m = None /\ assign_arbitrary lval /\ nodeque
  | print lval => nop /\ nodeque
  | hash lval rval => m = None /\ assign_arbitrary lval /\ nodeque
  end
.

Definition client_step' (st: ClState) (log: list Event) (st': ClState) (m: option Msg) : Prop :=
  let 'mkSt env prog logindex := st in
  let 'mkSt env' prog' logindex' := st' in
  match prog with
  | [] => False
  | cmd::cmds =>  prog' = cmds
                  /\ client_cmd_step env cmd logindex (nth_error log logindex) env' m logindex'
  end
.

Definition client_step '(st, log) '(st', m) : Prop :=
  client_step' st log st' (head m).

