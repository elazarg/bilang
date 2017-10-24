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


(* Semantics *)
Definition Env := var -> nat.
Record ClState : Set := mkSt {
  Cenv: Env;
  Cprog: Prog;
  Clog_index: nat
}.

Section X.

Variables (env: Env) (n: nat) (log: option Event).

(* As defined here, this requires FunctionalExtensionality on update env *)
Inductive client_cmd_step : ClientCmd -> Env * option Msg * nat -> Prop :=
  | is_drop : client_cmd_step drop (env, None, S n)
  | is_receive : forall lval x, log = (Some (M_nat x)) ->
                client_cmd_step (receive lval) ((update env lval x), None, S n)
  | is_send : forall lval,
                client_cmd_step (send lval) (env, Some (M_nat (env lval)), n)
  | is_hash : forall lval rval,
                client_cmd_step (hash lval rval) ((update env lval rval), None, n)
  | is_print : forall lval,
                client_cmd_step (print lval) (env, None, n)
  | is_input : forall lval x,
                client_cmd_step (input lval) ((update env lval x), None, n)
.

End X.

Definition client_step' (st: ClState) (log: list Event) (st': ClState) (m: option Msg) : Prop :=
  let 'mkSt env prog logindex := st in
  let 'mkSt env' prog' logindex' := st' in
  match prog with
  | [] => False
  | cmd::cmds =>  prog' = cmds
                  /\ client_cmd_step env logindex (nth_error log logindex) cmd (env', m, logindex')
  end
.

Definition client_step '(st, log) '(st', m) : Prop :=
  client_step' st log st' m.

Definition init_env := (fun (x: var) => 0).
Definition st := (mkSt init_env mh_host 0).
Definition st' := (mkSt (update init_env var_car 0) (tail mh_host) 0).

Example input_can_be_nop : (client_step' st [] st' None).
  split.
  * reflexivity.
  * exact (is_input init_env 0 None var_car 0).
Qed.
