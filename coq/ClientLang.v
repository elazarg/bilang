Require Import Common.

Module Client <: ClientSem.

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


Section Semantics.

Definition Env := var -> nat.
Definition State : Set :=  Env * Prog * nat.

Section VariablesForInductive.
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
End VariablesForInductive.

Definition client_step' (st: State) (log: list Event) (st': State) (m: option Msg) : Prop :=
  let '(env, prog, logindex) := st in
  let '(env', prog', logindex') := st' in
  match prog with
  | [] => False
  | cmd::cmds =>  prog' = cmds
                  /\ client_cmd_step env logindex (nth_error log logindex) cmd (env', m, logindex')
  end
.

Definition step : (State * list Event) -> (State * option Msg) -> Prop :=
  fun '(st, log) '(st', m) => client_step' st log st' m.

End Semantics.

End Client.
