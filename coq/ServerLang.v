Require Import Common.

Require EqNat.

Module Server <: ServerSem.

Definition var := nat.
Definition Env := var -> nat.

Section Syntax.

Inductive Cmd :=
  | call_coq (v: var) (coq: Env -> nat)
.

Inductive Method :=
  | proc (i: nat) (lval: var) (cmds: list Cmd) (emit: var)
.

Definition Prog := list Method.

End Syntax.

Section Semantics.

Definition State: Set := Env * Prog.

Definition server_eval_cmd (env: Env) (cmd: Cmd) : Env :=
  match cmd with
  | call_coq v cf => update env v (cf env)
  end
.

Fixpoint server_eval_cmds (env: Env) (cmds: list Cmd) : Env :=
  match cmds with
  | [] => env
  | cmd::cmds => server_eval_cmds (server_eval_cmd env cmd) cmds
  end.

Definition eval '(st, packet) : (State * Event) :=
  let '(env, prog) := st in
  match (prog, packet) with
  | (proc expected v1 cmds v2 :: ms, mkPkt actual (M_nat m)) =>
      if Nat.eqb actual expected then
        let env' := update env v1 m in
        let env'' := server_eval_cmds env' cmds in
        ((env'', ms), M_nat (env'' v2))
      else
        (st, M_empty)
  | (_, _) =>
        (st, M_empty)
  end
.


Definition owns_user (client: nat) st :=
  forall actual content,
    actual = client \/
      eval (st, mkPkt actual content) = (st, M_empty).

Lemma owns_receiver : forall id lval cmd emit env ms,
  owns_user id (env, proc id lval cmd emit::ms).
Proof.
  unfold owns_user;
  intros;
  destruct (EqNat.eq_nat_decide actual id); [left | right].
  * exact (EqNat.eq_nat_eq actual id e).
  * simpl.
    destruct content, (Nat.eqb actual id) eqn:BEQ; try reflexivity.
    exfalso.
    apply EqNat.beq_nat_true in BEQ.
    subst.
    apply n, EqNat.eq_nat_refl.
Qed.

End Semantics.

End Server.