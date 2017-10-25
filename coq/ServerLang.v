Require Import Common.


Definition var := nat.

Inductive Cmd :=
  | call (func v: var)
.

Inductive Method :=
  | proc (i: nat) (lval: var) (cmds: list Cmd) (emit: var)
.

Definition Prog := list Method.

Definition var_car := 0.
Definition var_door1 := 1.
Definition var_goat := 2.
Definition var_door2 := 3.
Definition var_winner := 4.
Definition var_hcar := 5.
Definition var_compute_winner := 6.

Definition receive_emit role var :=  proc role var [] var.

Definition host := 0.
Definition guest := 1.

Definition Monty := [
  receive_emit host  var_hcar;
  receive_emit guest var_door1;
  receive_emit host  var_goat;
  receive_emit guest var_door2;
  receive_emit host  var_car;
  proc guest 0 [call var_compute_winner var_winner] var_winner
].

Definition Env := var -> nat.
Definition ServState: Set := Env * Prog.


Definition guest_winner (hcar door1 goat door2 car : nat) : bool :=
  negb (Nat.eqb hcar car)
  || Nat.eqb car goat
  || Nat.eqb goat door1
  || Nat.eqb car door2
  .

Definition server_eval_cmd (env: Env) (cmd: Cmd) : Env :=
  match cmd with
  | call 6 v1 =>
    let winner := 
      if guest_winner (env var_hcar) (env var_door1) (env var_goat) (env var_door2) (env var_car) then
        1
      else
        0
    in (update env v1 winner)
  | call _ v1 => env
  end
.

Fixpoint server_eval_cmds (env: Env) (cmds: list Cmd) : Env :=
  match cmds with
  | [] => env
  | cmd::cmds => server_eval_cmds (server_eval_cmd env cmd) cmds
  end.

Definition server_eval '(st, packet) : (ServState * Event) :=
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

Require Import EqNat.

Definition owns_client (client: nat) st :=
  forall actual content,
    actual = client \/
      fst (server_eval (st, mkPkt actual content)) = st.

Lemma owns_receiver : forall id lval cmd emit env ms,
  owns_client id (env, proc id lval cmd emit::ms).
Proof.
  unfold owns_client.
  intros.
  destruct (eq_nat_decide actual id).
  * left. exact (eq_nat_eq actual id e).
  * right. unfold not in n.
    simpl.
    destruct content; try reflexivity.
    destruct (Nat.eqb actual id) eqn:EQ; try reflexivity.
    exfalso.
    apply beq_nat_true in EQ.
    subst actual.
    exact (n (eq_nat_refl id)).
Qed.
