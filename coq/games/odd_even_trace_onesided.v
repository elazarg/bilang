Require Import List.
Import ListNotations.

Inductive role := E | O .

Let even := 0.
Let odd := 1.


Definition value := option bool.


Module High.

Inductive prefix :=
  | Start
  | Joined (r1 r2: nat)
  | Played (r1 r2: nat) (v1 v2: value)
.

Definition trace_prev (p: prefix): prefix :=
  match p with
  | Start => Start
  | Joined _ _ => Start
  | Played r1 r2 _ _ => Joined r1 r2
  end.

Definition winner (p: prefix) : option role :=
  match p with
  | Played _ _ (Some v1) None => Some E
  | Played _ _ (Some v1) (Some v2) => if Bool.eqb v1 v2 then Some E else Some O
  | Played _ _ None (Some v2) => Some O
  | Played _ _ None None => None
  | _ => None
  end.

Definition strategy (r: role) := value.

Definition play (s1: strategy E) (s2: strategy O) (p: prefix) : Prop :=
  p = Played even odd s1 s2.

End High.


Module Middle.

Inductive prefix :=
  | Start
  | Joined (r1 r2: nat)
  | Hidden (r1 r2: nat) (v1 v2: value)
  | Open (r1 r2: nat) (v1 v2: value)
.

Definition trace_prev (p: prefix): prefix :=
  match p with
  | Start => Start
  | Joined _ _ => Start
  | Hidden r1 r2 _ _ => Joined r1 r2
  | Open r1 r2 v1 v2 => Hidden r1 r2 v1 v2
  end.

Definition abstract (p: prefix) :=
  match p with
  | Start => High.Start
  | Joined r1 r2 => High.Joined r1 r2
  | Hidden r1 r2 v1 v2 => High.Joined r1 r2
  | Open r1 r2 v1 v2 => High.Played r1 r2 v1 v2
  end.

Definition winner (p: prefix) : option role := High.winner (abstract p).

Definition E_strategy := unit -> value.
Definition O_strategy := unit -> value.


End Middle.


Module LowReceive.

Inductive item :=
  | Join
  | Hidden (v: value)
  | Open (v: value)
.

Inductive packet := Packet (user: nat) (r: role) (content: item).

Inductive _0 := Start.
Inductive _10 := JoinedFirst (r: nat).
Inductive _11 := JoinedSecond (r1 r2: nat).
Inductive _20 := HiddenFirst (r1 r2: nat) (h: value).
Inductive _21 := HiddenSeoncd (r1 r2: nat) (h1 h2: value).
Inductive _30 := OpenFirst (r1 r2: nat) (v h: value).
Inductive _31 := OpenSeoncd (r1 r2: nat) (v1 v2: value).

Inductive either (t1 t2: Set) :=
  | Left (t: t1)
  | Right (t: t2)
.

Definition schedule: Set := 
    _0  -> either _10 _11
  * _10 -> _11
  * _11 -> either _20 _21
  * _20 -> _21
  * _21 -> either _30 _31
  * _30 -> _31
.

x_odd :=
  | Start
  | JoinedFirst (fst_role: role) (r: nat)
  | JoinedBoth  (fst_role: role) (r1 r2: nat)
  | HiddenFirst (fst_role: role) (r1 r2: nat) (fst_h: role) (h: value)
  | HiddenBoth  (fst_role: role) (r1 r2: nat) (fst_h: role) (h1 h2: value)
  | OpenFirst   (fst_role: role) (r1 r2: nat) (fst_h: role) (fst_v: role) (v h: value)
  | OpenBoth    (fst_role: role) (r1 r2: nat) (fst_h: role) (fst_v: role) (v1 v2: value)
.

Definition trace_prev (p: prefix): prefix :=
  match p with
  | Start => Start
  | JoinedFirst _ _ => Start
  | JoinedBoth  fst_role r1 r2             => JoinedFirst fst_role (if fst_role then r1 else r2)
  | HiddenFirst fst_role r1 r2 fst_h h     => JoinedBoth  fst_role r1 r2
  | HiddenBoth  fst_role r1 r2 fst_h h1 h2 => HiddenFirst fst_role r1 r2 fst_h (if fst_h then h1 else h2)
  | OpenFirst   fst_role r1 r2 fst_h v_even v h =>
      let '(h1, h2) := match (fst_h, v_even) with
                       | (E, E) => (v, h)
                       | (O, O) => (v, h)
                       | _ => (h, v)
                       end
      in HiddenBoth fst_role r1 r2 fst_h h1 h2
  | OpenBoth    fst_role r1 r2 fst_h fst_v v1 v2 =>
      let '(h1, h2) := match (fst_h, fst_v) with
                       | (E, E) => (v1, v2)
                       | (O, O) => (v1, v2)
                       | _ => (v2, v1)
                       end
      in OpenFirst fst_role r1 r2 fst_h fst_v v1 v2
  end.

Definition abstract (p: prefix) :=
  match p with
  | Start => Middle.Start
  | JoinedFirst fst_role r => Middle.Start
  | JoinedBoth  fst_role r1 r2             => Middle.Joined r1 r2
  | HiddenFirst fst_role r1 r2 fst_h h     => Middle.Joined r1 r2
  | HiddenBoth  fst_role r1 r2 fst_h h1 h2 => Middle.Hidden r1 r2 h1 h2
  | OpenFirst   fst_role r1 r2 fst_h v_even v h =>
      let '(h1, h2) := if v_even then (v, h) else (h, v)
      in Middle.Hidden r1 r2 h1 h2
  | OpenBoth    fst_role r1 r2 fst_h fst_v v1 v2 => Middle.Open r1 r2 v1 v2
  end.

Definition winner (p: prefix) : option role := Middle.winner (abstract p).

(* possibly mutual ownership *)
Definition owner (p: prefix) (r: role) : Prop :=
  match p with
  | Start => True
  | JoinedFirst fst_role _ => r <> fst_role
  | JoinedBoth  fst_role r1 r2             => True
  | HiddenFirst fst_role r1 r2 fst_h h     => r <> fst_h
  | HiddenBoth  fst_role r1 r2 fst_h h1 h2 => True
  | OpenFirst   fst_role r1 r2 fst_h v_even v h => r <> v_even
  | OpenBoth    fst_role r1 r2 fst_h fst_v v1 v2 => True
  end.

(* This definition is probably not good enough for actual network asynchronicity *)
Definition strategy (r: role) := forall p, owner p r -> {p' | trace_prev p' = p}.

Definition schedule := forall st_e st_o p,
   {p': prefix | owner p E /\ p' = st_e p}
 + {p': prefix | owner p O /\ p' = st_o p}.

(* schedule? *)
Definition play (s: schedule) (s1: strategy E) (s2: strategy O) (p: prefix): Prop :=
  .

(* ? *)
Definition strategy_preserved (r1 r2: role) := exists to_high to_low,
  forall (st1_h: High.strategy r1) (st2_l: strategy r2),
  ~ High.winner (High.game st1_h (to_high st2_l))
  -> exists (s: schedule), ~ winner (game sched (to_low st1_h) st2_l).

Lemma strategy_preserved_both: strategy_preserved O E /\ strategy_preserved E O.

End LowReceive.

(* The point of asynchrony is not the information dependence,
but the lack of control on message arrival which is on the scheduler.
*)
