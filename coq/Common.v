Require Export List.
Export ListNotations.

Inductive Content :=
  | M_empty
  | M_nat : nat -> Content
.

Definition ClientId := nat.

Definition Event: Set := Content.
Definition Msg: Set := Content.
Definition Packet: Set := ClientId * Msg.

Definition update {T: Type} f (id: nat) (v: T) id' :=
  if Nat.eqb id id' then v
  else f id.

