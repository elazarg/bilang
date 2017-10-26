Require Export List.
Export ListNotations.

Inductive Content :=
  | M_empty
  | M_nat (n: nat)
  | M_hashed (h: nat)
.

Definition ClientId := nat.

Definition Event: Set := Content.
Definition Msg: Set := Content.
Record Packet : Set := mkPkt {
  sender: ClientId;
  msgof: Msg
}.

Definition update {T: Type} f (id: nat) (v: T) id' :=
  if Nat.eqb id id' then v
  else f id.


Module Type ServerSem.
Parameter State: Set.
Parameter eval : (State * Packet) -> (State * Event).
End ServerSem.

Module Type ClientSem.
Parameter State: Set.
Parameter step : (State * list Event) -> (State * option Msg) -> Prop.
End ClientSem.


Definition inject_cons {T} (x: option T) xs :=
  match x with
    | Some x => x::xs
    | None => xs
  end.
