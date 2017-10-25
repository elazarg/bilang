Require Import Common.

Require Import ClientLang.
(*
Parameter ServState: Set.
Parameter server_eval : (ServState * Packet) -> (ServState * Event).
*) 


Require Import ServerLang.
(*
Parameter ClState: Set.
Parameter client_step : (ClState * list Event) -> (ClState * option Msg) -> Prop.
*)

Module NetSem.

Record State : Set := mkSt {
  S_K: nat -> ClState;
  S_Q: nat -> list Msg;
  S_ST: ServState;
  S_ES: list Event
}.

Notation "'[' a | b '|->' c ']'" := (update a b c) (at level 9, no associativity).
Notation "a '~>' b" := (client_step a b) (at level 81, no associativity).
Notation "a '\\' b" := (server_eval a = b) (at level 81, no associativity).

Definition inject_cons {T} (x: option T) xs :=
  match x with
    | Some x => x::xs
    | None => xs
  end.

Notation "a '?::' b" := (inject_cons a b) (at level 40, left associativity).

Inductive Step : State -> State -> Prop :=
  | Perform_client : forall id K Q es m s k',

             (K id, es) ~> (k', m)
             ->
             Step (mkSt K Q s es) (mkSt [K| id |-> k'] [Q| id |-> m?::(Q id)] s es)

  | Perform_transaction : forall id K Q es m s s' e,

             (s, (id, m)) \\ (s', e) 
             ->
             Step (mkSt K Q s es) (mkSt K [Q| id |-> removelast (Q id)] s' (e::es))
.


End NetSem.
