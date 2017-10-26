Require Import Common.

Module System (Client: ClientSem) (Server: ServerSem).

Record State : Set := mkSt {
  S_K: nat -> Client.State;
  S_Q: nat -> list Msg;
  S_ST: Server.State;
  S_ES: list Event
}.

Notation "'[' a | b '|->' c ']'" := (update a b c) (at level 9, no associativity).
Notation "a '~>' b" := (Client.step a b) (at level 81, no associativity).
Notation "a '\\' b" := (Server.eval a = b) (at level 81, no associativity).

Notation "a '?::' b" := (inject_cons a b) (at level 40, left associativity).

Inductive Step : State -> State -> Prop :=
  | Perform_client : forall id K Q es m s k',

             (K id, es) ~> (k', m)
             ->
             Step (mkSt K Q s es) (mkSt [K| id |-> k'] [Q| id |-> m?::(Q id)] s es)

  | Perform_transaction : forall (id: ClientId) K Q es m s s' e,

             (s, (mkPkt id m)) \\ (s', e) 
             ->
             Step (mkSt K Q s es) (mkSt K [Q| id |-> removelast (Q id)] s' (e::es))
.


End System.
