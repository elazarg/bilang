Require Import Common.

Module NetSem.

Parameter ServState: Set.
Parameter server_eval : (ServState * Packet) -> (ServState * Event).

Parameter ClState: Set.
Parameter client_step : (ClState * list Event) -> (ClState * Msg) -> Prop.


Record State : Set := mkSt {
  K: nat -> ClState;
  Q: nat -> list Msg;
  ST: ServState;
  ES: list Event
}.

Notation "'[' a | b '|->' c ']'" := (update a b c) (at level 9, no associativity).
Notation "a '~>' b" := (client_step a b) (at level 81, no associativity).
Notation "a '\\' b" := (server_eval a = b) (at level 81, no associativity).

Inductive Step : State -> State -> Prop :=
  | Send : forall id K Q es m s k',

             (K id, es) ~> (k', m)
             ->
             Step (mkSt K Q s es) (mkSt [K| id |-> k'] [Q| id |-> m::(Q id)] s es)

  | Perform : forall id K Q es m s s' e,

             (s, (id, m)) \\ (s', e) 
             ->
             Step (mkSt K Q s es) (mkSt K [Q| id |-> removelast (Q id)] s' (e::es))
.

End NetSem.