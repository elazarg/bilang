Require Import List.
Module Import ListNotations.

Variable ServState: Set.
Variable ClState: Set.
Variable Event: Set.
Variable Msg: Set.

Record State : Set := mkSt {
  K: nat -> ClState;
  Q: nat -> list Msg;
  ST: ServState;
  ES: list Event
}.

Definition Packet: Type := (nat * Msg).
Variable client_step : (ClState * list Event) -> (ClState * Msg) -> Prop.
Variable server_eval : (ServState * Packet) -> (ServState * Event).

Definition update {T: Type} f (id: nat) (v: T) id' :=
  if Nat.eqb id id' then v
  else f id.

Notation "a '[[' b '|->' c ']]'" := (update a b c) (at level 80, no associativity).
Notation "a '~>' b" := (client_step a b) (at level 81, no associativity).
Notation "a '\\' b" := (server_eval a = b) (at level 81, no associativity).

Inductive Step : State -> State -> Prop :=
  | Send : forall id K Q es m s k',

             (K id, es) ~> (k', m)
             ->
             Step (mkSt K Q s es) (mkSt (K[[id |-> k']]) (Q[[id |-> Q id ++ m::nil ]]) s es)

  | Perform : forall id K Q es m s s' e,

             (s, (id, m)) \\ (s', e) 
             ->
             Step (mkSt K Q s es) (mkSt K (Q[[id |-> tl (Q id)]]) s' (e::es))
.
