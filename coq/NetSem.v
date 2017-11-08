Require Import Common.

Module System (Client: ClientSem) (Server: ServerSem).

(*
Record State : Set := St {
  client: Client.State;
  inFlight: list Msg;
  server: Server.State;
  events: list Event
}.
*)
Definition State : Set := Client.State * list Msg * Server.State * list Event.

Definition World := ClientId -> State.

Notation " a '[' b '↦' c ']'" := (update a b c) (at level 9, no associativity).
Notation "a '~>' b" := (Client.step a b) (at level 81, no associativity).
Notation "a '\\' b" := (Server.eval a = b) (at level 41, no associativity).
Notation "a '?::' b" := (inject_cons a b) (at level 40, left associativity).

Inductive SessionStep : State -> State -> Prop :=
  | Perform_client : forall s k k' m q es,
      (k, es) ~> (k', m)
      ->
      SessionStep (k, q, s, es) (k', m?::q, s, es)

  | Perform_transaction : forall k es payload s s' e q',
      (s, mkPkt payload) \\ (s', e)
      ->
      SessionStep (k, q' ++ [payload], s, es) (k, q', s', e::es)
.

(* TODO: additional semantics, for session creation, joining and intercommunication *)
(* Sketch: each step
    1. each session receive message from client; writes local summary
    2. c' waits for all summaries, and then for the tempo-maker; then makes a global summary
    3. each client draws global summary (maybe +local summary)
*)
End System.
