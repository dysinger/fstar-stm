(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)


(**
Data.StateMachine.Types — Core State Machine Types

Parametric state machine abstractions: [state_machine_t], [moore_t],
[mealy_t] with smart constructors and validity predicates.  All types
are [noeq] to support function fields.

@header Data.StateMachine.Types
*)
module Data.StateMachine.Types


(** State machine type — parametric over state and event types.

    @param s The state type.
    @param e The event type. *)
noeq type state_machine_t (s: Type) (e: Type) = {
  initial : s;                    (** The initial state. *)
  step    : s -> e -> option s;   (** Transition function — [None] on invalid input. *)
}


(** Moore machine: output depends only on state.

    @param s The state type.
    @param e The event type.
    @param o The output type. *)
noeq type moore_t (s: Type) (e: Type) (o: Type) = {
  sm     : state_machine_t s e;   (** The underlying state machine. *)
  output : s -> o;                (** Output function of state only. *)
}


(** Mealy machine: output depends on state and event.

    @param s The state type.
    @param e The event type.
    @param o The output type. *)
noeq type mealy_t (s: Type) (e: Type) (o: Type) = {
  sm     : state_machine_t s e;   (** The underlying state machine. *)
  output : s -> e -> option (o & s);  (** Output + next state, or [None]. *)
}


(** Transition validity *)


(** Check if a transition is valid for a given state and event.

    @param sm The state machine.
    @param st The current state.
    @param ev The event.
    @returns [true] iff [sm.step st ev] returns [Some]. *)
let valid_transition (#s: Type) (#e: Type) (sm: state_machine_t s e) (st: s) (ev: e)
  : bool
  = Some? (sm.step st ev)


(** Terminal state predicate — no further transitions are defined.

    Uses [prop] (not [bool]) because it quantifies over all events
    of a potentially infinite type.

    @param sm The state machine.
    @param st The state to check.
    @returns [True] iff all events are rejected. *)
let terminal (#s: Type) (#e: Type) (sm: state_machine_t s e) (st: s)
  : prop
  = forall (ev: e). sm.step st ev == None


(** Terminal states have no valid transitions — bridging [prop] and [bool].

    [terminal sm st] (a [prop]) implies that [valid_transition sm st ev]
    is [false] for all events.

    @param sm The state machine.
    @param st A terminal state.
    @param ev Any event.
    @ensures [valid_transition sm st ev == false] *)
let lemma_terminal_implies_not_valid (#s #e: Type) (sm: state_machine_t s e) (st: s) (ev: e) : Lemma
  (requires terminal sm st)
  (ensures valid_transition sm st ev == false)
  = ()


(** Smart constructors *)


(** Construct a [state_machine_t]. Always succeeds.

    @param init The initial state.
    @param step_fn The transition function.
    @returns The constructed state machine. *)
let mk_state_machine (#s: Type) (#e: Type) (init: s) (step_fn: s -> e -> option s)
  : state_machine_t s e
  = { initial = init; step = step_fn }


(** Construct a [moore_t]. Always succeeds.

    @param init The initial state.
    @param step_fn The transition function.
    @param out_fn The output function of state.
    @returns The constructed Moore machine. *)
let mk_moore (#s: Type) (#e: Type) (#o: Type)
  (init: s) (step_fn: s -> e -> option s) (out_fn: s -> o)
  : moore_t s e o
  = { sm = mk_state_machine init step_fn; output = out_fn }


(** Construct a [mealy_t]. Always succeeds.

    The transition function is derived from the output function: a step
    succeeds iff the output function returns [Some].

    @param init The initial state.
    @param out_fn The output+transition function.
    @returns The constructed Mealy machine. *)
let mk_mealy (#s: Type) (#e: Type) (#o: Type)
  (init: s) (out_fn: s -> e -> option (o & s))
  : mealy_t s e o
  = {
    sm = { initial = init; step = (fun st ev -> match out_fn st ev with
                                                | Some (_, st') -> Some st'
                                                | None -> None) };
    output = out_fn;
  }
