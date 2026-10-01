(**
Data.StateMachine.Machine — Transition Logic & Machine Patterns

Copyright 2026 Department of Code LLC. All rights reserved.

Run-to-completion semantics, event sourcing replay, Moore/Mealy output,
composite states (OR-decomposition), and orthogonal regions
(AND-decomposition).  Zero admits — all lemmas are proven by induction
or definitional reflexivity.

@header Data.StateMachine.Machine
*)
module Data.StateMachine.Machine

open Data.StateMachine.Types

(** Run-to-Completion *)

(** Fold events from a given state through [step].

    Returns [None] if any step in the sequence fails.

    @param sm The state machine.
    @param st The starting state.
    @param events The sequence of events to process.
    @returns [Some final_state] if all transitions succeed, [None] otherwise. *)
let rec run_from (#s #e: Type) (sm: state_machine_t s e) (st: s) (events: list e)
  : Tot (option s) (decreases events)
  = match events with
    | [] -> Some st
    | ev :: rest ->
      match sm.step st ev with
      | None -> None
      | Some st' -> run_from sm st' rest

(** Run a trace of events from the initial state.

    Short-circuits on the first invalid event.

    @param sm The state machine.
    @param events The sequence of events.
    @returns [Some final_state] or [None] on invalid transition. *)
let run (#s #e: Type) (sm: state_machine_t s e) (events: list e) : option s
  = run_from sm sm.initial events

(** Event Sourcing Replay *)

(** Fold events from a given state, assuming all transitions are defined.

    If any step returns [None], the function returns the last known
    good state [st] silently — there is no error signaling.  Callers
    MUST ensure the event log is valid (all transitions defined) before
    calling [replay_from].  Use [run_from] for error-aware folding.

    @param sm The state machine.
    @param st The starting state.
    @param events The sequence of events (assumed valid).
    @returns The final state, or [st] on undefined transition. *)
let rec replay_from (#s #e: Type) (sm: state_machine_t s e) (st: s) (events: list e)
  : Tot s (decreases events)
  = match events with
    | [] -> st
    | ev :: rest ->
      match sm.step st ev with
      | Some st' -> replay_from sm st' rest
      | None -> st

(** Reconstruct the current state from an event log.

    Assumes the log is valid (all transitions are defined).

    @param sm The state machine.
    @param events The event log (assumed valid).
    @returns The reconstructed state. *)
let replay (#s #e: Type) (sm: state_machine_t s e) (events: list e) : s
  = replay_from sm sm.initial events

(** Moore Machine *)

(** Combine Moore transition and output.

    Output depends only on the current state.

    @param m The Moore machine.
    @param st The current state.
    @param ev The event.
    @returns [Some (output, next_state)] or [None]. *)
let step_with_output (#s #e #o: Type) (m: moore_t s e o) (st: s) (ev: e)
  : option (o & s)
  = match m.sm.step st ev with
    | None -> None
    | Some st' -> Some (m.output st, st')

(** Mealy Machine *)

(** Mealy output integrated with transition.

    This is a thin wrapper around [m.output] — it exists only to provide
    a consistent naming convention alongside [step_with_output] for
    Moore machines.  Both functions have the same type signature.

    @param m The Mealy machine.
    @param st The current state.
    @param ev The event.
    @returns [Some (output, next_state)] or [None]. *)
let step_with_output_mealy (#s #e #o: Type) (m: mealy_t s e o) (st: s) (ev: e)
  : option (o & s)
  = m.output st ev

(** Orthogonal Regions — AND-decomposition *)

(** Compose two independent step functions for a product state.

    Both regions must succeed for the transition to be valid.
    The same event [ev] is dispatched to both regions — this follows
    standard UML statechart semantics for orthogonal regions.

    @param step_a Step function for region A.
    @param step_b Step function for region B.
    @param st The product state (a, b).
    @param ev The event (shared across both regions).
    @returns [Some (a', b')] if both succeed, [None] otherwise. *)
let product_step (#a #b #e: Type)
  (step_a: a -> e -> option a) (step_b: b -> e -> option b)
  (st: a & b) (ev: e)
  : option (a & b)
  = let (a_st, b_st) = st in
    match step_a a_st ev, step_b b_st ev with
    | Some a', Some b' -> Some (a', b')
    | _ -> None

(** Composite States — OR-decomposition *)

(** Dispatch an event to a composite state.

    Tries the inner (substate) transition first.  If the substate does not
    handle the event, falls back to the outer transition (exiting the
    composite state).

    @param inner_step The substate transition function.
    @param outer_step The outer state transition function.
    @param wrap Lifts an inner state into the outer state type.
    @param st The current inner state.
    @param ev The event.
    @returns [Some outer'] or [None]. *)
let composite_step (#outer #inner #e: Type)
  (inner_step: inner -> e -> option inner)
  (outer_step: outer -> e -> option outer)
  (wrap: inner -> outer)
  (st: inner) (ev: e)
  : option outer
  = match inner_step st ev with
    | Some inner' -> Some (wrap inner')
    | None -> outer_step (wrap st) ev

(** Lemmas *)

(** Run of an empty event list returns the initial state.

    Proved by definition: [run_from sm st [] = Some st].

    @param sm The state machine.
    @ensures [run sm [] == Some sm.initial] *)
let lemma_run_empty (#s #e: Type) (sm: state_machine_t s e) : Lemma
  (ensures run sm [] == Some sm.initial)
  = ()

(** Moore output depends only on state — calling [step_with_output]
    twice with the same state and different events yields the same output.

    Proved by definition: the output field is a function of state only.

    @param m The Moore machine.
    @param st The state.
    @param ev1 First event.
    @param ev2 Second event.
    @ensures Both calls produce identical output values. *)
let lemma_moore_output (#s #e #o: Type) (m: moore_t s e o) (st: s) (ev1 ev2: e) : Lemma
  (ensures (match step_with_output m st ev1, step_with_output m st ev2 with
            | Some (o1, _), Some (o2, _) -> o1 == o2
            | _ -> True))
  = ()

(** Mealy output determines transition validity — the step succeeds
    iff the output function returns [Some].

    @param m The Mealy machine.
    @param st The current state.
    @param ev The event.
    @ensures [step_with_output_mealy m st ev == m.output st ev] *)
let lemma_mealy_valid (#s #e #o: Type) (m: mealy_t s e o) (st: s) (ev: e) : Lemma
  (ensures step_with_output_mealy m st ev == m.output st ev)
  = ()

(** Replay reproduces run result — when [run] succeeds, [replay]
    and [run] return the same state.

    Proved by induction on [events].

    @param sm The state machine.
    @param events The event list.
    @ensures If [run sm events] succeeds, [replay sm events] returns
             the same state. *)
#push-options "--z3rlimit 40"
let rec lemma_replay_from_equals_run_from (#s #e: Type)
  (sm: state_machine_t s e) (st: s) (events: list e)
  : Lemma
    (requires Some? (run_from sm st events))
    (ensures replay_from sm st events == Some?.v (run_from sm st events))
    (decreases events)
  = match events with
    | [] -> ()
    | ev :: rest ->
      let Some st' = sm.step st ev in
      lemma_replay_from_equals_run_from sm st' rest

(** Top-level variant: [run] and [replay] agree on valid traces.

    @param sm The state machine.
    @param events The event list.
    @ensures [replay sm events] equals [Some?.v (run sm events)]
             when [run] succeeds. *)
let lemma_replay_equals_run (#s #e: Type)
  (sm: state_machine_t s e) (events: list e)
  : Lemma
    (requires Some? (run sm events))
    (ensures replay sm events == Some?.v (run sm events))
  = lemma_replay_from_equals_run_from sm sm.initial events
#pop-options
