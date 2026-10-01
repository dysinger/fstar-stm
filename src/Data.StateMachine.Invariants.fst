(**
Data.StateMachine.Invariants — Lemma library: progress, safety, bridging

Copyright 2026 Department of Code LLC. All rights reserved.

Progress and safety lemmas for state machines.  All lemmas are
proven by definitional equality — zero admits.

Invariant-preservation lemmas are NOT included here.  They require
concrete knowledge of the transition function and MUST be defined
in the consumer module (e.g., [Data.StateMachine.Examples] proves
preservation for each of the 10 concrete machines).  The pattern is:
define your invariant, write a lemma with body [()], and let SMT
case-analyze over your finite state/event types.

@header Data.StateMachine.Invariants
*)
module Data.StateMachine.Invariants

open Data.StateMachine.Types

(** Progress — deadlock freedom *)

(** Convenience re-wrap: if a specific event produces a valid transition,
    then progress is possible from this state (existential introduction).
    The lemma body is a trivial [exists_intro] at the witness [ev].

    For concrete machines with finite event types, consumers prove
    that every non-terminal state has at least one valid event.

    @param sm The state machine.
    @param st The state.
    @param ev A witness event that produces a valid transition.
    @ensures A valid transition exists from [st] (trivially, [ev] itself). *)
let lemma_progress (#s: Type) (#e: Type)
  (sm: state_machine_t s e) (st: s) (ev: e)
  : Lemma
    (requires Some? (sm.step st ev))
    (ensures exists ev'. Some? (sm.step st ev'))
  = ()

(** Safety — terminal states have no outgoing transitions *)

(** Definitional identity: [terminal sm st] expands to the ensures clause.
    This lemma exists for cross-module callers where the [terminal]
    predicate may be opaque — it restates the definition as a provable
    equality.  The body [()] suffices because the ensures is the unfold.

    @param sm The state machine.
    @param st A terminal state.
    @ensures All events are rejected at [st] (unfolding of [terminal]). *)
let lemma_terminal_no_transitions (#s: Type) (#e: Type)
  (sm: state_machine_t s e) (st: s)
  : Lemma
    (requires terminal sm st)
    (ensures forall (ev: e). sm.step st ev == None)
  = ()

(** Replay and Determinism — available via [Machine] *)

(** [lemma_replay_from_equals_run_from], [lemma_replay_equals_run],
    [lemma_moore_output], and [lemma_mealy_valid]
    are defined in [Data.StateMachine.Machine].  Per fstar-lang §2,
    [open] is NOT transitive — consumers of [Invariants] must also
    [open Data.StateMachine.Machine] to access these lemmas. *)
