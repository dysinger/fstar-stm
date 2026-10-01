# Data.StateMachine API

## Data.StateMachine.Types

Core type definitions for the state machine framework.

### `state_machine_t s e`

A verified state machine record:

- `initial : s` — The initial state
- `step : s -> e -> option s` — Pure transition function

### `moore_t s e o`

A Moore machine — output depends only on state:

- `sm : state_machine_t s e` — The underlying state machine
- `output : s -> o` — Output function of state only

### `mealy_t s e o`

A Mealy machine — output depends on state and event:

- `sm : state_machine_t s e` — The underlying state machine
- `output : s -> e -> option (o & s)` — Output + next state

### Smart constructors

- `mk_state_machine init step_fn`
- `mk_moore init step_fn out_fn`
- `mk_mealy init out_fn`

### Predicates

- `valid_transition sm st ev : bool` — True iff `step st ev` returns `Some`
- `terminal sm st : prop` — True iff no events produce a transition

### Lemmas

- `lemma_terminal_implies_not_valid` — Bridges [terminal] ([prop]) to
  [valid_transition] ([bool])

---

## Data.StateMachine.Machine

Transition operations with induction proofs.  Zero admits.

### Run-to-completion

- `run_from sm st events : option s` — Fold events from a given state
- `run sm events : option s` — Fold events from initial state

### Event sourcing replay

- `replay_from sm st events : s` — Reconstruct state from event log
- `replay sm events : s` — Reconstruct state from initial

### Moore/Mealy output

- `step_with_output m st ev : option (o & s)` — Moore transition + output
- `step_with_output_mealy m st ev : option (o & s)` — Mealy output

### Composition

- `product_step step_a step_b st ev` — AND-decomposition (orthogonal regions)
- `composite_step inner_step outer_step wrap st ev` — OR-decomposition

### Lemmas

- `lemma_run_empty` — `run sm [] == Some sm.initial`
- `lemma_moore_output` — Moore output independent of event
- `lemma_mealy_valid` — Mealy step validity equals output function result
- `lemma_replay_equals_run` — valid traces replay = run
- `lemma_replay_from_equals_run_from` — same, from arbitrary state

---

## Data.StateMachine.Invariants

Progress and safety lemmas.  All proven by definitional equality — zero admits.
Invariant-preservation lemmas belong in concrete consumer modules
(e.g., the 10 examples in `Data.StateMachine.Examples`), not at the
generic level where SMT cannot reason about opaque step functions.

### Safety & progress

- `lemma_progress sm st ev` — Existence of a valid transition
  (existential introduction at the witness event `ev`)
- `lemma_terminal_no_transitions sm st` — Terminal states reject all
  events (unfolding of the `terminal` predicate)

---

## Data.StateMachine.Examples

10 verified example machines with demo traces and preservation proofs.

| # | Name | Pattern |
|---|------|---------|
| 1 | Traffic Light | Moore machine, cyclic FSM |
| 2 | Turnstile | Mealy machine |
| 3 | TCP Connection | Protocol state machine (RFC 793) |
| 4 | HTTP/2 Stream | Orthogonal regions (AND-decomposition) |
| 5 | Elevator | Rich state with safety invariants |
| 6 | Card Game Turn | Multi-phase state machine |
| 7 | Login/Logout | Auth session with timeout & lockout |
| 8 | Retry with Backoff | Error recovery, parameterized states |
| 9 | Saga/Transaction | Long-running with compensation |
| 10 | Vending Machine | Multi-step transaction, accumulated state |

Each example exports:
- State/event type definitions
- Transition function + machine instance
- Invariant predicate + preservation lemma
- Demo trace lemma(s)

---

## Data.StateMachine.Pulse

C-extractable Pulse module (Custard).  Single-byte state tags for the
`sm_state` enumeration (`SS_Idle`, `SS_Active`, `SS_Error`, `SS_Done`).

- `encode t buf off` — Write tag byte at offset, returns 1ul
- `decode buf off` — Read tag byte, returns `opt_sm_state`
- `tag_of t` — Pure spec mapping (noextract)
- `tag_to_type b` — Pure spec reverse mapping (noextract)
- `lemma_roundtrip t` — `tag_to_type (tag_of t) == Some t`
- `lemma_pulse_roundtrip` — Buffer-level encode→decode roundtrip
- `lemma_pulse_encode_decode_match` — Master roundtrip across all four tags

Zero admits.  The encode/decode `fn`s carry byte-level post-conditions tied to
the pure spec; the roundtrip lemmas follow directly.
