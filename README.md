# stm — verified state machine library

A formally verified state machine framework in F*.  Defines state machines as
transition functions with initial states, supports Moore/Mealy machines,
invariants (progress & safety), composite/orthogonal decomposition, and C
extraction via Pulse + Custard.

## Architecture

```
Data.StateMachine.Types      — Core types, state_machine_t/moore_t/mealy_t records
Data.StateMachine.Invariants — Progress & safety lemmas
Data.StateMachine.Machine    — run, replay, composition, output lemmas
Data.StateMachine.Examples   — 10 verified example machines
Data.StateMachine.Pulse      — C-extractable state-tag codec (Custard)
```

### Key properties

- **Zero admits / zero magic.**  Every module verifies with structural proofs
  (definitional equality, case analysis, or induction); no `admit()`, no
  `magic ()`.
- **C extraction.**  [Data.StateMachine.Pulse] extracts to C11 via Custard
  (`--custard_backend C`).  A single-byte tag selects the state —
  [SS_Idle] (0x00), [SS_Active] (0x01), [SS_Error] (0x02), [SS_Done] (0x03).
- **100% fsdoc.**  All modules carry `@header`, `@param`, `@returns`, and
  `@ensures` tags.  Zero `///` comments, zero ASCII-art headers.
- **Integration test.**  `test/Data.StateMachine.Test.Integration.fst` binds
  every public symbol across all 5 core modules for mechanical coverage.

## Modules

| Module | Admits | Description |
|--------|--------|-------------|
| `Data.StateMachine.Types` | 0 | Core types: state_machine_t, moore_t, mealy_t |
| `Data.StateMachine.Invariants` | 0 | Progress and safety lemmas (proven definitionally) |
| `Data.StateMachine.Machine` | 0 | run, replay, product_step, composite_step |
| `Data.StateMachine.Examples` | 0 | 10 examples, preservation by SMT case analysis |
| `Data.StateMachine.Pulse` | 0 | C extraction: sm_state tags (zero admits) |
| `Data.StateMachine.Test.Integration` | 0 | Binds all public symbols |

## Build

```sh
nix develop
make check    # Verify all modules (src + test)
```

Or via nix:

```sh
nix build .#checked  # F* verification gate (0-admit)
nix build .#native   # C11 shared/static lib (default)
nix build .#ocaml    # OCaml findlib package
nix build .#fsharp   # .NET library
```

## Dependencies

None.  The `stm` package is self-contained — it depends only on the F* standard
library (and Pulse for the C-extractable leaf).
