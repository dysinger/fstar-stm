# fstar-stm — Agent Guide & Handoff

`Data.StateMachine` — verified state machine library, extracted from the xeno
monorepo.  F* source is 0-admit.  This file records the completed Pulse port so
the next session resumes cleanly.

## ⛔ MANDATES (binding — read before doing anything)

1. **NEVER run `fstar.exe`, `nix build`, or `make` in the foreground.**  They
   can hang forever.  **Always** run them **detached** and poll the log:

   ```bash
   cd /Users/user/_/fstar-stm
   rm -f /tmp/stm-build.log
   nohup nix build .#checked --print-out-paths --no-link > /tmp/stm-build.log 2>&1 &
   # … poll: tail /tmp/stm-build.log ; ps -p $!
   ```

   A stuck process (0% CPU `stopped`, or 100% CPU spin) is a hang — kill it,
   diagnose, don't wait.  Per-step budgets: fstar verify ≤ 10 min, `nix build`
   ≤ 15 min (but the F\* bootstrap itself takes ~20 min *only on first build*;
   it is now cached).

2. **The F\* overlay in `flake.nix` MUST stay byte-identical to
   `fstar-codec`/`fstar-basen`/`fstar-text`'s.**  Any comment/whitespace change
   to the `buildPhase`/`installPhase` strings changes the derivation hash and
   forces a full F\* bootstrap.  Do NOT touch those strings.

## ✅ Current state — Pulse port DONE, 4/4 targets GREEN

The KaRaMeL→Custard port is complete and verified 0-admit.  The old
`src/Data.StateMachine.Low` (KaRaMeL Low\*: `FStar.HyperStack.ST`,
`LowStar.Buffer`, `Stack`) was **deleted** (Low\* stdlib removed in
`v2026.09.20`), replaced by `src/Data.StateMachine.Pulse.fst` (`#lang-pulse`).

### Build matrix (verified, F* `v2026.09.20+lsp`)

| Target | Status | Output |
|---|---|---|
| `checked` | ✅ GREEN 0-admit | 6 modules verified (5 src + 1 test) |
| `native` (C) | ✅ GREEN | `Custard.c`/`Custard.h`/`stm.h`, `libstm.{dylib,a}` (C11, no karamel) |
| `ocaml` | ✅ GREEN | findlib `stm-ocaml` |
| `fsharp` (.NET) | ✅ GREEN | `Custard.dll` (.NET 10) |

Target names: `default = native`, `checked`, `ocaml`, `native`, `fsharp`.
`nix flake check` is GREEN.

### Roll-forward fixes (landed, 0-admit preserved)

- `src/Data.StateMachine.Examples.fst`: removed `open FStar.Mul` (module
  deleted in v2026.09.20; `*` is now natively multiplication).
- `src/Data.StateMachine.Low.fst` → `src/Data.StateMachine.Pulse.fst`: full
  KaRaMeL→Pulse port (`FStar.HyperStack`/`LowStar.Buffer`/`Stack` →
  `Pulse.Lib.Array`/`fn`), following `fstar-text`'s `Data.Text.Codec.Pulse.fst`
  shape exactly (4 tags instead of 3).
- `test/Data.StateMachine.Test.Integration.fst`: `open …Low` → `open …Pulse`;
  dropped the `FStar.HyperStack.ST`/`LowStar.Buffer` opens; the Low anchors now
  point at `lemma_pulse_roundtrip` / `lemma_pulse_encode_decode_match` (the
  retired `lemma_encode_match` / `lemma_decode_match` are gone).

## Architecture (post-port)

```
Data.StateMachine.Types      — state_machine_t/moore_t/mealy_t + predicates
Data.StateMachine.Invariants — progress & safety lemmas
Data.StateMachine.Machine    — run/replay/composition + output lemmas
Data.StateMachine.Examples   — 10 verified example machines
Data.StateMachine.Pulse      — C-extractable state-tag codec (Custard)
```

The Pulse leaf is trivial compared to `fstar-codec`/`fstar-basen`/`fstar-text`:
a single 1-byte tag (`SS_Idle` 0x00 / `SS_Active` 0x01 / `SS_Error` 0x02 /
`SS_Done` 0x03), `encode`/`decode` (`A.array U8.t`, `fn`), plus
`lemma_roundtrip` (pure), `lemma_pulse_roundtrip`,
`lemma_pulse_encode_decode_match`.  No varint, no multi-byte arithmetic — so
none of the varint/word32 SMT-hang complexity applies here.

## No internal dependencies

`fstar-stm` is self-contained — it consumes **no** `Data.Codec` and has no
flake-input dependency beyond `nixpkgs` / `flake-utils` / `treefmt-nix` /
`fstar`.  There is no `fstar-codec` input, no `codec-src`/`codec-checked`
injection.

## Build commands

```bash
nix build .#checked   # F* verification gate (0-admit)
nix build .#native    # C11 shared/static lib (default)
nix build .#ocaml     # OCaml findlib package
nix build .#fsharp    # .NET library
nix develop && make check   # dev loop (no nix)
```

## Reference

- Canonical references: `../fstar-text` (the token/tag Pulse port whose
  `Data.Text.Codec.Pulse.fst` is near-identical in shape), `../fstar-codec`
  (the codec, incl. its `Data.Codec.Pulse`), and `../fstar-basen`.
- The F\* skill: `~/.pi/agent/skills/fstar/fstar-2026.09.20/SKILL.md`
  (Custard, Pulse idiom, `U8.v`/`U32.v` → `Int.Cast`, the dead-Low\* delta).
