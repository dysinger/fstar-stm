(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.StateMachine.Pulse — C-extractable state-machine tag codec via Pulse + Custard.

A single-byte tag selects the state of
the machine — [SS_Idle] (0x00), [SS_Active] (0x01), [SS_Error] (0x02), or
[SS_Done] (0x03) — written/read through a [Pulse.Lib.Array.array].

Each encode/decode `fn` carries a byte-level post-condition tied to the pure
spec [tag_of]/[tag_to_type] (both `noextract`; the tag→type mapping is the
single source of truth shared with the pure [Data.StateMachine] layer).

Written for F* v2026.09.20 (Custard `--custard_backend C`).  Zero admits.

@header Data.StateMachine.Pulse

@section Types
- [sm_state] — SS_Idle, SS_Active, SS_Error, SS_Done
- [opt_sm_state] — C-friendly decode result (no [option])

@section Tag bytes
- [tag_idle] / [tag_active] / [tag_error] / [tag_done] — the four tag byte constants

@section Specs
- [tag_of] — sm_state → tag byte
- [tag_to_type] — tag byte → sm_state option

@section Encode
- [encode] — write [tag_of t] at [off], returns 1ul

@section Decode
- [decode] — read the tag at [off] into [opt_sm_state]

@section Roundtrip lemmas
- [lemma_roundtrip] — pure [tag_of] ∘ [tag_to_type] roundtrip
- [lemma_pulse_roundtrip] — buffer-level encode→decode roundtrip
- [lemma_pulse_encode_decode_match] — master roundtrip across every tag
*)
module Data.StateMachine.Pulse
#lang-pulse

open Pulse
open Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq

open FStar.Seq

(* ── Types (alphabetical) ──────────────────────────────────────────── *)

(** [sm_state] — the states the tag byte selects. *)
type sm_state =
  | SS_Idle
  | SS_Active
  | SS_Error
  | SS_Done

(** [opt_sm_state] — option wrapper for the decode result (C-friendly, no
    [option]). *)
type opt_sm_state =
  | OSM_None
  | OSM_Some of (sm_state & U32.t)

(* ── Tag bytes — single source of truth (fstar-proofs §33) ──────────── *)

(** [tag_idle] — the Idle tag byte (0x00). *)
let tag_idle : U8.t = 0x00uy

(** [tag_active] — the Active tag byte (0x01). *)
let tag_active : U8.t = 0x01uy

(** [tag_error] — the Error tag byte (0x02). *)
let tag_error : U8.t = 0x02uy

(** [tag_done] — the Done tag byte (0x03). *)
let tag_done : U8.t = 0x03uy

(* ── Pure spec (noextract: not C-representable) ─────────────────────── *)

(** [tag_of t] — pure spec: [sm_state] → tag byte. *)
noextract
let tag_of (t: sm_state) : U8.t =
  match t with
  | SS_Idle -> tag_idle
  | SS_Active -> tag_active
  | SS_Error -> tag_error
  | SS_Done -> tag_done

(** [tag_to_type b] — pure spec: tag byte → [sm_state] option.

    Returns [option sm_state] (not [opt_sm_state]) — [tag_to_type] is the
    PURE spec and is never extracted; only [decode] uses the C-friendly
    [opt_sm_state] wrapper. *)
noextract
let tag_to_type (b: U8.t) : option sm_state =
  if U8.eq b tag_idle then Some SS_Idle
  else if U8.eq b tag_active then Some SS_Active
  else if U8.eq b tag_error then Some SS_Error
  else if U8.eq b tag_done then Some SS_Done
  else None

(* ── Encode ─────────────────────────────────────────────────────────── *)

(** [encode t buf off] — encode a state tag into [buf] at [off]; returns 1
    (bytes written).

    @param t The state to write.
    @param buf The destination buffer (must hold at least 1 byte at [off]).
    @param off The write offset.
    @returns The number of bytes written (always [1ul]).
    The byte written equals [tag_of t]. *)
fn encode (t: sm_state) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns w: U32.t
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1 **
        pure (U32.v off + 1 <= A.length buf /\
              Seq.length s1 == A.length buf /\
              Seq.index s1 (U32.v off) == tag_of t)) **
      pure (w == 1ul)
{
  let j = US.uint32_to_sizet off;
  A.pts_to_len buf;
  buf.(j) <- tag_of t;
  1ul
}

(* ── Decode ─────────────────────────────────────────────────────────── *)

(** [decode buf off] — decode a state tag from [buf] at [off].

    @param buf The source buffer (must hold at least 1 byte at [off]).
    @param off The read offset.
    @returns [OSM_Some (t, 1ul)] when the byte is a known tag, else
             [OSM_None]. *)
fn decode (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns r: opt_sm_state
    ensures
      A.pts_to buf s0 **
      pure (
        A.length buf == Seq.length s0 /\
        U32.v off + 1 <= A.length buf /\
        (let b = Seq.index s0 (U32.v off) in
         match r, tag_to_type b with
         | OSM_Some (t, n), Some t' -> n == 1ul /\ t == t'
         | OSM_None, None -> True
         | _, _ -> False))
{
  A.pts_to_len buf;
  let j = US.uint32_to_sizet off;
  let tag = buf.(j);
  if U8.eq tag tag_idle {
    OSM_Some (SS_Idle, 1ul)
  } else if U8.eq tag tag_active {
    OSM_Some (SS_Active, 1ul)
  } else if U8.eq tag tag_error {
    OSM_Some (SS_Error, 1ul)
  } else if U8.eq tag tag_done {
    OSM_Some (SS_Done, 1ul)
  } else {
    OSM_None
  }
}

(* ── Roundtrip lemmas (alphabetical) ────────────────────────────────── *)

(** [lemma_roundtrip t] — pure roundtrip: encoding then decoding returns the
    original value. *)
let lemma_roundtrip (t: sm_state) : Lemma (tag_to_type (tag_of t) == Some t) =
  match t with
  | SS_Idle -> ()
  | SS_Active -> ()
  | SS_Error -> ()
  | SS_Done -> ()

(** [lemma_pulse_roundtrip t buf off] — encode then decode a tag roundtrips.

    @param t The state to roundtrip.
    @param buf The buffer.
    @param off The offset.
    Proves [decode buf off] after [encode t buf off] returns
    [OSM_Some (t, 1ul)]. *)
fn lemma_pulse_roundtrip (t: sm_state) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns res: (U32.t & opt_sm_state)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 1ul /\ snd res == OSM_Some (t, 1ul))
{
  let n = encode t buf off;
  let r = decode buf off;
  lemma_roundtrip t;
  (n, r)
}

(** [lemma_pulse_encode_decode_match t buf off] — master roundtrip across
    every tag.

    @param t The state.
    @param buf The buffer.
    @param off The offset.
    Proves [decode]∘[encode] returns [OSM_Some (t, 1ul)] for all four tags. *)
fn lemma_pulse_encode_decode_match (t: sm_state) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns res: (U32.t & opt_sm_state)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 1ul /\ snd res == OSM_Some (t, 1ul))
{
  match t {
    SS_Idle -> { lemma_pulse_roundtrip SS_Idle buf off }
    SS_Active -> { lemma_pulse_roundtrip SS_Active buf off }
    SS_Error -> { lemma_pulse_roundtrip SS_Error buf off }
    SS_Done -> { lemma_pulse_roundtrip SS_Done buf off }
  }
}
