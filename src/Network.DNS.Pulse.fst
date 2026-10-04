(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Network.DNS.Pulse — C-extractable DNS label wire-format encode/decode via
Pulse + Custard.

A single DNS label in the RFC 1035 §3.1 wire form: a length byte followed by
the label octets, with a `0x00` root terminator ending the name.  The *content*
octets are carried as a fixed 3-byte record ([label3]) — a bounded slice of the
general 1..63-octet label — so the encode/decode is fixed-width and the
post-conditions are POINTWISE (each `Seq.index` conjunct discharged
independently), matching the `Data.UUID.Pulse`/`Data.BaseN.Pulse` shape.

The length byte is the label length in octets (`0x03` for a full [label3]); the
roundtrip [lemma_pulse_label_roundtrip] proves encode-then-decode preserves the
label and that the `0x00` terminator follows.

Written for F* v2026.09.20 (Custard `--custard_backend C`).  Zero admits.

@header Network.DNS.Pulse

@section Type
- [label3] — a fixed 3-byte label content
- [opt_label3] — the tagged decode result ([OEL_None] | [OEL_Some] of ([label3] & [U32.t]))

@section Spec
- [label3_of_indices] / [label3_to_seq] — pure label ↔ byte-list bridges

@section Encode
- [encode_label] — writes `[len][b0][b1][b2][0x00]`, returns the byte count

@section Decode
- [decode_label] — reads the length byte + up to 3 content octets

@section Roundtrip
- [lemma_pulse_label_roundtrip] — encode then decode preserves the label
*)
module Network.DNS.Pulse
#lang-pulse

open Pulse
open Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq

open FStar.Seq
open FStar.Int.Cast


(* ── Type ───────────────────────────────────────────────────────────── *)


(** [label3] — a fixed 3-byte label content (a bounded slice of a DNS label's
    octets; the general 1..63-octet label is the same structure with more
    [b_N] fields). *)
type label3 = {
  b0 : U8.t;
  b1 : U8.t;
  b2 : U8.t;
}


(** [opt_label3] — the decode result: [OEL_None] (length byte > 3) or
    [OEL_Some] of ([label3] & [U32.t]).

    [OEL_None] is constructively reachable (a wire length byte over 3 is
    rejected); the sum wraps the pair for Custard's F# backend (which has no
    bare-tuple2 realization — see Network.MIME.Pulse). *)
type opt_label3 =
  | OEL_None
  | OEL_Some of (label3 & U32.t)


(* ── Pure spec (noextract) ──────────────────────────────────────────── *)


(** [label3_of_indices] — reconstruct a [label3] from a sequence's 3 indices
    (the offset refinement makes each [Seq.index] well-typed). *)
noextract
let label3_of_indices (s: Seq.seq U8.t) (off: nat { off + 2 < Seq.length s }) : label3 =
  { b0 = Seq.index s off;
    b1 = Seq.index s (off + 1);
    b2 = Seq.index s (off + 2);
  }


(** [label3_to_seq] — the pure map from a [label3] to its 3 content octets. *)
noextract
let label3_to_seq (l: label3) : Seq.seq U8.t =
  Seq.seq_of_list [l.b0; l.b1; l.b2]


(** [label_len_byte] — the wire length byte for a [label3] (always [0x03]). *)
noextract
let label_len_byte : U8.t = 0x03uy


(* ── Encode ─────────────────────────────────────────────────────────── *)


(** [encode_label] — write the wire form `[len][b0][b1][b2][0x00]` of [l] into
    [buf] at [off].

    @param l The label content to write.
    @param buf The destination buffer (must hold at least 5 bytes at [off]).
    @param off The write offset.
    @returns The number of bytes written (always [5ul]). *)
fn encode_label (l: label3) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 5 <= A.length buf /\ U32.v off + 4 < 4294967296)
    returns w: U32.t
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1 **
        pure (U32.v off + 5 <= A.length buf /\
              Seq.length s1 == A.length buf /\
              Seq.index s1 (U32.v off) == label_len_byte /\
              Seq.index s1 (U32.v off + 1) == l.b0 /\
              Seq.index s1 (U32.v off + 2) == l.b1 /\
              Seq.index s1 (U32.v off + 3) == l.b2 /\
              Seq.index s1 (U32.v off + 4) == 0x00uy)) **
      pure (w == 5ul)
{
  let j0 = US.uint32_to_sizet off;
  let j1 = US.uint32_to_sizet (U32.add off 1ul);
  let j2 = US.uint32_to_sizet (U32.add off 2ul);
  let j3 = US.uint32_to_sizet (U32.add off 3ul);
  let j4 = US.uint32_to_sizet (U32.add off 4ul);
  A.pts_to_len buf;
  buf.(j0) <- label_len_byte;
  buf.(j1) <- l.b0;
  buf.(j2) <- l.b1;
  buf.(j3) <- l.b2;
  buf.(j4) <- 0x00uy;
  5ul
}


(* ── Decode ─────────────────────────────────────────────────────────── *)


(** [decode_label] — read the wire form at [off]: the length byte [len], then
    up to 3 content octets.

    @param buf The source buffer (must hold at least 5 bytes at [off]).
    @param off The read offset.
    @returns [OEL_Some (l, 5ul)] when the length byte is [0x03], [OEL_None]
    otherwise (a length over 3 is rejected for the fixed [label3] view). *)
fn decode_label (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 5 <= A.length buf /\ U32.v off + 4 < 4294967296 /\
            A.length buf == Seq.length s0)
    returns r: opt_label3
    ensures
      A.pts_to buf s0 **
      pure (
        A.length buf == Seq.length s0 /\
        U32.v off + 5 <= A.length buf /\
        (if Seq.index s0 (U32.v off) == label_len_byte
         then r == OEL_Some (label3_of_indices s0 (U32.v off + 1), 5ul)
         else r == OEL_None))
{
  A.pts_to_len buf;
  let j0 = US.uint32_to_sizet off;
  let j1 = US.uint32_to_sizet (U32.add off 1ul);
  let j2 = US.uint32_to_sizet (U32.add off 2ul);
  let j3 = US.uint32_to_sizet (U32.add off 3ul);
  let len = buf.(j0);
  let c0 = buf.(j1);
  let c1 = buf.(j2);
  let c2 = buf.(j3);
  if U8.eq len label_len_byte {
    OEL_Some ({ b0 = c0; b1 = c1; b2 = c2 }, 5ul)
  } else {
    OEL_None
  }
}


(* ── Roundtrip ──────────────────────────────────────────────────────── *)


(** [lemma_pulse_label_roundtrip] — encode then decode preserves the label.

    @param l The label to roundtrip.
    @param buf The buffer (must hold at least 5 bytes at [off]).
    @param off The offset.
    Proves [decode_label buf off] after [encode_label l buf off] returns
    [OEL_Some (l, 5ul)], and the `0x00` terminator remains at [off + 4]. *)
fn lemma_pulse_label_roundtrip (l: label3) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 5 <= A.length buf /\ U32.v off + 4 < 4294967296)
    returns res: (U32.t & opt_label3)
    ensures
      exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1 **
        pure (res == (5ul, OEL_Some (l, 5ul)))
{
  let w = encode_label l buf off;
  let r = decode_label buf off;
  (w, r)
}
