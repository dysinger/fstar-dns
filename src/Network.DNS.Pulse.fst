(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Network.DNS.Pulse — C-extractable DNS label wire-format encode/decode via
Pulse + Custard.

A single DNS label in the RFC 1035 §3.1 wire form: a length byte (1..63)
followed by the label octets, with a `0x00` root terminator ending the name.
The content octets are carried in a caller-provided [Pulse.Lib.Array] of
[U8.t]; the length byte names how many of them form the label.

The wire form is `[len][b0..b_{len-1}][0x00]` — a *variable-length* label
(1..63 octets), NOT the earlier fixed 3-byte `label3` slice.  The copy is a
Pulse [while] loop whose invariant carries the `pts_to` frames plus a
`len`-progress measure, matching [Pulse.Lib.Array.memcpy_l] (offset-indexed).

Written for F* v2026.09.20 (Custard `--custard_backend C`).  Zero admits.

@header Network.DNS.Pulse

@section Type
- [opt_label] — the tagged decode result ([ODL_None] | [ODL_Some] of [U32.t])

@section Encode
- [encode_label] — writes `[len][b0..][0x00]`, returns the byte count

@section Decode
- [decode_label] — reads the length byte + content + terminator

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


(* ========================================================================
   Type
   ======================================================================== *)


(** [opt_label] — the decode result: [ODL_None] (a length byte outside 1..63)
    or [ODL_Some] of the label octet length ([U32.t]).

    The content octets themselves stay in the caller's buffer (the decode
    reads them in place, it does not copy them out); only the length crosses
    the C ABI.  [ODL_None] is constructively reachable (a wire length byte 0
    or over 63 is rejected). *)
type opt_label =
  | ODL_None
  | ODL_Some of U32.t


(* ========================================================================
   Named constants
   ======================================================================== *)


(** [root_byte] — the [0x00] root-label terminator that ends a name on the
    wire (RFC 1035 §3.1). *)
let root_byte : U8.t = 0x00uy


(** [u32_max] — [2^32], the U32 overflow bound ([U32.v i + k < u32_max]). *)
let u32_max : nat = 4294967296


(** [lemma_cast_roundtrip] — [uint32_to_uint8] then [uint8_to_uint32] is the
    identity for values under 256 (the width is lossless below [2^8]). *)
noextract
let lemma_cast_roundtrip (x: U32.t) : Lemma
  (requires U32.v x < 256)
  (ensures uint8_to_uint32 (uint32_to_uint8 x) == x)
  [SMTPat (uint8_to_uint32 (uint32_to_uint8 x))]
  = ()


(* ========================================================================
   Encode
   ======================================================================== *)


(** [encode_label] — write the wire form of a label into [dst] at [off].

    [src] holds the 1..63 content octets at indices [0 .. len); [len] names
    how many (a byte, so [U32.v len <= 63]).  The wire form is:

        [dst[off] = len][dst[off+1 .. off+len] = src[0 .. len)][dst[off+len+1] = 0x00]

    i.e. [len + 2] bytes total (length byte, content, root terminator).

    The writes are a [while] loop over the content range; only the bytes in
    [off .. off+len+2) change — every other byte of [dst] is preserved (see
    the [ensures]).

    @param src The source content octets (length [>= U32.v len]).
    @param len The label octet count (1..63).
    @param dst The destination buffer (holds [len+2] bytes at [off]).
    @param off The write offset.
    @returns The number of bytes written ([len + 2]). *)
fn encode_label (src: A.array U8.t) (len: U32.t) (dst: A.array U8.t) (off: U32.t)
    (#src0: erased (Seq.seq U8.t))
    (#dst0: erased (Seq.seq U8.t))
    requires
      A.pts_to src src0 **
      A.pts_to dst dst0 **
      pure (1 <= U32.v len /\ U32.v len <= 63 /\
            U32.v len <= A.length src /\
            U32.v off + U32.v len + 2 <= A.length dst /\
            U32.v off + U32.v len + 1 < u32_max /\
            U32.v len + 2 < u32_max)
    returns w: U32.t
    ensures
      A.pts_to src src0 **
      (exists* (s1: Seq.seq U8.t).
        A.pts_to dst s1 **
        pure (1 <= U32.v len /\ U32.v len <= 63 /\
              U32.v len <= A.length src /\
              Seq.length src0 == A.length src /\
              U32.v off + U32.v len + 2 <= A.length dst /\
              Seq.length s1 == A.length dst /\
              U32.v len + 2 < u32_max /\
              Seq.index s1 (U32.v off) == uint32_to_uint8 len /\
              (forall (j: nat). j < U32.v len ==>
                 Seq.index s1 (U32.v off + 1 + j) == Seq.index src0 j) /\
              Seq.index s1 (U32.v off + 1 + U32.v len) == root_byte)) **
      pure (w == U32.add_mod len 2ul)
{
  A.pts_to_len src;
  A.pts_to_len dst;
  let joff = US.uint32_to_sizet off;
  (* Length byte. *)
  dst.(joff) <- uint32_to_uint8 len;
  (* Content octets: copy src[0..len) into dst[off+1 .. off+1+len). *)
  let mut i : US.t = 0sz;
  while (US.lt !i (US.uint32_to_sizet len))
    invariant exists* (vi: US.t) (s: Seq.seq U8.t).
      pts_to i vi **
      A.pts_to src src0 **
      A.pts_to dst s **
      pure (
        US.v vi <= U32.v len /\
        1 <= U32.v len /\ U32.v len <= 63 /\
        U32.v len <= A.length src /\
        Seq.length src0 == A.length src /\
        U32.v off + U32.v len + 2 <= A.length dst /\
        Seq.length s == A.length dst /\
        Seq.index s (U32.v off) == uint32_to_uint8 len /\
        (forall (j: nat). j < US.v vi ==>
           Seq.index s (U32.v off + 1 + j) == Seq.index src0 j))
    decreases (U32.v len - US.v !i)
  {
    let vi = !i;
    let jdst = US.add (US.add joff 1sz) vi;
    dst.(jdst) <- src.(vi);
    i := US.add vi 1sz;
  };
  (* Root terminator. *)
  let jterm = US.add (US.add joff 1sz) (US.uint32_to_sizet len);
  dst.(jterm) <- root_byte;
  U32.add_mod len 2ul
}


(* ========================================================================
   Decode
   ======================================================================== *)


(** [decode_label] — read the wire form at [off]: the length byte [len], then
    [len] content octets, then the terminator.

    A length byte 0 or over 63 is rejected (0 is the root terminator, over 63
    is an out-of-range or compression-pointer length).

    @param buf The source buffer.
    @param off The read offset.
    @returns [ODL_Some (spec, len)] on a well-formed label, else [ODL_None],
             where [spec] carries the octet length and the content slice. *)
fn decode_label (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 65 <= A.length buf /\
            A.length buf == Seq.length s0 /\
            U32.v off + 64 < u32_max)
    returns r: opt_label
    ensures
      A.pts_to buf s0 **
      pure (
        A.length buf == Seq.length s0 /\
        U32.v off + 65 <= A.length buf /\
        (let lb = Seq.index s0 (U32.v off) in
         let v = U8.v lb in
         if 1 <= v && v <= 63
         then r == ODL_Some (uint8_to_uint32 lb)
         else r == ODL_None))
{
  A.pts_to_len buf;
  let joff = US.uint32_to_sizet off;
  let lb = buf.(joff);
  if (U8.lt lb 1uy || U8.gt lb 63uy) {
    ODL_None
  } else {
    ODL_Some (uint8_to_uint32 lb)
  }
}


(* ========================================================================
   Roundtrip
   ======================================================================== *)


(** [lemma_pulse_label_roundtrip] — encode then decode preserves the label.

    @param src The content octets.
    @param len The label octet count (1..63).
    @param dst The buffer (holds [len+2] bytes at [off]).
    @param off The offset.
    @returns [(len+2, ODL_Some len)] — encode then decode recovers the label
             length, and the content octets in [dst] equal [src[0..len)]. *)
fn lemma_pulse_label_roundtrip (src: A.array U8.t) (len: U32.t) (dst: A.array U8.t) (off: U32.t)
    (#src0: erased (Seq.seq U8.t))
    (#dst0: erased (Seq.seq U8.t))
    requires
      A.pts_to src src0 **
      A.pts_to dst dst0 **
      pure (1 <= U32.v len /\ U32.v len <= 63 /\
            U32.v len <= A.length src /\
            U32.v off + U32.v len + 2 <= A.length dst /\
            U32.v off + U32.v len + 1 < u32_max /\
            U32.v off + 65 <= A.length dst /\
            U32.v off + 64 < u32_max)
    returns res: (U32.t & opt_label)
    ensures
      exists* (s1: Seq.seq U8.t).
        A.pts_to src src0 **
        A.pts_to dst s1 **
        pure (res == (U32.add_mod len 2ul, ODL_Some len))
{
  let w = encode_label src len dst off;
  let r = decode_label dst off;
  (w, r)
}
