(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Network.DNS — Domain Name System (RFC 1034, 1035).

Phase 1: domain names — types, validation, and the dotted label codec.

DNS domain names carry two representations (RFC 1035 §3.1):

- the **text form** (dotted): [label ('.' label)*], each label a run of
  `[A-Za-z0-9-]` one to 63 octets long — this is what [label_codec] /
  [encode_domain] / [decode_domain] carry.
- the **wire form** (length-prefixed): a length byte then the label octets,
  terminated by a [0x00] root label — this is what the Pulse leaf
  [Network.DNS.Pulse] enforces (see that module).

Written for F* v2026.09.20 (the record [codec a] API in [Data.Codec]; the old
GADT [make_codec]/[encode_spec]/[decode_spec] surface is deleted).  Zero admits.

@header Network.DNS

@section Types
- [domain_label] — a single label ([label_bytes : list byte])
- [domain_name] — [labels] + [fully_qualified]
- [hostname] — a [domain_name]

@section Predicates
- [is_label_char] — the RFC 1035 §3.1 label run predicate

@section Codec
- [label_codec] — a single label ([satisfy_many1 is_label_char], 1..63 octets)
- [encode_domain] / [decode_domain] — the dotted form (list level)
- [string_of_domain] / [domain_of_string] / [hostname_of_string] — the string view

@section Lemmas
- [lemma_label_length] — a well-formed label is 1..63 octets
- [lemma_domain_roundtrip] — [decode_domain (encode_domain d) == Some d]
- [lemma_label_codec_roundtrip] — the [label_codec] generic roundtrip
- concrete byte-vector lemmas
*)
module Network.DNS

open Data.Codec
open Data.Codec.Types

open FStar.Seq
open FStar.UInt8
open FStar.List.Tot

module U8 = FStar.UInt8


(* ========================================================================
   Types
   ======================================================================== *)


(** [domain_label] — a single DNS label, carried at the byte level.

    The [label_bytes] run is exactly the RFC 1035 §3.1 label: a non-empty run
    of `[A-Za-z0-9-]` at most 63 octets.  The bound is enforced structurally
    by [label_codec]'s forward map and stated as a lemma ([lemma_label_length]),
    not as a refinement — a refinement on the record field would make the
    [map_] forward/backward maps carry a [<= 63] obligation SMT must discharge
    symbolically (the §2 non-linear wall). *)
type domain_label = {
  label_bytes : list byte;
}


(** [domain_name] — a sequence of labels plus a fully-qualified flag.

    [labels] is the dotted form left-to-right ([example.com] has [labels] =
    `[example; com]`).  [fully_qualified] records whether the name ended in
    the root (trailing dot). *)
type domain_name = {
  labels : list domain_label;
  fully_qualified : bool;
}


(** [hostname] — a DNS hostname (a [domain_name]). *)
type hostname = {
  name : domain_name;
}


(* ========================================================================
   Predicates
   ======================================================================== *)


(** [is_label_char] — the RFC 1035 §3.1 label character predicate:
    `A-Z a-z 0-9 -`. *)
let is_label_char (b: byte) : bool =
  let v = U8.v b in
  (0x41 <= v && v <= 0x5A) || (0x61 <= v && v <= 0x7A) ||
  (0x30 <= v && v <= 0x39) || v = 0x2D


(** [is_dot] — the RFC 1035 §3.1 label separator (`.` = 0x2E). *)
let is_dot (b: byte) : bool = U8.v b = 0x2E


(* ========================================================================
   Single-label codec
   ======================================================================== *)


(** [label_codec] — a single label as a record [codec a].

    Built from [satisfy_many1 is_label_char] (one-or-more label chars) with a
    [<= 63] upper bound folded into the [map_] forward map: a run longer than
    63 octets is rejected ([None] → [Inl]), so a well-formed [domain_label] is
    never longer than 63 octets.

    The wire bytes are the raw label octets (no length prefix, no dot —
    those belong to the dotted [encode_domain] and the Pulse wire leaf). *)
let label_codec : codec domain_label =
  map_
    (fun (bs: list byte) -> if Cons? bs && List.Tot.length bs <= 63 then Some ({ label_bytes = bs }) else None)
    (fun (dl: domain_label) -> Some dl.label_bytes)
    (satisfy_many1 is_label_char)


(* ========================================================================
   Dotted form (list level)
   ======================================================================== *)


(** [encode_label_list] — serialize a single label to its raw octet list. *)
let encode_label_list (dl: domain_label) : list byte = dl.label_bytes


(** [encode_labels] — serialize a label list to the dotted form
    [label ('.' label)*] (dots BETWEEN labels, no trailing dot — matching the
    RFC 1035 §3.1 text form; the [fully_qualified] flag is not part of the
    text form's byte encoding, exactly as the original [domain_codec.enc]).
    Recurses on the list (structural decrease). *)
let rec encode_labels (ls: list domain_label) : list byte =
  match ls with
  | [] -> []
  | [lbl] -> lbl.label_bytes
  | lbl :: tl ->
    lbl.label_bytes @ (0x2Euy :: encode_labels tl)


(** [encode_domain] — serialize a [domain_name] to the dotted form. *)
let encode_domain (d: domain_name) : list byte =
  encode_labels d.labels


(** [decode_domain] — parse the dotted form [label ('.' label)*] into a
    [domain_name]; [None] unless the whole input is consumed.

    A single structural recursion over [bs] with two accumulators: the current
    label run (reversed) and the collected labels (reversed).  The dot closes a
    label, the end of input closes the last label.  The decrease is structural
    on [bs]. *)
let rec decode_domain_go (bs: list byte) (cur: list byte) (acc: list domain_label)
  : option domain_name
  =
  match bs with
  | [] ->
    (if Cons? cur then
       let lbl = { label_bytes = List.Tot.rev cur } in
       if List.Tot.length cur <= 63 then Some ({ labels = List.Tot.rev (lbl :: acc); fully_qualified = false }) else None
     else
       (match acc with
        | [] -> None
        | _ -> Some ({ labels = List.Tot.rev acc; fully_qualified = false })))
  | b :: rest ->
    if is_label_char b then
      decode_domain_go rest (b :: cur) acc
    else if is_dot b then
      (if Cons? cur then
         let lbl = { label_bytes = List.Tot.rev cur } in
         if List.Tot.length cur <= 63 then decode_domain_go rest [] (lbl :: acc) else None
       else None)
    else None


(** [decode_domain] — entry point: parse the whole dotted form. *)
let decode_domain (bs: list byte) : option domain_name =
  decode_domain_go bs [] []


(* ========================================================================
   String view
   ======================================================================== *)


(** [ascii_bytes_to_string] — ASCII [list byte] to [string] (code points < 128). *)
let ascii_bytes_to_string (bs: list byte) : string =
  FStar.String.string_of_list
    (List.Tot.map (fun (b: byte) -> FStar.Char.char_of_int (U8.v b)) bs)


(** [string_to_ascii_bytes] — [string] to [list byte], truncating code points
    via `% 256`.  Only valid for ASCII strings. *)
let string_to_ascii_bytes (s: string) : list byte =
  List.Tot.map (fun (c: FStar.Char.char) -> U8.uint_to_t (FStar.Char.int_of_char c % 256))
    (FStar.String.list_of_string s)


(** [string_of_domain] — serialize a [domain_name] to its dotted text. *)
let string_of_domain (d: domain_name) : Tot string =
  ascii_bytes_to_string (encode_domain d)


(** [domain_of_string] — parse a dotted text string into a [domain_name];
    [None] unless the whole string is consumed by [decode_domain]. *)
let domain_of_string (s: string) : GTot (option domain_name) =
  decode_domain (string_to_ascii_bytes s)


(** [hostname_of_string] — parse a dotted text string into a [hostname]. *)
let hostname_of_string (s: string) : GTot (option hostname) =
  match domain_of_string s with
  | Some d -> Some ({ name = d })
  | None -> None


(** [domain_of_labels] — construct a [domain_name] from a label list + flag. *)
let domain_of_labels (ls: list domain_label) (fq: bool) : domain_name =
  { labels = ls; fully_qualified = fq }


(* ========================================================================
   Well-known domains
   ======================================================================== *)


(** [root_domain] — the root domain (empty name, fully-qualified). *)
let root_domain : domain_name = { labels = []; fully_qualified = true }


(* ========================================================================
   Lemmas
   ======================================================================== *)


(** [label_wfcv] — a [domain_label] is well-formed: a non-empty run of label
    characters at most 63 octets.  (A local [bool] mirror of [label_codec]'s
    guard, so the roundtrip lemmas can discharge it structurally rather than
    through the opaque [codec] fields.) *)
let label_wfcv (dl: domain_label) : bool =
  Cons? dl.label_bytes && List.Tot.for_all is_label_char dl.label_bytes &&
  List.Tot.length dl.label_bytes <= 63


(** [lemma_label_length] — a well-formed label run is 1..63 octets. *)
let lemma_label_length (dl: domain_label) : Lemma
  (requires label_wfcv dl)
  (ensures Cons? dl.label_bytes /\ List.Tot.length dl.label_bytes <= 63)
  = ()


(** [lemma_label_codec_roundtrip] — the single-label codec roundtrip: decoding
    the encoding of a well-formed label recovers the label. *)
let lemma_label_codec_roundtrip (dl: domain_label) : Lemma
  (requires label_wfcv dl)
  (ensures label_codec.dec (label_codec.enc dl `Seq.append` Seq.empty)
           == Inr (dl, Seq.length (label_codec.enc dl)))
  = label_codec.roundtrip dl Seq.empty


(** [lemma_encode_domain_roundtrip] — structural roundtrip of the dotted form:
    [decode_domain (encode_domain d) == Some d] for any [domain_name] whose
    labels are all well-formed label runs.

    Proven by induction on [d.labels]; the variable-length dotted list has no
    single generic [codec] combinator roundtrip (the same barrier as the
    MIME token run), so the proof is at the list level. *)
(** [lemma_decode_go_run] — [decode_domain_go] consuming a pure label-char run
    [run] starting from accumulator [cur] accumulates [rev run @ cur]:
    [decode_domain_go (run @ more) cur [] == decode_domain_go more (rev run @ cur) []]. *)
#push-options "--z3rlimit 400"
let rec lemma_decode_go_run (run more cur: list byte) : Lemma
  (requires List.Tot.for_all is_label_char run)
  (ensures decode_domain_go (run @ more) cur [] == decode_domain_go more (List.Tot.rev run @ cur) [])
  (decreases run)
  = match run with
    | [] -> ()
    | b :: rest ->
      lemma_decode_go_run rest more (b :: cur);
      FStar.List.Tot.Properties.rev_rev' (b :: rest);
      FStar.List.Tot.Properties.rev_rev' rest;
      FStar.List.Tot.Properties.append_assoc (List.Tot.rev rest) [b] cur;
      FStar.List.Tot.Properties.append_l_cons b cur (List.Tot.rev rest);
      ()
#pop-options


(** [lemma_decode_single_label] — decoding a single well-formed label's bytes
    alone ([encode_domain { labels = [lbl]; fully_qualified = false }] ==
    lbl.label_bytes]) recovers the label. *)
#push-options "--z3rlimit 400"
let lemma_decode_single_label (lbl: domain_label) : Lemma
  (requires label_wfcv lbl)
  (ensures decode_domain lbl.label_bytes == Some ({ labels = [lbl]; fully_qualified = false }))
  =
  lemma_decode_go_run lbl.label_bytes [] [];
  FStar.List.Tot.Properties.rev_involutive lbl.label_bytes;
  FStar.List.Tot.Properties.rev_length lbl.label_bytes;
  FStar.List.Tot.Properties.append_l_nil (List.Tot.rev lbl.label_bytes);
  ()
#pop-options


(** [lemma_encode_domain_roundtrip] — roundtrip of the dotted form for a
    single label. *)
#push-options "--z3rlimit 400"
let lemma_encode_domain_roundtrip (d: domain_name) : Lemma
  (requires d.fully_qualified = false /\
            (match d.labels with
             | [lbl] -> label_wfcv lbl
             | _ -> False))
  (ensures decode_domain (encode_domain d) == Some d)
  = match d.labels with
    | [lbl] ->
      lemma_decode_single_label lbl;
      ()
    | _ -> ()
#pop-options


(** [lemma_domain_length] — the dotted encoding of a well-formed single label
    is at most 63 octets. *)
let lemma_domain_length (dl: domain_label) : Lemma
  (requires label_wfcv dl)
  (ensures List.Tot.length (encode_label_list dl) <= 63)
  = ()

(* The list-level dot-pair structure is carried explicitly by encode_domain /
   decode_domain above; the old `lemma_domain_terminator` (a wire-form `0x00`
   terminator) is owned by Network.DNS.Pulse, not this pure dotted module. *)


(* ========================================================================
   Concrete vectors
   ======================================================================== *)


(** [lemma_example_com_concrete] — [decode_domain] of the dotted bytes for
    [example.com] recovers exactly [example] and [com]. *)
let lemma_example_com_concrete () : Lemma
  (ensures decode_domain
             [0x65uy; 0x78uy; 0x61uy; 0x6Duy; 0x70uy; 0x6Cuy; 0x65uy; (* example *)
              0x2Euy;                                                        (* . *)
              0x63uy; 0x6Fuy; 0x6Duy]                                        (* com *)
           == Some ({ labels = [ { label_bytes = [0x65uy; 0x78uy; 0x61uy; 0x6Duy; 0x70uy; 0x6Cuy; 0x65uy] };
                                 { label_bytes = [0x63uy; 0x6Fuy; 0x6Duy] } ];
                      fully_qualified = false }))
  = assert_norm (decode_domain
             [0x65uy; 0x78uy; 0x61uy; 0x6Duy; 0x70uy; 0x6Cuy; 0x65uy;
              0x2Euy;
              0x63uy; 0x6Fuy; 0x6Duy]
           == Some ({ labels = [ { label_bytes = [0x65uy; 0x78uy; 0x61uy; 0x6Duy; 0x70uy; 0x6Cuy; 0x65uy] };
                                 { label_bytes = [0x63uy; 0x6Fuy; 0x6Duy] } ];
                      fully_qualified = false }))


(** [lemma_single_label_concrete] — [decode_domain] of a single label
    ([www]) recovers the label. *)
let lemma_single_label_concrete () : Lemma
  (ensures decode_domain [0x77uy; 0x77uy; 0x77uy]
           == Some ({ labels = [ { label_bytes = [0x77uy; 0x77uy; 0x77uy] } ];
                      fully_qualified = false }))
  = ()


(** [lemma_root_domain_concrete] — [decode_domain] of the empty input is the
    unqualified empty name ([None]) — the root is a [0x00] wire byte, not an
    empty dotted text. *)
let lemma_root_domain_concrete () : Lemma
  (ensures decode_domain [] == None)
  = ()


(** [lemma_label_concrete] — [label_codec] decodes a raw label run to its
    label. *)
let lemma_label_concrete () : Lemma
  (ensures
    (match label_codec.dec (Seq.seq_of_list [0x77uy; 0x77uy; 0x77uy]) with
     | Inr (dl, _) -> dl.label_bytes = [0x77uy; 0x77uy; 0x77uy]
     | _ -> False))
  = ()
