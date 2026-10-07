(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Network.DNS — Domain Name System (RFC 1034, 1035).

Domain names in their two RFC 1035 §3.1 representations:

- the **text form** (dotted): [label ('.' label)*], each label a run of
  `[A-Za-z0-9-]` one to 63 octets long — carried by [label_codec] /
  [encode_domain] / [decode_domain] here.
- the **wire form** (length-prefixed): a length byte then the label octets,
  terminated by a [0x00] root label — enforced by the Pulse leaf
  [Network.DNS.Pulse] (see that module).

Written for F* v2026.09.20 (the record [codec a] API in [Data.Codec]; the old
GADT [make_codec]/[encode_spec]/[decode_spec] surface is deleted).  Zero admits.

@header Network.DNS

@section Types
- [domain_label] — a single label ([label_bytes : list byte])
- [domain_name] — [labels] + [fully_qualified]
- [hostname] — a [domain_name]

@section Predicates
- [is_dot] — the `.` separator
- [is_label_char] — the RFC 1035 §3.1 label run predicate
- [label_wfcv] — a well-formed label (non-empty, ≤ 63 label chars)

@section Codec
- [label_codec] — a single label ([satisfy_many1 is_label_char], 1..63 octets)
- [decode_domain] / [encode_domain] — the dotted form (list level)

@section String view
- [ascii_bytes_to_string] / [string_to_ascii_bytes] — ASCII bridges
- [string_of_domain] / [domain_of_string] / [hostname_of_string]

@section Constructors
- [domain_of_labels] / [root_domain]

@section Lemmas
- [lemma_domain_roundtrip] / [lemma_encode_domain_roundtrip] /
  [lemma_label_codec_roundtrip] / [lemma_label_length]
- concrete encode-vector lemmas ([example.com], [www]) + reject lemmas
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


(** [is_dot] — the RFC 1035 §3.1 label separator (`.` = 0x2E).

    @param b The byte to test.
    @returns [true] iff [b] is the dot separator ([0x2E]). *)
let is_dot (b: byte) : bool = U8.v b = 0x2E


(** [is_label_char] — the RFC 1035 §3.1 label character predicate:
    `A-Z a-z 0-9 -`.

    @param b The byte to test.
    @returns [true] iff [b] is in the label alphabet. *)
let is_label_char (b: byte) : bool =
  let v = U8.v b in
  (0x41 <= v && v <= 0x5A) || (0x61 <= v && v <= 0x7A) ||
  (0x30 <= v && v <= 0x39) || v = 0x2D


(** [label_wfcv] — a [domain_label] is well-formed: a non-empty run of label
    characters at most 63 octets.  (A local [bool] mirror of [label_codec]'s
    guard, so the roundtrip lemmas can discharge it structurally rather than
    through the opaque [codec] fields.)

    @param dl The label to test.
    @returns [true] iff [dl.label_bytes] is a non-empty run of label chars of
             length at most 63. *)
let label_wfcv (dl: domain_label) : bool =
  Cons? dl.label_bytes && List.Tot.for_all is_label_char dl.label_bytes &&
  List.Tot.length dl.label_bytes <= 63


(* ========================================================================
   Codec
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
   Dotted form (codec)
   ======================================================================== *)


(** [domain_codec] — the dotted form [label ('.' label)*] as a record [codec
    (list domain_label)], built from the [sep_by1] separator-fold (Mandate 22:
    no bespoke scanner).  Encodes labels left-to-right with a [.] (0x2E)
    BETWEEN them (no trailing dot — the non-FQ text form).

    The [max] is 127 (RFC 1035 §2.3.4 label-count bound), which is the
    termination fuel for [sep_by1]'s greedy decoder. *)
let domain_codec : codec (list domain_label) =
  sep_by1 label_codec (byte_val 0x2Euy) 127


(** [domain_wfcv] — a non-empty label list is well-formed for [domain_codec]:
    definitionally [domain_codec.wfcv ls] (each label is a [label_wfcv] label
    and there are at most 127 labels — RFC 1035 §2.3.4 bounds a name's label
    count). *)
let domain_wfcv (ls: list domain_label) : bool =
  domain_codec.wfcv ls


(** [domain_wfcv_prop] — the propositional side of [domain_codec.wfcv]. *)
let domain_wfcv_prop (ls: list domain_label) : prop =
  domain_codec.wfcv_prop ls


(** [domain_rest_cond] — the trailing-suffix condition of [domain_codec]. *)
let domain_rest_cond (ls: list domain_label) (r: byte_seq) : prop =
  domain_codec.rest_cond ls r


(** [encode_domain] — serialize a [domain_name] to the dotted form via
    [domain_codec.enc] (crossing the [byte_seq]→[list byte] boundary).

    @param d The name to serialize.
    @returns The dotted byte list of [d.labels]. *)
let encode_domain (d: domain_name) : Tot (list byte) =
  Seq.seq_to_list (domain_codec.enc d.labels)


(** [decode_domain] — parse the dotted form [label ('.' label)*] into a
    [domain_name] via [domain_codec.dec] (crossing the [list byte]→[byte_seq]
    boundary).  [None] unless the WHOLE input is consumed (the decoder
    consumed [n] == [Seq.length] input).  The dotted text form carries no
    [fully_qualified] flag, so the result is always [fully_qualified = false]
    (the trailing-dot FQ form is out of scope for the pure dotted codec — see
    the 8.2 decision).

    @param bs The dotted byte list.
    @returns [Some d] when [bs] is exactly the dotted form, else [None]. *)
let decode_domain (bs: list byte) : option domain_name =
  let s = Seq.seq_of_list bs in
  match domain_codec.dec s with
  | Inl _ -> None
  | Inr (ls, n) ->
      if n = Seq.length s then Some ({ labels = ls; fully_qualified = false })
      else None


(* ========================================================================
   String view
   ======================================================================== *)


(** [ascii_bytes_to_string] — ASCII [list byte] to [string] (code points < 128).

    @param bs The ASCII byte list.
    @returns The reconstructed [string]. *)
let ascii_bytes_to_string (bs: list byte) : string =
  FStar.String.string_of_list
    (List.Tot.map (fun (b: byte) -> FStar.Char.char_of_int (U8.v b)) bs)


(** [string_to_ascii_bytes] — [string] to [list byte], truncating code points
    via `% 256`.  Only valid for ASCII strings.

    @param s The [string] to convert.
    @returns The byte list (ASCII only). *)
let string_to_ascii_bytes (s: string) : list byte =
  List.Tot.map (fun (c: FStar.Char.char) -> U8.uint_to_t (FStar.Char.int_of_char c % 256))
    (FStar.String.list_of_string s)


(** [string_of_domain] — serialize a [domain_name] to its dotted text.

    @param d The name to serialize.
    @returns The dotted text (ASCII). *)
let string_of_domain (d: domain_name) : Tot string =
  ascii_bytes_to_string (encode_domain d)


(** [domain_of_string] — parse a dotted text string into a [domain_name];
    [None] unless the whole string is consumed by [decode_domain].

    @param s The dotted text string.
    @returns [Some d] on a complete parse, else [None]. *)
let domain_of_string (s: string) : GTot (option domain_name) =
  decode_domain (string_to_ascii_bytes s)


(** [hostname_of_string] — parse a dotted text string into a [hostname].

    @param s The dotted text string.
    @returns [Some h] on a complete parse, else [None]. *)
let hostname_of_string (s: string) : GTot (option hostname) =
  match domain_of_string s with
  | Some d -> Some ({ name = d })
  | None -> None


(* ========================================================================
   Constructors
   ======================================================================== *)


(** [domain_of_labels] — construct a [domain_name] from a label list + flag.

    @param ls The labels.
    @param fq The fully-qualified flag.
    @returns The name [ { labels = ls; fully_qualified = fq } ]. *)
let domain_of_labels (ls: list domain_label) (fq: bool) : domain_name =
  { labels = ls; fully_qualified = fq }


(** [root_domain] — the root domain (empty name, fully-qualified). *)
let root_domain : domain_name = { labels = []; fully_qualified = true }


(* ========================================================================
   Lemmas
   ======================================================================== *)


(** [lemma_domain_roundtrip] — the dotted-form codec roundtrip: decoding the
    encoding of a well-formed non-empty label list recovers the list (at the
    Seq level, via [domain_codec.roundtrip]).

    @param ls The labels (require [domain_wfcv ls] / [domain_wfcv_prop ls] /
             [domain_rest_cond ls Seq.empty]).
    Ensures [domain_codec.dec (domain_codec.enc ls ++ empty) == Inr (ls, |enc ls|)]. *)
let lemma_domain_roundtrip (ls: list domain_label) : Lemma
  (requires domain_wfcv ls /\ domain_wfcv_prop ls /\ domain_rest_cond ls Seq.empty)
  (ensures domain_codec.dec (domain_codec.enc ls `Seq.append` Seq.empty)
           == Inr (ls, Seq.length (domain_codec.enc ls)))
  = domain_codec.roundtrip ls Seq.empty


(** [lemma_encode_domain_roundtrip] — roundtrip of the dotted form through the
    [encode_domain]/[decode_domain] wrappers: decoding the encoding of a
    well-formed non-empty label name recovers the name ([fully_qualified = false]).

    @param d The name (require [fully_qualified = false] and a well-formed
             non-empty label list).
    Ensures [decode_domain (encode_domain d) == Some d]. *)
let lemma_encode_domain_roundtrip (d: domain_name) : Lemma
  (requires d.fully_qualified = false /\
            domain_wfcv d.labels /\ domain_wfcv_prop d.labels /\
            domain_rest_cond d.labels Seq.empty)
  (ensures decode_domain (encode_domain d) == Some d)
  =
  lemma_domain_roundtrip d.labels;
  Seq.append_empty_r (domain_codec.enc d.labels);
  lemma_seq_list_bij (domain_codec.enc d.labels);
  lemma_seq_of_list_length (Seq.seq_to_list (domain_codec.enc d.labels));
  assert (domain_codec.dec (Seq.seq_of_list (Seq.seq_to_list (domain_codec.enc d.labels)))
          == Inr (d.labels, Seq.length (domain_codec.enc d.labels)));
  assert (Seq.seq_of_list (Seq.seq_to_list (domain_codec.enc d.labels)))
          == domain_codec.enc d.labels;
  ()



(** [lemma_example_com_concrete] — encoding the two-label name
    [example.com] produces the exact dotted byte list (RGB §85 Wall 2: the
    concrete ENCODE is proven via [Seq.lemma_eq_intro], not a [decode]
    reduction through [sep_by1]). *)
let lemma_example_com_concrete () : Lemma
  (ensures
    encode_domain ({ labels = [ { label_bytes = [0x65uy; 0x78uy; 0x61uy; 0x6Duy; 0x70uy; 0x6Cuy; 0x65uy] };
                                { label_bytes = [0x63uy; 0x6Fuy; 0x6Duy] } ];
                     fully_qualified = false })
    == [0x65uy; 0x78uy; 0x61uy; 0x6Duy; 0x70uy; 0x6Cuy; 0x65uy;
        0x2Euy;
        0x63uy; 0x6Fuy; 0x6Duy])
  = Seq.lemma_eq_intro
      (domain_codec.enc [ { label_bytes = [0x65uy; 0x78uy; 0x61uy; 0x6Duy; 0x70uy; 0x6Cuy; 0x65uy] };
                           { label_bytes = [0x63uy; 0x6Fuy; 0x6Duy] } ])
      (seq_of_list [0x65uy; 0x78uy; 0x61uy; 0x6Duy; 0x70uy; 0x6Cuy; 0x65uy;
                    0x2Euy;
                    0x63uy; 0x6Fuy; 0x6Duy]);
    ()


(** [lemma_label_codec_roundtrip] — the single-label codec roundtrip: decoding
    the encoding of a well-formed label recovers the label.

    @param dl The label (require [label_wfcv dl]).
    Ensures [label_codec.dec (label_codec.enc dl ++ empty) == Inr (dl, |enc dl|)]. *)
let lemma_label_codec_roundtrip (dl: domain_label) : Lemma
  (requires label_wfcv dl)
  (ensures label_codec.dec (label_codec.enc dl `Seq.append` Seq.empty)
           == Inr (dl, Seq.length (label_codec.enc dl)))
  = label_codec.roundtrip dl Seq.empty


(** [lemma_label_concrete] — [label_codec] decodes a raw label run to its
    label. *)
let lemma_label_concrete () : Lemma
  (ensures
    (match label_codec.dec (Seq.seq_of_list [0x77uy; 0x77uy; 0x77uy]) with
     | Inr (dl, _) -> dl.label_bytes = [0x77uy; 0x77uy; 0x77uy]
     | _ -> False))
  = ()


(** [lemma_label_length] — a well-formed label run is 1..63 octets.

    @param dl The label (require [label_wfcv dl]).
    Ensures [Cons? dl.label_bytes /\\ |dl.label_bytes| <= 63]. *)
let lemma_label_length (dl: domain_label) : Lemma
  (requires label_wfcv dl)
  (ensures Cons? dl.label_bytes /\ List.Tot.length dl.label_bytes <= 63)
  = ()


(** [lemma_root_domain_concrete] — the well-formedness guard rejects the empty
    label list ([domain_wfcv [] == false]): the root is a [0x00] wire byte,
    not an empty dotted text (which [sep_by1]'s non-empty [wfcv] excludes). *)
let lemma_root_domain_concrete () : Lemma
  (ensures domain_wfcv [] == false)
  = ()


(** [lemma_single_label_concrete] — encoding a single [www] label produces
    exactly its three byte octets (concrete ENCODE via [Seq.lemma_eq_intro],
    mirroring MIME's concrete-encode pattern — §85 Wall 2). *)
let lemma_single_label_concrete () : Lemma
  (ensures
    encode_domain ({ labels = [ { label_bytes = [0x77uy; 0x77uy; 0x77uy] } ];
                     fully_qualified = false })
    == [0x77uy; 0x77uy; 0x77uy])
  = Seq.lemma_eq_intro
      (domain_codec.enc [ { label_bytes = [0x77uy; 0x77uy; 0x77uy] } ])
      (seq_of_list [0x77uy; 0x77uy; 0x77uy]);
    ()
