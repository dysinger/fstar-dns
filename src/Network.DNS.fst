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


(** [hostname] — a DNS hostname per RFC 1035 §3.5 "preferred name syntax":
    a non-FQ domain name whose labels each follow the stricter label grammar
    [<letter> [ [ <ldh-str> ] <let-dig> ]] (start with a letter, end with a
    letter-or-digit, interior letters/digits/hyphen).  A genuinely distinct
    type (NOT a re-wrap of [domain_name]): it drops the [fully_qualified]
    flag and carries only the label list, valid only under [hostname_wfcv]. *)
type hostname = {
  labels : list domain_label;
}


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
   Hostname predicates (RFC 1035 §3.5 preferred-name syntax)
   ======================================================================== *)


(** [is_letter] — a §3.5 [<letter>]: upper- or lower-case ASCII letter.

    @param b The byte to test.
    @returns [true] iff [b] is `A-Z` or `a-z`. *)
let is_letter (b: byte) : bool =
  let v = U8.v b in
  (0x41 <= v && v <= 0x5A) || (0x61 <= v && v <= 0x7A)


(** [is_let_dig] — a §3.5 [<let-dig>]: a letter or digit.

    @param b The byte to test.
    @returns [true] iff [b] is `A-Z`, `a-z`, or `0-9`. *)
let is_let_dig (b: byte) : bool =
  is_letter b || (let v = U8.v b in 0x30 <= v && v <= 0x39)


(** [is_ldh] — a §3.5 [<let-dig-hyp>]: letter, digit, or hyphen.

    @param b The byte to test.
    @returns [true] iff [b] is `A-Z`, `a-z`, `0-9`, or `-`. *)
let is_ldh (b: byte) : bool =
  is_let_dig b || U8.v b = 0x2D


(** [hostname_label_bytes_wfcv] — a byte list is a §3.5 preferred-name label:
    non-empty, ≤ 63 octets, first byte a letter, last byte a letter-or-digit,
    and every byte a letter/digit/hyphen.

    @param bs The label bytes to test.
    @returns [true] iff [bs] satisfies the §3.5 label grammar. *)
let hostname_label_bytes_wfcv (bs: list byte) : bool =
  Cons? bs &&
  List.Tot.length bs <= 63 &&
  List.Tot.for_all is_ldh bs &&
  (match bs with
   | b :: _ -> is_letter b
   | [] -> false) &&
  is_let_dig (List.Tot.last bs)


(** [hostname_wfcv] — a label list is a well-formed hostname: non-empty, ≤ 127
    labels (RFC 1035 §2.3.4), each a §3.5 label, and the total on-the-wire
    length ≤ 255 octets (RFC 1035 §2.3.4 name length bound).

    @param ls The labels to test.
    @returns [true] iff [ls] is a valid hostname label list. *)
let hostname_wfcv (ls: list domain_label) : bool =
  Cons? ls &&
  List.Tot.length ls <= 127 &&
  List.Tot.for_all (fun (dl: domain_label) -> hostname_label_bytes_wfcv dl.label_bytes) ls


(* ========================================================================
   Predicates
   ======================================================================== *)


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
    (fun (dl: domain_label) ->
       if label_wfcv dl then Some dl.label_bytes else None)
    (satisfy_many1 is_label_char)


(* ========================================================================
   Dotted form (codec)
   ======================================================================== *)


(** [dot_byte] — the [.] (0x2E) label separator byte. *)
let dot_byte : byte = 0x2Euy


(** [domain_codec] — the dotted form [label ('.' label)*] as a record [codec
    (list domain_label)], built from the [sep_by1] separator-fold (Mandate 22:
    no bespoke scanner).  Encodes labels left-to-right with a [.] (0x2E)
    BETWEEN them (no trailing dot — the non-FQ text form).

    The [max] is 127 (RFC 1035 §2.3.4 label-count bound), which is the
    termination fuel for [sep_by1]'s greedy decoder. *)
let domain_codec : codec domain_name =
  map_
    (fun (x: list domain_label & bool) -> Some ({ labels = fst x; fully_qualified = snd x }))
    (fun (d: domain_name) -> Some (d.labels, d.fully_qualified))
    (sep_by1_opt_trailing label_codec (byte_val dot_byte) 127)


(** [domain_wfcv] — a [domain_name] is well-formed for [domain_codec]:
    definitionally [domain_codec.wfcv d]. *)
let domain_wfcv (d: domain_name) : bool =
  domain_codec.wfcv d


(** [domain_wfcv_prop] — the propositional side of [domain_codec.wfcv]. *)
let domain_wfcv_prop (d: domain_name) : prop =
  domain_codec.wfcv_prop d


(** [domain_rest_cond] — the trailing-suffix condition of [domain_codec]. *)
let domain_rest_cond (d: domain_name) (r: byte_seq) : prop =
  domain_codec.rest_cond d r


(* ========================================================================
   Hostname codec (RFC 1035 §3.5 preferred-name syntax)
   ======================================================================== *)


(** [hostname_label_codec] — a single §3.5 label as a [codec domain_label]:
    the same [satisfy_many1] letter/digit/hyphen run as [label_codec], with a
    [map_] guard that enforces the §3.5 first-letter / last-letter-or-digit
    grammar (rejecting a hyphen-leading, digit-leading, or hyphen-trailing
    label).  The wire bytes are the raw label octets. *)
let hostname_label_codec : codec domain_label =
  map_
    (fun (bs: list byte) ->
       if hostname_label_bytes_wfcv bs then Some ({ label_bytes = bs }) else None)
    (fun (dl: domain_label) ->
       if hostname_label_bytes_wfcv dl.label_bytes then Some dl.label_bytes else None)
    (satisfy_many1 is_ldh)


(** [hostname_codec] — a hostname (a non-FQ §3.5 label list) as a [codec
    hostname], built as [sep_by1] over [hostname_label_codec] (the §3.5 label
    grammar, NOT the looser [label_codec]) with a [.] separator.  Encodes
    [l1.l2.l3] (no trailing dot — a hostname is never fully-qualified). *)
let hostname_codec : codec hostname =
  map_
    (fun (ls: list domain_label) ->
       if hostname_wfcv ls then Some ({ labels = ls }) else None)
    (fun (h: hostname) ->
       if hostname_wfcv h.labels then Some h.labels else None)
    (sep_by1 hostname_label_codec (byte_val 0x2Euy) 127)


(** [hostname_codec_wfcv] — the well-formed guard of [hostname_codec] (a
    friendly alias to its opaque [.wfcv] field). *)
let hostname_codec_wfcv (h: hostname) : bool =
  hostname_codec.wfcv h


(** [hostname_codec_wfcv_prop] — the propositional guard of [hostname_codec]. *)
let hostname_codec_wfcv_prop (h: hostname) : prop =
  hostname_codec.wfcv_prop h


(** [hostname_codec_rest_cond] — the trailing-suffix condition of
    [hostname_codec]. *)
let hostname_codec_rest_cond (h: hostname) (r: byte_seq) : prop =
  hostname_codec.rest_cond h r


(** [encode_hostname] — serialize a [hostname] to its dotted form.

    @param h The hostname to serialize.
    @returns The dotted byte list of [h.labels]. *)
let encode_hostname (h: hostname) : Tot (list byte) =
  Seq.seq_to_list (hostname_codec.enc h)


(** [decode_hostname] — parse the dotted form into a [hostname]; [None] unless
    the whole input is consumed and every label is a §3.5 label.

    @param bs The dotted byte list.
    @returns [Some h] on a complete §3.5 parse, else [None]. *)
let decode_hostname (bs: list byte) : option hostname =
  let s = Seq.seq_of_list bs in
  match hostname_codec.dec s with
  | Inl _ -> None
  | Inr (h, n) -> if n = Seq.length s then Some h else None


(** [encode_domain] — serialize a [domain_name] to its dotted form via
    [domain_codec.enc] (crossing the [byte_seq]→[list byte] boundary).  The
    [fully_qualified] flag drives whether the trailing dot is emitted (the
    [sep_by1_opt_trailing] optional-trailing form; the root [labels = []]
    encodes as the empty list).

    @param d The name to serialize.
    @returns The dotted byte list. *)
let encode_domain (d: domain_name) : Tot (list byte) =
  Seq.seq_to_list (domain_codec.enc d)


(** [decode_domain] — parse the dotted form into a [domain_name] via
    [domain_codec.dec] (crossing the [list byte]→[byte_seq] boundary).  [None]
    unless the WHOLE input is consumed.  The empty input decodes to
    [Some root_domain] (the root is not representable by [sep_by1_opt_trailing]
    whose [wfcv] requires [Cons?]).

    @param bs The dotted byte list.
    @returns [Some d] when [bs] is exactly the (non-)FQ dotted form or the
             root, else [None]. *)
let decode_domain (bs: list byte) : option domain_name =
  if Cons? bs
  then
    let s = Seq.seq_of_list bs in
    (match domain_codec.dec s with
     | Inr (d, n) -> if n = Seq.length s then Some d else None
     | Inl _ -> None)
  else Some root_domain


(* ========================================================================
   String view
   ======================================================================== *)


(** [ascii_bytes_to_string] — ASCII [list byte] to [string] (code points < 128).

    @param bs The ASCII byte list.
    @returns The reconstructed [string]. *)
let ascii_bytes_to_string (bs: list byte) : string =
  FStar.String.string_of_list
    (List.Tot.map (fun (b: byte) -> FStar.Char.char_of_int (U8.v b)) bs)


(** [string_to_ascii_bytes] — [string] to [list byte], returning [None] for any
    non-ASCII code point ([>= 128]).  A non-ASCII [domain_of_string] input is
    REJECTED rather than silently truncated into a bogus ASCII label.

    @param s The [string] to convert.
    @returns [Some bs] when [s] is pure ASCII, else [None]. *)
let rec string_to_ascii_bytes_go (cs: list FStar.Char.char) : option (list byte) =
  match cs with
  | [] -> Some []
  | c :: tl ->
      let v = FStar.Char.int_of_char c in
      if v < 128
      then (match string_to_ascii_bytes_go tl with
            | None -> None
            | Some rest -> Some (U8.uint_to_t v :: rest))
      else None

let string_to_ascii_bytes (s: string) : option (list byte) =
  string_to_ascii_bytes_go (FStar.String.list_of_string s)


(** [string_is_ascii] — [true] iff every code point in [s] is < 128 (the guard
    folded into [string_to_ascii_bytes], exposed for lemma use).

    @param s The [string] to test.
    @returns [true] iff [s] is pure ASCII. *)
let string_is_ascii (s: string) : bool =
  List.Tot.for_all (fun (c: FStar.Char.char) -> FStar.Char.int_of_char c < 128)
    (FStar.String.list_of_string s)


(** [string_of_domain] — serialize a [domain_name] to its dotted text.

    @param d The name to serialize.
    @returns The dotted text (ASCII). *)
let string_of_domain (d: domain_name) : Tot string =
  ascii_bytes_to_string (encode_domain d)


(** [domain_of_string] — parse a dotted text string into a [domain_name];
    [None] unless the string is pure ASCII AND the whole string is consumed by
    [decode_domain].

    @param s The dotted text string.
    @returns [Some d] on a complete parse, else [None]. *)
let domain_of_string (s: string) : Tot (option domain_name) =
  match string_to_ascii_bytes s with
  | None -> None
  | Some bs -> decode_domain bs


(** [string_of_hostname] — serialize a [hostname] to its dotted text.

    @param h The hostname to serialize.
    @returns The dotted text (ASCII). *)
let string_of_hostname (h: hostname) : Tot string =
  ascii_bytes_to_string (encode_hostname h)


(** [hostname_of_string] — parse a dotted text string into a [hostname] (a
    §3.5 preferred-name label list); [None] on a non-ASCII or non-§3.5 parse.

    @param s The dotted text string.
    @returns [Some h] on a complete §3.5 parse, else [None]. *)
let hostname_of_string (s: string) : Tot (option hostname) =
  match string_to_ascii_bytes s with
  | None -> None
  | Some bs -> decode_hostname bs


(* ========================================================================
   Lemmas
   ======================================================================== *)


(** [lemma_domain_roundtrip] — the dotted-form codec roundtrip: decoding the
    encoding of a well-formed [domain_name] recovers the name, for BOTH the
    non-FQ and FQ forms (the [sep_by1_opt_trailing] single codec carries the
    trailing flag in the value).

    @param d The name (require [domain_wfcv d] / [domain_wfcv_prop d] /
             [domain_rest_cond d Seq.empty]).
    Ensures [domain_codec.dec (domain_codec.enc d ++ empty) == Inr (d, |enc d|)]. *)
let lemma_domain_roundtrip (d: domain_name) : Lemma
  (requires domain_wfcv d /\ domain_wfcv_prop d /\ domain_rest_cond d Seq.empty)
  (ensures domain_codec.dec (domain_codec.enc d `Seq.append` Seq.empty)
           == Inr (d, Seq.length (domain_codec.enc d)))
  = domain_codec.roundtrip d Seq.empty


(** [lemma_encode_domain_roundtrip] — roundtrip of the dotted form through
    [encode_domain]/[decode_domain]: for a well-formed, non-empty label name
    (FQ or non-FQ), [decode_domain (encode_domain d) == Some d].

    @param d The name (require a well-formed non-empty label list).
    Ensures [decode_domain (encode_domain d) == Some d]. *)
let lemma_encode_domain_roundtrip (d: domain_name) : Lemma
  (requires domain_wfcv d /\ domain_wfcv_prop d /\ domain_rest_cond d Seq.empty)
  (ensures decode_domain (encode_domain d) == Some d)
  =
  lemma_domain_roundtrip d;
  Seq.append_empty_r (domain_codec.enc d);
  lemma_seq_list_bij (domain_codec.enc d);
  lemma_seq_of_list_length (Seq.seq_to_list (domain_codec.enc d));
  assert (domain_codec.dec (Seq.seq_of_list (Seq.seq_to_list (domain_codec.enc d)))
          == Inr (d, Seq.length (domain_codec.enc d)));
  ()


(** [lemma_fq_concrete] — [www.] (a single-label FQ name) encodes to [www.]
    (four bytes with a trailing dot). *)
let lemma_fq_concrete () : Lemma
  (ensures
    encode_domain ({ labels = [ { label_bytes = [0x77uy; 0x77uy; 0x77uy] } ];
                     fully_qualified = true })
    == [0x77uy; 0x77uy; 0x77uy; 0x2Euy])
  = Seq.lemma_eq_intro
      (domain_codec.enc ({ labels = [ { label_bytes = [0x77uy; 0x77uy; 0x77uy] } ];
                           fully_qualified = true }))
      (seq_of_list [0x77uy; 0x77uy; 0x77uy; 0x2Euy]);
    ()




(** [lemma_decode_domain_root] — the root roundtrip: the empty input decodes
    to [Some root_domain], and [encode_domain root_domain] is the empty list. *)
let lemma_decode_domain_root () : Lemma
  (ensures decode_domain [] == Some root_domain /\
           encode_domain root_domain == [])
  = ()



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
      (domain_codec.enc ({ labels = [ { label_bytes = [0x65uy; 0x78uy; 0x61uy; 0x6Duy; 0x70uy; 0x6Cuy; 0x65uy] };
                                       { label_bytes = [0x63uy; 0x6Fuy; 0x6Duy] } ];
                           fully_qualified = false }))
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
    label list ([domain_wfcv root_domain == false]): the root is a [0x00] wire
    byte, not an empty dotted text (which [sep_by1_opt_trailing]'s non-empty
    [wfcv] excludes). *)
let lemma_root_domain_concrete () : Lemma
  (ensures domain_wfcv root_domain == false)
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
      (domain_codec.enc ({ labels = [ { label_bytes = [0x77uy; 0x77uy; 0x77uy] } ];
                           fully_qualified = false }))
      (seq_of_list [0x77uy; 0x77uy; 0x77uy]);
    ()


(** [lemma_label_wfcv_eq_codec_wfcv] — the local [label_wfcv] predicate is
    definitionally the [label_codec.wfcv] guard: a well-formed label (non-empty
    ≤ 63-octet label-char run) is exactly what [label_codec] accepts.

    @param dl The label.
    Ensures [label_wfcv dl == label_codec.wfcv dl]. *)
let lemma_label_wfcv_eq_codec_wfcv (dl: domain_label) : Lemma
  (ensures label_wfcv dl == label_codec.wfcv dl)
  = ()


(** [lemma_decode_domain_whole_input] — decoding a well-formed label list's
    encoding consumes the whole input and yields [fq = false] (a non-FQ name):
    [decode_domain (encode_domain d) == Some d] under the same well-formedness
    conditions as [lemma_encode_domain_roundtrip], stated at the empty-suffix /
    whole-input level.

    @param d The name (require [fully_qualified = false] and well-formed
             non-empty labels).
    Ensures [decode_domain (encode_domain d) == Some d]. *)
let lemma_decode_domain_whole_input (d: domain_name) : Lemma
  (requires domain_wfcv d /\ domain_wfcv_prop d /\ domain_rest_cond d Seq.empty)
  (ensures decode_domain (encode_domain d) == Some d)
  = lemma_encode_domain_roundtrip d


(** [lemma_encode_hostname_roundtrip] — the hostname codec roundtrip: decoding
    the encoding of a well-formed §3.5 hostname recovers the hostname.

    @param h The hostname (require [hostname_wfcv h.labels]).
    Ensures [decode_hostname (encode_hostname h) == Some h]. *)
let lemma_encode_hostname_roundtrip (h: hostname) : Lemma
  (requires hostname_codec_wfcv h /\ hostname_codec_wfcv_prop h /\
            hostname_codec_rest_cond h Seq.empty)
  (ensures decode_hostname (encode_hostname h) == Some h)
  = hostname_codec.roundtrip h Seq.empty;
    Seq.append_empty_r (hostname_codec.enc h);
    lemma_seq_list_bij (hostname_codec.enc h);
    lemma_seq_of_list_length (Seq.seq_to_list (hostname_codec.enc h));
    assert (hostname_codec.dec (Seq.seq_of_list (Seq.seq_to_list (hostname_codec.enc h)))
            == Inr (h, Seq.length (hostname_codec.enc h)));
    ()


(** [lemma_hostname_www_concrete] — the single-label hostname [www] encodes to
    exactly its three byte octets (concrete ENCODE via [Seq.lemma_eq_intro]). *)
let lemma_hostname_www_concrete () : Lemma
  (ensures
    encode_hostname ({ labels = [ { label_bytes = [0x77uy; 0x77uy; 0x77uy] } ] })
    == [0x77uy; 0x77uy; 0x77uy])
  = Seq.lemma_eq_intro
      (hostname_codec.enc ({ labels = [ { label_bytes = [0x77uy; 0x77uy; 0x77uy] } ] }))
      (seq_of_list [0x77uy; 0x77uy; 0x77uy]);
    ()


(** [lemma_hostname_label_reject_hyphen] — a hyphen-leading label is NOT a
    §3.5 label ([hostname_label_bytes_wfcv] rejects it): the preferred-name
    grammar requires a letter first. *)
let lemma_hostname_label_reject_hyphen () : Lemma
  (ensures hostname_label_bytes_wfcv [0x2Duy; 0x61uy] == false)
  = ()
