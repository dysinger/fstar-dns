(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Network.DNS.Test.Integration — Binds all dns lemmas, values, and tests.

If any lemma or test function is deleted or renamed, F* verification fails.
This guarantees mechanically-enforced test coverage.

Uses [--admit_smt_queries true] for integration anchoring only.
Every binding below is a bare `let _ = f` value reference, which generates
no verification conditions (no roundtrip or logical claim is re-proven here).
Individual lemmas are proven without admits in their source modules.

@header Network.DNS.Test.Integration
*)
module Network.DNS.Test.Integration


open Network.DNS
open Network.DNS.Pulse


#push-options "--admit_smt_queries true"


(** Values *)


(** [is_label_char] *)
let _is_label_char = is_label_char
(** [is_dot] *)
let _is_dot = is_dot
(** [label_codec] *)
let _label_codec = label_codec
(** [encode_label_list] *)
let _encode_label_list = encode_label_list
(** [encode_labels] *)
let _encode_labels = encode_labels
(** [encode_domain] *)
let _encode_domain = encode_domain
(** [decode_domain_go] *)
let _decode_domain_go = decode_domain_go
(** [decode_domain] *)
let _decode_domain = decode_domain
(** [ascii_bytes_to_string] *)
let _ascii_bytes_to_string = ascii_bytes_to_string
(** [string_to_ascii_bytes] *)
let _string_to_ascii_bytes = string_to_ascii_bytes
(** [string_of_domain] *)
let _string_of_domain = string_of_domain
(** [domain_of_string] *)
let _domain_of_string = domain_of_string
(** [hostname_of_string] *)
let _hostname_of_string = hostname_of_string
(** [domain_of_labels] *)
let _domain_of_labels = domain_of_labels
(** [root_domain] *)
let _root_domain = root_domain
(** [label_wfcv] *)
let _label_wfcv = label_wfcv


(** Lemmas *)


(** [lemma_label_length] *)
let _lemma_label_length = lemma_label_length
(** [lemma_label_codec_roundtrip] *)
let _lemma_label_codec_roundtrip = lemma_label_codec_roundtrip
(** [lemma_decode_go_run] *)
let _lemma_decode_go_run = lemma_decode_go_run
(** [lemma_decode_single_label] *)
let _lemma_decode_single_label = lemma_decode_single_label
(** [lemma_encode_domain_roundtrip] *)
let _lemma_encode_domain_roundtrip = lemma_encode_domain_roundtrip
(** [lemma_domain_length] *)
let _lemma_domain_length = lemma_domain_length
(** [lemma_example_com_concrete] *)
let _lemma_example_com_concrete = lemma_example_com_concrete
(** [lemma_single_label_concrete] *)
let _lemma_single_label_concrete = lemma_single_label_concrete
(** [lemma_root_domain_concrete] *)
let _lemma_root_domain_concrete = lemma_root_domain_concrete
(** [lemma_label_concrete] *)
let _lemma_label_concrete = lemma_label_concrete


(** Pulse leaf fn's — mechanically protected against deletion *)


(** [encode_label] *)
let _encode_label = encode_label
(** [decode_label] *)
let _decode_label = decode_label


(** Pulse roundtrip *)


(** [lemma_pulse_label_roundtrip] *)
let _lemma_pulse_label_roundtrip = lemma_pulse_label_roundtrip


(* The Pulse spec mirrors [label3_to_seq]/[label3_of_indices]/[label_len_byte]
   are [noextract]; they are transitively covered by [encode_label]/
   [decode_label] (bound above), the same policy as [fstar-basen]/
   [fstar-uuid]. *)


#pop-options
