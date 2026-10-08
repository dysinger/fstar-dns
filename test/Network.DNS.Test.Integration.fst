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
(** [label_codec] *)
let _label_codec = label_codec
(** [domain_codec] *)
let _domain_codec = domain_codec
(** [domain_wfcv] *)
let _domain_wfcv = domain_wfcv
(** [dot_byte] *)
let _dot_byte = dot_byte
(** [encode_domain] *)
let _encode_domain = encode_domain
(** [decode_domain] *)
let _decode_domain = decode_domain
(** [ascii_bytes_to_string] *)
let _ascii_bytes_to_string = ascii_bytes_to_string
(** [string_to_ascii_bytes] *)
let _string_to_ascii_bytes = string_to_ascii_bytes
(** [string_to_ascii_bytes_go] *)
let _string_to_ascii_bytes_go = string_to_ascii_bytes_go
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
(** [string_is_ascii] *)
let _string_is_ascii = string_is_ascii
(** [is_letter] *)
let _is_letter = is_letter
(** [is_let_dig] *)
let _is_let_dig = is_let_dig
(** [is_ldh] *)
let _is_ldh = is_ldh
(** [hostname_label_bytes_wfcv] *)
let _hostname_label_bytes_wfcv = hostname_label_bytes_wfcv
(** [hostname_wfcv] *)
let _hostname_wfcv = hostname_wfcv
(** [hostname_label_codec] *)
let _hostname_label_codec = hostname_label_codec
(** [hostname_codec] *)
let _hostname_codec = hostname_codec
(** [hostname_codec_wfcv] *)
let _hostname_codec_wfcv = hostname_codec_wfcv
(** [hostname_codec_wfcv_prop] *)
let _hostname_codec_wfcv_prop = hostname_codec_wfcv_prop
(** [hostname_codec_rest_cond] *)
let _hostname_codec_rest_cond = hostname_codec_rest_cond
(** [encode_hostname] *)
let _encode_hostname = encode_hostname
(** [decode_hostname] *)
let _decode_hostname = decode_hostname
(** [string_of_hostname] *)
let _string_of_hostname = string_of_hostname


(** Lemmas *)


(** [lemma_label_length] *)
let _lemma_label_length = lemma_label_length
(** [lemma_label_codec_roundtrip] *)
let _lemma_label_codec_roundtrip = lemma_label_codec_roundtrip
(** [lemma_domain_roundtrip] *)
let _lemma_domain_roundtrip = lemma_domain_roundtrip
(** [lemma_encode_domain_roundtrip] *)
let _lemma_encode_domain_roundtrip = lemma_encode_domain_roundtrip
(** [lemma_example_com_concrete] *)
let _lemma_example_com_concrete = lemma_example_com_concrete
(** [lemma_single_label_concrete] *)
let _lemma_single_label_concrete = lemma_single_label_concrete
(** [lemma_root_domain_concrete] *)
let _lemma_root_domain_concrete = lemma_root_domain_concrete
(** [lemma_label_concrete] *)
let _lemma_label_concrete = lemma_label_concrete
(** [lemma_label_wfcv_eq_codec_wfcv] *)
let _lemma_label_wfcv_eq_codec_wfcv = lemma_label_wfcv_eq_codec_wfcv
(** [lemma_decode_domain_whole_input] *)
let _lemma_decode_domain_whole_input = lemma_decode_domain_whole_input
(** [lemma_decode_domain_root] *)
let _lemma_decode_domain_root = lemma_decode_domain_root
(** [lemma_fq_concrete] *)
let _lemma_fq_concrete = lemma_fq_concrete
(** [lemma_encode_hostname_roundtrip] *)
let _lemma_encode_hostname_roundtrip = lemma_encode_hostname_roundtrip
(** [lemma_hostname_www_concrete] *)
let _lemma_hostname_www_concrete = lemma_hostname_www_concrete
(** [lemma_hostname_label_reject_hyphen] *)
let _lemma_hostname_label_reject_hyphen = lemma_hostname_label_reject_hyphen


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
