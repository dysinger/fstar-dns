# Network.DNS API Reference

## Types

### Network.DNS — Pure Spec
| Name | Kind | Description |
|------|------|-------------|
| `domain_label` | record | a single label — `label_bytes : list byte` |
| `domain_name` | record | `labels : list domain_label` + `fully_qualified : bool` |
| `hostname` | record | a §3.5 preferred name — `labels : list domain_label` (no `fully_qualified`) |

### Network.DNS.Pulse — Extractable Leaf
| Name | Kind | Description |
|------|------|-------------|
| `label3` | record | a fixed 3-byte label content (`b0`/`b1`/`b2`) |
| `opt_label3` | sum | `OEL_None` / `OEL_Some of (label3 & U32.t)` |

## Predicates

| Function | Signature | Description |
|----------|-----------|-------------|
| `is_label_char` | `U8.t -> bool` | RFC 1035 §3.1 label predicate `[A-Za-z0-9-]` |
| `is_letter` | `U8.t -> bool` | §3.5 `<letter>` (`A-Z`/`a-z`) |
| `is_let_dig` | `U8.t -> bool` | §3.5 `<let-dig>` (letter or digit) |
| `is_ldh` | `U8.t -> bool` | §3.5 `<let-dig-hyp>` (letter/digit/hyphen) |
| `hostname_label_bytes_wfcv` | `list byte -> bool` | §3.5 label grammar (first letter, last let-dig) |
| `hostname_wfcv` | `list domain_label -> bool` | a well-formed §3.5 hostname label list |

## Codec

| Function | Signature | Description |
|----------|-----------|-------------|
| `label_codec` | `codec domain_label` | a single label (`satisfy_many1 is_label_char`, 1..63 octets) |
| `domain_codec` | `codec (list domain_label)` | the dotted form `label ('.' label)*` via `sep_by1` |
| `domain_fq_codec` | `codec (list domain_label)` | the FQ form `label ('.' label)* '.'` via `sep_by1_trailing` |
| `dot_byte` | `byte` | the `0x2E` separator byte |
| `domain_wfcv` | `list domain_label -> bool` | [domain_codec]'s well-formed guard (alias) |
| `domain_wfcv_prop` | `list domain_label -> prop` | the propositional side of the guard |
| `domain_rest_cond` | `list domain_label -> byte_seq -> prop` | the trailing-suffix condition |
| `encode_domain` | `domain_name -> list byte` | serialize a name to dotted bytes (codec-delegating) |
| `decode_domain` | `list byte -> option domain_name` | parse the (non-)FQ dotted form; `[]` → `Some root_domain` |
| `hostname_codec` | `codec hostname` | the §3.5 preferred-name dotted form via `sep_by1` |
| `encode_hostname` | `hostname -> list byte` | serialize a hostname to dotted bytes |
| `decode_hostname` | `list byte -> option hostname` | parse the dotted form (whole input) |

## String view

| Function | Signature | Description |
|----------|-----------|-------------|
| `string_of_domain` | `domain_name -> string` | serialize to dotted text |
| `domain_of_string` | `string -> option domain_name` | parse a dotted text string (rejects non-ASCII) |
| `string_of_hostname` | `hostname -> string` | serialize a hostname to dotted text |
| `hostname_of_string` | `string -> option hostname` | parse a §3.5 hostname string |
| `string_is_ascii` | `string -> bool` | `true` iff every code point is `< 128` |
| `ascii_bytes_to_string` | `list byte -> string` | ASCII byte list to string |
| `string_to_ascii_bytes` | `string -> option (list byte)` | string to bytes (`None` on non-ASCII) |

## Constructors

| Function | Kind | Description |
|----------|------|-------------|
| `domain_of_labels` | `list domain_label -> bool -> domain_name` | construct a name |
| `root_domain` | `domain_name` | the root (`{ labels = []; fully_qualified = true }`) |

## Pulse leaf

| Function | Signature | Description |
|----------|-----------|-------------|
| `encode_label` | `fn (label3) (A.array U8.t) (U32.t) -> U32.t` | write `[len][b0][b1][b2][0x00]`, returns `5ul` |
| `decode_label` | `fn (A.array U8.t) (U32.t) -> opt_label3` | read the length byte + up to 3 content octets |
| `lemma_pulse_label_roundtrip` | Pulse `fn` | encode then decode preserves the label |
| `label3_to_seq` / `label3_of_indices` / `label_len_byte` | `noextract` pure | label ↔ byte bridges + the `0x03` length byte |

## Lemmas

| Lemma | Proves |
|-------|--------|
| `lemma_label_length` | a well-formed label is 1..63 octets |
| `lemma_label_codec_roundtrip` | `label_codec.dec (label_codec.enc dl) == Inr (dl, …)` |
| `lemma_domain_roundtrip` | `domain_codec.dec (enc ls) == Inr (ls, …)` for well-formed `ls` |
| `lemma_encode_domain_roundtrip` | `decode_domain (encode_domain d) == Some d` (non-FQ roundtrip) |
| `lemma_domain_fq_roundtrip` | the FQ codec roundtrip (codec level) |
| `lemma_decode_domain_root` | `decode_domain [] == Some root_domain` / `encode_domain root_domain == []` |
| `lemma_fq_concrete` | `www.` (FQ) encodes to exactly `[www.]` |
| `lemma_example_com_concrete` | `example.com` encodes to the exact dotted byte list |
| `lemma_single_label_concrete` | `www` encodes to exactly `[www]` |
| `lemma_root_domain_concrete` | the empty label list is rejected (`domain_wfcv [] == false`) |
| `lemma_label_concrete` | `label_codec` decodes a raw `[www]` run |
| `lemma_label_wfcv_eq_codec_wfcv` | `label_wfcv dl == label_codec.wfcv dl` |
| `lemma_decode_domain_reject_empty` | `decode_domain [] == None` |
| `lemma_decode_domain_whole_input` | `decode_domain (encode_domain d) == Some d` (whole input) |
| `lemma_encode_hostname_roundtrip` | `decode_hostname (encode_hostname h) == Some h` (whole input) |
| `lemma_hostname_www_concrete` | `www` hostname encodes to exactly `[www]` |
| `lemma_hostname_label_reject_hyphen` | a hyphen-leading label is not a §3.5 label |
