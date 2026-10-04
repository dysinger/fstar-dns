# Network.DNS API Reference

## Types

### Network.DNS — Pure Spec
| Name | Kind | Description |
|------|------|-------------|
| `domain_label` | record | a single label — `label_bytes : list byte` |
| `domain_name` | record | `labels : list domain_label` + `fully_qualified : bool` |
| `hostname` | record | a `domain_name` (`name : domain_name`) |

### Network.DNS.Pulse — Extractable Leaf
| Name | Kind | Description |
|------|------|-------------|
| `label3` | record | a fixed 3-byte label content (`b0`/`b1`/`b2`) |
| `opt_label3` | sum | `OEL_None` / `OEL_Some of (label3 & U32.t)` |

## Predicates

| Function | Signature | Description |
|----------|-----------|-------------|
| `is_label_char` | `U8.t -> bool` | RFC 1035 §3.1 label predicate `[A-Za-z0-9-]` |
| `is_dot` | `U8.t -> bool` | the `.` separator (`0x2E`) |

## Codec

| Function | Signature | Description |
|----------|-----------|-------------|
| `label_codec` | `codec domain_label` | a single label (`satisfy_many1 is_label_char`, 1..63 octets) |
| `encode_label_list` | `domain_label -> list byte` | a label's raw octets |
| `encode_labels` | `list domain_label -> list byte` | the dotted form `label ('.' label)*` |
| `encode_domain` | `domain_name -> list byte` | serialize a name to dotted bytes |
| `decode_domain` | `list byte -> option domain_name` | parse the dotted form |

## String view

| Function | Signature | Description |
|----------|-----------|-------------|
| `string_of_domain` | `domain_name -> string` | serialize to dotted text |
| `domain_of_string` | `string -> option domain_name` | parse a dotted text string |
| `hostname_of_string` | `string -> option hostname` | parse a hostname string |
| `ascii_bytes_to_string` / `string_to_ascii_bytes` | `list byte -> string` / `string -> list byte` | local ASCII bridges |

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
| `lemma_decode_go_run` | the decoder's accumulator reflexivity over a label run |
| `lemma_decode_single_label` | `decode_domain lbl.label_bytes == Some { labels = [lbl]; … }` |
| `lemma_encode_domain_roundtrip` | single-label dotted roundtrip |
| `lemma_domain_length` | a well-formed label encodes to ≤ 63 octets |
| `lemma_example_com_concrete` | `example.com` dotted bytes decode to `[example; com]` |
| `lemma_single_label_concrete` | `www` decodes to a single label |
| `lemma_root_domain_concrete` | empty dotted input is rejected (`None`) |
| `lemma_label_concrete` | `label_codec` decodes a raw `[www]` run |
