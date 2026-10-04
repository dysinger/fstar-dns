# Changelog

All notable changes to this project are documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

(no unreleased changes)

## [0.1.0] — initial extraction

### Added

- Extracted `Network.DNS` out of the original monorepo into a standalone
  repository built from `fstar-nix-flake-template`.
- Source modules:
  - `Network.DNS` — the `domain_label`/`domain_name` records, the dotted
    label codec (RFC 1035 §3.1, `[A-Za-z0-9-]{1,63}`), and the pure
    `string_of_domain`/`hostname_of_string` views.
  - `Network.DNS.Pulse` — C-extractable length-prefixed label wire
    encode/decode (RFC 1035 §3.1 wire form: length byte + label octets +
    `0x00` root terminator).
- Test module: `Network.DNS.Test.Integration`.
- Nix flake targets: `.#checked`, `.#ocaml`, `.#native`, `.#fsharp`.
- Dual licensing: AGPL-3.0-or-later, or a commercial license from the author.

### Changed

- Renamed the C leaf `Network.DNS.Low` → `Network.DNS.Pulse` (the KaRaMeL
  `.Low` convention is retired; the Pulse/Custard layer is the successor).
- Migrated the codec off the deleted GADT API (`make_codec`/`encode_spec`/
  `decode_spec`/`Data.Codec.Lemmas`) onto the record `codec a` combinator API
  (`satisfy_many1`/`byte_val`/`map_`), 0-admit.
- Ported the label wire-format leaf from KaRaMeL Low\* (`Stack` +
  `LowStar.Buffer`) to Pulse (`fn` + `Pulse.Lib.Array`), 0-admit, extracting
  to C11 via Custard.
- Deleted `magic ()` from `string_of_domain`/`hostname_of_string`; implemented
  them as pure functions over the codec's `dec`, proven on concrete vectors.
- Replaced every `admit ()` (`lemma_label_length`, `lemma_domain_length`,
  `lemma_domain_terminator`) with structural lemmas.
- Rolled F\* forward to `v2026.09.20+lsp` (first stable tag shipping the
  Custard extractor).
- Removed the KaRaMeL/Low\* toolchain and all its targets.

### Fixed

- Removed `open FStar.Mul` and `Prims.op_Multiply` (both deleted upstream).
- Removed `--split_queries always` from `#push-options` (option deleted).
- Removed the `Lemma (True)` tautology that was the old `.Low`
  `lemma_roundtrip`.

### Notes

- Zero admits / zero magic / zero `assume` across all modules.
