# dns — RFC 1034/1035 Domain Name System

`Network.DNS` implements DNS domain names per RFC 1034/1035 §3.1.

## Modules

| Module | Purpose |
|--------|---------|
| `Network.DNS` | Pure spec: the `domain_label`/`domain_name` records, the dotted label codec, and 0-admit lemmas |
| `Network.DNS.Pulse` | C/OCaml/F#-extractable Pulse leaf: length-prefixed label wire encode/decode over `Pulse.Lib.Array` |

## RFC coverage

| Feature | RFC | Notes |
|---------|-----|-------|
| Label character set | 1035 §3.1 | `A-Z a-z 0-9 -` |
| Label length | 1035 §3.1 | 1 to 63 octets per label |
| Dotted text form | 1035 §3.1 | `label ('.' label)*` (`encode_domain` / `decode_domain`) |
| Wire form | 1035 §3.1 | length byte + label octets + `0x00` root terminator (`Network.DNS.Pulse`) |
| String view | — | `string_of_domain` / `domain_of_string` / `hostname_of_string` |

## Build

```bash
nix build .#checked   # F* verification gate (0-admit)
nix build .#native    # C11 shared/static lib (default)
nix build .#fsharp    # .NET library
nix build .#ocaml     # OCaml findlib package
nix fmt               # format nix files (treefmt)
nix develop && make check   # dev loop (no nix)
```

The `codec` dependency is injected as a flake input (`github:dysinger/fstar-codec`),
its source as `codec-src` and its pre-verified `.checked` set as `codec-checked`.
