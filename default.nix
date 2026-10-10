# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

# dns — Network.DNS verified DNS (RFC 1034/1035) library.
#
# Takes the F* toolchain as concrete derivations (no `pkgs` blob, no overlay
# assumption, no module-name/order arguments).  Module names and their
# dependency order live in the Makefile (the no-nix build); `checked` delegates
# to `make check`, exporting the toolchain paths the Makefile already reads.
#
# The codec dependency (Data.Codec.Types) is injected as a source dir +
# pre-verified `.checked` cache (`codec-src` / `codec-checked`), sourced from
# the separate `fstar-codec` flake input in flake.nix.
#
# Artifacts (named by deliverable, not by backend):
#   - `checked` — F* verification of src/ + test/ (the 0-admit gate).
#   - `ocaml`   — findlib package shipping ALL OCaml-extractable modules:
#                 the pure spec (Network.DNS) AND the Pulse leaf (Network.DNS.Pulse,
#                 `--custard_backend OCaml`) as one dune library.
#   - `native`  — C11 shared/static lib of the Pulse leaf (Network.DNS.Pulse,
#                 `--custard_backend C`).
#   - `fsharp`  — .NET library of the Pulse leaf (`--custard_backend FSharp`).
#
# Returns { checked; ocaml; native; fsharp; }.

{
  fstar,
  fstar-checked,
  lib,
  ocamlPackages,
  stdenv,
  dotnet,
  codec-src,
  codec-checked,
}:

let
  inherit (stdenv) mkDerivation;

  # Package name.  The package is "dns" (git repo "fstar-dns"), but the internal
  # derivation/artifact names drop the "fstar-" prefix.
  pname = "dns";

  pure-modules = [
    "Network.DNS"
  ];

  fstar-exe = "${fstar}/bin/fstar.exe";
  flib = "${fstar}/lib/fstar";
  ulib = "${flib}/ulib";

  # Pulse ships in the install under $(locate_lib)/pulse (sources under
  # pulse/{common,pulse/lib}, `.checked` under pulse/{common.checked,
  # pulse.checked}).
  pulse-incs = [
    "${flib}/pulse/common"
    "${flib}/pulse/common.checked"
    "${flib}/pulse/pulse/lib"
    "${flib}/pulse/pulse.checked"
  ];

  meta = {
    license = lib.licenses.agpl3Plus;
    # The LICENSE.md blurb mentions commercial dual-licensing terms.  The
    # SPDX above records the code license (AGPL-3.0-or-later); the commercial
    # terms are out-of-band (negotiated directly with the author), not a
    # second SPDX identifier.  See LICENSE.md.
    longDescription = ''
      A formally verified DNS (RFC 1034/1035) library in F*.  The code license
      is AGPL-3.0-or-later; commercial licensing terms are available
      out-of-band from the author (see LICENSE.md).
    '';
    maintainers = [
      {
        name = "Tim Dysinger";
        email = "tim@dysinger.net";
      }
    ];
  };

  # The toolchain environment the Makefile reads (see its guards).
  make-env = ''
    export FSTAR="${fstar-exe}"
    export FSTAR_CHECKED="${fstar-checked}"
    export CODEC_SRC="${codec-src}"
    export CODEC_CHECKED="${codec-checked}"
  '';

  # Shared preamble for the extract backends (native + fsharp): compute the
  # Pulse include flags and seed the `cache` dir with the pre-verified
  # `.checked` files (F* ulib + codec) so cross-module inlining resolves.
  # Assumes `cache` already exists in $out's build dir.
  seed-cache = ''
    ULIB="${ulib}"
    PULSE_INCS=""
    for d in ${lib.concatStringsSep " " pulse-incs}; do
      PULSE_INCS="$PULSE_INCS --include $d"
    done
    cp ${fstar-checked}/*.checked cache/ 2>/dev/null || true
    cp ${codec-checked}/*.checked cache/ 2>/dev/null || true
  '';

  # Verify Network.DNS (pure spec) + Network.DNS.Pulse (Pulse leaf) in
  # dependency order into `cache`, so a later extraction pass can resolve our
  # own modules' `.checked` files.  Shared by native + fsharp (and ocaml-src
  # does its own two-step verify-extract because it emits OCaml).
  verify-both = ''
    for m in Network.DNS Network.DNS.Pulse; do
      ${fstar-exe} \
        --no_default_includes --include "$ULIB" $PULSE_INCS --include ${codec-src}/src --include ./src \
        --already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore \
        --z3rlimit 120 \
        --cache_checked_modules --cache_dir cache --odir cache \
        src/$m.fst || exit 1
    done
  '';

  checked = mkDerivation {
    pname = "${pname}-checked";
    version = "0.1.0";
    src = ./.;
    nativeBuildInputs = [
      fstar
      fstar-checked
    ];
    inherit meta;
    buildPhase = ''
      ${make-env}
      make check OUT="$out"
      # Flatten $(OUT)/checked/*.checked to $out/*.checked.  Robust to whether
      # `make check` wrote a `checked/` subdir (the Makefile $OUT/checked
      # layout) or straight to $out.  Emit a manifest so consumers of the
      # `checked` artifact can locate the `.checked` tree without a fixed
      # dirname assumption.
      if [ -d "$out/checked" ]; then
        find "$out/checked" -maxdepth 1 -name '*.checked' -exec sh -c 'mv "$1" "$out/"' _ {} \;
        rmdir "$out/checked" 2>/dev/null || true
      fi
      (cd "$out" && ls *.checked 2>/dev/null | sort) > "$out/manifest"
    '';
    installPhase = "true";
  };

  # ── OCaml source backend ────────────────────────────────────────────
  #
  # `fstar.exe --codegen OCaml` extracts the pure spec module; the Pulse leaf
  # is extracted via `--codegen Custard --custard_backend OCaml` and merged into
  # one dune library.  One file per invocation, in dependency order; the codec
  # dependency's `.checked` cache is seeded so cross-module inlining resolves.

  ocaml-lib-name = builtins.replaceStrings [ "-" ] [ "_" ] pname;
  # The dns pure spec PLUS the codec pure spec (`Data.Codec.Types`,
  # `Data.Codec`), extracted locally (NOT from `codec-ocaml`) so the raw
  # top-level `Data_Codec_Types`/`Data_Codec` names resolve unwrapped.
  # NOTE (maintenance, 8.24): the hard-wired `Data_Codec_Types`/`Data_Codec`
  # extraction list mirrors the `fstar-codec` repo's own pure-module list
  # (its `default.nix` `pure-modules`).  If the codec repo adds/renames its
  # pure spec modules, update this list (and the `m` loop below) to match
  # `fstar-codec`'s `default.nix` `pure-modules`.
  ocaml-modules = (map (m: builtins.replaceStrings [ "." ] [ "_" ] m) pure-modules) ++ [
    "Data_Codec_Types"
    "Data_Codec"
  ];

  ocaml-src = mkDerivation {
    name = "${pname}-ocaml-src";
    src = ./.;
    nativeBuildInputs = [
      fstar
      fstar-checked
    ];
    buildPhase = ''
            export ULIB="${ulib}"
            mkdir -p $out cache
            cp ${fstar-checked}/*.checked cache/ 2>/dev/null || true
            cp ${codec-checked}/*.checked cache/ 2>/dev/null || true
            # 0) Extract the codec pure spec (Data.Codec.Types + Data.Codec) locally
            #    so the top-level `Data_Codec_Types`/`Data_Codec` module names the
            #    dns `.ml` emit resolve unwrapped (codec-ocaml wraps them).
            for m in Data.Codec.Types Data.Codec; do
              ${fstar-exe} \
                --no_default_includes --include "$ULIB" --include ${codec-src}/src \
                --cache_checked_modules --cache_dir cache --odir cache \
                ${codec-src}/src/$m.fst || exit 1
              ${fstar-exe} \
                --no_default_includes --include "$ULIB" --include ${codec-src}/src --include cache \
                --cache_checked_modules --cache_dir cache \
                --codegen OCaml --odir $out \
                ${codec-src}/src/$m.fst || exit 1
            done
            # 1) Extract the pure spec via legacy `--codegen OCaml` (one file per
            #    invocation, dependency order).
            for m in ${builtins.concatStringsSep " " pure-modules}; do
              ${fstar-exe} \
                --no_default_includes --include "$ULIB" --include ${codec-src}/src --include ./src \
                --cache_checked_modules --cache_dir cache --odir cache \
                src/$m.fst || exit 1
              ${fstar-exe} \
                --no_default_includes --include "$ULIB" --include ${codec-src}/src --include ./src --include cache \
                --cache_checked_modules --cache_dir cache \
                --codegen OCaml --odir $out \
                src/$m.fst || exit 1
            done
            # 2) Extract the Pulse leaf (Network.DNS.Pulse), OCaml backend.
            PULSE_INCS=""
            for d in ${lib.concatStringsSep " " pulse-incs}; do
              PULSE_INCS="$PULSE_INCS --include $d"
            done
            ${fstar-exe} \
              --no_default_includes --include "$ULIB" $PULSE_INCS --include ${codec-src}/src --include ./src \
              --already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore \
              --z3rlimit 120 \
              --cache_checked_modules --cache_dir cache --odir cache \
              src/Network.DNS.Pulse.fst || exit 1
            ${fstar-exe} \
              --no_default_includes --include "$ULIB" $PULSE_INCS --include ${codec-src}/src --include ./src --include cache \
              --already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore \
              --cache_checked_modules --cache_dir cache \
              --codegen Custard --custard_backend OCaml --custard_monomorphize_types true \
              --custard_entry Network.DNS.Pulse.encode_label \
              --custard_entry Network.DNS.Pulse.decode_label \
              --odir $out \
              src/Network.DNS.Pulse.fst || exit 1
            # One dune library: pure spec + Pulse leaf together.
            cat > $out/dune-project <<DUNE_PROJECT
      (lang dune 3.11)
      (name ${pname}-ocaml)
      (package (name ${pname}-ocaml))
      DUNE_PROJECT
            cat > $out/dune <<DUNE
      (library
       (name ${ocaml-lib-name})
       (public_name ${pname}-ocaml)
       (modules ${builtins.concatStringsSep " " ocaml-modules} Custard)
       (libraries fstar.lib))
      DUNE
    '';
    installPhase = "true";
  };

  ocaml = ocamlPackages.buildDunePackage {
    pname = "${pname}-ocaml";
    version = "0.1.0";
    src = ocaml-src;
    inherit meta;
    propagatedBuildInputs = [ fstar ];
    buildInputs = with ocamlPackages; [
      batteries
      pprint
      stdint
      yojson
      zarith
      ppx_deriving
      ppx_deriving_yojson
    ];
    OCAMLPATH = "${fstar}/lib";
  };

  # ── native (C) backend ─────────────────────────────────────────────
  #
  # `--codegen Custard --custard_backend C` extracts the Pulse leaf to C11.
  # The whole module is a library (no `main`), rooted at the two leaf
  # encode/decode functions.

  native = mkDerivation {
    pname = "${pname}-native";
    version = "0.1.0";
    src = ./.;
    nativeBuildInputs = [
      fstar
      fstar-checked
    ];
    inherit meta;
    buildPhase = ''
      mkdir -p $out cache
      ${seed-cache}
      ${verify-both}
      # Extract the whole `Network.DNS.Pulse` module to C (library mode).
      ${fstar-exe} \
        --no_default_includes --include "$ULIB" $PULSE_INCS --include ${codec-src}/src --include ./src --include cache \
        --already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore \
        --cache_checked_modules --cache_dir cache \
        --codegen Custard --custard_backend C --custard_monomorphize_types true \
        --custard_entry Network.DNS.Pulse.encode_label \
        --custard_entry Network.DNS.Pulse.decode_label \
        --odir $out \
        src/Network.DNS.Pulse.fst || exit 1
      # Compile the emitted C11 to a shared object + static lib.
      cc -c -Wall -Wextra -Werror -std=c11 -O2 -fPIC -I $out $out/Custard.c -o $out/Custard.o
      if [ "$(uname -s)" = Darwin ]; then
        cc -dynamiclib $out/Custard.o -o $out/lib${pname}.dylib
      else
        cc -shared $out/Custard.o -o $out/lib${pname}.so
      fi
      ar rcs $out/lib${pname}.a $out/Custard.o
      cp $out/Custard.h $out/${pname}.h
    '';
    installPhase = "true";
  };

  # ── F# (.NET) backend ─────────────────────────────────────────────
  #
  # Same flat pattern as `native`: verify → extract F# → compile with
  # `dotnet build` into a .NET library assembly.  Rooted at the two leaf
  # encode/decode functions.

  fsharp = mkDerivation {
    pname = "${pname}-fsharp";
    version = "0.1.0";
    src = ./.;
    nativeBuildInputs = [
      fstar
      fstar-checked
      dotnet
    ];
    inherit meta;
    buildPhase = ''
      mkdir -p $out cache src-out
      export DOTNET_CLI_TELEMETRY_OPTOUT=1
      export DOTNET_NOLOGO=1
      export DOTNET_SKIP_FIRST_TIME_EXPERIENCE=1
      export HOME=$NIX_BUILD_TOP
      ${seed-cache}
      ${verify-both}
      ${fstar-exe} \
        --no_default_includes --include "$ULIB" $PULSE_INCS --include ${codec-src}/src --include ./src --include cache \
        --already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore \
        --cache_checked_modules --cache_dir cache \
        --codegen Custard --custard_backend FSharp --custard_monomorphize_types true \
        --custard_entry Network.DNS.Pulse.encode_label \
        --custard_entry Network.DNS.Pulse.decode_label \
        --odir src-out \
        src/Network.DNS.Pulse.fst || exit 1
      dotnet build src-out/Custard.fsproj -c Release -o $out || exit 1
    '';
    installPhase = "true";
  };

in
{
  inherit
    checked
    ocaml
    native
    fsharp
    ;
}
