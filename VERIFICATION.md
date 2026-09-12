# External verification: exact commands and results

Recorded 2026-09-12. This file makes the checks reported in the companion paper (Section 8)
reproducible. Nothing here is needed to build or audit the library; it documents runs performed
against the `afm-v2` commits.

## Tool versions

| Tool | Source | Revision | Notes |
|---|---|---|---|
| `lean4export` | github.com/leanprover/lean4export | `8554815c2` | the commit pinned to Lean `v4.31.0`; later commits target newer toolchains and will not read these oleans |
| `nanoda` | github.com/ammkrn/nanoda_lib | `master`, v0.4.16 (`0505569`) | tag `v0.3.2` parses the older whitespace export format and fails on lean4export 3.1.0 NDJSON |
| `comparator` | github.com/leanprover/comparator | `fd2e25de1` | the commit pinned to Lean `v4.31.0` |
| `landrun` | github.com/Zouuup/landrun | `811cfff` | needs Landlock ABI v9, so a Linux 7.1 or later host |

## nanoda: re-checking a theorem's own closure

Export the declaration's closure, not whole modules. A module export drags in
`Lean.trustCompiler` from unrelated declarations and nanoda then aborts.

    cd flt-vandiver-primes-kernel
    lake env /path/to/lean4export FLT37 -- FLT37.fermatLastTheoremFor_37 > FLT37.ndjson
    nanoda_bin config.nanoda.json

with `config.nanoda.json`:

    {
        "export_file_path": "FLT37.ndjson",
        "use_stdin": false,
        "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "unpermitted_axiom_hard_error": true,
        "nat_extension": true,
        "string_extension": true,
        "pp_declars": [],
        "pp_to_stdout": false,
        "print_success_message": true
    }

Results, on a 64-vCPU GCP `c4d-standard-64`, each reporting
`Checked N declarations with no typechecker errors`:

| target | declarations | export | check | peak RSS |
|---|---|---|---|---|
| `FLT37.fermatLastTheoremFor_37` | 96,391 | 53 s | 119 s | 0.9 GiB |
| `FLT59` … `FLT157` (7 more) | ~96,000 each | 31–124 s | 99–466 s | 2.9–44.7 GiB |
| `FLT37SG.fermatLastTheoremFor_37` (Germain route) | 94,686 | 31 s | 81 s | 1.2 GiB |
| `RegPrimes.flt_17` … `flt_349` (47, one export) | 96,485 | 34 s | 3,965 s | 22.4 GiB |

## comparator: statement fidelity

`config.json` in this repository ships with `"enable_nanoda": false`, so that `lake exe` style
use does not require a nanoda binary on `PATH`. The runs reported in the paper used a copy with
that field set to `true`. Run from the repository root:

    systemd-run --user --scope -q -p MemoryMax=20G \
      -E COMPARATOR_LANDRUN=/path/to/landrun-wrapper.sh \
      -E COMPARATOR_LEAN4EXPORT=/path/to/lean4export \
      -E COMPARATOR_NANODA=/path/to/nanoda_bin \
      --working-directory "$PWD" -- \
      bash -c 'lake env /path/to/comparator /path/to/config-with-nanoda-true.json'

Both pairs report `Nanoda kernel accepts the solution`, `Lean default kernel accepts the
solution`, `Your solution is okay!`: `fermatLastTheoremFor_59` here and `flt_107` in
`flt-regular-extended`.

Two environment notes. Current `landrun` uses a CLI front end that swallows the first `--` in
its child's arguments, which is exactly the separator `lean4export` needs; `landrun-wrapper.sh`
re-inserts one after the sandbox options and changes nothing else. And
`systemd-run --user --scope` rejects the `RestrictAddressFamilies` property the comparator README
suggests; that property guards a sandbox escape fixed in Linux 7.1, which these runs were on.

## Scope

These checks cover the proof layer: the descent, the `Q_i`-to-Vandiver bridge, and the Germain
bridge. They do not re-run any `native_decide` evaluation, which reaches an external kernel as a
named axiom, and they do not reach the evaluator bridges `QiCertFast`, `QiCertFast2` or the slice
recombination in `QiCertAppend`, since the kernel instances reduce through a pure-`Nat` mirror
instead.
