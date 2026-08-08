# flt-regular-extended

[![Build check](https://github.com/batchatco/flt-regular-extended/actions/workflows/build-check.yml/badge.svg)](https://github.com/batchatco/flt-regular-extended/actions/workflows/build-check.yml)

Extends **`flt_regular`** (FLT for regular primes) to regular primes **beyond 13**,
`native_decide`-free.

Mathlib gives FLT for exponent 3; the `flt-regular` project gives 5, 7, 11, 13. This repo
delivers `FermatLastTheoremFor q` for every **regular** prime `17 ≤ q < 350` (47 primes), with
the prime-specific input — that `q` is regular — discharged by a **kernel `decide`** of a
pure-`Nat`/`List` Bernoulli check (no `native_decide`, no compiler trust). Each theorem is
axiom-clean: `[propext, Classical.choice, Quot.sound]`.

The `< 350` frontier is a **time budget of kernel `decide`, not a soundness or memory wall.**
The check grows super-cubically in `q`: measured on a `c4d-standard-64`, `q = 349` (the largest
of the 47 primes) takes ~15.5 single-threaded minutes at ~73 GiB — memory stays well under a
large box, so the practical limit is compute time. `native_decide` (in the sibling
`flt-vandiver-primes`) removes the wall entirely, reaching every regular prime below 1000 (and,
for irregular exponents, the Vandiver route reaches the Wolstenholme primes 16843 and 2124679).

Only the **direction we need** is formalized: `q` Bernoulli-clean ⟹ `q` regular ⟹
`FermatLastTheoremFor q` (via `flt_regular`). The full equivalence (regular ⟺ Kummer's
criterion, both directions) is the concurrent Brasca–Birkbeck development, not this repo.

Together with the **irregular** primes < 200 in the sibling `flt-vandiver-primes-kernel`, this
repo gives kernel-checked, zero-compiler-trust FLT for **every** prime `17 ≤ p < 200` (the
regulars here, the 8 irregulars there).

## What's here

- `fermatLastTheoremFor_of_bernoulli` (`FltOfBernoulli.lean`) — the generic theorem: for an odd prime
  `q`, if `q` divides no numerator of `B₂, …, B_{q-3}` (i.e. `q` is regular) then
  `FermatLastTheoremFor q`. Builds `IsRegularPrime` from the Bernoulli condition via the
  Herbrand–Ribet / Step-C / plus-part machinery (`Component1`, `VandiverCocycle`, `PlusBridge`),
  then applies `flt_regular`.
- `RegularPrimes.lean` — `flt_of_regCheck`: a regular prime has an empty irregular-index list
  (`irrListCert q [] = true`), kernel-decided.
- `Reg/Flt<q>.lean` — `flt_<q>` for each regular prime `17 ≤ q < 350`, **one module per prime**
  (each kernel `decide` runs in its own process; a monolithic file accumulates memory across primes).
- `FLTRegularPrimes.lean` — aggregator importing all 47; `#print axioms` confirms clean.
- `AxiomAudit.lean` — reprints the headline theorems' axiom base.

## Build

```bash
lake exe cache get
lake build FLTRegularPrimes   # all 47 primes; or one, e.g. lake build Reg.Flt223
```

Kernel `decide` memory climbs steeply with `q`: ~7 GiB at `q = 151`, ~19 GiB at `223`, up to ~73 GiB at
`349` (measured on a `c4d-standard-64`); the frontier is compute time (`349` ≈ 15.5 min). A bare
`lake build FLTRegularPrimes` builds all 47 **in parallel** and will OOM anything but a large box —
serialize under a cap (`systemd-run --scope -p MemoryMax=… env LEAN_NUM_THREADS=1 lake build FLTRegularPrimes`)
or just build the primes your machine handles (`lake build Reg.Flt<q>`) and skip the heavy tail. Your call.

**Expected warnings.** `q ≥ 269` prints `exponent … exceeds the threshold 256, … not evaluated` — harmless
(the `decide` does the proof); left in place to avoid recompiling the big primes.

## Dependencies

`require`s **`flt-cyclotomic-nt`** (path). The shared
base provides everything this repo needs:
- the Bernoulli kernel check — `CyclotomicNT.Faithfulness` (pure-`Nat` faithfulness bridge) +
  `CyclotomicNT.IrrCertNat` (the generic irregular-index cert);
- the **class-group core** — `Herbrand` / `Stickelberger` / `KPlusGalois` / `CaseII` / the
  Kummer + Eigen + Cyclotomic-unit machinery that `Component1` / `PlusBridge` / `VandiverCocycle`
  use to turn the Bernoulli condition into `IsRegularPrime`. (This core is shared with the
  Vandiver-certificate side; it lives in `flt-cyclotomic-nt`, not here.)
- transitively `flt-regular`, `flt-stickelberger`, and mathlib.

## Part of the flt-vandiver family

Six sibling libraries (clone them as siblings — Lake uses relative paths), release tag
**`afm-v1`**, GitHub topic
[`flt-vandiver`](https://github.com/batchatco?tab=repositories&q=topic:flt-vandiver).

| Repo | Role |
|------|------|
| `flt-vandiver` | Engine: Case I/II descent, crown theorems, certificate bridges (Washington 9.5) |
| `flt-vandiver-primes` | `native_decide` instances: every prime 17 ≤ p < 1000, plus 16843 and 2124679 |
| `flt-vandiver-primes-kernel` | Kernel `decide` (zero compiler trust): the 8 irregular primes < 200 |
| `flt-regular-extended` | Kernel Bernoulli ⟹ regular FLT, 17 ≤ q < 350 (47 primes) |
| `flt-cyclotomic-nt` | Herbrand, cyclotomic unit index, class-group Stickelberger, certificate base |
| `flt-stickelberger` | Clean-room Gauss-sum / Stickelberger core (Mathlib-only) |

Each ships an `AxiomAudit.lean` reprinting its headline theorems' axiom base. `sorry`-free on
Lean / Mathlib `v4.31.0`.

## Blueprint & metadata

A dependency-graph blueprint of this library is under [`blueprint/`](blueprint/) (rendered web + PDF published to GitHub Pages once the family is public). Family-level metadata lives in [`formalization.yaml`](https://github.com/batchatco/flt-vandiver/blob/afm-v1/formalization.yaml) in the flt-vandiver repo.

---

Apache License 2.0 — see [LICENSE](LICENSE).
© Bradley Taylor. Code written largely by Claude (Anthropic) under the author's direction.
