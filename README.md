# flt-regular-extended

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

Standard Lake project (toolchain pinned in `lean-toolchain`). **Do not run a bare
`lake build FLTRegularPrimes`**: Lake schedules the 47 independent per-prime modules
concurrently, and several kernel `decide`s at once overrun RAM (the largest, near `q = 349`,
peak ~73 GiB *each*). Force a **single decide at a time** with `LEAN_NUM_THREADS=1`, under a
memory cap sized to your machine:

```bash
# one module (one decide) resident at a time; set MemoryMax to your box
systemd-run --scope -p MemoryMax=80G --user \
  env LEAN_NUM_THREADS=1 lake build FLTRegularPrimes
```

The small primes fit in a few GiB (buildable on a laptop); the high primes need a big-memory
machine — `q = 349` alone peaks ~73 GiB. (There is no `-j`/`--jobs` flag in this Lake — Lake
schedules build jobs on Lean's task runtime, so `LEAN_NUM_THREADS` is the concurrency knob. `=1`
serializes the modules; ≥2 risks OOM at the high primes, and an individual `decide` is
single-threaded, so a higher value gains nothing on the bottleneck. To build a single prime,
e.g. `lake build Reg.Flt349` — the heaviest.)

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

---

Apache License 2.0 — see [LICENSE](LICENSE).
© Bradley Taylor. Code written largely by Claude (Anthropic) under the author's direction.
