import VandiverCocycle
import Component1
import PlusBridge
import FltRegular.FltRegular

/-!
FLT for regular primes, `native_decide`-free, via the regular-prime route.

Generic chain, for an odd prime `q` whose even Bernoulli numerators `B₂, B₄, …, B_{q-3}` are all
prime-to-`q` (i.e. `q` is regular):
        Bernoulli / regularity hypothesis
        ⟹ ¬q∣|A⁻|  (Herbrand–Ribet minus part)
        ⟹ IsVandiverPrime q  (Step C eigen non-vanishing + Washington Thm 8.14)
        ⟹ ¬q∣|A⁺|  (plus-part bridge, `PlusBridge`)
        ⟹ ¬q∣|Cl ℚ(ζ_q)|  (J-eigendecomposition)
        = IsRegularPrime q  ⟹  flt_regular  ⟹  FermatLastTheoremFor q.

The single export `fermatLastTheoremFor_of_bernoulli` is fully generic; a concrete prime only
needs to discharge the finite Bernoulli hypothesis `hB` (e.g. by a kernel `decide`, as the
per-prime modules in `Reg/` do via `RegularPrimes.flt_of_regCheck`).
-/

open NumberField IsCyclotomicExtension.Rat CyclotomicNT RegPrimes
open scoped NumberField

namespace FltOfBernoulli

variable {p : ℕ} [hpri : Fact p.Prime]
variable {K : Type*} [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}

omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] in
/-- helper: an order-`p` element of a subgroup `H` forces `p ∣ |H|`. -/
private theorem dvd_card_of_mem {H : Subgroup (ClassGroup (𝓞 K))} {x : ClassGroup (𝓞 K)}
    (hx : x ∈ H) (hxne : x ≠ 1) (hxp : x ^ p = 1) : p ∣ Nat.card H := by
  have hord : orderOf (⟨x, hx⟩ : H) = p := by
    apply orderOf_eq_prime
    · apply Subtype.ext; rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hxp
    · intro h; exact hxne (by have := Subtype.ext_iff.mp h; simpa using this)
  rw [← hord]; exact orderOf_dvd_natCard _

/-- **J-eigendecomposition of the `p`-Sylow** (`p` odd): with `p∤|A⁺|` and `p∤|A⁻|`
    the full class group has no `p`-torsion, so `p∤|Cl K|`. Here `A⁺ = RegPrimes.plusPart`
    (the plus-part bridge's def) and `A⁻ = minusPart` (defined in `Component1`). -/
theorem not_dvd_card_classGroup (hp2 : p ≠ 2) (hζ : IsPrimitiveRoot ζ p)
    (hplus : ¬ p ∣ Nat.card (RegPrimes.plusPart (K := K)))
    (hminus : ¬ p ∣ Nat.card (minusPart (K := K))) :
    ¬ p ∣ Nat.card (ClassGroup (𝓞 K)) := by
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hp1 := hpri.out.one_lt
  have hgne : g ≠ 1 := by intro h; rw [h, orderOf_one] at hg; omega
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hconj2 : conjGal (K := K) * conjGal (K := K) = 1 := by
    apply (galEquivZMod p K).injective
    rw [map_mul, galEquivZMod_conjGal hζ, map_one]; simp
  set J : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K) := classGroupGalAct (conjGal (K := K)) with hJ
  have hJ2 : ∀ cl, J (J cl) = cl := fun cl => by rw [hJ, classGroupGalAct_mul, hconj2,
    classGroupGalAct_one]
  have hJg : J g ^ p = 1 := by rw [← map_pow, hgp, map_one]
  have he2 : 2 * ((p + 1) / 2) = p + 1 := by
    obtain ⟨m, hm⟩ := hpri.out.odd_of_ne_two hp2; omega
  have hgpmem : (g * J g) ^ ((p + 1) / 2) ∈ RegPrimes.plusPart (K := K) := by
    show J ((g * J g) ^ ((p + 1) / 2)) = (g * J g) ^ ((p + 1) / 2)
    rw [map_pow, map_mul, hJ2, mul_comm (J g) g]
  have hgmmem : (g * (J g)⁻¹) ^ ((p + 1) / 2) ∈ minusPart (K := K) := by
    show J ((g * (J g)⁻¹) ^ ((p + 1) / 2)) = ((g * (J g)⁻¹) ^ ((p + 1) / 2))⁻¹
    rw [map_pow, map_mul, map_inv, hJ2, ← inv_pow, mul_inv, inv_inv, mul_comm]
  have hprod : (g * J g) ^ ((p + 1) / 2) * (g * (J g)⁻¹) ^ ((p + 1) / 2) = g := by
    rw [← mul_pow, show (g * J g) * (g * (J g)⁻¹) = g ^ 2 by
      rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, pow_two], ← pow_mul, he2, pow_succ,
      hgp, one_mul]
  have hgppow : ((g * J g) ^ ((p + 1) / 2)) ^ p = 1 := by
    rw [← pow_mul, mul_comm ((p + 1) / 2) p, pow_mul, mul_pow, hgp, hJg, mul_one, one_pow]
  have hgmpow : ((g * (J g)⁻¹) ^ ((p + 1) / 2)) ^ p = 1 := by
    rw [← pow_mul, mul_comm ((p + 1) / 2) p, pow_mul, mul_pow, hgp, inv_pow, hJg, inv_one,
      mul_one, one_pow]
  rcases (by
      by_contra hc; push Not at hc; rw [hc.1, hc.2, mul_one] at hprod; exact hgne hprod.symm :
      (g * J g) ^ ((p + 1) / 2) ≠ 1 ∨ (g * (J g)⁻¹) ^ ((p + 1) / 2) ≠ 1) with h | h
  · exact hplus (dvd_card_of_mem hgpmem h hgppow)
  · exact hminus (dvd_card_of_mem hgmmem h hgmpow)

/-- **Step C ⟹ Vandiver**: the Bernoulli condition makes every Step-C eigen-unit a non-`p`-th
    power, so by Washington's Thm 8.14 (`vandiver_aux`) `p ∤ h⁺`. -/
theorem not_dvd_classNumber_real (hp2 : p ≠ 2) (hζ : IsPrimitiveRoot ζ p)
    (hB : ∀ k : Fin ((p - 3) / 2), ¬ (p : ℤ) ∣ (bernoulli (2 * (k.1 + 1))).num) :
    ¬ p ∣ Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K))) :=
  vandiver_aux hζ hp2 (fun k => StepC.eigenFamily_ne_zero_of_not_dvd_bernoulli hζ hp2 k (hB k))

/-- **FLT for any regular prime, native_decide-free, via Kummer's criterion.** For an odd prime
    `p`, if `p` divides no numerator of `B₂, B₄, …, B_{p-3}` (i.e. `p` is regular), then
    `FermatLastTheoremFor p`. This is fully generic; a concrete prime only needs to discharge the
    finite Bernoulli hypothesis `hB` (e.g. by kernel `decide`, as the `Reg/` modules do). -/
theorem fermatLastTheoremFor_of_bernoulli (q : ℕ) [Fact q.Prime] (hq : 2 < q)
    (hB : ∀ k : Fin ((q - 3) / 2), ¬ (q : ℤ) ∣ (bernoulli (2 * (k.1 + 1))).num) :
    FermatLastTheoremFor q := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : NeZero ((q : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero⟩
  haveI : IsCyclotomicExtension {q} ℚ (CyclotomicField q ℚ) :=
    CyclotomicField.isCyclotomicExtension q ℚ
  haveI : NumberField.IsCMField (CyclotomicField q ℚ) :=
    IsCyclotomicExtension.Rat.isCMField (CyclotomicField q ℚ) (S := {q})
      ⟨q, Set.mem_singleton q, hq⟩
  have hq2 : q ≠ 2 := by omega
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ)) q :=
    IsCyclotomicExtension.zeta_spec q ℚ (CyclotomicField q ℚ)
  -- minus part: no irregular index ⟹ `q ∤ h⁻`
  have hminus : ¬ q ∣ Nat.card (minusPart (K := CyclotomicField q ℚ)) := by
    intro hdvd
    obtain ⟨i, hev, h2i, hle, hdvd'⟩ := irregular_of_dvd_minusPart hq2 hζ hdvd
    obtain ⟨m, hm⟩ := hev
    refine hB ⟨m - 1, by omega⟩ ?_
    rw [show 2 * (m - 1 + 1) = i by omega]; exact hdvd'
  -- plus part: Step C ⟹ `q ∤ h⁺`, then the plus-part bridge ⟹ `q ∤ |A⁺|`
  have hvand : IsVandiverPrime q := by
    rw [IsVandiverPrime, Nat.Prime.coprime_iff_not_dvd Fact.out]
    exact not_dvd_classNumber_real (K := CyclotomicField q ℚ) hq2 hζ hB
  have hplus : ¬ q ∣ Nat.card (RegPrimes.plusPart (K := CyclotomicField q ℚ)) :=
    RegPrimes.not_dvd_card_plusPart_of_isVandiver hq hvand
  -- eigendecomposition ⟹ `q ∤ |Cl|` = regular ⟹ FLT
  have hreg : IsRegularPrime q := by
    rw [IsRegularPrime, IsRegularNumber, Nat.Prime.coprime_iff_not_dvd Fact.out,
      ← Nat.card_eq_fintype_card]
    exact not_dvd_card_classGroup hq2 hζ hplus hminus
  exact flt_regular hreg hq2

end FltOfBernoulli
