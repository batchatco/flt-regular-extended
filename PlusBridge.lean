import CyclotomicNT.CaseII
import CyclotomicNT.Stickelberger
import CyclotomicNT.KPlusGalois
import CyclotomicNT.RegularPrimes
import CyclotomicNT.StkAnnihilation

/-!
Plus-part bridge: `IsVandiverPrime p ⟹ p ∤ |plusPart(Cl K)|` for `K = ℚ(ζ_p)`.

This closes the "one genuine remaining bridge" of the FLT-17 regular-prime route. The handoff
scoped it as needing either (i) a relative-norm Galois-orbit-product identity or (ii) showing every
p-part plus class is in the image of `classGroupExtend`. We take a third, short path that subsumes
(ii): the engine ALREADY proves (axiom-clean, `CaseII.lean`) that any conjugation-fixed ideal `B`
coprime to `(p)` with `B^p` principal is itself principal, GIVEN `IsVandiverPrime p`
(`isPrincipal_of_conjFixed_of_pow`). To kill an order-`p` plus class `c`, take any coprime-to-`p`
representative `J` and set `B := J · conj(J)`: it is *exactly* conjugation-fixed, coprime to `(p)`,
with `[B] = c·J(c) = c²` and `B^p` principal. The engine lemma gives `B` principal, so `c² = 1`;
with `c^p = 1` and `p` odd, `c = 1` — contradiction.

Standalone; check from this package root with:
    lake env lean PlusBridge.lean
-/

open CyclotomicNT

open NumberField IsCyclotomicExtension.Rat
open scoped NumberField nonZeroDivisors Pointwise

namespace RegPrimes

variable {p : ℕ} [hpri : Fact p.Prime]

section PlusPart
variable {K : Type*} [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

/-- The **plus part** `A⁺ = {cl | J cl = cl}` (J = complex conjugation). -/
def plusPart : Subgroup (ClassGroup (𝓞 K)) where
  carrier := {cl | classGroupGalAct (conjGal (K := K)) cl = cl}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; rw [map_mul, ha, hb]
  inv_mem' := by intro a ha; simp only [Set.mem_setOf_eq] at *; rw [map_inv, ha]

end PlusPart

omit hpri in
/-- The ring-of-integers automorphism underlying `classGroupGalAct conjGal` is exactly
`ringOfIntegersComplexConj`. -/
theorem mapRingEquiv_conjGal_toRingHom_eq (K : Type*) [Field K] [CharZero K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] :
    ((RingOfIntegers.mapRingEquiv (conjGal (K := K)).toRingEquiv).toRingHom
        : 𝓞 K →+* 𝓞 K)
      = (NumberField.IsCMField.ringOfIntegersComplexConj K : 𝓞 K →+* 𝓞 K) := by
  ext x
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingOfIntegers.mapRingEquiv_apply,
    NumberField.IsCMField.coe_ringOfIntegersComplexConj]
  rfl

open NumberField.IsCMField in
/-- **The plus-part bridge.** If `p` is a Vandiver prime (`p ∤ h⁺`), then the plus part of the
class group of `K = ℚ(ζ_p)` has no `p`-torsion, hence `p ∤ |A⁺|`. -/
theorem not_dvd_card_plusPart_of_isVandiver (hp : 2 < p)
    [IsCMField (CyclotomicField p ℚ)] (hvand : IsVandiverPrime p) :
    ¬ p ∣ Nat.card (plusPart (K := CyclotomicField p ℚ)) := by
  intro hdvd
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hpri.out.ne_zero⟩
  set K := CyclotomicField p ℚ with hKdef
  haveI : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  set ρ : 𝓞 K →+* 𝓞 K := (ringOfIntegersComplexConj K : 𝓞 K →+* 𝓞 K) with hρdef
  have hρinj : Function.Injective ρ := (ringOfIntegersComplexConj K).injective
  have hpne : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hpri.out.ne_zero
  -- ρ ∘ ρ = id
  have hρρ : ρ.comp ρ = RingHom.id (𝓞 K) := by
    ext y
    simp only [RingHom.comp_apply, RingHom.id_apply, hρdef, RingHom.coe_coe,
      coe_ringOfIntegersComplexConj, complexConj_apply_apply]
  -- Cauchy: an order-`p` plus class `c`
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set c : ClassGroup (𝓞 K) := (x : ClassGroup (𝓞 K)) with hcdef
  have hcp : c ^ p = 1 := by
    have hxp : x ^ p = 1 := by have h := pow_orderOf_eq_one x; rwa [hxord] at h
    rw [hcdef, ← SubmonoidClass.coe_pow, hxp, OneMemClass.coe_one]
  have hc1 : c ≠ 1 := by
    intro hh
    have hx1 : x = 1 := Subtype.ext (by rw [OneMemClass.coe_one]; exact hh)
    rw [hx1, orderOf_one] at hxord; exact hpri.out.one_lt.ne' hxord.symm
  have hcfix : classGroupGalAct (conjGal (K := K)) c = c := x.2
  -- a representative ideal `J` of `c`, coprime to `(p)`
  obtain ⟨I0, hI0⟩ := ClassGroup.mk0_surjective c
  have hI0ne : (I0 : Ideal (𝓞 K)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I0.2
  have hMne : (Ideal.span {(p : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hpne
  obtain ⟨xx, yy, J, hxx, hJne, hspaneq, hJcop⟩ :=
    Ideal.exists_span_mul_eq_span_mul_coprime hMne hI0ne
  have hyyne : yy ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero, Ideal.bot_mul, Ideal.mul_eq_bot] at hspaneq
    rcases hspaneq with h | h
    · rw [Ideal.span_singleton_eq_bot] at h; exact hxx h
    · exact hI0ne (h.trans Ideal.zero_eq_bot.symm)
  have hJmem : J ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hJne
  have hmkJ : ClassGroup.mk0 ⟨J, hJmem⟩ = c := by
    rw [← hI0]; symm; rw [ClassGroup.mk0_eq_mk0_iff]; exact ⟨xx, yy, hxx, hyyne, hspaneq⟩
  -- `J.map ρ` is nonzero and its class is again `c`
  have hJmapne : J.map ρ ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective hρinj, ← Ideal.zero_eq_bot]
    exact hJne
  have hJmapmem : J.map ρ ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hJmapne
  have hmkJc : ClassGroup.mk0 ⟨J.map ρ, hJmapmem⟩ = c := by
    have h1 : classGroupGalAct (conjGal (K := K)) (ClassGroup.mk0 ⟨J, hJmem⟩)
        = ClassGroup.mk0 ⟨J.map ρ, hJmapmem⟩ := by
      rw [classGroupGalAct, classGroupMapEquiv_mk0]
      refine congrArg ClassGroup.mk0 (Subtype.ext ?_)
      rw [idealMapEquiv_coe, mapRingEquiv_conjGal_toRingHom_eq (p := p) K]
    rw [hmkJ, hcfix] at h1; exact h1.symm
  -- `B := J · ρ(J)` is exactly conj-fixed, coprime to `(p)`, with `[B] = c²`
  set B : Ideal (𝓞 K) := J * J.map ρ with hBdef
  have hBne : B ≠ 0 := mul_ne_zero hJne hJmapne
  have hBmem : B ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hBne
  set B' : (Ideal (𝓞 K))⁰ := ⟨B, hBmem⟩ with hB'def
  have hBfix : B.map ρ = B := by
    rw [hBdef, Ideal.map_mul, Ideal.map_map, hρρ, Ideal.map_id, mul_comm]
  have hcopB : IsCoprime B (Ideal.span {(p : 𝓞 K)}) := by
    rw [hBdef]
    apply IsCoprime.mul_left
    · rw [Ideal.isCoprime_iff_sup_eq]; exact hJcop
    · rw [Ideal.isCoprime_iff_sup_eq]
      have hps : (Ideal.span {(p : 𝓞 K)}).map ρ = Ideal.span {(p : 𝓞 K)} := by
        rw [Ideal.map_span, Set.image_singleton, map_natCast]
      calc (J.map ρ) ⊔ Ideal.span {(p : 𝓞 K)}
          = (J.map ρ) ⊔ (Ideal.span {(p : 𝓞 K)}).map ρ := by rw [hps]
        _ = (J ⊔ Ideal.span {(p : 𝓞 K)}).map ρ := (Ideal.map_sup ρ _ _).symm
        _ = (⊤ : Ideal (𝓞 K)).map ρ := by rw [hJcop]
        _ = ⊤ := Ideal.map_top ρ
  have hmkB : ClassGroup.mk0 B' = c ^ 2 := by
    have hsplit : B' = (⟨J, hJmem⟩ : (Ideal (𝓞 K))⁰) * ⟨J.map ρ, hJmapmem⟩ :=
      Subtype.ext (by rw [hB'def]; rfl)
    rw [hsplit, map_mul, hmkJ, hmkJc, ← pow_two]
  have hBpprin : (B ^ p).IsPrincipal := by
    have hmem : B ^ p ∈ (Ideal (𝓞 K))⁰ := pow_mem hBmem p
    rw [← ClassGroup.mk0_eq_one_iff hmem]
    have heq : (⟨B ^ p, hmem⟩ : (Ideal (𝓞 K))⁰) = B' ^ p :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow])
    rw [heq, map_pow, hmkB, ← pow_mul, mul_comm 2 p, pow_mul, hcp, one_pow]
  -- the engine lemma: `B` is principal, so `c² = 1`
  have hBprin : B.IsPrincipal := isPrincipal_of_conjFixed_of_pow hp hvand hBfix hcopB hBpprin
  have hc2 : c ^ 2 = 1 := by
    rw [← hmkB]; exact (ClassGroup.mk0_eq_one_iff hBmem).mpr hBprin
  -- `c^p = 1`, `c² = 1`, `gcd(2,p)=1` ⟹ `c = 1`, contradiction
  have hcop2p : Nat.gcd 2 p = 1 :=
    (Nat.coprime_primes Nat.prime_two hpri.out).mpr (by omega)
  have hord1 : orderOf c ∣ 1 :=
    hcop2p ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc2) (orderOf_dvd_of_pow_eq_one hcp)
  exact hc1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord1))

end RegPrimes
