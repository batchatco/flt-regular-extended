import CyclotomicNT.Herbrand
import CyclotomicNT.KPlusGalois

/-!
Minus-part assembly — building blocks, all proven, sorry-free.
Axioms: propext, Classical.choice, Quot.sound. Check from this package root with:
    lake env lean Component1.lean

  1. `exists_eigenProj_ne_one` — a nontrivial order-`p` class has a nontrivial weight-`k`
     eigencomponent (closes the gap named in `CyclotomicNT.herbrand_eigenProj`'s docstring).
  2. `eigenProj_inv` — `eigenProj p k` is a hom in `cl`.
  3. `eigenProj_galAct` — naturality: `eigenProj` commutes with the (abelian) Galois action.
  4. `eigenProj_even_minus` — **even-weight eigencomponents vanish on minus-part elements**
     (`J cl = cl⁻¹`, `J` = complex conjugation = `−1 ∈ (ℤ/p)ˣ` via `KPlusGalois`). Hence a
     nontrivial minus-part `p`-class has its nontrivial component at ODD `k` — the input to
     `herbrand_eigenProj`. Uses `isEigenClass_eigenProj` + `galCommutative` + the `x²=1 ∧
     x^p=1, p odd ⇒ x=1` endgame.

  5. `floor_sum`, `sum_units_zmod` — number-theory crux for (a):
     `2·∑_{c=1}^{p-1}⌊cv/p⌋ = (p-1)(v-1)` (pairing c↔p-c); `∑ units of ZMod p = 0`.
  6. `eigenProj_one_eq_one` — **(a): `A^{(1)}=0`** (the ω / weight-1 eigenspace is trivial).
     Summing `eigenClass_dvd_sum` over all c gives `p ∣ ∑_c S(c)`, but `∑_c S(c) ≡ 2⁻¹ ≢ 0` —
     contradiction. (Elementary; no Fermat quotient.)
  7. `minusPart` — the minus part `A⁻ = {cl | J cl = cl⁻¹}` (a subgroup).
  8. `exists_odd_eigenProj_of_dvd_minusPart` (b) and **`irregular_of_dvd_minusPart`** — the
     full assembly: `p ∣ |A⁻| ⟹ ∃ irregular index` (Cauchy + (a) + (b) + `herbrand_eigenProj`).
-/

open CyclotomicNT CyclotomicNT.QiCert Finset NumberField IsCyclotomicExtension.Rat
set_option maxHeartbeats 2000000
variable {p : ℕ} [hpri : Fact p.Prime]

omit hpri in
theorem floor_sum (hp : p.Prime) {v : ℕ} (hv1 : 1 ≤ v) (hvp : v < p) :
    2 * ∑ c ∈ Ico 1 p, c * v / p = (p - 1) * (v - 1) := by
  have hp2 := hp.two_le
  have hpair : ∀ c ∈ Ico 1 p, c * v / p + (p - c) * v / p = v - 1 := by
    intro c hc
    rw [mem_Ico] at hc; obtain ⟨hc1, hcp⟩ := hc
    have hndvd : ∀ {x : ℕ}, 1 ≤ x → x < p → ¬ p ∣ x * v := by
      intro x hx1 hxp h
      rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
      · exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
      · exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
    have hr1 : 1 ≤ c * v % p :=
      Nat.one_le_iff_ne_zero.mpr fun h => hndvd hc1 hcp (Nat.dvd_of_mod_eq_zero h)
    have hr2 : 1 ≤ (p - c) * v % p :=
      Nat.one_le_iff_ne_zero.mpr fun h => hndvd (by omega) (by omega) (Nat.dvd_of_mod_eq_zero h)
    have hr1p : c * v % p < p := Nat.mod_lt _ (by omega)
    have hr2p : (p - c) * v % p < p := Nat.mod_lt _ (by omega)
    have hd1 : p * (c * v / p) + c * v % p = c * v := Nat.div_add_mod (c * v) p
    have hd2 : p * ((p - c) * v / p) + (p - c) * v % p = (p - c) * v :=
      Nat.div_add_mod ((p - c) * v) p
    have hsum_v : c * v + (p - c) * v = p * v := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' (le_of_lt hcp)]
    have hmoddvd : p ∣ (c * v % p + (p - c) * v % p) := by
      have h0 : (c * v % p + (p - c) * v % p) % p = (c * v + (p - c) * v) % p :=
        (Nat.add_mod _ _ _).symm
      rw [hsum_v, Nat.mul_mod_right] at h0
      exact Nat.dvd_of_mod_eq_zero h0
    have hrr : c * v % p + (p - c) * v % p = p := by
      have hge := Nat.le_of_dvd (by omega) hmoddvd
      obtain ⟨k, hk⟩ := hmoddvd
      have hk1 : k = 1 := by nlinarith [hr1p, hr2p]
      rw [hk1, mul_one] at hk; exact hk
    have hXY : p * (c * v / p + (p - c) * v / p) + p = p * v := by nlinarith [hd1, hd2, hrr, hsum_v]
    have hpv : c * v / p + (p - c) * v / p + 1 = v := by nlinarith [hXY]
    omega
  have hreindex : ∑ c ∈ Ico 1 p, (p - c) * v / p = ∑ c ∈ Ico 1 p, c * v / p := by
    apply Finset.sum_nbij' (fun c => p - c) (fun c => p - c) <;> intro a ha <;>
      simp only [mem_Ico] at * <;> omega
  have hcard : (Ico 1 p).card = p - 1 := by rw [Nat.card_Ico]
  calc 2 * ∑ c ∈ Ico 1 p, c * v / p
      = ∑ c ∈ Ico 1 p, c * v / p + ∑ c ∈ Ico 1 p, (p - c) * v / p := by rw [hreindex]; ring
    _ = ∑ c ∈ Ico 1 p, (c * v / p + (p - c) * v / p) := (Finset.sum_add_distrib).symm
    _ = ∑ _c ∈ Ico 1 p, (v - 1) := Finset.sum_congr rfl hpair
    _ = (p - 1) * (v - 1) := by rw [Finset.sum_const, hcard, smul_eq_mul]

/-- sum of the units of `ZMod p` (p odd) is `0`. -/
theorem sum_units_zmod (hp2 : p ≠ 2) :
    ∑ a : (ZMod p)ˣ, ((a : (ZMod p)ˣ) : ZMod p) = 0 := by
  set S := ∑ a : (ZMod p)ˣ, ((a : (ZMod p)ˣ) : ZMod p) with hS
  have hbij : S = ∑ a : (ZMod p)ˣ, (((-1 : (ZMod p)ˣ) * a : (ZMod p)ˣ) : ZMod p) :=
    (Equiv.sum_comp (Equiv.mulLeft (-1 : (ZMod p)ˣ)) (fun a => ((a : (ZMod p)ˣ) : ZMod p))).symm
  have hneg : S = - S := by
    conv_lhs => rw [hbij]
    simp only [Units.val_neg, neg_one_mul]
    rw [Finset.sum_neg_distrib, ← hS]
  have h2 : S + S = 0 := by nth_rewrite 1 [hneg]; ring
  have hchar : (2 : ZMod p) ≠ 0 := by
    rw [show (2:ZMod p) = ((2:ℕ):ZMod p) by push_cast; ring, Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hpri.out Nat.prime_two).mp h)
  have : (2 : ZMod p) * S = 0 := by rw [two_mul]; exact h2
  exact (mul_eq_zero.mp this).resolve_left hchar

section
variable {k₀ : Type*} [Field k₀] [NumberField k₀] [IsCyclotomicExtension {p} ℚ k₀]

/-- A nontrivial order-`p` class has a nontrivial weight-`k` eigencomponent (some `k < p-1`). -/
theorem exists_eigenProj_ne_one {cl : ClassGroup (𝓞 k₀)}
    (hne1 : cl ≠ 1) (hclp : cl ^ p = 1) :
    ∃ k ∈ Finset.range (p - 1), eigenProj p k cl ≠ 1 := by
  by_contra h
  push Not at h
  have hprod : ∏ k ∈ Finset.range (p - 1), eigenProj p k cl = 1 := Finset.prod_eq_one h
  rw [prod_eigenProj hclp] at hprod
  have hord : orderOf cl = p := orderOf_eq_prime hclp hne1
  have hdvd : orderOf cl ∣ (p - 1) := orderOf_dvd_of_pow_eq_one hprod
  rw [hord] at hdvd
  have hp2 := hpri.out.two_le
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

/-- `eigenProj p k` is a hom in `cl`. -/
theorem eigenProj_inv (k : ℕ) (cl : ClassGroup (𝓞 k₀)) :
    eigenProj p k cl⁻¹ = (eigenProj p k cl)⁻¹ := by
  rw [eigenProj, eigenProj, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [map_inv, inv_pow]

/-- Naturality: `eigenProj` commutes with the (abelian) Galois action. -/
theorem eigenProj_galAct (k : ℕ) (g : k₀ ≃ₐ[ℚ] k₀) (cl : ClassGroup (𝓞 k₀)) :
    eigenProj p k (classGroupGalAct g cl) = classGroupGalAct g (eigenProj p k cl) := by
  rw [eigenProj, eigenProj, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [map_pow, classGroupGalAct_mul, classGroupGalAct_mul]
  have hXY : ((galEquivZMod p k₀).symm a)⁻¹ * g = g * ((galEquivZMod p k₀).symm a)⁻¹ := by
    refine (galEquivZMod p k₀).injective ?_
    rw [map_mul, map_mul]
    exact mul_comm _ _
  rw [hXY]

/-- **(a): `A^{(1)} = 0`** — the weight-1 (ω) eigenprojection is trivial. -/
theorem eigenProj_one_eq_one (hp2 : p ≠ 2) {cl : ClassGroup (𝓞 k₀)} (hclp : cl ^ p = 1) :
    eigenProj p 1 cl = 1 := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  by_contra hne
  have hep : (eigenProj p 1 cl) ^ p = 1 := eigenProj_pow_p hclp 1
  have heig : IsEigenClass p 1 (eigenProj p 1 cl) := isEigenClass_eigenProj hclp 1
  -- p ∣ S(c) for all c
  have hSdvd : ∀ c : ℕ, p ∣ ∑ a : (ZMod p)ˣ,
      ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val * (c * (a : ZMod p).val / p) := by
    intro c
    have h := eigenClass_dvd_sum hne hep heig c
    simpa only [pow_one] using h
  have hTdvd : p ∣ ∑ c ∈ Ico 1 p, ∑ a : (ZMod p)ˣ,
      ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val * (c * (a : ZMod p).val / p) :=
    Finset.dvd_sum fun c _ => hSdvd c
  have hple : 1 ≤ p := hpri.out.one_le
  have hNat : 2 * ∑ c ∈ Ico 1 p, ∑ a : (ZMod p)ˣ,
        ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val * (c * (a : ZMod p).val / p)
      = ∑ a : (ZMod p)ˣ, ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val * ((p - 1) * ((a : ZMod p).val - 1)) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hv1 : 1 ≤ (a : ZMod p).val := by
      rw [Nat.one_le_iff_ne_zero, Ne, ZMod.val_eq_zero]; exact Units.ne_zero a
    have hvp : (a : ZMod p).val < p := ZMod.val_lt _
    rw [← Finset.mul_sum, show 2 * (((a⁻¹ : (ZMod p)ˣ) : ZMod p).val *
        ∑ c ∈ Ico 1 p, c * (a : ZMod p).val / p)
        = ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val *
        (2 * ∑ c ∈ Ico 1 p, c * (a : ZMod p).val / p) by ring,
      floor_sum hpri.out hv1 hvp]
  have hcard : (Fintype.card (ZMod p)ˣ : ZMod p) = -1 := by
    have hc : Fintype.card (ZMod p)ˣ = p - 1 := by
      rw [ZMod.card_units_eq_totient, Nat.totient_prime hpri.out]
    rw [hc, Nat.cast_sub hple, Nat.cast_one, ZMod.natCast_self, zero_sub]
  have hinvsum : ∑ a : (ZMod p)ˣ, ((a⁻¹ : (ZMod p)ˣ) : ZMod p) = 0 := by
    have he : ∑ a : (ZMod p)ˣ, ((a⁻¹ : (ZMod p)ˣ) : ZMod p)
        = ∑ a : (ZMod p)ˣ, ((a : (ZMod p)ˣ) : ZMod p) :=
      Equiv.sum_comp (Equiv.inv ((ZMod p)ˣ)) (fun a => ((a : (ZMod p)ˣ) : ZMod p))
    rw [he]; exact sum_units_zmod hp2
  have hcast : (((∑ a : (ZMod p)ˣ, ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val *
        ((p - 1) * ((a : ZMod p).val - 1))) : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_sum]
    have hterm : ∀ a : (ZMod p)ˣ,
        (((((a⁻¹ : (ZMod p)ˣ) : ZMod p).val * ((p - 1) * ((a : ZMod p).val - 1))) : ℕ) : ZMod p)
        = ((a⁻¹ : (ZMod p)ˣ) : ZMod p) - 1 := by
      intro a
      have hv1 : 1 ≤ (a : ZMod p).val := by
        rw [Nat.one_le_iff_ne_zero, Ne, ZMod.val_eq_zero]; exact Units.ne_zero a
      have hcancel : ((a : ZMod p))⁻¹ * (a : ZMod p) = 1 := inv_mul_cancel₀ (Units.ne_zero a)
      push_cast [Nat.cast_sub hple, Nat.cast_sub hv1, ZMod.natCast_zmod_val, ZMod.natCast_self]
      linear_combination -hcancel
    rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_sub_distrib, hinvsum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
    ring
  have hT0 : ((∑ c ∈ Ico 1 p, ∑ a : (ZMod p)ˣ,
        ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val * (c * (a : ZMod p).val / p) : ℕ) : ZMod p) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hTdvd
  have e1 : ((2 * ∑ c ∈ Ico 1 p, ∑ a : (ZMod p)ˣ,
        ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val * (c * (a : ZMod p).val / p) : ℕ) : ZMod p) = 1 := by
    rw [hNat]; exact hcast
  rw [Nat.cast_mul, hT0, mul_zero] at e1
  exact one_ne_zero e1.symm

end

section
variable {K : Type*} [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}

/-- **Even-weight eigencomponents vanish on minus-part elements.** -/
theorem eigenProj_even_minus (hp2 : p ≠ 2) (hζ : IsPrimitiveRoot ζ p) {k : ℕ} (hk : Even k)
    {cl : ClassGroup (𝓞 K)} (hclp : cl ^ p = 1)
    (hminus : classGroupGalAct (conjGal (K := K)) cl = cl⁻¹) :
    eigenProj p k cl = 1 := by
  haveI : Fact (1 < p) := ⟨hpri.out.one_lt⟩
  have hcg : conjGal (K := K) = (galEquivZMod p K).symm (-1) := by
    conv_lhs => rw [← (galEquivZMod p K).symm_apply_apply (conjGal (K := K)),
      galEquivZMod_conjGal hζ]
  have hconj : classGroupGalAct (conjGal (K := K)) (eigenProj p k cl) = eigenProj p k cl := by
    rw [hcg, isEigenClass_eigenProj hclp k (-1), hk.neg_one_pow, Units.val_one, ZMod.val_one,
      pow_one]
  have h2 : eigenProj p k cl⁻¹ = eigenProj p k cl := by
    rw [← hminus, eigenProj_galAct, hconj]
  rw [eigenProj_inv] at h2
  have hsq : (eigenProj p k cl) ^ 2 = 1 := by
    rw [pow_two]; nth_rewrite 1 [← h2]; exact inv_mul_cancel _
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr (hpri.out.odd_of_ne_two hp2)
  have hord1 : orderOf (eigenProj p k cl) = 1 :=
    Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hsq)
      (orderOf_dvd_of_pow_eq_one (eigenProj_pow_p hclp k)))
  exact orderOf_eq_one_iff.mp hord1

/-- **The minus part** of the class group: classes inverted by complex conjugation
    `J = conjGal`. A subgroup (J is an involution; the group is abelian). -/
def minusPart : Subgroup (ClassGroup (𝓞 K)) where
  carrier := {cl | classGroupGalAct (conjGal (K := K)) cl = cl⁻¹}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb, mul_inv]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv, ha]

/-- **(b) modulo (a)**: if `p ∣ |A⁻|`, then some order-`p` minus-part class has a
    nontrivial eigencomponent at an ODD weight `k < p-1`. Combined with the remaining
    lemma (a) (`A^{(1)}=0`, forcing `k ≥ 3`) and `herbrand_eigenProj`, this gives
    `p ∣ h⁻ ⟹ p irregular`. The whole difficulty is now isolated into "the odd k is ≥ 3". -/
theorem exists_odd_eigenProj_of_dvd_minusPart (hp2 : p ≠ 2) (hζ : IsPrimitiveRoot ζ p)
    (hdvd : p ∣ Nat.card (minusPart (K := K))) :
    ∃ (cl : ClassGroup (𝓞 K)) (k : ℕ), cl ≠ 1 ∧ cl ^ p = 1 ∧
      classGroupGalAct (conjGal (K := K)) cl = cl⁻¹ ∧ Odd k ∧ k < p - 1 ∧
      eigenProj p k cl ≠ 1 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hord : orderOf (x : ClassGroup (𝓞 K)) = p :=
    (orderOf_injective (minusPart (K := K)).subtype Subtype.val_injective x).trans hx
  have hne : (x : ClassGroup (𝓞 K)) ≠ 1 := by
    intro h; rw [h, orderOf_one] at hord; have := hpri.out.one_lt; omega
  have hpow : (x : ClassGroup (𝓞 K)) ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hminus : classGroupGalAct (conjGal (K := K)) (x : ClassGroup (𝓞 K))
      = (x : ClassGroup (𝓞 K))⁻¹ := x.2
  obtain ⟨k, hkrange, hkne⟩ := exists_eigenProj_ne_one hne hpow
  rw [Finset.mem_range] at hkrange
  have hkodd : Odd k := by
    rcases Nat.even_or_odd k with he | ho
    · exact absurd (eigenProj_even_minus hp2 hζ he hpow hminus) hkne
    · exact ho
  exact ⟨(x : ClassGroup (𝓞 K)), k, hne, hpow, hminus, hkodd, hkrange, hkne⟩

/-- **MINUS-PART ASSEMBLY COMPLETE**: `p ∣ |A⁻| ⟹ p is irregular` (∃ irregular index).
    Combines `exists_odd_eigenProj_of_dvd_minusPart` (b), `eigenProj_one_eq_one` (a, ruling
    out `k=1`), and `herbrand_eigenProj`. -/
theorem irregular_of_dvd_minusPart (hp2 : p ≠ 2) (hζ : IsPrimitiveRoot ζ p)
    (hdvd : p ∣ Nat.card (minusPart (K := K))) :
    ∃ i, IsIrregularIndex p i := by
  obtain ⟨cl, k, hne1, hclp, hminus, hkodd, hklt, hkne⟩ :=
    exists_odd_eigenProj_of_dvd_minusPart hp2 hζ hdvd
  have hk1 : k ≠ 1 := by
    intro h; exact hkne (by rw [h]; exact eigenProj_one_eq_one hp2 hclp)
  have hk3 : 3 ≤ k := by rcases hkodd with ⟨m, hm⟩; omega
  exact ⟨p - k, herbrand_eigenProj hkodd hk3 (by omega) hclp hkne⟩

end
