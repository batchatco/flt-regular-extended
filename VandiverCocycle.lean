import CyclotomicNT.KummerLogDeriv
import CyclotomicNT.HerbrandBernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import CyclotomicNT.KummerReduction
import CyclotomicNT.CaseIKummer
import CyclotomicNT.EigenIndep
import CyclotomicNT.IndexReduction
import CyclotomicNT.PowerSumZMod
import CyclotomicNT.CyclotomicUnitGroup

/-!
Step C, bridge (2) backbone: the Kummer log-derivative `ℓ_n` of the cyclotomic-sum unit
`G_a := ∑_{j<a} Xʲ` (the lift of `ξ_a=(1-ζ^a)/(1-ζ)`) satisfies a 1-cocycle
`ℓ_n(G_{ab}) = ℓ_n(G_a) + aⁿ·ℓ_n(G_b)`, which averages to the coboundary
`ℓ_n(G_a) = (aⁿ-1)·T_n`, `T_n = ∑_b ℓ_n(G_b)`.  Numerically `T_n ≡ B_n/n` (Sage-verified).

Check from this package root with: `lake env lean VandiverCocycle.lean`.
-/

open CyclotomicNT CyclotomicNT.KummerLog

open Finset AddMonoidAlgebra
namespace RegPrimes
namespace KummerLog

variable {p : ℕ} [hpri : Fact p.Prime]

/-! ### The cyclotomic-sum element `G_a := ∑_{j<a} Xʲ` -/

/-- The cyclotomic-sum element `G_a := ∑_{j<a} Xʲ ∈ P` (the lift of `ξ_a = (1-ζ^a)/(1-ζ)`). -/
noncomputable def gsum (a : ℕ) : P p := ∑ j ∈ Finset.range a, single ((j : ZMod p)) 1

@[simp] theorem gsum_zero : gsum (p := p) 0 = 0 := by rw [gsum, Finset.range_zero, Finset.sum_empty]

theorem gsum_succ (a : ℕ) : gsum (p := p) (a + 1) = gsum a + single ((a : ZMod p)) 1 := by
  rw [gsum, gsum, Finset.sum_range_succ]

/-- `ε(G_a) = a`. -/
@[simp] theorem eps_gsum (a : ℕ) : eps (gsum (p := p) a) = (a : ZMod p) := by
  rw [gsum, map_sum, Finset.sum_congr rfl (fun j _ => eps_single _ _), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]

/-- `G_a` is a unit when `p ∤ a` (its augmentation `a` is nonzero). -/
noncomputable def gsumUnit (a : ℕ) (ha : (a : ZMod p) ≠ 0) : (P p)ˣ :=
  (isUnit_of_eps_ne_zero (f := gsum a) (by rw [eps_gsum]; exact ha)).unit

@[simp] theorem gsumUnit_val (a : ℕ) (ha : (a : ZMod p) ≠ 0) :
    ((gsumUnit a ha : (P p)ˣ) : P p) = gsum a :=
  IsUnit.unit_spec _

/-! ### Telescoping `G_A·σ_a(G_B) = G_{A·B}` and the `N`-wraparound -/

/-- Splitting off the top block: `G_{m+A} = G_m + G_A·Xᵐ`. -/
theorem gsum_add (m A : ℕ) :
    gsum (p := p) (m + A) = gsum m + gsum A * single ((m : ZMod p)) 1 := by
  have h1 : gsum (p := p) (m + A)
      = (∑ k ∈ Finset.range m, single ((k : ZMod p)) (1 : ZMod p))
        + ∑ i ∈ Finset.range A, single (((m + i : ℕ) : ZMod p)) (1 : ZMod p) := by
    rw [gsum, Finset.sum_range_add]
  rw [h1]
  congr 1
  rw [gsum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [single_mul_single, mul_one]
  congr 1
  push_cast; ring

/-- The Galois twist of a geometric sum. -/
theorem sigma_gsum (a : (ZMod p)ˣ) (B : ℕ) :
    sigma a (gsum (p := p) B)
      = ∑ j ∈ Finset.range B, single ((a : ZMod p) * (j : ZMod p)) 1 := by
  rw [gsum, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [sigma_single]

/-- **The telescoping identity** `G_A · σ_a(G_B) = G_{A·B}` in `P` (base-`A` digit
decomposition of `range (A·B)`), with `A = (a:ZMod p).val`. -/
theorem gsum_mul_sigma (a : (ZMod p)ˣ) (B : ℕ) :
    gsum (p := p) ((a : ZMod p).val) * sigma a (gsum B)
      = gsum ((a : ZMod p).val * B) := by
  set A := (a : ZMod p).val with hA
  have hcast : ((A : ℕ) : ZMod p) = (a : ZMod p) := by rw [hA, ZMod.natCast_val, ZMod.cast_id]
  induction B with
  | zero => simp
  | succ B ih =>
      rw [gsum_succ, map_add, mul_add, ih, sigma_single, Nat.mul_succ, gsum_add (A * B) A]
      have hc : ((a : ZMod p)) * (B : ZMod p) = ((A * B : ℕ) : ZMod p) := by
        rw [Nat.cast_mul, hcast]
      rw [hc]

/-- `G_p = N` (the residues `0,…,p−1` enumerate `ℤ/p`). -/
theorem gsum_p : gsum (p := p) p = nelt := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  rw [gsum, ← sum_val_eq_sum_range (p := p) (fun a => single ((a : ZMod p)) (1 : ZMod p)), nelt]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [ZMod.natCast_val, ZMod.cast_id]

/-- Adding a full period `p` adds one copy of `N`. -/
theorem gsum_add_p (n : ℕ) : gsum (p := p) (n + p) = gsum n + nelt := by
  rw [gsum_add n p, gsum_p]
  congr 1
  rw [mul_comm, mul_nelt, eps_single, one_smul]

/-- Adding `q` periods adds `q` copies of `N`. -/
theorem gsum_add_p_mul (n q : ℕ) : gsum (p := p) (n + p * q) = gsum n + q • nelt := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, gsum_add_p, ih, succ_nsmul]
      abel

/-- **The `N`-wraparound**: `G_n = G_{n%p} + ⌊n/p⌋·N`. -/
theorem gsum_wrap (n : ℕ) : gsum (p := p) n = gsum (n % p) + (n / p) • nelt := by
  conv_lhs => rw [← Nat.mod_add_div n p]
  rw [gsum_add_p_mul]

/-! ### Base-2 bridge to the engine's Mirimanoff evaluation `ell_geomUnit` -/

/-- `G_2 = 1 + X = 1 − (−1)·X`, so the base-2 unit is the engine geometric unit `geomUnit (−1)`.
This gives an explicit handle on `ℓ_n(U_2)` via `ell_geomUnit` (a Mirimanoff sum). -/
theorem gsumUnit_two_eq_geomUnit (h2 : ((2 : ℕ) : ZMod p) ≠ 0) (ht : (-1 : ZMod p) ≠ 1) :
    gsumUnit 2 h2 = geomUnit (-1) ht := by
  apply Units.ext
  rw [gsumUnit_val]
  show gsum 2 = 1 - single 1 (-1 : ZMod p)
  have hG : gsum (p := p) 2 = (1 : P p) + single 1 (1 : ZMod p) := by
    rw [gsum_succ, gsum_succ, gsum_zero, zero_add, Nat.cast_one, Nat.cast_zero,
      AddMonoidAlgebra.one_def]
  have hneg : single (1 : ZMod p) (-1 : ZMod p) = - single 1 (1 : ZMod p) :=
    map_neg (Finsupp.singleAddHom (1 : ZMod p)) 1
  rw [hG, hneg]
  ring

/-- **Explicit Mirimanoff value of `ℓ_n` at base 2**: `ℓ_n(U_2) = −2⁻¹·∑_{j<p} jⁿ⁻¹(−1)ʲ`
(for `2 ≤ n`).  Combined with `ell_uu_eq` this pins `(2ⁿ−1)·T_n` to a power sum. -/
theorem ell_gsumUnit_two (n : ℕ) (hn : 2 ≤ n) (h2 : ((2 : ℕ) : ZMod p) ≠ 0)
    (ht : (-1 : ZMod p) ≠ 1) :
    ell n (gsumUnit 2 h2)
      = -(2 : ZMod p)⁻¹ * ∑ j ∈ Finset.range p, ((j : ZMod p)) ^ (n - 1) * (-1) ^ j := by
  rw [gsumUnit_two_eq_geomUnit h2 ht, ell_geomUnit n hn]
  norm_num

/-- **Base-2 case of the linchpin `ℓ_n(U_c) ≡ F_c`** (`F_c = ∑_a (ca)ⁿ⁻¹⌊ca/p⌋`, the engine's
floor sum in `den_mul_sum_floor_modEq`).  Reindexing `j ↦ (2a)%p` turns the Mirimanoff alternating
sum into `−2·F_2` (the constant block `∑(2a)ⁿ⁻¹` vanishes as a power sum), so `ℓ_n(U_2) = F_2`. -/
theorem ell_gsumUnit_two_eq_floor (n : ℕ) (hn : 2 ≤ n) (hp2 : p ≠ 2)
    (hpd : ¬ (p - 1) ∣ (n - 1)) (h2 : ((2 : ℕ) : ZMod p) ≠ 0) (ht : (-1 : ZMod p) ≠ 1) :
    ell n (gsumUnit 2 h2)
      = ((∑ a ∈ Finset.range p, (2 * a) ^ (n - 1) * (2 * a / p) : ℕ) : ZMod p) := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  have hp2div : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hpri.out Nat.prime_two).mp h)
  have h2z : (2 : ZMod p) ≠ 0 := by simpa using h2
  -- the constant block ∑ (2a)ⁿ⁻¹ vanishes (power sum, (p-1)∤(n-1))
  have hsum0 : (∑ a ∈ Finset.range p, ((2 * a : ℕ) : ZMod p) ^ (n - 1)) = 0 := by
    have hfac : (∑ a ∈ Finset.range p, ((2 * a : ℕ) : ZMod p) ^ (n - 1))
        = (2 : ZMod p) ^ (n - 1) * ∑ a ∈ Finset.range p, ((a : ℕ) : ZMod p) ^ (n - 1) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by push_cast; ring
    have hz : (∑ a ∈ Finset.range p, ((a : ℕ) : ZMod p) ^ (n - 1)) = 0 := by
      rw [← sum_val_eq_sum_range (p := p) (fun a => ((a : ℕ) : ZMod p) ^ (n - 1)),
        Finset.sum_congr rfl (fun x _ => by rw [ZMod.natCast_val, ZMod.cast_id])]
      exact sum_pow_zmod_eq_zero (by omega) hpd
    rw [hfac, hz, mul_zero]
  -- the alternating sum equals −2·F₂
  have hA : (∑ j ∈ Finset.range p, ((j : ZMod p)) ^ (n - 1) * (-1) ^ j)
      = -2 * ((∑ a ∈ Finset.range p, (2 * a) ^ (n - 1) * (2 * a / p) : ℕ) : ZMod p) := by
    have hterm : ∀ a ∈ Finset.range p,
        (((2 * a) % p : ℕ) : ZMod p) ^ (n - 1) * (-1 : ZMod p) ^ ((2 * a) % p)
        = ((2 * a : ℕ) : ZMod p) ^ (n - 1)
          + (-2) * (((2 * a : ℕ) : ZMod p) ^ (n - 1) * ((2 * a / p : ℕ) : ZMod p)) := by
      intro a ha
      have halt : a < p := Finset.mem_range.mp ha
      obtain ⟨q, hq⟩ : ∃ q, 2 * a / p = q := ⟨_, rfl⟩
      have hlt : q < 2 := hq ▸ Nat.div_lt_of_lt_mul (by omega)
      have hdm : p * q + (2 * a) % p = 2 * a := by rw [← hq]; exact Nat.div_add_mod (2 * a) p
      rw [hq]
      have h01 : q = 0 ∨ q = 1 := by omega
      rcases h01 with h | h
      · subst h
        have hmod : (2 * a) % p = 2 * a := by omega
        rw [hmod, Even.neg_one_pow ⟨a, by ring⟩]
        push_cast; ring
      · subst h
        have hple : p ≤ 2 * a := by omega
        have hmod : (2 * a) % p = 2 * a - p := by omega
        have hcastsub : (((2 * a - p : ℕ)) : ZMod p) = ((2 * a : ℕ) : ZMod p) := by
          rw [Nat.cast_sub hple, ZMod.natCast_self, sub_zero]
        rw [hmod, hcastsub,
          Odd.neg_one_pow (Nat.Even.sub_odd hple ⟨a, by ring⟩ (hpri.out.odd_of_ne_two hp2))]
        push_cast; ring
    rw [(sum_fn_mod_mul_eq hp2div (fun j => ((j : ZMod p)) ^ (n - 1) * (-1) ^ j)).symm,
      Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hsum0, zero_add, ← Finset.mul_sum]
    congr 1
    push_cast; rfl
  rw [ell_gsumUnit_two n hn h2 ht, hA, ← mul_assoc,
    show -(2 : ZMod p)⁻¹ * (-2) = 1 by field_simp, one_mul]

/-! ### The abstract averaging lemma (1-cocycle ⟹ coboundary over `(ZMod p)ˣ`) -/

/-- **Averaging a 1-cocycle into a coboundary.** If `f(ab) = f(a) + χ(a)·f(b)` for all `a,b`
in the finite group `(ZMod p)ˣ`, then `f(a) = (χ(a)-1)·T` where `T = ∑_b f(b)`.  (No condition
on the twist `χ` is needed; the proof reindexes `b ↦ ab` and uses `|(ZMod p)ˣ| = p-1 ≡ -1`.) -/
theorem cocycle_coboundary (f χ : (ZMod p)ˣ → ZMod p)
    (hcoc : ∀ a b, f (a * b) = f a + χ a * f b) (a : (ZMod p)ˣ) :
    f a = (χ a - 1) * ∑ b, f b := by
  have hbij : ∑ b : (ZMod p)ˣ, f (a * b) = ∑ b : (ZMod p)ˣ, f b :=
    Fintype.sum_equiv (Equiv.mulLeft a) (fun b => f (a * b)) f (fun b => rfl)
  have hexp : ∑ b : (ZMod p)ˣ, f (a * b)
      = (Fintype.card (ZMod p)ˣ : ZMod p) * f a + χ a * ∑ b : (ZMod p)ˣ, f b := by
    rw [Finset.sum_congr rfl (fun b _ => hcoc a b), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, ← Finset.mul_sum, nsmul_eq_mul]
  rw [hbij] at hexp
  have hcard : (Fintype.card (ZMod p)ˣ : ZMod p) = -1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hpri.out]
    have h1 := hpri.out.one_lt
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    rw [ZMod.natCast_self]; ring
  rw [hcard] at hexp
  linear_combination hexp

/-- `θ(G_c) = ∑_{k<c} k·Xᵏ`. -/
theorem theta_gsum (c : ℕ) :
    theta (gsum (p := p) c) = ∑ k ∈ Finset.range c, single ((k : ZMod p)) ((k : ZMod p)) := by
  rw [gsum, ← Function.iterate_one theta, theta_iterate_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [Function.iterate_one, theta_single, mul_one]

/-! ### The cocycle and its coboundary form for `ℓ_n` -/

/-- The cyclotomic-sum unit `U_a := G_{a.val}`, indexed by `a : (ZMod p)ˣ`. -/
noncomputable def uu (a : (ZMod p)ˣ) : (P p)ˣ :=
  gsumUnit ((a : ZMod p).val) (by rw [ZMod.natCast_val, ZMod.cast_id]; exact Units.ne_zero a)

@[simp] theorem uu_val (a : (ZMod p)ˣ) : ((uu a : (P p)ˣ) : P p) = gsum ((a : ZMod p).val) :=
  gsumUnit_val _ _

/-- **The cocycle relation** `ℓ_n(U_{ab}) = ℓ_n(U_a) + aⁿ·ℓ_n(U_b)` — from the telescoping
`U_a·σ_a(U_b) = U_{ab} + c·N`, `ℓ_n`'s `N`-insensitivity, additivity, and `σ_a`-equivariance. -/
theorem ell_uu_mul {n : ℕ} (hn : 2 ≤ n) (h1d : ¬ (p - 1) ∣ (n - 1)) (h2d : ¬ (p - 1) ∣ n)
    (a b : (ZMod p)ˣ) :
    ell n (uu (a * b)) = ell n (uu a) + (a : ZMod p) ^ n * ell n (uu b) := by
  set A := (a : ZMod p).val with hAdef
  set B := (b : ZMod p).val with hBdef
  have hval : ((uu a * sigmaU a (uu b) : (P p)ˣ) : P p)
      = ((uu (a * b) : (P p)ˣ) : P p) + (((A * B / p : ℕ) : ZMod p)) • nelt := by
    rw [Units.val_mul, sigmaU_val, uu_val, uu_val, uu_val, gsum_mul_sigma, gsum_wrap (A * B),
      ← Nat.cast_smul_eq_nsmul (ZMod p)]
    have hmod : ((a * b : (ZMod p)ˣ) : ZMod p).val = A * B % p := by
      rw [Units.val_mul, ZMod.val_mul]
    rw [hmod]
  have hee := ell_eq_of_val_eq_add_smul_N hn h1d h2d (uu (a * b)) (uu a * sigmaU a (uu b))
    (((A * B / p : ℕ) : ZMod p)) hval
  rw [ell_mul, ell_sigmaU n (by omega) a (uu b)] at hee
  exact hee.symm

/-- **The coboundary form** `ℓ_n(U_a) = (aⁿ−1)·T_n`, where `T_n = ∑_b ℓ_n(U_b)` (numerically
`T_n ≡ B_n/n`, Sage-verified).  This is the `F_p[ℤ/p]` analogue of `cyclotomicLogDeriv_coeff`. -/
theorem ell_uu_eq {n : ℕ} (hn : 2 ≤ n) (h1d : ¬ (p - 1) ∣ (n - 1)) (h2d : ¬ (p - 1) ∣ n)
    (a : (ZMod p)ˣ) :
    ell n (uu a) = ((a : ZMod p) ^ n - 1) * ∑ b : (ZMod p)ˣ, ell n (uu b) :=
  cocycle_coboundary (fun a => ell n (uu a)) (fun a => (a : ZMod p) ^ n)
    (ell_uu_mul hn h1d h2d) a

/-- **`p ∤ B_n ⟹ T_n ≠ 0`** (the cocycle constant `T_n = ∑_b ℓ_n(U_b)` is nonzero) whenever
`2ⁿ ≠ 1`.  Combines the base-2 floor identity `ell_gsumUnit_two_eq_floor` with the engine's Kummer
congruence `den_mul_sum_floor_modEq`: `den(B_n)·n·ℓ_n(U_2) ≡ (2ⁿ−1)·num(B_n)`, and
`ℓ_n(U_2) = (2ⁿ−1)·T_n`, so `den(B_n)·n·T_n ≡ num(B_n)`.  (This is the `2ⁿ≠1` half of `T_n ≡ B_n/n`;
the general index needs `ℓ_n(U_c) ≡ F_c` for a primitive-root base.) -/
theorem sum_ell_uu_ne_zero (n : ℕ) (hn : 2 ≤ n) (hub : n ≤ p - 3) (hp2 : p ≠ 2)
    (hpd1 : ¬ (p - 1) ∣ (n - 1)) (hpd : ¬ (p - 1) ∣ n) (h2pow : (2 : ZMod p) ^ n ≠ 1)
    (hB : ¬ (p : ℤ) ∣ (bernoulli n).num) :
    (∑ b : (ZMod p)ˣ, ell n (uu b)) ≠ 0 := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  have hp3 : 3 ≤ p := by have := hpri.out.two_le; omega
  have h2div : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hpri.out Nat.prime_two).mp h)
  have h2z : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := fun h => h2div ((ZMod.natCast_eq_zero_iff 2 p).mp h)
    simpa using h
  have h2nat : ((2 : ℕ) : ZMod p) ≠ 0 := by simpa using h2z
  have ht : (-1 : ZMod p) ≠ 1 := fun h => h2z (by linear_combination -h)
  have hn1 : n - 1 + 1 = n := by omega
  set S : ℕ := ∑ a ∈ Finset.range p, (2 * a) ^ (n - 1) * (2 * a / p) with hSdef
  -- the unit "2", with `U_2 = gsumUnit 2`
  set a2 : (ZMod p)ˣ := (isUnit_iff_ne_zero.mpr h2z).unit with ha2def
  have hval2 : (a2 : ZMod p) = 2 := IsUnit.unit_spec _
  have hvaln : (a2 : ZMod p).val = 2 := by
    rw [hval2, show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by push_cast; ring,
      ZMod.val_natCast_of_lt (by omega)]
  have huu : uu a2 = gsumUnit 2 h2nat := by
    apply Units.ext; rw [uu_val, hvaln, gsumUnit_val]
  -- coboundary + floor identities give `(S : ZMod p) = (2ⁿ−1)·T`
  have hkey : (S : ZMod p) = ((2 : ZMod p) ^ n - 1) * ∑ b : (ZMod p)ˣ, ell n (uu b) := by
    rw [← ell_gsumUnit_two_eq_floor n hn hp2 hpd1 h2nat ht, ← huu,
      ell_uu_eq hn hpd1 hpd a2, hval2]
  -- engine congruence, cast to `ZMod p`
  have hcong := den_mul_sum_floor_modEq (p := p) hp2 (m := n - 1) (by omega) (c := 2) h2div
  rw [hn1, ← hSdef] at hcong
  have hncast : (((n - 1 : ℕ) : ZMod p)) + 1 = (n : ZMod p) := by
    have h : ((n - 1 + 1 : ℕ) : ZMod p) = ((n : ℕ) : ZMod p) := by rw [hn1]
    push_cast at h; exact h
  have hcz : ((bernoulli n).den : ZMod p) * (n : ZMod p) * (S : ZMod p)
      = ((2 : ZMod p) ^ n - 1) * ((bernoulli n).num : ZMod p) := by
    have h := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hcong
    push_cast at h
    rw [hncast] at h
    linear_combination h
  -- conclude
  intro hT0
  rw [hkey, hT0, mul_zero, mul_zero] at hcz
  have hnum : ((bernoulli n).num : ZMod p) = 0 := by
    rcases mul_eq_zero.mp hcz.symm with h | h
    · exact absurd h (sub_ne_zero.mpr h2pow)
    · exact h
  exact hB ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hnum)

/-! ### Explicit closed form for `ℓ_n(U_c)` (any base, no geomUnit restriction) -/

/-- **The explicit inverse** `G_c⁻¹ = σ_c(G_{c'}) − (⌊c·c'/p⌋·c⁻¹)·N`, where `c'=(a⁻¹).val`.
Proven from `G_c·σ_c(G_{c'}) = G_{c·c'} = 1 + ⌊c·c'/p⌋·N`
(`gsum_mul_sigma`+`gsum_wrap`, `c·c'≡1`). -/
theorem uu_inv_val (a : (ZMod p)ˣ) :
    (((uu a)⁻¹ : (P p)ˣ) : P p)
      = sigma a (gsum (((a⁻¹ : (ZMod p)ˣ) : ZMod p).val))
        - (((((a : ZMod p).val * ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val) / p : ℕ) : ZMod p)
            * (a : ZMod p)⁻¹) • nelt := by
  haveI : Fact (1 < p) := ⟨hpri.out.one_lt⟩
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  apply Units.inv_eq_of_mul_eq_one_right
  have hane : (a : ZMod p) ≠ 0 := Units.ne_zero a
  have hepsc : eps (gsum (p := p) ((a : ZMod p).val)) = (a : ZMod p) := by
    rw [eps_gsum, ZMod.natCast_val, ZMod.cast_id]
  have hmod1 : ((a : ZMod p).val * ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val) % p = 1 := by
    rw [← ZMod.val_mul, Units.mul_inv, ZMod.val_one]
  have hG1 : gsum (p := p) 1 = 1 := by
    rw [gsum, Finset.sum_range_one, Nat.cast_zero, ← AddMonoidAlgebra.one_def]
  have hT1 : (uu a : (P p)ˣ).val * sigma a (gsum (((a⁻¹ : (ZMod p)ˣ) : ZMod p).val))
      = 1 + (((((a : ZMod p).val * ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val) / p : ℕ)) : ZMod p)
          • nelt := by
    rw [uu_val, gsum_mul_sigma, gsum_wrap, hmod1, hG1, ← Nat.cast_smul_eq_nsmul (ZMod p)]
  have hT2 : (uu a : (P p)ˣ).val
        * (((((((a : ZMod p).val * ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val) / p : ℕ)) : ZMod p)
            * (a : ZMod p)⁻¹) • nelt)
      = (((((a : ZMod p).val * ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val) / p : ℕ)) : ZMod p) • nelt := by
    rw [mul_smul_comm, uu_val, mul_nelt, hepsc, smul_smul, mul_assoc, inv_mul_cancel₀ hane, mul_one]
  rw [mul_sub, hT1, hT2]
  abel

/-- **The explicit closed form** `ℓ_n(U_a) = ∑_{k<c}∑_{j<c'} (k + a·j)ⁿ⁻¹·k`
(`c=(a).val`, `c'=(a⁻¹).val`), valid for ANY base `a` (Sage-verified; the `2ⁿ≠1` restriction of
the geomUnit route is gone).  Mechanism: `dlog(U_a)=θG_c·σ_a(G_{c'})` up to an `N`-term that dies
under `ε∘θ^{n-1}` (`∑jⁿ⁻¹=0`), then `ε(θ^{n-1}(single A B))=Aⁿ⁻¹·B`.  This is the missing input
for the `2ⁿ=1` indices (e.g. p=17, n=8): with a primitive-root base `cⁿ≠1`. -/
theorem ell_uu_explicit (n : ℕ) (hn : 2 ≤ n) (hpd1 : ¬ (p - 1) ∣ (n - 1)) (a : (ZMod p)ˣ) :
    ell n (uu a)
      = ∑ k ∈ Finset.range ((a : ZMod p).val),
          ∑ j ∈ Finset.range (((a⁻¹ : (ZMod p)ˣ) : ZMod p).val),
            ((k : ZMod p) + (a : ZMod p) * (j : ZMod p)) ^ (n - 1) * (k : ZMod p) := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  -- the `N`-term of `dlog` vanishes under `ε∘θ^{n-1}`
  have hNzero : eps (theta^[n - 1] (nelt : P p)) = 0 := by
    rw [eps_theta_iterate_nelt]; exact sum_pow_zmod_eq_zero (by omega) hpd1
  have hdlog : dlog (uu a)
      = theta (gsum ((a : ZMod p).val)) * sigma a (gsum (((a⁻¹ : (ZMod p)ˣ) : ZMod p).val))
        - ((((((a : ZMod p).val * ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val) / p : ℕ) : ZMod p)
              * (a : ZMod p)⁻¹) * eps (theta (gsum ((a : ZMod p).val)))) • nelt := by
    rw [dlog, uu_val, uu_inv_val, mul_sub, mul_smul_comm, mul_nelt, smul_smul]
  -- so `ℓ_n(U_a) = ε(θ^{n-1}(θG_c·σ_a G_{c'}))`
  have hell : ell n (uu a)
      = eps (theta^[n - 1] (theta (gsum ((a : ZMod p).val))
          * sigma a (gsum (((a⁻¹ : (ZMod p)ˣ) : ZMod p).val)))) := by
    rw [ell, hdlog, sub_eq_add_neg, ← neg_smul, theta_iterate_add, map_add, theta_iterate_smul,
      eps_smul, hNzero, mul_zero, add_zero]
  rw [hell, theta_gsum, sigma_gsum, Finset.sum_mul, theta_iterate_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, theta_iterate_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [single_mul_single, mul_one, theta_iterate_single, eps_single]

/-! ### Single-sum form (toward the Bernoulli evaluation `E_c ≡ (cⁿ−1)·B_n/n`) -/

/-- The base-`c` digit reindexing `range (c·c') ≃ range c ×ˢ range c'`, `m ↦ (m%c, m/c)`. -/
theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (c c' : ℕ) (g : ℕ → M) :
    ∑ m ∈ Finset.range (c * c'), g m
      = ∑ k ∈ Finset.range c, ∑ j ∈ Finset.range c', g (k + c * j) := by
  induction c' with
  | zero => simp
  | succ c' ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_range_succ]
      congr 1
      rw [Nat.add_comm (c * c') k]

/-- **Single-sum form of the closed form**: `ℓ_n(U_a) = ∑_{m<c·c'} mⁿ⁻¹·(m mod c)`. -/
theorem ell_uu_single (n : ℕ) (hn : 2 ≤ n) (hpd1 : ¬ (p - 1) ∣ (n - 1)) (a : (ZMod p)ˣ) :
    ell n (uu a)
      = ∑ m ∈ Finset.range ((a : ZMod p).val * ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val),
          (m : ZMod p) ^ (n - 1) * ((m % (a : ZMod p).val : ℕ) : ZMod p) := by
  rw [ell_uu_explicit n hn hpd1, sum_range_mul_eq ((a : ZMod p).val)
    (((a⁻¹ : (ZMod p)ˣ) : ZMod p).val)
    (fun m => (m : ZMod p) ^ (n - 1) * ((m % (a : ZMod p).val : ℕ) : ZMod p))]
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun j _ => ?_
  have hkc : k < (a : ZMod p).val := Finset.mem_range.mp hk
  have hac : (((a : ZMod p).val : ℕ) : ZMod p) = (a : ZMod p) := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  congr 1
  · push_cast [hac]; ring
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hkc]

/-- `t` full periods of `p` consecutive `k`-th powers sum to zero (`(p−1)∤k`). -/
theorem sum_range_p_mul_pow_eq_zero {k : ℕ} (hk : 1 ≤ k) (hkd : ¬ (p - 1) ∣ k) (t : ℕ) :
    ∑ i ∈ Finset.range (p * t), (i : ZMod p) ^ k = 0 := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, zero_add,
        Finset.sum_congr rfl (fun i _ => by
          rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add] :
          ∀ i ∈ Finset.range p, (((p * t + i : ℕ)) : ZMod p) ^ k = ((i : ℕ) : ZMod p) ^ k),
        ← sum_val_eq_sum_range (p := p) (fun i => ((i : ℕ) : ZMod p) ^ k),
        Finset.sum_congr rfl (fun x _ => by rw [ZMod.natCast_val, ZMod.cast_id])]
      exact sum_pow_zmod_eq_zero hk hkd

/-- `∑_{m < c·c'} mᵏ = 0` (since `c·c' = p·⌊c·c'/p⌋ + 1`: full periods vanish, the lone extra term
`(p·⌊⌋)ᵏ = 0`). -/
theorem sum_range_cc_pow_eq_zero {k : ℕ} (hk : 1 ≤ k) (hkd : ¬ (p - 1) ∣ k) (a : (ZMod p)ˣ) :
    ∑ m ∈ Finset.range ((a : ZMod p).val * ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val),
      (m : ZMod p) ^ k = 0 := by
  haveI : Fact (1 < p) := ⟨hpri.out.one_lt⟩
  have hmod1 : ((a : ZMod p).val * ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val) % p = 1 := by
    rw [← ZMod.val_mul, Units.mul_inv, ZMod.val_one]
  have hsplit : (a : ZMod p).val * ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val
      = p * ((a : ZMod p).val * ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val / p) + 1 := by
    conv_lhs =>
      rw [← Nat.div_add_mod ((a : ZMod p).val * ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val) p, hmod1]
  rw [hsplit, Finset.sum_range_succ, sum_range_p_mul_pow_eq_zero hk hkd, zero_add,
    Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_pow (by omega : k ≠ 0)]

/-- **Floor form** `ℓ_n(U_a) = −a·∑_{m<c·c'} mⁿ⁻¹·⌊m/c⌋` (Gemini step 1: `m mod c = m − c⌊m/c⌋`
and `∑ mⁿ = 0`).  The remaining E′ step is `∑_{m<cc'} mⁿ⁻¹⌊m/c⌋ ≡ −(cⁿ−1)Bₙ/(n·a)` via the
Bernoulli-polynomial closed form (`cyclotomicLogDeriv_coeff`). -/
theorem ell_uu_floor (n : ℕ) (hn : 2 ≤ n) (hpd1 : ¬ (p - 1) ∣ (n - 1)) (hpd : ¬ (p - 1) ∣ n)
    (a : (ZMod p)ˣ) :
    ell n (uu a)
      = -(a : ZMod p) * ∑ m ∈ Finset.range ((a : ZMod p).val * ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val),
          (m : ZMod p) ^ (n - 1) * ((m / (a : ZMod p).val : ℕ) : ZMod p) := by
  rw [ell_uu_single n hn hpd1]
  have hac : (((a : ZMod p).val : ℕ) : ZMod p) = (a : ZMod p) := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hterm : ∀ m ∈ Finset.range ((a : ZMod p).val * ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val),
      (m : ZMod p) ^ (n - 1) * ((m % (a : ZMod p).val : ℕ) : ZMod p)
      = (m : ZMod p) ^ n
        - (a : ZMod p) * ((m : ZMod p) ^ (n - 1) * ((m / (a : ZMod p).val : ℕ) : ZMod p)) := by
    intro m _
    have hc : (m : ZMod p)
        = (a : ZMod p) * ((m / (a : ZMod p).val : ℕ) : ZMod p)
          + ((m % (a : ZMod p).val : ℕ) : ZMod p) := by
      have h := congrArg (Nat.cast (R := ZMod p)) (Nat.div_add_mod m (a : ZMod p).val)
      push_cast [hac] at h
      exact h.symm
    have hmodcast : ((m % (a : ZMod p).val : ℕ) : ZMod p)
        = (m : ZMod p) - (a : ZMod p) * ((m / (a : ZMod p).val : ℕ) : ZMod p) := by
      rw [hc]; ring
    rw [hmodcast, show (m : ZMod p) ^ n = (m : ZMod p) ^ (n - 1) * (m : ZMod p) from by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, sum_range_cc_pow_eq_zero (by omega) hpd,
    zero_sub, ← Finset.mul_sum, neg_mul]

/-! ### Step (2a): Bernoulli-polynomial closed form (over ℚ) -/

/-- **Telescoping** `∑_{k<c} (y+k)ⁿ⁻¹ = (Bₙ(y+c) − Bₙ(y))/n` over ℚ, from Mathlib's
`Polynomial.bernoulli_eval_one_add` (`Bₙ(1+x) = Bₙ(x) + n·xⁿ⁻¹`).  Core of E′ step (2a). -/
theorem bernoulli_inner_sum (n : ℕ) (hn : 1 ≤ n) (y : ℚ) (c : ℕ) :
    ∑ k ∈ Finset.range c, (y + (k : ℚ)) ^ (n - 1)
      = ((Polynomial.bernoulli n).eval (y + (c : ℚ))
          - (Polynomial.bernoulli n).eval y) / (n : ℚ) := by
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hkey : ∀ k ∈ Finset.range c, (y + (k : ℚ)) ^ (n - 1)
      = ((Polynomial.bernoulli n).eval (y + ((k : ℚ) + 1))
          - (Polynomial.bernoulli n).eval (y + (k : ℚ))) / (n : ℚ) := by
    intro k _
    have h := Polynomial.bernoulli_eval_one_add n (y + (k : ℚ))
    rw [show (1 : ℚ) + (y + (k : ℚ)) = y + ((k : ℚ) + 1) from by ring] at h
    rw [h]; field_simp; ring
  rw [Finset.sum_congr rfl hkey, ← Finset.sum_div]
  congr 1
  have hts := Finset.sum_range_sub (fun i => (Polynomial.bernoulli n).eval (y + (i : ℚ))) c
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one] at hts
  exact hts

/-- **Abel summation**: `∑_{j<c'} j·(X_{j+1}−X_j) = c'·X_{c'} − ∑_{j≤c'} X_j + X_0`. -/
theorem abel_sum_telescope (X : ℕ → ℚ) (c' : ℕ) :
    ∑ j ∈ Finset.range c', (j : ℚ) * (X (j + 1) - X j)
      = (c' : ℚ) * X c' - ∑ j ∈ Finset.range (c' + 1), X j + X 0 := by
  induction c' with
  | zero => simp
  | succ c' ih =>
      rw [Finset.sum_range_succ, ih]
      conv_rhs => rw [Finset.sum_range_succ]
      push_cast; ring

/-- **E′ step (2a): the ℚ closed form** for the weighted floor sum. -/
theorem floorsum_closed (n : ℕ) (hn : 1 ≤ n) (c c' : ℕ) (hc : 0 < c) :
    ∑ m ∈ Finset.range (c * c'), (m : ℚ) ^ (n - 1) * ((m / c : ℕ) : ℚ)
      = ((c' : ℚ) * (Polynomial.bernoulli n).eval ((c * c' : ℕ) : ℚ)
          + (Polynomial.bernoulli n).eval 0
          - ∑ j ∈ Finset.range (c' + 1), (Polynomial.bernoulli n).eval ((c * j : ℕ) : ℚ)) / n := by
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  rw [sum_range_mul_eq c c' (fun m => (m : ℚ) ^ (n - 1) * ((m / c : ℕ) : ℚ))]
  -- reduce inner term: (k+c*j)/c = j, and swap to ∑_j j·∑_k (cj+k)^{n-1}
  have hstep : ∀ k ∈ Finset.range c, ∀ j ∈ Finset.range c',
      ((k + c * j : ℕ) : ℚ) ^ (n - 1) * (((k + c * j) / c : ℕ) : ℚ)
        = (j : ℚ) * (((c * j : ℕ) : ℚ) + (k : ℚ)) ^ (n - 1) := by
    intro k hk j _
    have hkc : k < c := Finset.mem_range.mp hk
    rw [Nat.add_mul_div_left k j hc, Nat.div_eq_of_lt hkc, Nat.zero_add]
    push_cast; ring
  rw [Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (hstep k hk)), Finset.sum_comm]
  -- inner sum via telescoping
  have hinner : ∀ j ∈ Finset.range c',
      ∑ k ∈ Finset.range c, (j : ℚ) * (((c * j : ℕ) : ℚ) + (k : ℚ)) ^ (n - 1)
        = (j : ℚ) * (((Polynomial.bernoulli n).eval ((c * (j + 1) : ℕ) : ℚ)
            - (Polynomial.bernoulli n).eval ((c * j : ℕ) : ℚ)) / (n : ℚ)) := by
    intro j _
    rw [← Finset.mul_sum, bernoulli_inner_sum n hn ((c * j : ℕ) : ℚ) c]
    congr 3
    push_cast; ring_nf
  rw [Finset.sum_congr rfl hinner]
  -- pull out 1/n and Abel-sum
  rw [Finset.sum_congr rfl (fun j _ => by
    rw [mul_div_assoc'] :
    ∀ j ∈ Finset.range c', (j : ℚ) * (((Polynomial.bernoulli n).eval ((c * (j + 1) : ℕ) : ℚ)
        - (Polynomial.bernoulli n).eval ((c * j : ℕ) : ℚ)) / (n : ℚ))
      = ((j : ℚ) * ((Polynomial.bernoulli n).eval ((c * (j + 1) : ℕ) : ℚ)
          - (Polynomial.bernoulli n).eval ((c * j : ℕ) : ℚ))) / (n : ℚ)),
    ← Finset.sum_div,
    abel_sum_telescope (fun j => (Polynomial.bernoulli n).eval ((c * j : ℕ) : ℚ)) c']
  simp only [Nat.mul_zero, Nat.cast_zero]
  ring

/-! ### Step (2b): the EGF identity (toward `∑_{j≤c'} Bₙ(cj) ≡ cⁿ⁻¹Bₙ+Bₙ mod p`) -/

open PowerSeries in
/-- **Summed Bernoulli-polynomial generating function**: `(∑_j B(cj,X))·(eˣ−1) = X·∑_j e^{cjX}`,
from Mathlib `Polynomial.bernoulli_generating_function`. -/
theorem sum_bernoulli_gen (c c' : ℕ) :
    (∑ j ∈ Finset.range (c' + 1),
        (mk fun n => Polynomial.aeval ((c * j : ℕ) : ℚ)
          ((1 / (Nat.factorial n) : ℚ) • Polynomial.bernoulli n)))
      * (exp ℚ - 1)
      = X * ∑ j ∈ Finset.range (c' + 1), rescale ((c * j : ℕ) : ℚ) (exp ℚ) := by
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ =>
    Polynomial.bernoulli_generating_function ((c * j : ℕ) : ℚ)

open PowerSeries in
/-- The geometric sum `(∑_{j≤c'} e^{cjX})·(e^{cX}−1) = e^{c(c'+1)X} − 1` in `ℚ⟦X⟧`. -/
theorem sum_rescale_exp_geom (c c' : ℕ) :
    (∑ j ∈ Finset.range (c' + 1), rescale ((c * j : ℕ) : ℚ) (exp ℚ)) * (rescale (c : ℚ) (exp ℚ) - 1)
      = rescale ((c : ℚ) * ((c' + 1 : ℕ) : ℚ)) (exp ℚ) - 1 := by
  have hr : ∀ j, rescale ((c * j : ℕ) : ℚ) (exp ℚ) = (rescale (c : ℚ) (exp ℚ)) ^ j := by
    intro j
    rw [← map_pow, exp_pow_eq_rescale_exp, rescale_rescale, Nat.cast_mul, mul_comm (c : ℚ) (j : ℚ)]
  rw [Finset.sum_congr rfl (fun j _ => hr j), geom_sum_mul, ← map_pow,
    exp_pow_eq_rescale_exp, rescale_rescale, Nat.cast_add, Nat.cast_one,
    mul_comm ((c' : ℚ) + 1) (c : ℚ)]

/-! ### Inverse-free extraction `∑_{j≤c'} Bₙ(cj) = (1+cⁿ⁻¹)Bₙ + (p-divisible)` -/

open PowerSeries in
/-- The summed Bernoulli EGF `BB = ∑_{j≤c'} B(cj,X)/n!`. -/
noncomputable def bgen (c c' : ℕ) : PowerSeries ℚ :=
  ∑ j ∈ Finset.range (c' + 1),
    (mk fun n => Polynomial.aeval ((c * j : ℕ) : ℚ)
      ((1 / (Nat.factorial n) : ℚ) • Polynomial.bernoulli n))

open PowerSeries in
/-- The summed rescaled exponentials `Sc = ∑_{j≤c'} e^{cjX}`. -/
noncomputable def sexp (c c' : ℕ) : PowerSeries ℚ :=
  ∑ j ∈ Finset.range (c' + 1), rescale ((c * j : ℕ) : ℚ) (exp ℚ)

open PowerSeries in
/-- The cyclotomic log-derivative EGF `clog = eˣ·B = X + B`. -/
noncomputable def clog : PowerSeries ℚ := exp ℚ * bernoulliPowerSeries ℚ

open PowerSeries in
theorem clog_eq : clog = X + bernoulliPowerSeries ℚ := by
  have h := bernoulliPowerSeries_mul_exp_sub_one (A := ℚ)
  rw [clog, show exp ℚ * bernoulliPowerSeries ℚ
      = bernoulliPowerSeries ℚ * (exp ℚ - 1) + bernoulliPowerSeries ℚ by ring, h]

open PowerSeries in
theorem coeff_clog {n : ℕ} (hn : 2 ≤ n) :
    PowerSeries.coeff n clog = (bernoulli n : ℚ) / (Nat.factorial n : ℚ) := by
  rw [clog_eq, map_add, coeff_X, if_neg (by omega : n ≠ 1), zero_add]
  simp [bernoulliPowerSeries]

open PowerSeries in
theorem exp_sub_one_ne_zero : (exp ℚ - 1) ≠ (0 : PowerSeries ℚ) := by
  intro h
  have := congrArg (PowerSeries.coeff 1) h
  simp [PowerSeries.coeff_exp, map_sub] at this

open PowerSeries in
theorem bgen_mul (c c' : ℕ) : bgen c c' * (exp ℚ - 1) = X * sexp c c' := by
  rw [bgen, sexp]; exact sum_bernoulli_gen c c'

open PowerSeries in
theorem sexp_geom (c c' : ℕ) :
    sexp c c' * (rescale (c : ℚ) (exp ℚ) - 1)
      = rescale ((c : ℚ) * ((c' + 1 : ℕ) : ℚ)) (exp ℚ) - 1 := by
  rw [sexp]; exact sum_rescale_exp_geom c c'

open PowerSeries in
/-- **(i) Cancellation**: `BB = B · Sc` (cancel `eˣ−1`). -/
theorem bgen_eq (c c' : ℕ) : bgen c c' = bernoulliPowerSeries ℚ * sexp c c' := by
  apply mul_right_cancel₀ exp_sub_one_ne_zero
  rw [bgen_mul, mul_right_comm, bernoulliPowerSeries_mul_exp_sub_one]

open PowerSeries in
/-- **(ii) KEY2**: `(BB−B)·(e^{cX}−1) = B·e^{cX}·(e^{cc'X}−1)`. -/
theorem bgen_key2 (c c' : ℕ) :
    (bgen c c' - bernoulliPowerSeries ℚ) * (rescale (c : ℚ) (exp ℚ) - 1)
      = bernoulliPowerSeries ℚ * rescale (c : ℚ) (exp ℚ)
        * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - 1) := by
  -- (BB - B) = B·(Sc - 1)
  have h1 : bgen c c' - bernoulliPowerSeries ℚ = bernoulliPowerSeries ℚ * (sexp c c' - 1) := by
    rw [mul_sub, mul_one, ← bgen_eq]
  -- (Sc - 1)·(e^{cX}-1) = e^{cX}·(e^{cc'X}-1)
  have hd : (c : ℚ) * ((c' + 1 : ℕ) : ℚ) = (c : ℚ) * (c' : ℚ) + (c : ℚ) := by push_cast; ring
  have h2 : (sexp c c' - 1) * (rescale (c : ℚ) (exp ℚ) - 1)
      = rescale (c : ℚ) (exp ℚ) * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - 1) := by
    rw [sub_mul, one_mul, sexp_geom, hd, ← exp_mul_exp_eq_exp_add]
    ring
  rw [h1, mul_assoc, h2, ← mul_assoc]

open PowerSeries in
/-- **(iii) kernel**: `B·(e^{cc'X}−1) = X + B·R`, `R = e^{cc'X}−eˣ`. -/
theorem bgen_kernel (c c' : ℕ) :
    bernoulliPowerSeries ℚ * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - 1)
      = X + bernoulliPowerSeries ℚ * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - exp ℚ) := by
  have h := bernoulliPowerSeries_mul_exp_sub_one (A := ℚ)
  rw [mul_sub, mul_sub, mul_one]
  rw [show bernoulliPowerSeries ℚ * (exp ℚ) = X + bernoulliPowerSeries ℚ by
    rw [show bernoulliPowerSeries ℚ * exp ℚ
      = bernoulliPowerSeries ℚ * (exp ℚ - 1) + bernoulliPowerSeries ℚ by ring, h]]
  ring

open PowerSeries in
/-- **(iv) TARGET** (inverse-free): `C(c)·(BB−B)·X = rescale c clog·(X +
B·R)`, `R = e^{cc'X}−eˣ`. -/
theorem bgen_target (c c' : ℕ) (hc : (c : ℚ) ≠ 0) :
    C (c : ℚ) * (bgen c c' - bernoulliPowerSeries ℚ) * X
      = rescale (c : ℚ) clog
        * (X + bernoulliPowerSeries ℚ * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - exp ℚ)) := by
  have hkey3 : (bgen c c' - bernoulliPowerSeries ℚ) * (rescale (c : ℚ) (exp ℚ) - 1)
      = rescale (c : ℚ) (exp ℚ)
        * (X + bernoulliPowerSeries ℚ * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - exp ℚ)) := by
    rw [bgen_key2]
    rw [show bernoulliPowerSeries ℚ * rescale (c : ℚ) (exp ℚ)
            * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - 1)
          = rescale (c : ℚ) (exp ℚ)
            * (bernoulliPowerSeries ℚ * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - 1)) from by ring,
        bgen_kernel]
  have hne : (rescale (c : ℚ) (exp ℚ) - 1) ≠ 0 := by
    intro h
    have hh := congrArg (PowerSeries.coeff 1) h
    simp [coeff_rescale, coeff_exp, map_sub, hc] at hh
  have hrc : rescale (c : ℚ) clog * (rescale (c : ℚ) (exp ℚ) - 1)
      = C (c : ℚ) * X * rescale (c : ℚ) (exp ℚ) := by
    have h1 : (rescale (c : ℚ) (exp ℚ) - 1) = rescale (c : ℚ) (exp ℚ - 1) := by
      rw [map_sub, map_one]
    rw [clog, map_mul, h1, mul_assoc, ← map_mul,
      bernoulliPowerSeries_mul_exp_sub_one, rescale_X]
    ring
  apply mul_right_cancel₀ hne
  calc C (c : ℚ) * (bgen c c' - bernoulliPowerSeries ℚ) * X * (rescale (c : ℚ) (exp ℚ) - 1)
      = C (c : ℚ) * X * ((bgen c c' - bernoulliPowerSeries ℚ) * (rescale (c : ℚ) (exp ℚ) - 1)) := by
        ring
    _ = C (c : ℚ) * X * (rescale (c : ℚ) (exp ℚ)
          * (X + bernoulliPowerSeries ℚ * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - exp ℚ))) := by
        rw [hkey3]
    _ = (C (c : ℚ) * X * rescale (c : ℚ) (exp ℚ))
          * (X + bernoulliPowerSeries ℚ * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - exp ℚ)) := by ring
    _ = (rescale (c : ℚ) clog * (rescale (c : ℚ) (exp ℚ) - 1))
          * (X + bernoulliPowerSeries ℚ * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - exp ℚ)) := by
        rw [hrc]
    _ = rescale (c : ℚ) clog
          * (X + bernoulliPowerSeries ℚ * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - exp ℚ))
          * (rescale (c : ℚ) (exp ℚ) - 1) := by ring

open PowerSeries in
/-- **Coefficient extraction**: `c·[Xⁿ]BB = (c+cⁿ)·Bₙ/n! + correction`, the correction a single
power-series coefficient that is `p`-divisible (since `R = e^{cc'X}−eˣ ≡ 0 mod p`). -/
theorem bgen_coeff_extract (c c' : ℕ) (hc : (c : ℚ) ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    (c : ℚ) * PowerSeries.coeff n (bgen c c')
      = ((c : ℚ) + (c : ℚ) ^ n) * (bernoulli n / (Nat.factorial n : ℚ))
        + PowerSeries.coeff (n + 1) (rescale (c : ℚ) clog
            * (bernoulliPowerSeries ℚ * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - exp ℚ))) := by
  have ht := congrArg (PowerSeries.coeff (n + 1)) (bgen_target c c' hc)
  have hB : PowerSeries.coeff n (bernoulliPowerSeries ℚ) = bernoulli n / (Nat.factorial n : ℚ) := by
    rw [bernoulliPowerSeries, coeff_mk]; simp
  simp only [mul_add, map_add, coeff_succ_mul_X, coeff_C_mul, map_sub, coeff_rescale] at ht
  rw [hB] at ht
  simp only [coeff_clog hn] at ht
  linear_combination ht

open PowerSeries in
/-- **(step 1) Coefficient bridge**: `[Xⁿ]BB = (∑_{j≤c'} Bₙ(cj))/n!`. -/
theorem coeff_bgen (c c' n : ℕ) :
    PowerSeries.coeff n (bgen c c')
      = (∑ j ∈ Finset.range (c' + 1), (Polynomial.bernoulli n).eval ((c * j : ℕ) : ℚ))
        / (Nat.factorial n : ℚ) := by
  rw [bgen, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_mk, map_smul, smul_eq_mul, Polynomial.coe_aeval_eq_eval]
  ring

/-- **(step 4, per term)** `Bₙ(N) = Bₙ + n·∑_{l<N} lⁿ⁻¹`. -/
theorem bernoulli_eval_split {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    (Polynomial.bernoulli n).eval ((N : ℕ) : ℚ)
      = bernoulli n + (n : ℚ) * ∑ l ∈ Finset.range N, (l : ℚ) ^ (n - 1) := by
  have h := bernoulli_inner_sum n hn 0 N
  simp only [zero_add, Polynomial.bernoulli_eval_zero] at h
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  rw [eq_div_iff hn0] at h
  linear_combination -h

/-- **(step 4)** `∑_{j≤c'} Bₙ(cj) = (c'+1)·Bₙ + n·PSum`, `PSum = ∑_{j≤c'} ∑_{l<cj} lⁿ⁻¹`. -/
theorem bsum_psum {n : ℕ} (hn : 1 ≤ n) (c c' : ℕ) :
    ∑ j ∈ Finset.range (c' + 1), (Polynomial.bernoulli n).eval ((c * j : ℕ) : ℚ)
      = ((c' + 1 : ℕ) : ℚ) * bernoulli n
        + (n : ℚ) * ∑ j ∈ Finset.range (c' + 1), ∑ l ∈ Finset.range (c * j), (l : ℚ) ^ (n - 1) := by
  rw [Finset.sum_congr rfl (fun j _ => bernoulli_eval_split hn (c * j)), Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, ← Finset.mul_sum, nsmul_eq_mul]

open PowerSeries in
/-- **(steps 1+2+4 combined) master ℚ identity**: `c·n·PSum = (cⁿ − c·c')·Bₙ + n!·Corr`. -/
theorem master_Q (c c' : ℕ) (hc : (c : ℚ) ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    (c : ℚ) * (n : ℚ)
        * (∑ j ∈ Finset.range (c' + 1), ∑ l ∈ Finset.range (c * j), (l : ℚ) ^ (n - 1))
      = ((c : ℚ) ^ n - (c : ℚ) * (c' : ℚ)) * bernoulli n
        + (Nat.factorial n : ℚ) * PowerSeries.coeff (n + 1) (rescale (c : ℚ) clog
            * (bernoulliPowerSeries ℚ * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - exp ℚ))) := by
  have hnf : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  have h3 := bgen_coeff_extract c c' hc hn
  rw [coeff_bgen, bsum_psum (show 1 ≤ n by omega)] at h3
  field_simp at h3
  push_cast at h3 ⊢
  linear_combination h3

/-- **(step 5) floor identity over ℚ**: `Sfloor = c'·P(cc') − PSum`. -/
theorem floor_id_Q (c c' : ℕ) (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    ∑ m ∈ Finset.range (c * c'), (m : ℚ) ^ (n - 1) * ((m / c : ℕ) : ℚ)
      = (c' : ℚ) * ∑ l ∈ Finset.range (c * c'), (l : ℚ) ^ (n - 1)
        - ∑ j ∈ Finset.range (c' + 1), ∑ l ∈ Finset.range (c * j), (l : ℚ) ^ (n - 1) := by
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  rw [floorsum_closed n hn c c' hc, bernoulli_eval_split hn (c * c'),
    Polynomial.bernoulli_eval_zero,
    bsum_psum hn c c']
  push_cast
  field_simp
  ring

/-! ### (step 3) `p`-integrality of the correction coefficient -/

open PowerSeries in
theorem pint_coeff_bern (hp2 : p ≠ 2) {k : ℕ} (hk : k ≤ p - 2) :
    PInt p (PowerSeries.coeff k (bernoulliPowerSeries ℚ)) := by
  have he : PowerSeries.coeff k (bernoulliPowerSeries ℚ) = bernoulli k / (Nat.factorial k : ℚ) := by
    rw [bernoulliPowerSeries, coeff_mk]; simp
  rw [he]
  have hkfac : ¬ p ∣ Nat.factorial k := by
    have h2 := hpri.out.two_le
    rw [Nat.Prime.dvd_factorial hpri.out]; omega
  refine PInt.div_nat ?_ hkfac
  rcases eq_or_ne k 0 with rfl | hk0
  · simpa [bernoulli_zero] using PInt.one (p := p)
  · exact not_dvd_den_bernoulli hp2 (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) (by
      have h2 := hpri.out.two_le; omega))

open PowerSeries in
theorem pint_coeff_clog (hp2 : p ≠ 2) {k : ℕ} (hk : k ≤ p - 2) :
    PInt p (PowerSeries.coeff k clog) := by
  rw [clog_eq, map_add, coeff_X]
  refine PInt.add ?_ (pint_coeff_bern hp2 hk)
  rcases eq_or_ne k 1 with h | h
  · rw [if_pos h]; exact PInt.one
  · rw [if_neg h]; simpa using PInt.intCast (p := p) 0

open PowerSeries in
theorem pint_coeff_A (hp2 : p ≠ 2) (c : ℕ) {i : ℕ} (hi : i ≤ p - 2) :
    PInt p (PowerSeries.coeff i (rescale (c : ℚ) clog * bernoulliPowerSeries ℚ)) := by
  rw [PowerSeries.coeff_mul]
  refine PInt.sum _ _ fun x hx => ?_
  have hx2 : x.2 ≤ i := by have := Finset.mem_antidiagonal.mp hx; omega
  have hx1 : x.1 ≤ i := by have := Finset.mem_antidiagonal.mp hx; omega
  rw [coeff_rescale]
  exact (((PInt.natCast c).pow x.1).mul (pint_coeff_clog hp2 (by omega))).mul
    (pint_coeff_bern hp2 (by omega))

open PowerSeries in
/-- **(step 3) `Corr = p·S` with `S` `p`-integral** (since `cc' ≡ 1 (p)` makes `R = e^{cc'X}−eˣ`
have all coefficients `p`-divisible). -/
theorem corr_p_dvd (hp2 : p ≠ 2) (c c' : ℕ) {n : ℕ} (hn2 : 2 ≤ n) (hub : n ≤ p - 3)
    (hcc : (c * c') % p = 1) :
    ∃ S : ℚ, PInt p S ∧
      PowerSeries.coeff (n + 1) (rescale (c : ℚ) clog
          * (bernoulliPowerSeries ℚ * (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - exp ℚ)))
        = (p : ℚ) * S := by
  have hcc1 : ((c * c' : ℕ) : ℚ) = (c : ℚ) * (c' : ℚ) := by push_cast; ring
  have hcc0 : 0 < c * c' := Nat.pos_of_ne_zero (by rintro h; rw [h] at hcc; simp at hcc)
  have hmod : (c * c') ≡ 1 [MOD p] := by
    unfold Nat.ModEq; rw [hcc, Nat.one_mod_eq_one.mpr hpri.out.ne_one]
  have hdvd : ∀ j : ℕ, p ∣ (c * c') ^ j - 1 := by
    intro j
    have h1 := Nat.ModEq.pow j hmod
    rw [one_pow] at h1
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow j (c * c') hcc0)).mp h1.symm
  have hcoeffR : ∀ j : ℕ, PowerSeries.coeff j (rescale ((c : ℚ) * (c' : ℚ)) (exp ℚ) - exp ℚ)
      = (p : ℚ) * (((((c * c') ^ j - 1) / p : ℕ) : ℚ) / (Nat.factorial j : ℚ)) := by
    intro j
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpri.out.ne_zero
    have hcc1' : 1 ≤ (c * c') ^ j := Nat.one_le_pow j (c * c') hcc0
    have he : (((c * c') ^ j - 1) / p : ℕ) * p = (c * c') ^ j - 1 := Nat.div_mul_cancel (hdvd j)
    have hkey : (((c * c') ^ j : ℕ) : ℚ) - 1 = (p : ℚ) * ((((c * c') ^ j - 1) / p : ℕ) : ℚ) := by
      rw [show (p : ℚ) * ((((c * c') ^ j - 1) / p : ℕ) : ℚ)
          = ((((c * c') ^ j - 1) / p * p : ℕ) : ℚ) by push_cast; ring, he, Nat.cast_sub hcc1']
      push_cast; ring
    rw [map_sub, coeff_rescale]
    simp only [coeff_exp, Algebra.algebraMap_self_apply]
    have hkey2 : ((c : ℚ) * (c' : ℚ)) ^ j - 1 = (p : ℚ) * ((((c * c') ^ j - 1) / p : ℕ) : ℚ) := by
      rw [show ((c : ℚ) * (c' : ℚ)) ^ j = (((c * c') ^ j : ℕ) : ℚ) by push_cast; ring]; exact hkey
    rw [mul_one_div, div_sub_div_same, hkey2, mul_div_assoc]
  rw [← mul_assoc, PowerSeries.coeff_mul]
  refine ⟨∑ x ∈ Finset.antidiagonal (n + 1),
      PowerSeries.coeff x.1 (rescale (c : ℚ) clog * bernoulliPowerSeries ℚ)
        * (((((c * c') ^ x.2 - 1) / p : ℕ) : ℚ) / (Nat.factorial x.2 : ℚ)), ?_, ?_⟩
  · refine PInt.sum _ _ fun x hx => ?_
    have h2 := hpri.out.two_le
    have hx1 : x.1 ≤ n + 1 := by have := Finset.mem_antidiagonal.mp hx; omega
    have hx2 : x.2 ≤ n + 1 := by have := Finset.mem_antidiagonal.mp hx; omega
    refine (pint_coeff_A hp2 c (by omega : x.1 ≤ p - 2)).mul ((PInt.natCast _).div_nat ?_)
    rw [Nat.Prime.dvd_factorial hpri.out]; omega
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [hcoeffR x.2]; ring

/-- If an integer `N` equals `p·x` with `x` `p`-integral, then `p ∣ N`. -/
theorem pint_p_dvd {N : ℤ} {x : ℚ} (h : (N : ℚ) = (p : ℚ) * x) (hx : PInt p x) : (p : ℤ) ∣ N := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpri.out.ne_zero
  have hxN : x = (N : ℚ) / (p : ℚ) := by rw [h, mul_comm, mul_div_assoc, div_self hp0, mul_one]
  have hden : x.den ∣ p := by
    have hx2 : x = ((N : ℚ)) / (((p : ℕ) : ℤ) : ℚ) := by rw [hxN]; push_cast; ring
    calc x.den ∣ (N : ℚ).den * (((((p : ℕ) : ℤ) : ℚ))⁻¹).den := by
          rw [hx2, div_eq_mul_inv]; exact Rat.mul_den_dvd _ _
      _ ∣ p := by
          rw [Rat.den_intCast, one_mul,
            show ((((p : ℕ) : ℤ)) : ℚ) = ((p : ℕ) : ℚ) by push_cast; ring,
            Rat.inv_natCast_den_of_pos hpri.out.pos]
  have hcop : Nat.Coprime x.den p := Nat.coprime_comm.mp (hpri.out.coprime_iff_not_dvd.mpr hx)
  have hden1 : x.den = 1 := Nat.Coprime.eq_one_of_dvd hcop hden
  obtain ⟨z, hz⟩ : ∃ z : ℤ, x = z := ⟨x.num, ((Rat.den_eq_one_iff x).mp hden1).symm⟩
  refine ⟨z, ?_⟩
  have : (N : ℚ) = ((p : ℤ) * z : ℤ) := by rw [h, hz]; push_cast; ring
  exact_mod_cast this

end KummerLog

/-! ## Step C — the Kummer log-derivative functional on `(𝓞 K)ˣ` and the bridge to `uu` -/

open KummerLog NumberField NumberField.IsCMField Finset

namespace StepC

variable {p : ℕ} [hpri : Fact p.Prime]
variable {K : Type*} [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}

omit [NumberField K] [IsCMField K] in
/-- A unit of `𝓞 K` is not in the prime ideal `(ζ-1)`, so it has a `piRed`-lift. -/
theorem coe_unit_notMem (hζ : IsPrimitiveRoot ζ p) (u : (𝓞 K)ˣ) :
    ((u : (𝓞 K)ˣ) : 𝓞 K) ∉ Ideal.span ({(↑hζ.unit' - 1 : 𝓞 K)} : Set (𝓞 K)) :=
  fun hmem => (hζ.isPrime_one_sub_zeta).ne_top (Ideal.eq_top_of_isUnit_mem _ hmem u.isUnit)

/-- A chosen `piRed`-lift of a unit `u`. -/
noncomputable def ellLift (hζ : IsPrimitiveRoot ζ p) (u : (𝓞 K)ˣ) : (P p)ˣ :=
  Classical.choose (exists_unit_lift hζ (coe_unit_notMem hζ u))

omit [IsCMField K] in
theorem ellLift_spec (hζ : IsPrimitiveRoot ζ p) (u : (𝓞 K)ˣ) :
    piRed hζ ((ellLift hζ u : P p)) = Ideal.Quotient.mk _ ((u : (𝓞 K)ˣ) : 𝓞 K) :=
  Classical.choose_spec (exists_unit_lift hζ (coe_unit_notMem hζ u))

/-- **The Kummer log-derivative functional** `ellU n u`, defined by lifting `u` through `piRed`. -/
noncomputable def ellU (hζ : IsPrimitiveRoot ζ p) (n : ℕ) (u : (𝓞 K)ˣ) : ZMod p :=
  ell n (ellLift hζ u)

variable (hζ : IsPrimitiveRoot ζ p) {n : ℕ}

omit [IsCMField K] in
/-- `ellU n u = ell n γ` for any `piRed`-lift `γ` of `u`. -/
theorem ellU_eq_of_lift (hn : 2 ≤ n) (h1 : ¬ (p - 1) ∣ (n - 1)) (h2 : ¬ (p - 1) ∣ n)
    (u : (𝓞 K)ˣ) {γ : (P p)ˣ}
    (hγ : piRed hζ ((γ : P p)) = Ideal.Quotient.mk _ ((u : (𝓞 K)ˣ) : 𝓞 K)) :
    ellU hζ n u = ell n γ :=
  ell_eq_of_piRed_eq hζ hn h1 h2 ((ellLift_spec hζ u).trans hγ.symm)

theorem ell_one_eq_zero (hn : 2 ≤ n) : ell n (1 : (P p)ˣ) = 0 := by
  have h1 : (1 : (P p)ˣ) = singleUnit (0 : ZMod p) (1 : ZMod p) one_ne_zero :=
    Units.ext (by rw [Units.val_one]; show (1 : P p) = single 0 1; rw [AddMonoidAlgebra.one_def])
  rw [h1, ell_singleUnit n hn]

omit [IsCMField K] in
theorem ellU_one (hn : 2 ≤ n) (h1 : ¬ (p - 1) ∣ (n - 1)) (h2 : ¬ (p - 1) ∣ n) :
    ellU hζ n (1 : (𝓞 K)ˣ) = 0 := by
  rw [ellU_eq_of_lift hζ hn h1 h2 (1 : (𝓞 K)ˣ) (γ := 1)
    (by rw [Units.val_one, map_one, Units.val_one, map_one]), ell_one_eq_zero hn]

omit [IsCMField K] in
theorem ellU_mul (hn : 2 ≤ n) (h1 : ¬ (p - 1) ∣ (n - 1)) (h2 : ¬ (p - 1) ∣ n) (u v : (𝓞 K)ˣ) :
    ellU hζ n (u * v) = ellU hζ n u + ellU hζ n v := by
  have hlift : piRed hζ (((ellLift hζ u * ellLift hζ v : (P p)ˣ) : P p))
      = Ideal.Quotient.mk _ (((u * v : (𝓞 K)ˣ)) : 𝓞 K) := by
    rw [Units.val_mul, map_mul, ellLift_spec, ellLift_spec, Units.val_mul, map_mul]
  rw [ellU_eq_of_lift hζ hn h1 h2 (u * v) hlift, ell_mul]; rfl

omit [IsCMField K] in
theorem ellU_pow (hn : 2 ≤ n) (h1 : ¬ (p - 1) ∣ (n - 1)) (h2 : ¬ (p - 1) ∣ n)
    (u : (𝓞 K)ˣ) (m : ℕ) : ellU hζ n (u ^ m) = (m : ZMod p) * ellU hζ n u := by
  induction m with
  | zero => rw [pow_zero, ellU_one hζ hn h1 h2, Nat.cast_zero, zero_mul]
  | succ k ih => rw [pow_succ, ellU_mul hζ hn h1 h2, ih, Nat.cast_succ]; ring

omit [IsCMField K] in
theorem ellU_prod (hn : 2 ≤ n) (h1 : ¬ (p - 1) ∣ (n - 1)) (h2 : ¬ (p - 1) ∣ n)
    {ι : Type*} (s : Finset ι) (f : ι → (𝓞 K)ˣ) :
    ellU hζ n (∏ a ∈ s, f a) = ∑ a ∈ s, ellU hζ n (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, ellU_one hζ hn h1 h2]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ellU_mul hζ hn h1 h2, ih]

/-! ### The zeta-power and `gsum` reductions under `piRed` -/

omit [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/-- `mk(ζ^e) = ζ̄^{(e mod p).val}` for any integer exponent `e`. -/
theorem mk_zetaUnit_zpow (e : ℤ) :
    Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) ((zetaUnit hζ ^ e : (𝓞 K)ˣ) : 𝓞 K)
      = (zetaBar hζ) ^ (((e : ZMod p)).val) := by
  set v := ((e : ZMod p)).val with hv
  have hek : ((e - (v : ℤ) : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [hv, ZMod.natCast_val, ZMod.cast_id, sub_self]
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (e - (v : ℤ)) p).mp hek
  have he : e = (v : ℤ) + (p : ℤ) * k := by linarith [hk]
  have hp1 : (zetaUnit hζ) ^ ((p : ℤ) * k) = 1 := by
    rw [zpow_mul, zpow_natCast, zetaUnit_pow_eq_one, one_zpow]
  have hzpow : (zetaUnit hζ ^ e : (𝓞 K)ˣ) = zetaUnit hζ ^ v := by
    rw [he, zpow_add, hp1, mul_one, zpow_natCast]
  have hz : ((zetaUnit hζ : (𝓞 K)ˣ) : 𝓞 K) = hζ.toInteger := by rw [zetaUnit, IsUnit.unit_spec]
  rw [hzpow, Units.val_pow_eq_pow_val, hz, map_pow]
  rfl

-- `CharZero K` is genuinely required here (it feeds `NumberField K` instance resolution), so `omit`
-- rejects it; `unusedSectionVars` flags it as a false positive, suppressed
-- for this one declaration.
-- `IsCMField K` is truly unused and is dropped via `omit`.
set_option linter.unusedSectionVars false in
omit [IsCMField K] in
theorem piRed_gsum (m : ℕ) (hm : m ≤ p) :
    piRed hζ (gsum m) = ∑ j ∈ Finset.range m, (zetaBar hζ) ^ j := by
  rw [gsum, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [piRed_single, one_smul]
  congr 1
  exact ZMod.val_natCast_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hj) hm)

/-! ### The bridge `ellU n (ξ_a) = ℓ_n(U_a)` -/

omit [IsCMField K] in
/-- **The key bridge**: the log-derivative functional `ellU n` of the real cyclotomic unit `ξ_a`
equals the cocycle value `ℓ_n(U_a)` (the `ζ^{(1-a)/2}` factor is `ℓ_n`-invisible). -/
theorem ellU_realCyclotomicUnit (hn : 2 ≤ n) (h1 : ¬ (p - 1) ∣ (n - 1)) (h2 : ¬ (p - 1) ∣ n)
    (a : ℕ) (ha : a.Coprime p) (halt : a < p) :
    ellU hζ n (realCyclotomicUnit hζ a ha) = ell n (uu (ZMod.unitOfCoprime a ha)) := by
  set e : ℤ := (1 - (a : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ) with he
  set ā : (ZMod p)ˣ := ZMod.unitOfCoprime a ha with hā
  have hāval : (ā : ZMod p).val = a := by
    rw [hā, ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt halt]
  -- RHS of `piRed` of the lift
  have hRHS : Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})
        ((realCyclotomicUnit hζ a ha : (𝓞 K)ˣ) : 𝓞 K)
      = (zetaBar hζ) ^ ((e : ZMod p)).val * ∑ j ∈ Finset.range a, (zetaBar hζ) ^ j := by
    rw [realCyclotomicUnit, Units.val_mul, map_mul, ← he, mk_zetaUnit_zpow hζ e]
    congr 1
    rw [coe_cyclotomicUnit, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_pow]; rfl
  -- the lift `γ := single (e) 1 · U_a`
  have hlift : piRed hζ
        (((singleUnit ((e : ZMod p)) (1 : ZMod p) one_ne_zero * uu ā : (P p)ˣ) : P p))
      = Ideal.Quotient.mk _ ((realCyclotomicUnit hζ a ha : (𝓞 K)ˣ) : 𝓞 K) := by
    rw [Units.val_mul, map_mul,
      show ((singleUnit ((e : ZMod p)) (1 : ZMod p) one_ne_zero : (P p)ˣ) : P p)
        = single (e : ZMod p) 1 from rfl,
      piRed_single, one_smul, uu_val, hāval, piRed_gsum hζ a (le_of_lt halt), hRHS]
  rw [ellU_eq_of_lift hζ hn h1 h2 _ hlift, ell_mul,
    show ((singleUnit ((e : ZMod p)) (1 : ZMod p) one_ne_zero : (P p)ˣ))
      = singleUnit (e : ZMod p) 1 one_ne_zero from rfl,
    ell_singleUnit n hn, zero_add]

/-! ### General `T_n ≠ 0` (Bernoulli-polynomial closed form) and step C -/

/-- **`p ∤ num B_n ⟹ T_n ≠ 0` for ALL even `n ∈ [2,p-3]`** (drops the `2ⁿ≠1` restriction of
`KummerLog.sum_ell_uu_ne_zero`).  PROVEN (sorry-free).

ROUTE.  Take `a` a primitive root mod `p`, `c = a.val`,
`c' = a⁻¹.val` (so `c·c' = p·t+1`, `cⁿ ≠ 1`).  Write `PSum = ∑_{j≤c'} ∑_{l<cj} lⁿ⁻¹` (a `ℕ`).

1. **Coefficient bridge**: `coeff n (bgen c c') = bsum / n!` where `bsum = ∑_{j≤c'} Bₙ(cj)`
   (from `bgen` def; `aeval = eval`, the `1/n!` scalar).
2. **Extraction** (`bgen_coeff_extract`, PROVEN): `c·bsum = (c+cⁿ)Bₙ + n!·Corr`, where
   `Corr = coeff (n+1) (rescale c clog · (B·R))`, `R = e^{cc'X} − eˣ`.
3. **`Corr` is `p`-divisible**: `coeff l R = ((cc')ˡ − 1)/l! = p·(p-integral)` since `cc' ≡ 1 (p)`
   and `l! ` is a `p`-unit (`l ≤ n+1 ≤ p-2`); `coeff k (rescale c clog · B)` is `p`-integral
   (von Staudt: `Bᵢ/i!` `p`-integral for `i ≤ p-2`).  So `Corr = p·s`, `s` `p`-integral
   (use the `PInt` framework from `HerbrandBernoulli` + `PowerSeries.coeff_mul`).
4. **`n·PSum = bsum − (c'+1)Bₙ`** (from `Bₙ(cj) = Bₙ + n·∑_{l<cj}lⁿ⁻¹`, i.e. `bernoulli_inner_sum`
   with `y=0`, summed).  Combine with 2: `c·n·PSum = (cⁿ − cc')Bₙ + n!·Corr`.  Times `den(Bₙ)`:
   `c·n·den·PSum = (cⁿ − cc')·num + den·n!·Corr`, an INTEGER identity with `den·n!·Corr ≡ 0 (p)`
   (step 3).  Reduce mod `p` (`cc' ≡ 1`): `c·n·den·PSum ≡ (cⁿ − 1)·num (mod p)`.
5. **Floor identity** `Sfloor = c'·P(cc') − PSum` over `ℤ` (`P(cc')=∑_{l<cc'}lⁿ⁻¹`; counting
   `⌊m/c⌋ = #{j≥1 : cj≤m}` + reindex; or `floorsum_closed` + step 4's `Bₙ(N)=Bₙ+nP(N)`).
   With `(P(cc') : ZMod p) = 0` (`sum_range_cc_pow_eq_zero`): `(Sfloor : ZMod p) = −(PSum)`.
6. **Assemble**: `ell n (uu a) = −c·Sfloor` (`ell_uu_floor`), so `n·den·ell n (uu a) = (cⁿ−1)·num`
   in `ZMod p` (steps 4,5).  And `ell n (uu a) = (cⁿ−1)·T_n` (`ell_uu_eq`).  As `cⁿ ≠ 1`:
   `n·den·T_n = num ≠ 0` (`p∤num`, `p∤den` von Staudt, `p∤n`), so `T_n ≠ 0`. -/
theorem sum_ell_uu_ne_zero_general (n : ℕ) (hn : 2 ≤ n) (hub : n ≤ p - 3) (hp2 : p ≠ 2)
    (hpd1 : ¬ (p - 1) ∣ (n - 1)) (hpd : ¬ (p - 1) ∣ n) (hB : ¬ (p : ℤ) ∣ (bernoulli n).num) :
    (∑ b : (ZMod p)ˣ, ell n (uu b)) ≠ 0 := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  have hp3 : 3 ≤ p := by have := hpri.out.two_le; omega
  -- primitive root g, with g^n ≠ 1
  obtain ⟨g, hg⟩ := exists_primRoot_pow_inj (p := p)
  set c := (g : ZMod p).val with hc
  set c' := ((g⁻¹ : (ZMod p)ˣ) : ZMod p).val with hc'
  have hc0 : 0 < c := Nat.pos_of_ne_zero fun h =>
    Units.ne_zero g (by rw [hc, ZMod.val_eq_zero] at h; exact h)
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hcZ : ((c : ℕ) : ZMod p) = (g : ZMod p) := by rw [hc, ZMod.natCast_val, ZMod.cast_id]
  have hc'Z : ((c' : ℕ) : ZMod p) = ((g⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    rw [hc', ZMod.natCast_val, ZMod.cast_id]
  have hcc1 : (g : ZMod p) * ((g⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := Units.mul_inv g
  have hccZ : ((c : ℕ) : ZMod p) * ((c' : ℕ) : ZMod p) = 1 := by rw [hcZ, hc'Z, hcc1]
  have hcn1 : ((c : ℕ) : ZMod p) ^ n ≠ 1 := by
    rw [hcZ]; intro h
    have h0 : (g : ZMod p) ^ n = (g : ZMod p) ^ 0 := by rw [h, pow_zero]
    exact absurd (hg n 0 (by omega) (by omega) h0) (by omega)
  have hccmod : c * c' % p = 1 := by
    have h : ((c * c' : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [Nat.cast_mul, hccZ, Nat.cast_one]
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
    rwa [Nat.ModEq, Nat.one_mod_eq_one.mpr hpri.out.ne_one] at h2
  -- abbreviations
  set num := (bernoulli n).num with hnumdef
  set den := (bernoulli n).den with hdendef
  have hdenbern : (den : ℚ) * bernoulli n = (num : ℚ) := Rat.den_mul_eq_num _
  -- Fact A: master congruence mod p
  obtain ⟨Sps, hSps_pint, hSps⟩ := corr_p_dvd hp2 c c' hn hub hccmod
  have hmaster := master_Q c c' hcQ hn
  rw [hSps] at hmaster
  have hQ : (c : ℚ) * (n : ℚ)
        * (∑ j ∈ Finset.range (c' + 1), ∑ l ∈ Finset.range (c * j), (l : ℚ) ^ (n - 1)) * (den : ℚ)
        - ((c : ℚ) ^ n - (c : ℚ) * (c' : ℚ)) * (num : ℚ)
      = (p : ℚ) * ((Nat.factorial n : ℚ) * (den : ℚ) * Sps) := by
    linear_combination (den : ℚ) * hmaster
      + ((c : ℚ) ^ n - (c : ℚ) * (c' : ℚ)) * hdenbern
  set N : ℤ := (c * n * (∑ j ∈ Finset.range (c' + 1), ∑ l ∈ Finset.range (c * j), l ^ (n - 1))
      * den : ℕ) - (((c ^ n : ℕ) : ℤ) - ((c * c' : ℕ) : ℤ)) * num with hNdef
  have hNcast : (N : ℚ) = (p : ℚ) * ((Nat.factorial n : ℚ) * (den : ℚ) * Sps) := by
    rw [hNdef]; push_cast; linear_combination hQ
  have hpN : (p : ℤ) ∣ N :=
    pint_p_dvd hNcast (((PInt.natCast _).mul (PInt.natCast _)).mul hSps_pint)
  have hNz : (N : ZMod p) = 0 := by rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hpN
  have hFactA : ((c : ℕ) : ZMod p) * (n : ZMod p) * (den : ZMod p)
        * (∑ j ∈ Finset.range (c' + 1), ∑ l ∈ Finset.range (c * j), ((l : ZMod p) ^ (n - 1)))
      = (((c : ℕ) : ZMod p) ^ n - 1) * (num : ZMod p) := by
    have h := hNz
    rw [hNdef] at h
    push_cast at h
    rw [hccZ] at h
    linear_combination h
  -- Fact B: floor identity mod p
  have hPccZ : (∑ l ∈ Finset.range (c * c'), (l : ZMod p) ^ (n - 1)) = 0 := by
    have h := sum_range_cc_pow_eq_zero (p := p) (show 1 ≤ n - 1 by omega) hpd1 g
    rwa [← hc, ← hc'] at h
  have hFloorℕ : (∑ m ∈ Finset.range (c * c'), m ^ (n - 1) * (m / c))
        + (∑ j ∈ Finset.range (c' + 1), ∑ l ∈ Finset.range (c * j), l ^ (n - 1))
      = c' * (∑ l ∈ Finset.range (c * c'), l ^ (n - 1)) := by
    have hQfl := floor_id_Q c c' hc0 (show 1 ≤ n by omega)
    have hh : ((∑ m ∈ Finset.range (c * c'), m ^ (n - 1) * (m / c) : ℕ) : ℚ)
          + ((∑ j ∈ Finset.range (c' + 1), ∑ l ∈ Finset.range (c * j), l ^ (n - 1) : ℕ) : ℚ)
        = ((c' : ℕ) : ℚ) * ((∑ l ∈ Finset.range (c * c'), l ^ (n - 1) : ℕ) : ℚ) := by
      push_cast; linear_combination hQfl
    exact_mod_cast hh
  have hFactB : (∑ m ∈ Finset.range (c * c'), (m : ZMod p) ^ (n - 1) * ((m / c : ℕ) : ZMod p))
      = - (∑ j ∈ Finset.range (c' + 1), ∑ l ∈ Finset.range (c * j), (l : ZMod p) ^ (n - 1)) := by
    have h2 := congrArg (fun z : ℕ => (z : ZMod p)) hFloorℕ
    simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] at h2
    rw [hPccZ, mul_zero] at h2
    linear_combination h2
  -- E1: n·den·ℓ(U_g) = (cⁿ−1)·num  in ZMod p
  have hE1 : (n : ZMod p) * (den : ZMod p) * ell n (uu g)
      = (((c : ℕ) : ZMod p) ^ n - 1) * (num : ZMod p) := by
    rw [ell_uu_floor n hn hpd1 hpd g, ← hc, ← hc', hFactB, ← hcZ]
    linear_combination hFactA
  -- conclude
  intro hT0
  rw [ell_uu_eq hn hpd1 hpd g, hT0, mul_zero, mul_zero] at hE1
  have hnum0 : ((num : ℤ) : ZMod p) = 0 := by
    rcases mul_eq_zero.mp hE1.symm with h | h
    · exact absurd h (sub_ne_zero.mpr hcn1)
    · exact h
  exact hB ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hnum0)

/-- **Step C.** A Bernoulli non-divisibility
forces the `k`-th cyclotomic-unit eigenvector to be nonzero. -/
theorem eigenFamily_ne_zero_of_not_dvd_bernoulli (hp : p ≠ 2)
    (k : Fin ((p - 3) / 2)) (hB : ¬ (p : ℤ) ∣ (bernoulli (2 * (k.1 + 1))).num) :
    eigenFamily hζ hp k ≠ 0 := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  set i := 2 * (k.1 + 1) with hidef
  have hp3 : 3 ≤ p := by have := hpri.out.two_le; omega
  have hk2 : k.1 < (p - 3) / 2 := k.2
  have hd2 : 2 * ((p - 3) / 2) ≤ p - 3 := by have := Nat.div_mul_le_self (p - 3) 2; omega
  have hile : i ≤ p - 3 := by omega
  have h2i : 2 ≤ i := by omega
  have hieven : Even i := ⟨k.1 + 1, by omega⟩
  have hi1 : ¬ (p - 1) ∣ (i - 1) := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hi2 : ¬ (p - 1) ∣ i := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hpm1even : Even (p - 1) := by
    obtain ⟨k, hk⟩ := hpri.out.odd_of_ne_two hp; exact ⟨k, by omega⟩
  -- T_i ≠ 0
  have hT : (∑ b : (ZMod p)ˣ, ell i (uu b)) ≠ 0 :=
    sum_ell_uu_ne_zero_general i h2i hile hp hi1 hi2 hB
  -- assume eigenFamily k = 0; derive E_i = w^p
  intro hzero
  rw [eigenFamily] at hzero
  obtain ⟨w, hw⟩ := (vOf_eq_zero_iff _).mp hzero
  have hEp : (eigenCyclotomicUnit hζ i : (𝓞 K)ˣ) = ((w : (𝓞 K)ˣ)) ^ p := by
    have h := congrArg (fun x : ↥(realUnits K) => (x : (𝓞 K)ˣ)) hw
    simpa only [SubmonoidClass.coe_pow] using h
  -- ellU of a p-th power is 0
  have h0 : ellU hζ i (eigenCyclotomicUnit hζ i) = 0 := by
    rw [hEp, ellU_pow hζ h2i hi1 hi2, ZMod.natCast_self, zero_mul]
  -- and ellU(E_i) = factor · T_i
  have hval : ellU hζ i (eigenCyclotomicUnit hζ i)
      = (∑ a ∈ (Icc 1 ((p - 1) / 2)).attach,
          ((a.1 : ZMod p)) ^ (p - 1 - i) * (((a.1 : ZMod p)) ^ i - 1))
        * (∑ b : (ZMod p)ˣ, ell i (uu b)) := by
    rw [eigenCyclotomicUnit, ellU_prod hζ h2i hi1 hi2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    have halt : a.1 < p := by have := (mem_Icc.mp a.2).2; omega
    rw [ellU_pow hζ h2i hi1 hi2,
      ellU_realCyclotomicUnit hζ h2i hi1 hi2 a.1 (coprime_of_mem_Icc a.2) halt,
      ell_uu_eq h2i hi1 hi2, ZMod.coe_unitOfCoprime]
    push_cast
    ring
  -- the power-sum factor equals (p-1)/2 ≠ 0
  have hfactor : (∑ a ∈ (Icc 1 ((p - 1) / 2)).attach,
        ((a.1 : ZMod p)) ^ (p - 1 - i) * (((a.1 : ZMod p)) ^ i - 1))
      = (((p - 1) / 2 : ℕ) : ZMod p) := by
    have hterm : ∀ a ∈ (Icc 1 ((p - 1) / 2)).attach,
        ((a.1 : ZMod p)) ^ (p - 1 - i) * (((a.1 : ZMod p)) ^ i - 1)
        = (a.1 : ZMod p) ^ (p - 1) - (a.1 : ZMod p) ^ (p - 1 - i) := by
      intro a _
      rw [mul_sub, mul_one, ← pow_add]
      congr 2
      omega
    have hone : ∀ a ∈ Icc 1 ((p - 1) / 2), (a : ZMod p) ^ (p - 1) = 1 := by
      intro a ha
      have hco : a.Coprime p := coprime_of_mem_Icc ha
      have hane : (a : ZMod p) ≠ 0 := fun h0 =>
        (hpri.out.coprime_iff_not_dvd.mp hco.symm) ((ZMod.natCast_eq_zero_iff a p).mp h0)
      exact ZMod.pow_card_sub_one_eq_one hane
    have hzero2 : (∑ a ∈ (Icc 1 ((p - 1) / 2)).attach, (a.1 : ZMod p) ^ (p - 1 - i)) = 0 := by
      rw [Finset.sum_attach (Icc 1 ((p - 1) / 2)) (fun a => (a : ZMod p) ^ (p - 1 - i))]
      exact half_sum_pow_eq_zero p hp (p - 1 - i) (by omega) (by omega)
        ((Nat.even_sub (by omega)).mpr (iff_of_true hpm1even hieven))
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hzero2, sub_zero,
      Finset.sum_attach (Icc 1 ((p - 1) / 2)) (fun a => (a : ZMod p) ^ (p - 1)),
      Finset.sum_congr rfl hone, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, mul_one]
  rw [hval, hfactor] at h0
  rcases mul_eq_zero.mp h0 with hf | hT0
  · refine absurd hf (fun hf0 => ?_)
    have hdvd : p ∣ (p - 1) / 2 := (ZMod.natCast_eq_zero_iff ((p - 1) / 2) p).mp hf0
    exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  · exact hT hT0

end StepC

end RegPrimes
