import CyclotomicNT.IrrCertNat
import FltOfBernoulli

/-!
Native_decide-free FLT for REGULAR primes, generically.

A regular prime has an empty irregular-index list, so `irrListCert q [] = true`
(checked in the kernel via the pure-`Nat` `bModN` recurrence, reusing the `Irr37`
bridge), which gives `∀ i, ¬ IsIrregularIndex q i` and feeds the generic regular-prime
route `FltOfBernoulli.fermatLastTheoremFor_of_bernoulli`. One kernel `decide` per prime.
-/

open CyclotomicNT.QiCert

namespace RegPrimes

/-- **FLT for a regular prime**, `native_decide`-free: the only prime-specific input is the
kernel-`decide`able empty-irregular-list check `irrListCertN q (bModN q (q-3)) [] = true`. -/
theorem flt_of_regCheck (q : ℕ) [Fact q.Prime] (hq5 : 5 ≤ q)
    (hreg : IrrCertNat.irrListCertN q (FaithSpike.bModN q (q - 3)) [] = true) :
    FermatLastTheoremFor q := by
  have hirr : irrListCert q [] = true := IrrCertNat.irrListCert_of_certN hq5 hreg
  have hni : ∀ i, ¬ IsIrregularIndex q i := by
    intro i hi
    have hmem := (irregularIndices_of_cert hirr i).mpr hi
    simp at hmem
  refine FltOfBernoulli.fermatLastTheoremFor_of_bernoulli q (by omega) ?_
  intro k hdvd
  refine hni (2 * (k.1 + 1)) ⟨⟨k.1 + 1, by ring⟩, by omega, ?_, hdvd⟩
  have := k.2; omega

end RegPrimes
