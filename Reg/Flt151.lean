import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `151`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_151 : Fact (Nat.Prime 151) := ⟨by norm_num⟩

/-- FLT for the regular prime 151, kernel-`decide`d (no `native_decide`). -/
theorem flt_151 : FermatLastTheoremFor 151 := flt_of_regCheck 151 (by norm_num) (by decide)

end RegPrimes
