import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `199`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_199 : Fact (Nat.Prime 199) := ⟨by norm_num⟩

/-- FLT for the regular prime 199, kernel-`decide`d (no `native_decide`). -/
theorem flt_199 : FermatLastTheoremFor 199 := flt_of_regCheck 199 (by norm_num) (by decide)

end RegPrimes
