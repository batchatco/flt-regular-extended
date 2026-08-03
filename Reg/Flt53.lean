import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `53`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_53 : Fact (Nat.Prime 53) := ⟨by norm_num⟩

/-- FLT for the regular prime 53, kernel-`decide`d (no `native_decide`). -/
theorem flt_53 : FermatLastTheoremFor 53 := flt_of_regCheck 53 (by norm_num) (by decide)

end RegPrimes
