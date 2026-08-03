import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `109`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_109 : Fact (Nat.Prime 109) := ⟨by norm_num⟩

/-- FLT for the regular prime 109, kernel-`decide`d (no `native_decide`). -/
theorem flt_109 : FermatLastTheoremFor 109 := flt_of_regCheck 109 (by norm_num) (by decide)

end RegPrimes
