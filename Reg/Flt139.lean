import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `139`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_139 : Fact (Nat.Prime 139) := ⟨by norm_num⟩

/-- FLT for the regular prime 139, kernel-`decide`d (no `native_decide`). -/
theorem flt_139 : FermatLastTheoremFor 139 := flt_of_regCheck 139 (by norm_num) (by decide)

end RegPrimes
