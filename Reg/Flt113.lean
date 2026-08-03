import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `113`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_113 : Fact (Nat.Prime 113) := ⟨by norm_num⟩

/-- FLT for the regular prime 113, kernel-`decide`d (no `native_decide`). -/
theorem flt_113 : FermatLastTheoremFor 113 := flt_of_regCheck 113 (by norm_num) (by decide)

end RegPrimes
