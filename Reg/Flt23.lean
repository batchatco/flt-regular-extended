import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `23`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_23 : Fact (Nat.Prime 23) := ⟨by norm_num⟩

/-- FLT for the regular prime 23, kernel-`decide`d (no `native_decide`). -/
theorem flt_23 : FermatLastTheoremFor 23 := flt_of_regCheck 23 (by norm_num) (by decide)

end RegPrimes
