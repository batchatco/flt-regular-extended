import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `193`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_193 : Fact (Nat.Prime 193) := ⟨by norm_num⟩

/-- FLT for the regular prime 193, kernel-`decide`d (no `native_decide`). -/
theorem flt_193 : FermatLastTheoremFor 193 := flt_of_regCheck 193 (by norm_num) (by decide)

end RegPrimes
