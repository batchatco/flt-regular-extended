import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `181`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_181 : Fact (Nat.Prime 181) := ⟨by norm_num⟩

/-- FLT for the regular prime 181, kernel-`decide`d (no `native_decide`). -/
theorem flt_181 : FermatLastTheoremFor 181 := flt_of_regCheck 181 (by norm_num) (by decide)

end RegPrimes
