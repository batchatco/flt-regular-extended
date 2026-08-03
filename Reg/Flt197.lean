import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `197`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_197 : Fact (Nat.Prime 197) := ⟨by norm_num⟩

/-- FLT for the regular prime 197, kernel-`decide`d (no `native_decide`). -/
theorem flt_197 : FermatLastTheoremFor 197 := flt_of_regCheck 197 (by norm_num) (by decide)

end RegPrimes
