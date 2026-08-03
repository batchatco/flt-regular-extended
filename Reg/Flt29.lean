import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `29`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_29 : Fact (Nat.Prime 29) := ⟨by norm_num⟩

/-- FLT for the regular prime 29, kernel-`decide`d (no `native_decide`). -/
theorem flt_29 : FermatLastTheoremFor 29 := flt_of_regCheck 29 (by norm_num) (by decide)

end RegPrimes
