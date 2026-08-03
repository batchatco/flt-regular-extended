import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `41`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_41 : Fact (Nat.Prime 41) := ⟨by norm_num⟩

/-- FLT for the regular prime 41, kernel-`decide`d (no `native_decide`). -/
theorem flt_41 : FermatLastTheoremFor 41 := flt_of_regCheck 41 (by norm_num) (by decide)

end RegPrimes
