import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `61`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_61 : Fact (Nat.Prime 61) := ⟨by norm_num⟩

/-- FLT for the regular prime 61, kernel-`decide`d (no `native_decide`). -/
theorem flt_61 : FermatLastTheoremFor 61 := flt_of_regCheck 61 (by norm_num) (by decide)

end RegPrimes
