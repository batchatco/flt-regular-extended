import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `19`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_19 : Fact (Nat.Prime 19) := ⟨by norm_num⟩

/-- FLT for the regular prime 19, kernel-`decide`d (no `native_decide`). -/
theorem flt_19 : FermatLastTheoremFor 19 := flt_of_regCheck 19 (by norm_num) (by decide)

end RegPrimes
