import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `223`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_223 : Fact (Nat.Prime 223) := ⟨by norm_num⟩

/-- FLT for the regular prime 223, kernel-`decide`d (no `native_decide`). -/
theorem flt_223 : FermatLastTheoremFor 223 := flt_of_regCheck 223 (by norm_num) (by decide)

end RegPrimes
