import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `31`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_31 : Fact (Nat.Prime 31) := ⟨by norm_num⟩

/-- FLT for the regular prime 31, kernel-`decide`d (no `native_decide`). -/
theorem flt_31 : FermatLastTheoremFor 31 := flt_of_regCheck 31 (by norm_num) (by decide)

end RegPrimes
