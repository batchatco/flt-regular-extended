import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `211`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_211 : Fact (Nat.Prime 211) := ⟨by norm_num⟩

/-- FLT for the regular prime 211, kernel-`decide`d (no `native_decide`). -/
theorem flt_211 : FermatLastTheoremFor 211 := flt_of_regCheck 211 (by norm_num) (by decide)

end RegPrimes
