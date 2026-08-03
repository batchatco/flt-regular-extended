import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `17`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- FLT for the regular prime 17, kernel-`decide`d (no `native_decide`). -/
theorem flt_17 : FermatLastTheoremFor 17 := flt_of_regCheck 17 (by norm_num) (by decide)

end RegPrimes
