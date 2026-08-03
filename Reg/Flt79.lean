import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `79`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_79 : Fact (Nat.Prime 79) := ⟨by norm_num⟩

/-- FLT for the regular prime 79, kernel-`decide`d (no `native_decide`). -/
theorem flt_79 : FermatLastTheoremFor 79 := flt_of_regCheck 79 (by norm_num) (by decide)

end RegPrimes
