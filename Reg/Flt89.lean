import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `89`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_89 : Fact (Nat.Prime 89) := ⟨by norm_num⟩

/-- FLT for the regular prime 89, kernel-`decide`d (no `native_decide`). -/
theorem flt_89 : FermatLastTheoremFor 89 := flt_of_regCheck 89 (by norm_num) (by decide)

end RegPrimes
