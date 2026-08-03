import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `107`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_107 : Fact (Nat.Prime 107) := ⟨by norm_num⟩

/-- FLT for the regular prime 107, kernel-`decide`d (no `native_decide`). -/
theorem flt_107 : FermatLastTheoremFor 107 := flt_of_regCheck 107 (by norm_num) (by decide)

end RegPrimes
