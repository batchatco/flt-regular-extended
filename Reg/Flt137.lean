import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `137`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_137 : Fact (Nat.Prime 137) := ⟨by norm_num⟩

/-- FLT for the regular prime 137, kernel-`decide`d (no `native_decide`). -/
theorem flt_137 : FermatLastTheoremFor 137 := flt_of_regCheck 137 (by norm_num) (by decide)

end RegPrimes
