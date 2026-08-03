import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `167`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_167 : Fact (Nat.Prime 167) := ⟨by norm_num⟩

/-- FLT for the regular prime 167, kernel-`decide`d (no `native_decide`). -/
theorem flt_167 : FermatLastTheoremFor 167 := flt_of_regCheck 167 (by norm_num) (by decide)

end RegPrimes
