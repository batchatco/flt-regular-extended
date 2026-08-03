import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `179`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_179 : Fact (Nat.Prime 179) := ⟨by norm_num⟩

/-- FLT for the regular prime 179, kernel-`decide`d (no `native_decide`). -/
theorem flt_179 : FermatLastTheoremFor 179 := flt_of_regCheck 179 (by norm_num) (by decide)

end RegPrimes
