import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `71`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_71 : Fact (Nat.Prime 71) := ⟨by norm_num⟩

/-- FLT for the regular prime 71, kernel-`decide`d (no `native_decide`). -/
theorem flt_71 : FermatLastTheoremFor 71 := flt_of_regCheck 71 (by norm_num) (by decide)

end RegPrimes
