import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `73`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_73 : Fact (Nat.Prime 73) := ⟨by norm_num⟩

/-- FLT for the regular prime 73, kernel-`decide`d (no `native_decide`). -/
theorem flt_73 : FermatLastTheoremFor 73 := flt_of_regCheck 73 (by norm_num) (by decide)

end RegPrimes
