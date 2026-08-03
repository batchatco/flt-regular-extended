import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `127`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_127 : Fact (Nat.Prime 127) := ⟨by norm_num⟩

/-- FLT for the regular prime 127, kernel-`decide`d (no `native_decide`). -/
theorem flt_127 : FermatLastTheoremFor 127 := flt_of_regCheck 127 (by norm_num) (by decide)

end RegPrimes
