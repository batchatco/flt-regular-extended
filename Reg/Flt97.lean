import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `97`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- FLT for the regular prime 97, kernel-`decide`d (no `native_decide`). -/
theorem flt_97 : FermatLastTheoremFor 97 := flt_of_regCheck 97 (by norm_num) (by decide)

end RegPrimes
