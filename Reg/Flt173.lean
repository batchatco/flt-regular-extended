import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `173`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_173 : Fact (Nat.Prime 173) := ⟨by norm_num⟩

/-- FLT for the regular prime 173, kernel-`decide`d (no `native_decide`). -/
theorem flt_173 : FermatLastTheoremFor 173 := flt_of_regCheck 173 (by norm_num) (by decide)

end RegPrimes
