import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `43`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_43 : Fact (Nat.Prime 43) := ⟨by norm_num⟩

/-- FLT for the regular prime 43, kernel-`decide`d (no `native_decide`). -/
theorem flt_43 : FermatLastTheoremFor 43 := flt_of_regCheck 43 (by norm_num) (by decide)

end RegPrimes
