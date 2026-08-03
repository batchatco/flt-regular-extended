import RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-! # Fermat's Last Theorem for the regular prime `47`, kernel-checked. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RegPrimes

instance factP_47 : Fact (Nat.Prime 47) := ⟨by norm_num⟩

/-- FLT for the regular prime 47, kernel-`decide`d (no `native_decide`). -/
theorem flt_47 : FermatLastTheoremFor 47 := flt_of_regCheck 47 (by norm_num) (by decide)

end RegPrimes
