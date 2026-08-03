import RegularPrimes
import Mathlib.Tactic.NormNum.Prime
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RegPrimes
instance factP_337 : Fact (Nat.Prime 337) := ⟨by norm_num⟩
theorem flt_337 : FermatLastTheoremFor 337 := flt_of_regCheck 337 (by norm_num) (by decide)
end RegPrimes
