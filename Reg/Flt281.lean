import RegularPrimes
import Mathlib.Tactic.NormNum.Prime
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RegPrimes
instance factP_281 : Fact (Nat.Prime 281) := ⟨by norm_num⟩
theorem flt_281 : FermatLastTheoremFor 281 := flt_of_regCheck 281 (by norm_num) (by decide)
end RegPrimes
