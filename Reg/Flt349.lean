import RegularPrimes
import Mathlib.Tactic.NormNum.Prime
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RegPrimes
instance factP_349 : Fact (Nat.Prime 349) := ⟨by norm_num⟩
theorem flt_349 : FermatLastTheoremFor 349 := flt_of_regCheck 349 (by norm_num) (by decide)
end RegPrimes
