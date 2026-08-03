import RegularPrimes
import Mathlib.Tactic.NormNum.Prime
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RegPrimes
instance factP_239 : Fact (Nat.Prime 239) := ⟨by norm_num⟩
theorem flt_239 : FermatLastTheoremFor 239 := flt_of_regCheck 239 (by norm_num) (by decide)
end RegPrimes
