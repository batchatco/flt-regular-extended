import RegularPrimes
import Mathlib.Tactic.NormNum.Prime
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RegPrimes
instance factP_277 : Fact (Nat.Prime 277) := ⟨by norm_num⟩
theorem flt_277 : FermatLastTheoremFor 277 := flt_of_regCheck 277 (by norm_num) (by decide)
end RegPrimes
