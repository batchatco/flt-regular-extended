import RegularPrimes
import Mathlib.Tactic.NormNum.Prime
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RegPrimes
instance factP_331 : Fact (Nat.Prime 331) := ⟨by norm_num⟩
theorem flt_331 : FermatLastTheoremFor 331 := flt_of_regCheck 331 (by norm_num) (by decide)
end RegPrimes
