import RegularPrimes
import Mathlib.Tactic.NormNum.Prime
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RegPrimes
instance factP_241 : Fact (Nat.Prime 241) := ⟨by norm_num⟩
theorem flt_241 : FermatLastTheoremFor 241 := flt_of_regCheck 241 (by norm_num) (by decide)
end RegPrimes
