import RegularPrimes
import Mathlib.Tactic.NormNum.Prime
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RegPrimes
instance factP_251 : Fact (Nat.Prime 251) := ⟨by norm_num⟩
theorem flt_251 : FermatLastTheoremFor 251 := flt_of_regCheck 251 (by norm_num) (by decide)
end RegPrimes
