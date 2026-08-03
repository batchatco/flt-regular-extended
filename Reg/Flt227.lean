import RegularPrimes
import Mathlib.Tactic.NormNum.Prime
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RegPrimes
instance factP_227 : Fact (Nat.Prime 227) := ⟨by norm_num⟩
theorem flt_227 : FermatLastTheoremFor 227 := flt_of_regCheck 227 (by norm_num) (by decide)
end RegPrimes
