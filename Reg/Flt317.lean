import RegularPrimes
import Mathlib.Tactic.NormNum.Prime
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RegPrimes
instance factP_317 : Fact (Nat.Prime 317) := ⟨by norm_num⟩
theorem flt_317 : FermatLastTheoremFor 317 := flt_of_regCheck 317 (by norm_num) (by decide)
end RegPrimes
