import RegularPrimes
import Mathlib.Tactic.NormNum.Prime
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RegPrimes
instance factP_229 : Fact (Nat.Prime 229) := ⟨by norm_num⟩
theorem flt_229 : FermatLastTheoremFor 229 := flt_of_regCheck 229 (by norm_num) (by decide)
end RegPrimes
