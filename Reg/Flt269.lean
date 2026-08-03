import RegularPrimes
import Mathlib.Tactic.NormNum.Prime
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RegPrimes
instance factP_269 : Fact (Nat.Prime 269) := ⟨by norm_num⟩
theorem flt_269 : FermatLastTheoremFor 269 := flt_of_regCheck 269 (by norm_num) (by decide)
end RegPrimes
