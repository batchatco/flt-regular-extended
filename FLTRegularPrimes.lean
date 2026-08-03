import Reg.Flt17
import Reg.Flt19
import Reg.Flt23
import Reg.Flt29
import Reg.Flt31
import Reg.Flt41
import Reg.Flt43
import Reg.Flt47
import Reg.Flt53
import Reg.Flt61
import Reg.Flt71
import Reg.Flt73
import Reg.Flt79
import Reg.Flt83
import Reg.Flt89
import Reg.Flt97
import Reg.Flt107
import Reg.Flt109
import Reg.Flt113
import Reg.Flt127
import Reg.Flt137
import Reg.Flt139
import Reg.Flt151
import Reg.Flt163
import Reg.Flt167
import Reg.Flt173
import Reg.Flt179
import Reg.Flt181
import Reg.Flt191
import Reg.Flt193
import Reg.Flt197
import Reg.Flt199
import Reg.Flt211
import Reg.Flt223
import Reg.Flt227
import Reg.Flt229
import Reg.Flt239
import Reg.Flt241
import Reg.Flt251
import Reg.Flt269
import Reg.Flt277
import Reg.Flt281
import Reg.Flt313
import Reg.Flt317
import Reg.Flt331
import Reg.Flt337
import Reg.Flt349

/-!
`FermatLastTheoremFor q` for every REGULAR prime `q` with `17 ≤ q < 350` (47 primes),
`native_decide`-free, extending `flt_regular` beyond 13. One module per prime (`Reg/Flt<q>.lean`),
each a single kernel `decide` of the empty-irregular-list check `irrListCertN q (bModN q (q-3)) [] = true`.

Per-prime modules (not one file) on purpose: each decide runs in its own process; build sequentially
or with bounded concurrency. The dominant cost is *time*: the decide grows super-cubically in `q`
(measured on c4d-standard-64: ~15.5 min at q=349), while memory stays modest (~73 G at q=349, well
under a large box). So the practical frontier is compute time, not RAM or soundness; `native_decide`
(in flt-vandiver-primes) removes it, reaching every regular prime below 1000.

Irregular primes < 200 (37, 59, 67, 101, 103, 131, 149, 157) are not here; they are the Vandiver
route in flt-vandiver-primes-kernel.
-/

#print axioms RegPrimes.flt_17
#print axioms RegPrimes.flt_349
