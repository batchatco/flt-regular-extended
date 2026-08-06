import Reg.Flt107

/-!
Solution side for Comparator: forwards to the project's kernel-checked proof of
FLT for exponent 107 -- kernel `decide` only; axioms `propext`, `Classical.choice`,
`Quot.sound`.
-/

theorem flt_107 : FermatLastTheoremFor 107 := RegPrimes.flt_107
