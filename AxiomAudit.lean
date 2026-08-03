import FLTRegularPrimes

/-!
Axiom audit: kernel-checked FLT for the 47 regular primes 17 <= q < 350
Run with:  lake env lean AxiomAudit.lean
Expected axiom base: [propext, Classical.choice, Quot.sound]  -- no Lean.ofReduceBool
-/

#print axioms RegPrimes.flt_17
#print axioms RegPrimes.flt_19
#print axioms RegPrimes.flt_23
#print axioms RegPrimes.flt_29
#print axioms RegPrimes.flt_31
#print axioms RegPrimes.flt_41
#print axioms RegPrimes.flt_43
#print axioms RegPrimes.flt_47
#print axioms RegPrimes.flt_53
#print axioms RegPrimes.flt_61
#print axioms RegPrimes.flt_71
#print axioms RegPrimes.flt_73
#print axioms RegPrimes.flt_79
#print axioms RegPrimes.flt_83
#print axioms RegPrimes.flt_89
#print axioms RegPrimes.flt_97
#print axioms RegPrimes.flt_107
#print axioms RegPrimes.flt_109
#print axioms RegPrimes.flt_113
#print axioms RegPrimes.flt_127
#print axioms RegPrimes.flt_137
#print axioms RegPrimes.flt_139
#print axioms RegPrimes.flt_151
#print axioms RegPrimes.flt_163
#print axioms RegPrimes.flt_167
#print axioms RegPrimes.flt_173
#print axioms RegPrimes.flt_179
#print axioms RegPrimes.flt_181
#print axioms RegPrimes.flt_191
#print axioms RegPrimes.flt_193
#print axioms RegPrimes.flt_197
#print axioms RegPrimes.flt_199
#print axioms RegPrimes.flt_211
#print axioms RegPrimes.flt_223
#print axioms RegPrimes.flt_227
#print axioms RegPrimes.flt_229
#print axioms RegPrimes.flt_239
#print axioms RegPrimes.flt_241
#print axioms RegPrimes.flt_251
#print axioms RegPrimes.flt_269
#print axioms RegPrimes.flt_277
#print axioms RegPrimes.flt_281
#print axioms RegPrimes.flt_313
#print axioms RegPrimes.flt_317
#print axioms RegPrimes.flt_331
#print axioms RegPrimes.flt_337
#print axioms RegPrimes.flt_349
