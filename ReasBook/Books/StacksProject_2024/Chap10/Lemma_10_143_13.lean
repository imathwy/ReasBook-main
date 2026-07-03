import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.143.13: if a monic polynomial `f ∈ R[X]` has a factorization
`f mod 𝔭 = ḡ * h̄` in the residue field `κ(𝔭)[X]` with `ḡ` and `h̄` coprime, then after passing
to an étale `R`-algebra there is a prime lying over `𝔭` with the same residue field and a lift of
this factorization to coprime factors upstairs. This is exactly the canonical theorem
`Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`, where
`Function.Bijective` on the residue-field map encodes `κ(𝔭) = κ(𝔭')` and `IsCoprime` encodes that
the lifted factors generate the unit ideal. -/
recall Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime
