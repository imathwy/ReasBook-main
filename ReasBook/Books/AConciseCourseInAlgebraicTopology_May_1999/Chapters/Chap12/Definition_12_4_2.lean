import Mathlib.Algebra.Homology.HomologicalComplexAbelian

-- `HomologicalComplex.shortExact_iff_degreewise_shortExact` is the canonical owner for the fact
-- that a short complex of homological complexes in an abelian category is short exact exactly when
-- each degreewise evaluation is short exact.

/- Definition 12.4.2: for a short exact sequence `0 ⟶ X' ⟶ X ⟶ X'' ⟶ 0` in
`ChainComplex (ModuleCat R) ℕ`, mathlib's canonical theorem
`HomologicalComplex.shortExact_iff_degreewise_shortExact` says equivalently that each degree `n`
induces a short exact sequence under `HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ)
n`. -/
#check HomologicalComplex.shortExact_iff_degreewise_shortExact
