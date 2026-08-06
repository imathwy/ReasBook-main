import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.Monoidal

open CategoryTheory
open HomologicalComplex
open scoped MonoidalCategory

universe u

-- Semantic recall: `lean_leansearch` surfaced `tensorObj` as the canonical owner for the tensor
-- product of chain complexes, written with the standard monoidal notation `X ⊗ Y`; `ιTensorObj`
-- gives the coproduct summand inclusions, and `mapBifunctor.d_eq` together with
-- `mapBifunctor.d₁_eq`, `mapBifunctor.d₂_eq`, and `ComplexShape.ε_down_ℕ` exposes the usual
-- differential formula with sign `(-1)^i`.

variable (R : Type u) [CommRing R]
variable (X Y : ChainComplex (ModuleCat R) ℕ)

/- Definition 12.3.1. For chain complexes `X Y : ChainComplex (ModuleCat R) ℕ`, the tensor
product chain complex is the canonical mathlib construction `tensorObj X Y`, written `X ⊗ Y`.
Its degree `n` object is the coproduct of the summands `X.X i ⊗ Y.X j` over `i + j = n`,
accessed by `ιTensorObj`, and its differential is the sum of the two standard components
`d(x ⊗ y) = dx ⊗ y + (-1)^i x ⊗ dy`, encoded by `mapBifunctor.d_eq` with the chain-complex sign
rule `ComplexShape.ε_down_ℕ`. -/
#check (X ⊗ Y : ChainComplex (ModuleCat R) ℕ)
#check ιTensorObj
#check mapBifunctor.d_eq
#check mapBifunctor.d₁_eq
#check mapBifunctor.d₂_eq
#check ComplexShape.ε_down_ℕ
