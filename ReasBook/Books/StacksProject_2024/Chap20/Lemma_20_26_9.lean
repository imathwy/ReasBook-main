import Mathlib
import StacksProject_2024.Chap17.Definition_17_17_1
import StacksProject_2024.Chap20.Definition_20_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

-- Proof sketch: apply Lemma `isKFlat_iff_stalkwise_isKFlat` to reduce to canonical stalk
-- complexes. For each `x : X`, the stalk complex of `K` at `x` is bounded above whenever `K` is bounded
-- above, and its term in degree `n` is flat over `\mathcal O_{X, x}` because `K.X n` is a flat
-- `\mathcal O_X`-module sheaf. Then use the module-theoretic bounded-above flat criterion from
-- Lemma `15.59.7` on every stalk complex.
/-- Lemma 20.26.9: a bounded above complex of flat `\mathcal O_X`-modules on a ringed space
`(X, \mathcal O_X)` is K-flat. -/
theorem isKFlat_of_boundedAbove_of_flat
    (K : CochainComplex (RingedSpace.Modules X) ℤ)
    (hbounded : ∃ n : ℤ, K.IsStrictlyLE n)
    (hFlat : ∀ n : ℤ, SheafOfModules.IsFlat (K.X n)) :
    IsKFlat K := sorry

end AlgebraicGeometry.RingedSpace
