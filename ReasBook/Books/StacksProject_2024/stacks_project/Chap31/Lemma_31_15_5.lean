import Mathlib
import StacksProject_2024.stacks_project.Chap28.Lemma_28_5_6
import StacksProject_2024.stacks_project.Chap30.Definition_30_11_1_Scheme
import StacksProject_2024.stacks_project.Chap31.Lemma_31_13_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical locally Noetherian scheme owner, and
-- the local Chapter 30 owner for `(S_k)` is `Scheme.satisfiesSerreConditionS`. Following the
-- Chapter 31 divisor precedent, the effective Cartier divisor is expressed as
-- `D : X.IdealSheafData`, and the conclusion is stated on the canonical closed subscheme
-- `D.subscheme`.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable [CategoryTheory.MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]

/-- A closed subscheme of a locally Noetherian scheme is locally Noetherian. -/
instance instIsLocallyNoetherianSubscheme (D : X.IdealSheafData) :
    IsLocallyNoetherian D.subscheme :=
  IsLocallyNoetherian.of_isImmersion D.subschemeι

/-- Lemma 31.15.5: if `X` is a locally Noetherian scheme satisfying Serre's condition `(S_k)` and
`D ⊆ X` is an effective Cartier divisor, then the closed subscheme `D` satisfies
Serre's condition `(S_{k - 1})`. -/
@[stacks 0B3R]
theorem satisfiesSerreConditionS_subscheme_pred_of_isEffectiveCartierDivisor
    (D : X.IdealSheafData) [D.IsEffectiveCartierDivisor] (k : ℕ)
    (hX : X.satisfiesSerreConditionS k) :
    D.subscheme.satisfiesSerreConditionS (k - 1) := by
  sorry

end AlgebraicGeometry.Scheme
