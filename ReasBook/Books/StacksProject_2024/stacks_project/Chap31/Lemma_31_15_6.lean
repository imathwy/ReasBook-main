import StacksProject_2024.Chap28.Lemma_28_12_5
import StacksProject_2024.Chap31.Lemma_31_15_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Source/core/bridge triage:
-- * source-facing: `subscheme_satisfiesSerreConditionS_one_of_isNormal`, the Stacks lemma for an
--   effective Cartier divisor on a normal locally Noetherian scheme;
-- * core/canonical: the earlier Chapter 28 owner `satisfiesSerreConditionS_two_of_isNormal`;
-- * bridge/view: Lemma 31.15.5, which lowers `(S₂)` on `X` to `(S₁)` on `D.subscheme`.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable [CategoryTheory.MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]

/-- Lemma 31.15.6: let `X` be a locally Noetherian normal scheme. Let `D ⊆ X` be an effective
Cartier divisor. Then `D` is `(S_1)`, formalized here as Serre's condition `(S_1)` on the
canonical closed subscheme `D.subscheme`. -/
@[stacks 0B3S]
  theorem subscheme_satisfiesSerreConditionS_one_of_isNormal
    (D : X.IdealSheafData) [D.IsEffectiveCartierDivisor] (hX : X.isNormal) :
    D.subscheme.satisfiesSerreConditionS 1 := by
  simpa using
    satisfiesSerreConditionS_subscheme_pred_of_isEffectiveCartierDivisor
      D 2 (satisfiesSerreConditionS_two_of_isNormal X hX)

end AlgebraicGeometry.Scheme
