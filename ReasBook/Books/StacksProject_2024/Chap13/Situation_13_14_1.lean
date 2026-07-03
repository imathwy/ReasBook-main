import Mathlib
import StacksProject_2024.Chap04.Definition_4_27_20

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MorphismProperty

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [IsTriangulated D] [IsTriangulated D']
  (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
  (S : MorphismProperty D) [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]

/-
Domain-style sampling:
- primary domain: exact functors between triangulated categories together with a saturated
  multiplicative system on the source category that is compatible with triangulation;
- relevant owner declarations already used upstream in the chapter/project:
  `Functor.CommShift ℤ`,
  `Functor.IsTriangulated`,
  `MorphismProperty.IsSaturatedMultiplicativeSystem`,
  `MorphismProperty.IsCompatibleWithTriangulation`.

Source/core/bridge triage:
- `source-facing`: Situation 13.14.1 is only the joint assumption that these four canonical owner
  classes hold for the pair `(F, S)`;
- `core/canonical`: the four owner classes listed above;
- `bridge/view`: downstream lemmas should request those owner classes directly, not a parallel
  wrapper around them.

Primitive data are exactly those four owner classes. There is no extra source-defined structure to
package here, so the refined file remains a direct canonical recall rather than introducing a new
bundled class.
-/

class ExactFunctorLocalizationSituation
    (F : D ⥤ D') (S : MorphismProperty D) extends
      F.CommShift ℤ, F.IsTriangulated,
      IsSaturatedMultiplicativeSystem S, S.IsCompatibleWithTriangulation

instance exactFunctorLocalizationSituation_of_instances
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    ExactFunctorLocalizationSituation F S where

/- Situation 13.14.1 uses the canonical shift-compatibility and exactness owners for `F`
together with the canonical saturation and triangulation-compatibility owners for `S`. -/
#check F.CommShift ℤ
#check F.IsTriangulated
#check IsSaturatedMultiplicativeSystem S
#check S.IsCompatibleWithTriangulation

end

end CategoryTheory
