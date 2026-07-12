import Mathlib
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap31.Definition_31_33_1
import StacksProject_2024.Chap31.Lemma_31_32_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.support`; local search
-- verified the project owners `idealSheafProduct`, `IsBlowup`, `strictTransformModule`, and
-- `moduleSectionSupport`.

/-- Lemma 31.33.5 (1): let `S` be a scheme, let `Z` be the closed subscheme defined by
`I`, and let `D` be an effective Cartier divisor on `S`. If `b : S' ⟶ S` is the blowup
of `S` in `Z`, then the same morphism is the blowup of `S` in the closed subscheme cut out
by the product ideal sheaf `I * D`. -/
@[stacks 080H]
theorem isBlowup_idealSheafProduct_of_isBlowup_effectiveCartier
    {S S' : Scheme.{u}} (I D : S.IdealSheafData) [IsEffectiveCartierDivisor D]
    (b : S' ⟶ S) [IsBlowup b I] :
    IsBlowup b (idealSheafProduct I D) := sorry

namespace Scheme.Modules

/-- Lemma 31.33.5 (2): with notation as in Lemma 31.33.5 (1), let `f : X ⟶ S` and let
`ℱ` be a quasi-coherent `\mathcal O_X`-module. If every local section of `ℱ` whose support
is contained in the inverse-image divisor `f⁻¹D` is zero, then the strict transform of `ℱ`
relative to the blowup in `I` agrees with the strict transform relative to the same morphism
viewed as the blowup in the product ideal sheaf `I * D`. -/
@[stacks 080H]
theorem strictTransformModule_eq_strictTransformModule_idealSheafProduct_of_noSectionsSupportedOn
    {S S' X : Scheme.{u}} (I D : S.IdealSheafData) [IsEffectiveCartierDivisor D]
    (b : S' ⟶ S) [IsBlowup b I]
    (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (hsections : ∀ (U : X.Opens) (s : ℱ.val.obj (op U)),
      moduleSectionSupport s ⊆
        {x : U | (x : X) ∈ ((D.comap f).support : Set X)} → s = 0) :
    strictTransformModule b (I.comap b) f ℱ =
      strictTransformModule b ((idealSheafProduct I D).comap b) f ℱ := sorry

end Scheme.Modules

end AlgebraicGeometry
