import Mathlib
import StacksProject_2024.Chap10.Definition_10_70_1
import StacksProject_2024.Chap31.Definition_31_21_1
import StacksProject_2024.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped AffineBlowupChart nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the affine ideal-sheaf owner
-- `Scheme.IdealSheafData.ideal`; local Chapter 31 precedent fixes blowups by `IsBlowup`, affine
-- charts by `affineBlowupChart`, and closed-subscheme ideals by `closedImmersionIdealSubobject`.

namespace Scheme.IdealSheafData

/-- The ideal of the stalk ring cut out by the closed subscheme represented by ideal sheaf data. -/
noncomputable def closedImmersionStalkIdeal {X : Scheme.{u}} (D : X.IdealSheafData) (x : X) :
    Ideal (X.presheaf.stalk x) :=
  LinearMap.range
    ((RingedSpace.moduleStalkHom x (closedImmersionIdealSubobject D.subschemeι).arrow ≫
        RingedSpace.unitStalkLinearMap x).hom)

/-- Unfold the stalk ideal attached to the closed immersion associated to ideal sheaf data. -/
theorem closedImmersionStalkIdeal_def {X : Scheme.{u}} (D : X.IdealSheafData) (x : X) :
    D.closedImmersionStalkIdeal x =
      LinearMap.range
        ((RingedSpace.moduleStalkHom x (closedImmersionIdealSubobject D.subschemeι).arrow ≫
            RingedSpace.unitStalkLinearMap x).hom) := sorry

end Scheme.IdealSheafData

section

variable {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]

/-- Lemma 31.32.6: let `b : X' ⟶ X` be the blowup of `X` in the closed subscheme
defined by `I`. Let `U = Spec(A)` be an affine open of `X`, let `I.ideal U ⊆ A` be the
ideal corresponding to the center on `U`, and let `a ∈ I.ideal U`. For the affine blowup
chart `U' = Spec(A[I/a])`, a point `x'` over `U` lies in `U'` if and only if the image of
`a` in `𝒪_{X', x'}` is a nonzerodivisor and generates the stalk ideal of the exceptional
divisor `I.comap b`. -/
@[stacks 0BFL]
theorem mem_affineBlowupChart_iff_exceptionalDivisor_stalkIdeal_eq_span
    (U : X.affineOpens) (a : I.ideal U) (U' : X'.affineOpens)
    (eU' : ((U' : X'.Opens).toScheme) ≅ Spec (.of (affineBlowupChart (I.ideal U) a)))
    (hU'_le : (U' : X'.Opens) ≤ b ⁻¹ᵁ (U : X.Opens))
    (x' : X') (hxU : b x' ∈ (U : Set X)) :
    x' ∈ (U' : Set X') ↔
      let a_x' : X'.presheaf.stalk x' :=
        (Scheme.Hom.stalkMap b x').hom
          (X.presheaf.germ (U : X.Opens) (b x') hxU a.1)
      a_x' ∈ nonZeroDivisors (X'.presheaf.stalk x') ∧
        (I.comap b).closedImmersionStalkIdeal x' =
          Ideal.span ({a_x'} : Set (X'.presheaf.stalk x')) := sorry

end

end AlgebraicGeometry
