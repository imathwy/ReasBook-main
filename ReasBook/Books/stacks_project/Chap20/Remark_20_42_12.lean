import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf of rings. -/
section

variable {X Y : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (SheafOfModules (ringCatSheaf X))
local notation "DModY" => DerivedCategory (SheafOfModules (ringCatSheaf Y))

variable (rightDerivedPushforward : DModX ⥤ DModY)
variable (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
variable (derivedTensorY : DModY ⥤ DModY ⥤ DModY)
variable (derivedInternalHomX : DModXᵒᵖ ⥤ DModX ⥤ DModX)
variable (derivedInternalHomY : DModYᵒᵖ ⥤ DModY ⥤ DModY)
variable
  (relativeDerivedCupProduct :
    ∀ (A B : DModX),
      (derivedTensorY.obj (rightDerivedPushforward.obj B)).obj
          (rightDerivedPushforward.obj A) ⟶
        rightDerivedPushforward.obj ((derivedTensorX.obj B).obj A))
variable
  (pushforwardInternalHomComparison :
    ∀ (K M : DModX),
      rightDerivedPushforward.obj ((derivedInternalHomX.obj (Opposite.op K)).obj M) ⟶
        (derivedInternalHomY.obj (Opposite.op (rightDerivedPushforward.obj K))).obj
          (rightDerivedPushforward.obj M))
variable
  (evaluationX :
    ∀ (K M : DModX),
      (derivedTensorX.obj K).obj ((derivedInternalHomX.obj (Opposite.op K)).obj M) ⟶ M)
variable
  (evaluationY :
    ∀ (K M : DModY),
      (derivedTensorY.obj K).obj ((derivedInternalHomY.obj (Opposite.op K)).obj M) ⟶ M)

-- Proof sketch: this is the compatibility of the pushforward-internal-Hom comparison with the
-- evaluation maps. The top arrow is the relative cup product, the left arrow is obtained by
-- tensoring the comparison map with `Rf_* K`, and the right and bottom arrows are the evaluation
-- morphisms on `X` and `Y`; the two routes through the square both express the pushed-forward
-- evaluation pairing.
/-- Remark 20.42.12: for a morphism of ringed spaces, the pushforward-internal-Hom comparison of
Remark `20.42.11` is compatible with evaluation. In the derived categories of module sheaves on
`X` and `Y`, if the top edge is the relative cup product of Remark `20.28.7`, the left edge is
the tensor of the comparison map
`Rf_* R\mathcal H\!\mathit{om}_{\mathcal O_X}(K, M) ⟶
R\mathcal H\!\mathit{om}_{\mathcal O_Y}(Rf_* K, Rf_* M)` with `Rf_* K`, and the right and
bottom edges are the evaluation morphisms on `X` and `Y`, then the resulting square commutes. -/
theorem pushforwardInternalHomComparison_evaluation_commSq
    (K M : DModX) :
    let A :=
      (derivedTensorY.obj (rightDerivedPushforward.obj K)).obj
        (rightDerivedPushforward.obj ((derivedInternalHomX.obj (Opposite.op K)).obj M))
    let B :=
      rightDerivedPushforward.obj
        ((derivedTensorX.obj K).obj ((derivedInternalHomX.obj (Opposite.op K)).obj M))
    let C :=
      (derivedTensorY.obj (rightDerivedPushforward.obj K)).obj
        ((derivedInternalHomY.obj (Opposite.op (rightDerivedPushforward.obj K))).obj
          (rightDerivedPushforward.obj M))
    let D :=
      rightDerivedPushforward.obj M
    let top : A ⟶ B :=
      relativeDerivedCupProduct ((derivedInternalHomX.obj (Opposite.op K)).obj M) K
    let left : A ⟶ C :=
      (derivedTensorY.obj (rightDerivedPushforward.obj K)).map
        (pushforwardInternalHomComparison K M)
    let right : B ⟶ D :=
      rightDerivedPushforward.map (evaluationX K M)
    let bot : C ⟶ D :=
      evaluationY (rightDerivedPushforward.obj K) (rightDerivedPushforward.obj M)
    CommSq top left right bot := sorry

end

end AlgebraicGeometry.RingedSpace
