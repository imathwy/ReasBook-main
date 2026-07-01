import Mathlib
import stacks_project.Chap20.Remark_20_28_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf of rings. -/
section

variable {X Y : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (SheafOfModules (ringCatSheaf X))
local notation "DModY" => DerivedCategory (SheafOfModules (ringCatSheaf Y))

variable (leftDerivedPullback : DModY ⥤ DModX)
variable (rightDerivedPushforward : DModX ⥤ DModY)
variable (pullPushAdj : leftDerivedPullback ⊣ rightDerivedPushforward)
variable (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
variable (derivedTensorY : DModY ⥤ DModY ⥤ DModY)
variable (pullbackTensorIso :
  ∀ (A B : DModY),
    leftDerivedPullback.obj ((derivedTensorY.obj B).obj A) ≅
      ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj (leftDerivedPullback.obj A)))
variable (tensorCommX :
  ∀ (A B : DModX),
    ((derivedTensorX.obj B).obj A) ≅ ((derivedTensorX.obj A).obj B))
variable (tensorCommY :
  ∀ (A B : DModY),
    ((derivedTensorY.obj B).obj A) ≅ ((derivedTensorY.obj A).obj B))

-- Proof sketch: transpose both routes across the adjunction `Lf^* ⊣ Rf_*`. By the defining
-- formula for `relativeDerivedCupProduct`, each transpose is obtained from the pullback-tensor
-- comparison followed by the two counit maps. The braidings `ψ` on `D(\mathcal O_X)` and
-- `D(\mathcal O_Y)` are compatible with these tensor products, so after inserting
-- `tensorCommX` and `tensorCommY` the two transposes agree. Injectivity of the adjunction
-- hom-equivalence then gives the commutative square in `D(\mathcal O_Y)`.
/-- Lemma 20.31.6: the relative cup product of Remark 20.28.7 is commutative. Equivalently, if
`ψ` denotes the commutativity constraint on the chosen derived tensor products of
`D(\mathcal O_X)` and `D(\mathcal O_Y)`, then for all `K, L ∈ D(\mathcal O_X)` the square
comparing the relative cup product on `(K, L)` with the one on `(L, K)` is commutative in
`D(\mathcal O_Y)`. -/
theorem relativeDerivedCupProduct_commutative
    (K L : DModX) :
    CommSq
      (relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
        derivedTensorX derivedTensorY pullbackTensorIso K L)
      (tensorCommY (rightDerivedPushforward.obj K) (rightDerivedPushforward.obj L)).hom
      (rightDerivedPushforward.map (tensorCommX K L).hom)
      (relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
        derivedTensorX derivedTensorY pullbackTensorIso L K) := sorry

end

end AlgebraicGeometry.RingedSpace
