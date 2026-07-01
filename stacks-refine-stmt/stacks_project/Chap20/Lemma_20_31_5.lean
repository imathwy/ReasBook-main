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
variable (tensorAssocX :
  ∀ (A B C : DModX),
    ((derivedTensorX.obj C).obj ((derivedTensorX.obj B).obj A)) ≅
      ((derivedTensorX.obj ((derivedTensorX.obj C).obj B)).obj A))
variable (tensorAssocY :
  ∀ (A B C : DModY),
    ((derivedTensorY.obj C).obj ((derivedTensorY.obj B).obj A)) ≅
      ((derivedTensorY.obj ((derivedTensorY.obj C).obj B)).obj A))

/-- The derived tensor product on `D(\mathcal O_X)` with explicit left and right factors. -/
private def tensorXObj
    (derivedTensorX : DModX ⥤ DModX ⥤ DModX) (A B : DModX) : DModX :=
  (derivedTensorX.obj B).obj A

/-- The derived tensor product on `D(\mathcal O_Y)` with explicit left and right factors. -/
private def tensorYObj
    (derivedTensorY : DModY ⥤ DModY ⥤ DModY) (A B : DModY) : DModY :=
  (derivedTensorY.obj B).obj A

/-- The common source object in the associativity square for the relative cup product. -/
private def relativeDerivedCupProductAssociativitySource
    (derivedTensorY : DModY ⥤ DModY ⥤ DModY)
    (rightDerivedPushforward : DModX ⥤ DModY)
    (K L M : DModX) : DModY :=
  tensorYObj derivedTensorY
    (tensorYObj derivedTensorY (rightDerivedPushforward.obj K) (rightDerivedPushforward.obj L))
    (rightDerivedPushforward.obj M)

/-- The common target object in the associativity square for the relative cup product. -/
private def relativeDerivedCupProductAssociativityTarget
    (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
    (rightDerivedPushforward : DModX ⥤ DModY)
    (K L M : DModX) : DModY :=
  rightDerivedPushforward.obj
    (tensorXObj derivedTensorX K (tensorXObj derivedTensorX L M))

/-- The top-then-right composite in the associativity square for the relative cup product. -/
private noncomputable def relativeDerivedCupProductAssociativityTop
    (K L M : DModX) :
    relativeDerivedCupProductAssociativitySource derivedTensorY rightDerivedPushforward K L M ⟶
      relativeDerivedCupProductAssociativityTarget derivedTensorX rightDerivedPushforward K L M :=
  (derivedTensorY.obj (rightDerivedPushforward.obj M)).map
      (relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
        derivedTensorX derivedTensorY pullbackTensorIso K L) ≫
    relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
      derivedTensorX derivedTensorY pullbackTensorIso (tensorXObj derivedTensorX K L) M ≫
    rightDerivedPushforward.map (tensorAssocX K L M).hom

/-- The left-then-bottom composite in the associativity square for the relative cup product. -/
private noncomputable def relativeDerivedCupProductAssociativityBottom
    (K L M : DModX) :
    relativeDerivedCupProductAssociativitySource derivedTensorY rightDerivedPushforward K L M ⟶
      relativeDerivedCupProductAssociativityTarget derivedTensorX rightDerivedPushforward K L M :=
  (tensorAssocY (rightDerivedPushforward.obj K) (rightDerivedPushforward.obj L)
      (rightDerivedPushforward.obj M)).hom ≫
    (derivedTensorY.map
        (relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
          derivedTensorX derivedTensorY pullbackTensorIso L M)).app
      (rightDerivedPushforward.obj K) ≫
    relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
      derivedTensorX derivedTensorY pullbackTensorIso K (tensorXObj derivedTensorX L M)

-- Proof sketch: both routes become adjoint under `pullPushAdj` to the same morphism
-- `Lf^*((Rf_* K ⊗ Rf_* L) ⊗ Rf_* M) ⟶ K ⊗ (L ⊗ M)`, namely the one obtained from the pullback
-- tensor comparison, the associators, and the three counit maps. Applying injectivity of the
-- adjunction hom-equivalence yields equality of the two relative cup-product composites.
/-- Lemma 20.31.5: the relative cup product of Remark 20.28.7 is associative, i.e. after
inserting the chosen tensor associators, the two composites
`(Rf_* K \otimes^{\mathbf L} Rf_* L) \otimes^{\mathbf L} Rf_* M ⟶
Rf_*(K \otimes^{\mathbf L} (L \otimes^{\mathbf L} M))`
obtained by cupping first in the pair `(K,L)` or first in the pair `(L,M)` agree. -/
theorem relativeDerivedCupProduct_associative
    (K L M : DModX) :
    relativeDerivedCupProductAssociativityTop K L M =
      relativeDerivedCupProductAssociativityBottom K L M := sorry

end

end AlgebraicGeometry.RingedSpace
