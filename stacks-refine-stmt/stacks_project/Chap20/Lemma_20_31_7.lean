import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y Z : RingedSpace.{u}}
variable (f : X ⟶ Y) (g : Y ⟶ Z)

local notation "DModX" => DerivedCategory (Modules X)
local notation "DModY" => DerivedCategory (Modules Y)
local notation "DModZ" => DerivedCategory (Modules Z)

variable
    (leftDerivedPullback_f : DModY ⥤ DModX)
    (rightDerivedPushforward_f : DModX ⥤ DModY)
    (pullPushAdj_f : leftDerivedPullback_f ⊣ rightDerivedPushforward_f)
    (leftDerivedPullback_g : DModZ ⥤ DModY)
    (rightDerivedPushforward_g : DModY ⥤ DModZ)
    (pullPushAdj_g : leftDerivedPullback_g ⊣ rightDerivedPushforward_g)
    (leftDerivedPullback_comp : DModZ ⥤ DModX)
    (rightDerivedPushforward_comp : DModX ⥤ DModZ)
    (pullPushAdj_comp : leftDerivedPullback_comp ⊣ rightDerivedPushforward_comp)
    (pushforwardCompIso :
      rightDerivedPushforward_f ⋙ rightDerivedPushforward_g ≅ rightDerivedPushforward_comp)

variable
    (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
    (derivedTensorY : DModY ⥤ DModY ⥤ DModY)
    (derivedTensorZ : DModZ ⥤ DModZ ⥤ DModZ)

variable
    (pullbackTensorIso_f :
      ∀ (A B : DModY),
        leftDerivedPullback_f.obj ((derivedTensorY.obj B).obj A) ≅
          ((derivedTensorX.obj (leftDerivedPullback_f.obj B)).obj
            (leftDerivedPullback_f.obj A)))

variable
    (pullbackTensorIso_g :
      ∀ (A B : DModZ),
        leftDerivedPullback_g.obj ((derivedTensorZ.obj B).obj A) ≅
          ((derivedTensorY.obj (leftDerivedPullback_g.obj B)).obj
            (leftDerivedPullback_g.obj A)))

variable
    (pullbackTensorIso_comp :
      ∀ (A B : DModZ),
        leftDerivedPullback_comp.obj ((derivedTensorZ.obj B).obj A) ≅
          ((derivedTensorX.obj (leftDerivedPullback_comp.obj B)).obj
            (leftDerivedPullback_comp.obj A)))

/-- The pullback-side morphism whose adjoint is the relative cup product for a chosen derived
pullback/pushforward adjunction. -/
private noncomputable abbrev relativeDerivedCupProductForAdjunctionAdjoint
    {A : Type u} [Category A] {B : Type u} [Category B]
    (leftDerivedPullback : B ⥤ A)
    (rightDerivedPushforward : A ⥤ B)
    (pullPushAdj : leftDerivedPullback ⊣ rightDerivedPushforward)
    (derivedTensorA : A ⥤ A ⥤ A)
    (derivedTensorB : B ⥤ B ⥤ B)
    (pullbackTensorIso :
      ∀ (U V : B),
        leftDerivedPullback.obj ((derivedTensorB.obj V).obj U) ≅
          ((derivedTensorA.obj (leftDerivedPullback.obj V)).obj
            (leftDerivedPullback.obj U)))
    (K L : A) :
    leftDerivedPullback.obj
        ((derivedTensorB.obj (rightDerivedPushforward.obj L)).obj
          (rightDerivedPushforward.obj K)) ⟶
      ((derivedTensorA.obj L).obj K) :=
  (pullbackTensorIso
      (rightDerivedPushforward.obj K)
      (rightDerivedPushforward.obj L)).hom ≫
    ((derivedTensorA.map (pullPushAdj.counit.app L)).app
      (leftDerivedPullback.obj (rightDerivedPushforward.obj K))) ≫
    ((derivedTensorA.obj L).map (pullPushAdj.counit.app K))

/-- The relative cup product attached to a chosen derived pullback/pushforward adjunction and
pullback-tensor comparison. -/
noncomputable def relativeDerivedCupProductForAdjunction
    {A : Type u} [Category A] {B : Type u} [Category B]
    (leftDerivedPullback : B ⥤ A)
    (rightDerivedPushforward : A ⥤ B)
    (pullPushAdj : leftDerivedPullback ⊣ rightDerivedPushforward)
    (derivedTensorA : A ⥤ A ⥤ A)
    (derivedTensorB : B ⥤ B ⥤ B)
    (pullbackTensorIso :
      ∀ (U V : B),
        leftDerivedPullback.obj ((derivedTensorB.obj V).obj U) ≅
          ((derivedTensorA.obj (leftDerivedPullback.obj V)).obj
            (leftDerivedPullback.obj U)))
    (K L : A) :
    ((derivedTensorB.obj (rightDerivedPushforward.obj L)).obj
      (rightDerivedPushforward.obj K)) ⟶
      rightDerivedPushforward.obj ((derivedTensorA.obj L).obj K) :=
  (pullPushAdj.homEquiv _ _)
    (relativeDerivedCupProductForAdjunctionAdjoint
      leftDerivedPullback rightDerivedPushforward pullPushAdj
      derivedTensorA derivedTensorB pullbackTensorIso K L)

/-- The clockwise composite in the composition-compatibility square for relative cup products. -/
noncomputable abbrev iteratedRelativeDerivedCupProduct
    (K L : DModX) :
    ((derivedTensorZ.obj (rightDerivedPushforward_comp.obj L)).obj
      (rightDerivedPushforward_comp.obj K)) ⟶
      rightDerivedPushforward_comp.obj ((derivedTensorX.obj L).obj K) :=
  ((derivedTensorZ.map
      (pushforwardCompIso.inv.app L)).app
      (rightDerivedPushforward_comp.obj K)) ≫
    ((derivedTensorZ.obj
      (rightDerivedPushforward_g.obj (rightDerivedPushforward_f.obj L))).map
      (pushforwardCompIso.inv.app K)) ≫
    relativeDerivedCupProductForAdjunction
      leftDerivedPullback_g rightDerivedPushforward_g pullPushAdj_g
      derivedTensorY derivedTensorZ pullbackTensorIso_g
      (rightDerivedPushforward_f.obj K) (rightDerivedPushforward_f.obj L) ≫
    rightDerivedPushforward_g.map
      (relativeDerivedCupProductForAdjunction
        leftDerivedPullback_f rightDerivedPushforward_f pullPushAdj_f
        derivedTensorX derivedTensorY pullbackTensorIso_f K L) ≫
    pushforwardCompIso.hom.app
      ((derivedTensorX.obj L).obj K)

/-- The relative cup product attached directly to the composite adjunction for `g ∘ f`. -/
private noncomputable abbrev compositeRelativeDerivedCupProduct
    (K L : DModX) :
    ((derivedTensorZ.obj (rightDerivedPushforward_comp.obj L)).obj
      (rightDerivedPushforward_comp.obj K)) ⟶
      rightDerivedPushforward_comp.obj ((derivedTensorX.obj L).obj K) :=
  relativeDerivedCupProductForAdjunction
    leftDerivedPullback_comp rightDerivedPushforward_comp pullPushAdj_comp
    derivedTensorX derivedTensorZ pullbackTensorIso_comp K L

-- Proof sketch: transport both paths across the adjunction for `L(g \circ f)^* ⊣ R(g \circ f)_*`.
-- The direct path is adjoint to the pullback-tensor comparison for `g \circ f` followed by the
-- counit `L(g \circ f)^* R(g \circ f)_* ⟶ 𝟭`. For the iterated path, apply
-- the defining adjunction formulas for the two relative cup products; the compatibility of
-- counits under composition from Categories, Lemma `4.24.9`, identifies the resulting composite
-- of counits with the counit of the composite adjunction, so both transposes are the same map.
/-- Lemma 20.31.7: for composable morphisms of ringed spaces `f : (X, \mathcal O_X) \to
(Y, \mathcal O_Y)` and `g : (Y, \mathcal O_Y) \to (Z, \mathcal O_Z)`, the relative cup product
for `g \circ f` agrees with the composite obtained by first applying the relative cup product for
`g` to `Rf_* K` and `Rf_* L`, then applying `Rg_*` to the relative cup product for `f`, and
finally identifying `Rg_* Rf_*` with `R(g \circ f)_*`. Equivalently, the composition square of
relative cup products is commutative in `D(\mathcal O_Z)` for all `K, L` in `D(\mathcal O_X)`. -/
theorem relativeDerivedCupProduct_comp
    (K L : DModX) :
    compositeRelativeDerivedCupProduct K L =
      iteratedRelativeDerivedCupProduct K L := sorry

end

end AlgebraicGeometry.RingedSpace
