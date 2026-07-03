import Mathlib
import StacksProject_2024.Chap20.Lemma_20_42_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape
open scoped CartesianClosed

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev commRingSheafPushforwardMap {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a ringed-space morphism after forgetting commutativity. -/
noncomputable abbrev pushforwardStructureSheafHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (commRingSheafPushforwardMap f)

/-- The direct-image functor on `\mathcal O_X`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules Y) :=
  SheafOfModules.pushforward (pushforwardStructureSheafHom f)

/-- The pullback functor on `\mathcal O_Y`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

/-- The quasi-isomorphisms in the homotopy category of `\mathcal O_X`-module complexes. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The homotopy-category functor used to define the total left derived pullback. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ RingedSpaceDerived X :=
  (modulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-category functor used to define the total right derived pushforward. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive] :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ RingedSpaceDerived Y :=
  (modulePushforward f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) ⥤ D(\mathcal O_X)`. -/
abbrev modulePullbackDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    RingedSpaceDerived Y ⥤ RingedSpaceDerived X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ RingedSpaceDerived Y)
    (ModuleQis Y)

/-- The derived pushforward functor `Rf_* : D(\mathcal O_X) ⥤ D(\mathcal O_Y)`. -/
abbrev moduleDerivedPushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    RingedSpaceDerived X ⥤ RingedSpaceDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ RingedSpaceDerived X)
    (ModuleQis X)

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

variable [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
variable [(modulePullback f).Additive] [(modulePushforward f).Additive]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]
variable [MonoidalCategory (RingedSpaceDerived Y)]
variable [BraidedCategory (RingedSpaceDerived Y)]
variable [MonoidalClosed (RingedSpaceDerived Y)]

/-- The tensor-internal-Hom adjunction on `D(\mathcal O_Y)`, written with the tensor factors in
the order used by the Stacks Project. -/
abbrev ringedSpaceDerivedInternalHomAdjunction
    (A B C : RingedSpaceDerived Y) :
    (A ⟶ (ihom B).obj C) ≃ (A ⊗ B ⟶ C) :=
  ((ihom.adjunction B).homEquiv A C).symm.trans
    ((β_ A B).symm.homCongr (Iso.refl C))

/-- The evaluation morphism
`R\mathcal H\!\mathit{om}(L, K) \otimes^{\mathbf L} L \to K` in `D(\mathcal O_X)`,
obtained from internal-Hom composition and the unit object. -/
noncomputable def ringedSpaceDerivedInternalHomEvaluation
    (L K : RingedSpaceDerived X) :
    (L ⟹ K) ⊗ L ⟶ K :=
  (𝟙 (L ⟹ K) ⊗ₘ
      (unitIsoSelf L).symm.hom) ≫
    (β_ (L ⟹ K) ((𝟙_ (RingedSpaceDerived X)) ⟹ L)).hom ≫
    comp (𝟙_ (RingedSpaceDerived X)) L K ≫
    (unitIsoSelf K).hom

/-- The relative cup product
`Rf_* A \otimes^{\mathbf L} Rf_* B \to Rf_*(A \otimes^{\mathbf L} B)` on derived categories of
module sheaves, given a chosen derived adjunction and pullback-tensor comparison. -/
noncomputable def ringedSpaceDerivedPushforwardCupProduct
    (pullPushAdj : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (pullbackTensorIso :
      ∀ (A B : RingedSpaceDerived Y),
        (modulePullbackDerived f).obj (A ⊗ B) ≅
          ((modulePullbackDerived f).obj A ⊗ (modulePullbackDerived f).obj B))
    (A B : RingedSpaceDerived X) :
    (moduleDerivedPushforward f).obj A ⊗ (moduleDerivedPushforward f).obj B ⟶
      (moduleDerivedPushforward f).obj (A ⊗ B) :=
  (pullPushAdj.homEquiv _ _)
    ((pullbackTensorIso
        ((moduleDerivedPushforward f).obj A)
        ((moduleDerivedPushforward f).obj B)).hom ≫
      (pullPushAdj.counit.app A ▷
        (modulePullbackDerived f).obj ((moduleDerivedPushforward f).obj B)) ≫
      (A ◁ pullPushAdj.counit.app B))

/-- Remark 20.42.11: after fixing the derived adjunction `Lf^* ⊣ Rf_*` and the pullback-tensor
comparison used in Remark `20.28.7`, there is a canonical morphism
`Rf_* R\mathcal H\!\mathit{om}(L, K) \to
R\mathcal H\!\mathit{om}(Rf_* L, Rf_* K)` in `D(\mathcal O_Y)`. -/
noncomputable def ringedSpaceDerivedPushforwardInternalHomComparison
    (pullPushAdj : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (pullbackTensorIso :
      ∀ (A B : RingedSpaceDerived Y),
        (modulePullbackDerived f).obj (A ⊗ B) ≅
          ((modulePullbackDerived f).obj A ⊗ (modulePullbackDerived f).obj B))
    (L K : RingedSpaceDerived X) :
    (moduleDerivedPushforward f).obj ((ihom L).obj K) ⟶
      (ihom ((moduleDerivedPushforward f).obj L)).obj ((moduleDerivedPushforward f).obj K) :=
  (ringedSpaceDerivedInternalHomAdjunction
      ((moduleDerivedPushforward f).obj ((ihom L).obj K))
      ((moduleDerivedPushforward f).obj L)
      ((moduleDerivedPushforward f).obj K)).symm
    (ringedSpaceDerivedPushforwardCupProduct f pullPushAdj pullbackTensorIso
        ((ihom L).obj K) L ≫
      (moduleDerivedPushforward f).map
        (ringedSpaceDerivedInternalHomEvaluation L K))

-- Proof sketch: unfold
-- `ringedSpaceDerivedPushforwardInternalHomComparison`; it is defined as the inverse image of the
-- displayed tensor morphism under the tensor-internal-Hom adjunction on `D(\mathcal O_Y)`.
/-- Applying the tensor-internal-Hom adjunction to the pushforward-internal-Hom comparison
recovers the relative cup product followed by the pushed-forward evaluation morphism. -/
theorem ringedSpaceDerivedPushforwardInternalHomComparison_homEquiv
    (pullPushAdj : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (pullbackTensorIso :
      ∀ (A B : RingedSpaceDerived Y),
        (modulePullbackDerived f).obj (A ⊗ B) ≅
          ((modulePullbackDerived f).obj A ⊗ (modulePullbackDerived f).obj B))
    (L K : RingedSpaceDerived X) :
    ringedSpaceDerivedInternalHomAdjunction
        ((moduleDerivedPushforward f).obj ((ihom L).obj K))
        ((moduleDerivedPushforward f).obj L)
        ((moduleDerivedPushforward f).obj K)
        (ringedSpaceDerivedPushforwardInternalHomComparison f pullPushAdj pullbackTensorIso
          L K) =
      ringedSpaceDerivedPushforwardCupProduct f pullPushAdj pullbackTensorIso
          ((ihom L).obj K) L ≫
        (moduleDerivedPushforward f).map
          (ringedSpaceDerivedInternalHomEvaluation L K) := sorry

end

end AlgebraicGeometry.RingedSpace
