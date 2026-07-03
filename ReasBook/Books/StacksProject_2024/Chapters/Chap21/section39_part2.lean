import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_21_39_13 (from Chap21) -/
open CategoryTheory
open Opposite
open scoped Simplicial

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u} [Category.{u} C]
variable {B : Type u} [Ring B]
variable [HasWeakSheafify (⊥ : GrothendieckTopology C) RingCat.{u}]
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat RingCat.{u})]

/-- Two simplicial sets are homotopy equivalent if there are maps in both directions whose
composites are simplicially homotopic to the corresponding identity morphisms. -/
def SimplicialSetHomotopyEquivalent (X Y : SSet.{u}) : Prop :=
  ∃ (f : X ⟶ Y) (g : Y ⟶ X),
    Nonempty (SimplicialObject.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (SimplicialObject.Homotopy (g ≫ f) (𝟙 Y))

/-- The simplicial set `n ↦ \operatorname{Mor}_{\mathcal C}(U_n, U)` attached to a cosimplicial
object `U_\bullet` and an object `U` of `C`. -/
abbrev cosimplicialHomSSet (Ubullet : CosimplicialObject C) (U : C) : SSet.{u} :=
  ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (Type u)).obj
      ((CategoryTheory.cosimplicialSimplicialEquiv C).functor.obj (op Ubullet))).obj
    (yoneda.obj U)

/-- The cosimplicial object hypothesis from Lemma `21.39.7`: every simplicial mapping space
`\operatorname{Mor}_{\mathcal C}(U_\bullet, U)` is homotopy equivalent to `\Delta[0]`. -/
def CosimplicialObjectHasPointlikeHomSpaces (Ubullet : CosimplicialObject C) : Prop :=
  ∀ U : C,
    SimplicialSetHomotopyEquivalent
      (cosimplicialHomSSet Ubullet U)
      (Δ[0] : SSet)

/-- The `RingCat`-valued structure sheaf on a category with the chaotic topology. -/
abbrev chaoticRingSheaf (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}) :
    Sheaf (⊥ : GrothendieckTopology C) RingCat.{u} :=
  (sheafCompose (⊥ : GrothendieckTopology C) (forget₂ CommRingCat RingCat.{u})).obj 𝒪

/-- The category `\mathrm{Mod}(\mathcal O)` of modules over a sheaf of commutative rings on a
category endowed with the chaotic topology. -/
abbrev moduleOnCategory (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}) :=
  SheafOfModules (chaoticRingSheaf 𝒪)

/-- The constant sheaf of rings `\underline B` on a category with the chaotic topology. -/
abbrev constantRingSheafOnCategory (B : Type u) [Ring B] :
    Sheaf (⊥ : GrothendieckTopology C) RingCat.{u} :=
  (constantSheaf (⊥ : GrothendieckTopology C) RingCat.{u}).obj (RingCat.of B)

/-- The category `\mathrm{Mod}(\underline B)` of modules over the constant sheaf of rings
`\underline B`. -/
abbrev constantModuleCategory (B : Type u) [Ring B] :=
  SheafOfModules
    ((constantRingSheafOnCategory B) :
      Sheaf (⊥ : GrothendieckTopology C) RingCat.{u})

/-- The constant sheaf `\underline B`, viewed as an `\mathcal O`-module via restriction of
scalars along the structure map `\mathcal O \to \underline B`. -/
abbrev targetAsSourceModule
    {𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
    (α : chaoticRingSheaf 𝒪 ⟶ constantRingSheafOnCategory B) :
    moduleOnCategory 𝒪 :=
  (SheafOfModules.restrictScalars α).obj
    (SheafOfModules.unit (constantRingSheafOnCategory B))

/-- The displayed functor `L\pi_! : D(\mathcal O) \to D(B)` obtained by composing derived base
change to `\underline B` with the derived lower shriek for the category-over-a-point situation
with coefficients in `B`. -/
abbrev derivedLowerShriekViaBaseChange
    {𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
    (derivedBaseChangeToConstant :
      DerivedCategory (moduleOnCategory 𝒪) ⥤
        DerivedCategory (@constantModuleCategory C _ _ B _))
    (constantModuleDerivedLowerShriek :
      DerivedCategory (@constantModuleCategory C _ _ B _) ⥤
        DerivedCategory (ModuleCat B)) :
    DerivedCategory (moduleOnCategory 𝒪) ⥤ DerivedCategory (ModuleCat B) :=
  derivedBaseChangeToConstant ⋙ constantModuleDerivedLowerShriek

-- Proof sketch: the displayed functor is literally the composite of the derived base-change
-- functor `- \otimes^{\mathbf L}_{\mathcal O} \underline B` with the already exact functor
-- `L\pi_! : D(\underline B) \to D(B)`, so the displayed functor is exactly that composite.
/-- The displayed `D(\mathcal O) \to D(B)` functor is, by definition, the composite of derived
base change to `\underline B` with the chosen `L\pi_! : D(\underline B) \to D(B)`. -/
theorem derivedLowerShriekViaBaseChange_def
    {𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
    (derivedBaseChangeToConstant :
      DerivedCategory (moduleOnCategory 𝒪) ⥤
        DerivedCategory (@constantModuleCategory C _ _ B _))
    (constantModuleDerivedLowerShriek :
      DerivedCategory (@constantModuleCategory C _ _ B _) ⥤
        DerivedCategory (ModuleCat B)) :
    derivedLowerShriekViaBaseChange
        derivedBaseChangeToConstant constantModuleDerivedLowerShriek =
      derivedBaseChangeToConstant ⋙ constantModuleDerivedLowerShriek := sorry

variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u})
variable [Abelian (moduleOnCategory 𝒪)]

-- Proof sketch: use the cosimplicial-object hypothesis from Lemma `21.39.7` to realize the
-- lower shriek on `D(\underline B)`, and use Lemma `21.39.12` applied to the map
-- `\mathcal O \to \underline B` to identify the underlying abelian derived lower shriek of `K`
-- with that of `K \otimes^{\mathbf L}_{\mathcal O} \underline B`. These identifications assemble
-- into a natural isomorphism from the abelian-valued `L\pi_!` to the composite through
-- `D(\underline B)` and hence through `D(B)`.
/-- Remark 21.39.13: for a category `\mathcal C` over a point and a map of sheaves of rings
`\mathcal O \to \underline B` whose image under `L\pi_!` is an isomorphism, the abelian derived
lower shriek on `D(\mathcal O)` factors through the displayed `D(B)`-valued functor obtained by
first base changing to `\underline B` and then applying `L\pi_! : D(\underline B) \to D(B)`. This
is the statement that `L\pi_!(K)` acquires a canonical functorial `B`-module structure. -/
theorem derivedLowerShriekOnAbelianSheaves_factors_through_B_modules
    (α : chaoticRingSheaf 𝒪 ⟶ constantRingSheafOnCategory B)
    (structureModuleMap :
      SheafOfModules.unit (chaoticRingSheaf 𝒪) ⟶
        targetAsSourceModule α)
    (hUbullet : ∃ Ubullet : CosimplicialObject C,
      CosimplicialObjectHasPointlikeHomSpaces Ubullet)
    (derivedBaseChangeToConstant :
      DerivedCategory (moduleOnCategory 𝒪) ⥤
        DerivedCategory (@constantModuleCategory C _ _ B _))
    (constantModuleDerivedLowerShriek :
      DerivedCategory (@constantModuleCategory C _ _ B _) ⥤
        DerivedCategory (ModuleCat B))
    (forgetToAbelian :
      DerivedCategory (ModuleCat B) ⥤ DerivedCategory AddCommGrpCat.{u})
    (derivedLowerShriekOnAbelianSheaves :
      DerivedCategory (moduleOnCategory 𝒪) ⥤
        DerivedCategory AddCommGrpCat.{u})
    (hα : IsIso
      (derivedLowerShriekOnAbelianSheaves.map
        ((DerivedCategory.singleFunctor (moduleOnCategory 𝒪) (0 : ℤ)).map
          structureModuleMap))) :
    ∃ comparison :
      derivedLowerShriekOnAbelianSheaves ⟶
        derivedBaseChangeToConstant ⋙ constantModuleDerivedLowerShriek ⋙
          forgetToAbelian,
      ∀ K, IsIso (comparison.app K) := sorry

end

end CategoryTheory.ModulesOnCategory
