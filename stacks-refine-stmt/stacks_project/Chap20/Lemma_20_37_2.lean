import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated
open CategoryTheory.Limits
open ComplexShape
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory

section

variable {D : Type u} [Category D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The family of objects underlying a sequential inverse system in a category. -/
abbrev inverseSystemFamily (Ksys : ℕᵒᵖ ⥤ D) : ℕ → D :=
  fun n ↦ Ksys.obj (Opposite.op n)

/-- The Milnor difference endomorphism of the product of a sequential inverse system. -/
def derivedLimitDifferenceMap (Ksys : ℕᵒᵖ ⥤ D)
    [HasProduct (inverseSystemFamily Ksys)] :
    ∏ᶜ inverseSystemFamily Ksys ⟶ ∏ᶜ inverseSystemFamily Ksys :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily Ksys) n -
      Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
        Ksys.map ((homOfLE (Nat.le_succ n)).op)

/-- An object is a derived limit of a sequential inverse system if it fits into the standard
Milnor distinguished triangle built from the product and the difference map `1 - shift`. -/
def IsDerivedLimit (Ksys : ℕᵒᵖ ⥤ D) (K : D) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily Ksys),
    ∃ (ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys)
      (δ : ∏ᶜ inverseSystemFamily Ksys ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ ∈ distTriang D

end

end CategoryTheory

namespace AlgebraicGeometry.RingedSpace

section

/-- The structure sheaf of a ringed space, regarded as a `RingCat`-valued sheaf. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
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

/-- The quasi-isomorphisms used to construct the derived category of `\mathcal O_X`-modules. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The cochain-level direct image functor followed by localization to the derived category. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive] :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  (modulePushforward f).mapHomologicalComplex (up ℤ) ⋙
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules Y) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y))

/-- The derived direct-image functor `Rf_* : D(\mathcal O_X) ⥤ D(\mathcal O_Y)`. -/
abbrev moduleDerivedPushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  (modulePushforwardToDerived f).totalRightDerived
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
    (ModuleQis X)

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor (DerivedCategory (RingedSpace.Modules X)) n)]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor (DerivedCategory (RingedSpace.Modules Y)) n)]
variable [(modulePushforward f).Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

-- Proof sketch: the usual derived pullback `Lf^*` is left adjoint to `Rf_*`, so `Rf_*` is a
-- right adjoint and therefore preserves all small limits.
/-- The derived pushforward functor is a right adjoint. -/
theorem moduleDerivedPushforward_isRightAdjoint :
    (moduleDerivedPushforward f).IsRightAdjoint := sorry

-- Proof sketch: choose the Milnor triangle defining `R lim K_n`, apply the exact functor
-- `Rf_*`, and use that `Rf_*` preserves products because it is a right adjoint. The resulting
-- triangle is again the defining Milnor triangle, now for the inverse system obtained by applying
-- `Rf_*` termwise.
/-- Lemma 20.37.2: if `K` is a derived limit of an inverse system `Ksys` in `D(\mathcal O_X)`,
then `Rf_* K` is a derived limit of the termwise direct-image system. Equivalently, the derived
pushforward functor `Rf_*` commutes with derived limits. -/
theorem moduleDerivedPushforward_preservesDerivedLimits
    {Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSpace.Modules X)}
    {K : DerivedCategory (RingedSpace.Modules X)}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit (Ksys ⋙ moduleDerivedPushforward f) ((moduleDerivedPushforward f).obj K) := sorry

end

end AlgebraicGeometry.RingedSpace
