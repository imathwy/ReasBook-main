import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_12
import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open scoped DerivedTensorWithAlgebra

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

attribute [local instance] HasDerivedCategory.standard

local instance extendScalars_additive :
    (ModuleCat.extendScalars (algebraMap A B)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).left_adjoint_additive

/-- Helper for Lemma 15.65.13: flat scalar extension preserves finite limits, so exact extension
already acts on the derived category. -/
local instance extendScalars_preservesFiniteLimits [Module.Flat A B] :
    Limits.PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap A B)) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr (show Module.Flat A B from inferInstance))

/-- Helper for Lemma 15.65.13: under flatness, exact scalar extension is already a left-derived
functor of the homotopy-level scalar-extension bridge. -/
private theorem extendScalars_mapDerivedCategory_isLeftDerivedFunctor
    [Module.Flat A B] :
    ((ModuleCat.extendScalars (algebraMap A B)).mapDerivedCategory).IsLeftDerivedFunctor
      ((ModuleCat.extendScalars (algebraMap A B)).mapDerivedCategoryFactorsh.hom)
      (HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ)) := by
  let F : ModuleCat A ⥤ ModuleCat B := ModuleCat.extendScalars (algebraMap A B)
  -- Exact scalar extension inverts quasi-isomorphisms, so the exact derived functor is already
  -- the left-derived owner.
  simpa [F] using
    (Functor.isLeftDerivedFunctor_of_inverts
      (HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ))
      F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh)

/-- Helper for Lemma 15.65.13: flatness identifies the derived tensor owner with exact scalar
extension on the derived category. -/
private noncomputable def derivedTensorWithAlgebra_iso_mapDerivedCategory_of_flat
    (hflat : (algebraMap A B).Flat) :
    derivedTensorWithAlgebra (algebraMap A B) ≅
      (ModuleCat.extendScalars (algebraMap A B)).mapDerivedCategory :=
  letI : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hflat
  let F₀ : ModuleCat A ⥤ ModuleCat B := ModuleCat.extendScalars (algebraMap A B)
  let F : HomotopyCategory (ModuleCat A) (ComplexShape.up ℤ) ⥤ DModB :=
    F₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  letI :
      F.HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ)) :=
    extendScalarsToDerived_hasLeftDerivedFunctor (R := A) (A := B) (algebraMap A B)
  letI :
      F₀.mapDerivedCategory.IsLeftDerivedFunctor
        F₀.mapDerivedCategoryFactorsh.hom
        (HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ)) :=
    extendScalars_mapDerivedCategory_isLeftDerivedFunctor (A := A) (B := B)
  -- Compare the exact flat scalar-extension functor with the chosen total-left-derived owner.
  ((show F₀.mapDerivedCategory ≅ derivedTensorWithAlgebra (algebraMap A B) from
      Functor.leftDerivedNatIso
        F₀.mapDerivedCategory
        (F.totalLeftDerived
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat A) (ComplexShape.up ℤ) ⥤ DModA)
          (HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ)))
        F₀.mapDerivedCategoryFactorsh.hom
        (Functor.totalLeftDerivedCounit
          F
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat A) (ComplexShape.up ℤ) ⥤ DModA)
          (HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ)))
        (HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ))
        (Iso.refl F))).symm

/-- Helper for Lemma 15.65.13: exact scalar extension carries a degree-zero module to the
degree-zero complex of its ordinary scalar extension. -/
private noncomputable def extendScalars_single0_iso [Module.Flat A B]
    (M : ModuleCat A) :
    (((ModuleCat.extendScalars (algebraMap A B)).mapDerivedCategory).obj
      (ModuleCat.single0Functor.obj M)) ≅
      ModuleCat.single0Functor.obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) :=
  (((ModuleCat.extendScalars (algebraMap A B)).mapDerivedCategory).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M)) ≪≫
    (ModuleCat.extendScalars (algebraMap A B)).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapCochainComplexSingleFunctor
        (ModuleCat.extendScalars (algebraMap A B))
        (0 : ℤ)).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat B) (0 : ℤ)).app
      ((ModuleCat.extendScalars (algebraMap A B)).obj M)).symm

/-- Helper for Lemma 15.65.13: flat derived scalar extension of `M[0]` agrees with the degree-zero
object of the ordinary scalar extension of `M`. -/
private noncomputable def derivedTensorWithAlgebra_single0_extendScalars_iso
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A) :
    ((derivedTensorWithAlgebra (algebraMap A B)).obj (ModuleCat.single0Functor.obj M)) ≅
      ModuleCat.single0Functor.obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) :=
  letI : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hflat
  (derivedTensorWithAlgebra_iso_mapDerivedCategory_of_flat (A := A) (B := B) hflat).app
      (ModuleCat.single0Functor.obj M) ≪≫
    extendScalars_single0_iso (A := A) (B := B) M

/- Domain-style sampling for Lemma 15.65.13:
- primary domain: pseudo-coherent modules under flat scalar extension, viewed through their
  degree-zero images in the derived category;
- sampled owner declarations:
  `ModuleCat.single0Functor`,
  `DerivedCategory.IsMPseudoCoherent`,
  `derivedTensorWithAlgebra_isMPseudoCoherent`,
  `derivedTensorWithAlgebra_isPseudoCoherent`;
- best owner abstraction: the core/canonical owner is derived scalar extension
  `derivedTensorWithAlgebra A B : D(A) ⥤ D(B)`, while the module-level theorems below are flat
  `bridge/view` consequences obtained only after identifying `M[0] ⊗[A]^L B` with ordinary scalar
  extension of `M` in degree `0`;
- primitive vs. derived:
  primitive data are the ring map `A → B`, the flatness hypothesis, and the module `M` viewed as
  `(ModuleCat.single0Functor : ModuleCat A ⥤ DerivedCategory (ModuleCat A)).obj M : D(A)`;
  the ordinary module pseudo-coherence conclusions are derived API obtained from the owner
  theorems in Lemma `15.65.12` plus the flat degree-zero comparison;
- layer: `bridge/view`. The public statement should therefore be a flat bridge from the derived
  owner theorem, not an arbitrary ordinary base-change theorem. -/

-- Proof sketch: `M.IsMPseudoCoherent m` is definitionally `m`-pseudo-coherence of the degree-zero
-- owner object `(ModuleCat.single0Functor.obj M)`. Apply
-- `derivedTensorWithAlgebra_isMPseudoCoherent`, then use flatness of `A → B` to identify the
-- derived base change of that degree-zero object with the degree-zero object of
-- `(ModuleCat.extendScalars (algebraMap A B)).obj M`.
/-- Lemma 15.65.13: for a flat ring map `A → B`, if an `A`-module `M` is `m`-pseudo-coherent,
then its scalar extension `M \otimes_A B` is `m`-pseudo-coherent as a `B`-module. -/
theorem isMPseudoCoherent_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A) (m : ℤ)
    (hM : M.IsMPseudoCoherent m) :
    ((ModuleCat.extendScalars (algebraMap A B)).obj M).IsMPseudoCoherent m := by
  let P : ObjectProperty DModB := fun K ↦ K.IsMPseudoCoherent m
  have hderived :
      DerivedCategory.IsMPseudoCoherent
        ((derivedTensorWithAlgebra (algebraMap A B)).obj (ModuleCat.single0Functor.obj M)) m := by
    -- Apply the derived preservation theorem to the degree-zero owner of `M`.
    simpa [ModuleCat.IsMPseudoCoherent] using
      derivedTensorWithAlgebra_isMPseudoCoherent (ModuleCat.single0Functor.obj M) m hM
  have htarget :
      DerivedCategory.IsMPseudoCoherent
        (ModuleCat.single0Functor.obj ((ModuleCat.extendScalars (algebraMap A B)).obj M)) m := by
    -- Transport the derived conclusion across the flat comparison between derived and exact base
    -- change on degree-zero objects.
    exact
      P.prop_of_iso
        (derivedTensorWithAlgebra_single0_extendScalars_iso (A := A) (B := B) hflat M)
        hderived
  simpa [ModuleCat.IsMPseudoCoherent] using htarget

-- Proof sketch: specialize the derived pseudo-coherent preservation theorem to the degree-zero
-- owner of `M`, then transport across the same flat degree-zero comparison as above.
/-- For a flat ring map `A → B`, ordinary scalar extension preserves pseudo-coherent modules. -/
theorem isPseudoCoherent_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A)
    (hM : M.IsPseudoCoherent) :
    ((ModuleCat.extendScalars (algebraMap A B)).obj M).IsPseudoCoherent := by
  let P : ObjectProperty DModB := fun K ↦ K.IsPseudoCoherent
  have hderived :
      DerivedCategory.IsPseudoCoherent
        ((derivedTensorWithAlgebra (algebraMap A B)).obj (ModuleCat.single0Functor.obj M)) := by
    -- Apply the derived pseudo-coherent preservation theorem to the degree-zero owner of `M`.
    simpa [ModuleCat.IsPseudoCoherent] using
      derivedTensorWithAlgebra_isPseudoCoherent (ModuleCat.single0Functor.obj M) hM
  have htarget :
      DerivedCategory.IsPseudoCoherent
        (ModuleCat.single0Functor.obj ((ModuleCat.extendScalars (algebraMap A B)).obj M)) := by
    -- Transport the derived conclusion across the same flat comparison used in the bounded case.
    exact
      P.prop_of_iso
        (derivedTensorWithAlgebra_single0_extendScalars_iso (A := A) (B := B) hflat M)
        hderived
  simpa [ModuleCat.IsPseudoCoherent] using htarget

end

end CategoryTheory
