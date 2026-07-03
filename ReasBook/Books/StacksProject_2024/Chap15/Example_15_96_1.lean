import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open HomologicalComplex
open ZeroObject
open scoped nonZeroDivisors

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

local notation "KModA" => HomotopyCategory (ModuleCat A) (ComplexShape.up ℤ)

/- Domain-style sampling for Example 15.96.1:
- primary domain: homotopy categories of cochain complexes in full subcategories of `ModuleCat A`,
  with the counterexample triangle built from the full subcategory of `f`-torsion-free
  `A`-modules and compared to the ambient homotopy category via the canonical inclusion;
- sampled owner declarations:
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.ι`,
  `Functor.mapHomotopyCategory`,
  `HomotopyCategory.singleFunctor`,
  `HomotopyCategory.singleFunctors.shiftIso`;
- best owner abstraction:
  `source-facing`: the counterexample triangle in
    `HomotopyCategory ((fTorsionFreeModuleProperty f).FullSubcategory) (up ℤ)`;
  `core/canonical`: the object property `fTorsionFreeModuleProperty f` together with
    `ObjectProperty.FullSubcategory` and the inclusion functor `ObjectProperty.ι`;
  `bridge/view`: the induced comparison triangle in `K(A`-modules)` obtained from
    `((fTorsionFreeModuleProperty f).ι).mapHomotopyCategory (up ℤ)`;
- primitive data: the `f`-torsion-free module objects `A` and `(f)` and the displayed morphisms
  between them in the full subcategory;
- derived API: the source-facing counterexample triangle and its ambient image triangle. -/

/-- The object property of `A`-modules on which multiplication by `f` is injective. -/
abbrev fTorsionFreeModuleProperty (f : A) : ObjectProperty (ModuleCat A) :=
  fun M ↦ IsSMulRegular M f

instance fTorsionFreeModuleProperty_containsZero (f : A) :
    (fTorsionFreeModuleProperty f).ContainsZero where
  exists_zero := by
    refine ⟨ModuleCat.of A PUnit, ModuleCat.isZero_of_subsingleton _, ?_⟩
    change IsSMulRegular PUnit f
    rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro x _
    simp

/-- The `f`-torsion-free module property is stable under isomorphism. -/
instance fTorsionFreeModuleProperty_isClosedUnderIsomorphisms (f : A) :
    (fTorsionFreeModuleProperty f).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    change IsSMulRegular X f at hX
    change IsSMulRegular Y f
    rw [isSMulRegular_iff_right_eq_zero_of_smul] at hX ⊢
    intro y hy
    have hpre : f • e.inv.hom y = 0 := by
      simpa using congrArg e.inv.hom hy
    have hzero : e.inv.hom y = 0 := hX _ hpre
    simpa using congrArg e.hom.hom hzero

/-- The `f`-torsion-free module property is closed under binary products. -/
instance fTorsionFreeModuleProperty_isClosedUnderBinaryProducts (f : A) :
    (fTorsionFreeModuleProperty f).IsClosedUnderBinaryProducts := by
  constructor
  rintro X ⟨p⟩
  let F := p.diag
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  let P : ModuleCat A := ModuleCat.of A (X × Y)
  have hP : fTorsionFreeModuleProperty f P := by
    change IsSMulRegular (X × Y) f
    rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro x hx
    refine Prod.ext
      ((isSMulRegular_iff_right_eq_zero_of_smul.mp (p.prop_diag_obj ⟨WalkingPair.left⟩)) x.1 (by
        simpa using congrArg Prod.fst hx))
      ((isSMulRegular_iff_right_eq_zero_of_smul.mp (p.prop_diag_obj ⟨WalkingPair.right⟩)) x.2 (by
        simpa using congrArg Prod.snd hx))
  let fstProj : P ⟶ X := ModuleCat.ofHom (LinearMap.fst A X Y)
  let sndProj : P ⟶ Y := ModuleCat.ofHom (LinearMap.snd A X Y)
  let productFan : BinaryFan X Y := BinaryFan.mk fstProj sndProj
  have hProductFan : IsLimit productFan :=
    BinaryFan.isLimitMk
      (fun s ↦ ModuleCat.ofHom (LinearMap.prod s.fst.hom s.snd.hom))
      (fun s ↦ by
        apply ModuleCat.hom_ext
        change (LinearMap.fst A X Y).comp (LinearMap.prod s.fst.hom s.snd.hom) = s.fst.hom
        exact LinearMap.fst_prod s.fst.hom s.snd.hom)
      (fun s ↦ by
        apply ModuleCat.hom_ext
        change (LinearMap.snd A X Y).comp (LinearMap.prod s.fst.hom s.snd.hom) = s.snd.hom
        exact LinearMap.snd_prod s.fst.hom s.snd.hom)
      (fun s m hm₁ hm₂ ↦ by
        apply ModuleCat.hom_ext
        ext x
        · simpa using congrFun (congrArg (fun k ↦ k.hom) hm₁) x
        · simpa using congrFun (congrArg (fun k ↦ k.hom) hm₂) x)
  let hProductFan' : IsLimit ((Cone.postcompose (diagramIsoPair F).hom).obj p.cone) :=
    (IsLimit.postcomposeHomEquiv (diagramIsoPair F) _).2 p.isLimit
  exact (fTorsionFreeModuleProperty f).prop_of_iso
    (IsLimit.conePointUniqueUpToIso hProductFan' hProductFan).symm hP

/-- In the additive full subcategory of `f`-torsion-free `A`-modules, binary products are binary
biproducts. -/
instance ftorsionFreeModuleCat_hasBinaryBiproducts (f : A) :
    HasBinaryBiproducts ((fTorsionFreeModuleProperty f).FullSubcategory) :=
  HasBinaryBiproducts.of_hasBinaryProducts

variable (f : A)

private abbrev FTorsionFreeModuleCat (f : A) :=
  ObjectProperty.FullSubcategory (fTorsionFreeModuleProperty f)

private abbrev FTorsionFreeHomotopyCat (f : A) :=
  HomotopyCategory (FTorsionFreeModuleCat f) (ComplexShape.up ℤ)

private abbrev ftorsionFreeHomotopyInclusion (f : A) :=
  (ObjectProperty.ι (fTorsionFreeModuleProperty f)).mapHomotopyCategory (ComplexShape.up ℤ)

private abbrev moduleHomotopyQuotient :
    CochainComplex (ModuleCat A) ℤ ⥤ KModA :=
  HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)

private abbrev fTorsionFreeHomotopyQuotient (f : A) :
    CochainComplex (FTorsionFreeModuleCat f) ℤ ⥤ FTorsionFreeHomotopyCat f :=
  HomotopyCategory.quotient (FTorsionFreeModuleCat f) (ComplexShape.up ℤ)

/-- The principal ideal `(f)` viewed as an object of `ModuleCat A`. -/
private abbrev principalIdealObject (f : A) : ModuleCat A :=
  ModuleCat.of A (principalIdeal f)

/-- Multiplication by `f` as a map `A ⟶ (f)`. -/
private abbrev principalIdealMulToObject (f : A) : ModuleCat.of A A ⟶ principalIdealObject f :=
  ModuleCat.ofHom
    (LinearMap.toSpanSingleton A (principalIdealObject f)
      (⟨f, by
        show f ∈ principalIdeal f
        simpa [principalIdeal] using Ideal.subset_span (by simp : f ∈ ({f} : Set A))⟩ :
        principalIdealObject f))

/-- Multiplication by `f` on the principal ideal `(f)`. -/
private abbrev principalIdealSelfMul (f : A) : principalIdealObject f ⟶ principalIdealObject f :=
  ModuleCat.ofHom (f • LinearMap.id)

private theorem principalIdealMul_bijective_of_mem_nonZeroDivisors
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    Function.Bijective (principalIdealMulToObject f).hom := sorry

/-- The isomorphism `A ≅ (f)` induced by multiplication by a nonzerodivisor `f`. -/
private noncomputable def principalIdealMulIso (f : A) (hf : f ∈ nonZeroDivisors A) :
    ModuleCat.of A A ≅ principalIdealObject f :=
  (LinearEquiv.ofBijective (principalIdealMulToObject f).hom
    (principalIdealMul_bijective_of_mem_nonZeroDivisors f hf)).toModuleIso

/-- The free rank-one module `A`, viewed as an object of the full subcategory of `f`-torsion-free
modules. -/
private abbrev etaCounterexampleSourceModule (f : A) (hf : f ∈ nonZeroDivisors A) :
    FTorsionFreeModuleCat f :=
  ⟨ModuleCat.of A A, by
    simpa using (Module.Flat.isSMulRegular_of_nonZeroDivisors hf : IsSMulRegular A f)⟩

/-- The principal ideal `(f)` as an object of the full subcategory of `f`-torsion-free
modules. -/
private abbrev etaCounterexampleIdealModule (f : A) (hf : f ∈ nonZeroDivisors A) :
    FTorsionFreeModuleCat f :=
  ⟨principalIdealObject f, by
    change IsSMulRegular (principalIdeal f) f
    simpa using IsSMulRegular.submodule (principalIdeal f) f
      (Module.Flat.isSMulRegular_of_nonZeroDivisors hf : IsSMulRegular A f)⟩

/-- Multiplication by `f : A → (f)` in the full subcategory of `f`-torsion-free modules. -/
private abbrev principalIdealMulToFTorsionFreeModule (f : A) (hf : f ∈ nonZeroDivisors A) :
    etaCounterexampleSourceModule f hf ⟶ etaCounterexampleIdealModule f hf :=
  (fTorsionFreeModuleProperty f).homMk (principalIdealMulToObject f)

/-- Multiplication by `f` on `(f)` in the full subcategory of `f`-torsion-free modules. -/
private abbrev principalIdealSelfMulFTorsionFreeModule
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    etaCounterexampleIdealModule f hf ⟶ etaCounterexampleIdealModule f hf :=
  (fTorsionFreeModuleProperty f).homMk (principalIdealSelfMul f)

/-- The relation `0 ⟶ 1` in `ComplexShape.up ℤ`. -/
private abbrev etaCounterexample_rel : (ComplexShape.up ℤ).Rel (0 : ℤ) 1 := rfl

/-- The third displayed `η_f`-image complex `A → (f)` in degrees `0` and `1`. -/
private abbrev etaCounterexampleConeComplex (f : A) : CochainComplex (ModuleCat A) ℤ :=
  double (principalIdealMulToObject f) etaCounterexample_rel

/-- The cone object of the `η_f` counterexample triangle in the homotopy category. -/
private abbrev etaCounterexampleConeObj (f : A) : KModA :=
  moduleHomotopyQuotient.obj (etaCounterexampleConeComplex f)

private theorem etaCounterexampleCone_isZero (f : A) (hf : f ∈ nonZeroDivisors A) :
    IsZero (etaCounterexampleConeObj f) := sorry

private theorem etaCounterexampleFirstMap_isUnit_of_isIso (f : A)
    (hiso : IsIso ((HomotopyCategory.singleFunctor (ModuleCat A) (1 : ℤ)).map
      (principalIdealSelfMul f))) :
    IsUnit f := sorry

/-- The first displayed `η_f`-image complex in `K(f`-torsion free `A`-modules)`, concentrated in
degree `1` with value `(f)`. -/
private abbrev etaCounterexampleFTorsionFreeIdealComplex
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    CochainComplex (FTorsionFreeModuleCat f) ℤ :=
  (CochainComplex.singleFunctor (FTorsionFreeModuleCat f) (1 : ℤ)).obj
    (etaCounterexampleIdealModule f hf)

/-- The third displayed `η_f`-image complex `A → (f)` in `K(f`-torsion free `A`-modules)`. -/
private abbrev etaCounterexampleFTorsionFreeConeComplex
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    CochainComplex (FTorsionFreeModuleCat f) ℤ :=
  double (principalIdealMulToFTorsionFreeModule f hf) etaCounterexample_rel

/-- The fourth displayed `η_f`-image complex in `K(f`-torsion free `A`-modules)`, concentrated in
degree `0` with value `A`. -/
private abbrev etaCounterexampleFTorsionFreeShiftedSourceComplex
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    CochainComplex (FTorsionFreeModuleCat f) ℤ :=
  (CochainComplex.singleFunctor (FTorsionFreeModuleCat f) (0 : ℤ)).obj
    (etaCounterexampleSourceModule f hf)

private theorem etaCounterexampleFTorsionFreeSecondMap_comm
    (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ)
    (hi : (ComplexShape.up ℤ).Rel (1 : ℤ) i) :
    (doubleXIso₁ (principalIdealMulToFTorsionFreeModule f hf) etaCounterexample_rel
      (by decide)).inv ≫ (etaCounterexampleFTorsionFreeConeComplex f hf).d 1 i = 0 := sorry

private noncomputable abbrev etaCounterexampleFTorsionFreeSecondMap
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    etaCounterexampleFTorsionFreeIdealComplex f hf ⟶
      etaCounterexampleFTorsionFreeConeComplex f hf :=
  mkHomFromSingle
    ((doubleXIso₁ (principalIdealMulToFTorsionFreeModule f hf)
      etaCounterexample_rel (by decide)).inv)
    (etaCounterexampleFTorsionFreeSecondMap_comm f hf)

private theorem etaCounterexampleFTorsionFreeThirdMap_comm
    (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ)
    (hi : (ComplexShape.up ℤ).Rel i (0 : ℤ)) :
    (etaCounterexampleFTorsionFreeConeComplex f hf).d i 0 ≫
      (-(doubleXIso₀ (principalIdealMulToFTorsionFreeModule f hf)
        etaCounterexample_rel).hom) = 0 := sorry

private noncomputable abbrev etaCounterexampleFTorsionFreeThirdMap
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    etaCounterexampleFTorsionFreeConeComplex f hf ⟶
      etaCounterexampleFTorsionFreeShiftedSourceComplex f hf :=
  mkHomToSingle
    (-(doubleXIso₀ (principalIdealMulToFTorsionFreeModule f hf)
      etaCounterexample_rel).hom)
    (etaCounterexampleFTorsionFreeThirdMap_comm f hf)

private noncomputable def etaCounterexampleShiftIso (f : A) (hf : f ∈ nonZeroDivisors A) :
    (HomotopyCategory.singleFunctor (FTorsionFreeModuleCat f) (0 : ℤ)).obj
        (etaCounterexampleSourceModule f hf) ≅
      ((HomotopyCategory.singleFunctor (FTorsionFreeModuleCat f) (1 : ℤ)).obj
        (etaCounterexampleIdealModule f hf))⟦(1 : ℤ)⟧ :=
  ((HomotopyCategory.singleFunctor (FTorsionFreeModuleCat f) (0 : ℤ)).mapIso
      ((fTorsionFreeModuleProperty f).isoMk (principalIdealMulIso f hf))) ≪≫
    (((HomotopyCategory.singleFunctors (FTorsionFreeModuleCat f)).shiftIso
      (1 : ℤ) (0 : ℤ) (1 : ℤ) (by simp)).symm.app (etaCounterexampleIdealModule f hf))

/-- The source-facing triangle of Example `15.96.1` in `K(f`-torsion free `A`-modules)`. -/
noncomputable def etaCounterexampleTriangle (f : A) (hf : f ∈ nonZeroDivisors A) :
    Triangle
      (HomotopyCategory ((fTorsionFreeModuleProperty f).FullSubcategory) (ComplexShape.up ℤ)) :=
  Triangle.mk
    ((HomotopyCategory.singleFunctor (FTorsionFreeModuleCat f) (1 : ℤ)).map
      (principalIdealSelfMulFTorsionFreeModule f hf))
    ((fTorsionFreeHomotopyQuotient f).map (etaCounterexampleFTorsionFreeSecondMap f hf))
    (((fTorsionFreeHomotopyQuotient f).map (etaCounterexampleFTorsionFreeThirdMap f hf)) ≫
      (etaCounterexampleShiftIso f hf).hom)

/-- The ambient comparison triangle in `K(A\text{-modules})`, obtained by applying the inclusion
`K(f`-torsion free `A`-modules) ⥤ K(A`-modules)` to the source-facing triangle. -/
noncomputable abbrev etaCounterexampleImageTriangle (f : A) (hf : f ∈ nonZeroDivisors A) :
    Triangle KModA :=
  (ftorsionFreeHomotopyInclusion f).mapTriangle.obj (etaCounterexampleTriangle f hf)

theorem etaCounterexample_distinguished_implies_isUnit (f : A) (hf : f ∈ nonZeroDivisors A)
    (hT : etaCounterexampleImageTriangle f hf ∈ distTriang KModA) :
    IsUnit f := sorry

theorem etaCounterexampleAmbient_not_distinguished_of_nonunit (f : A) (hf : f ∈ nonZeroDivisors A)
    (hunit : ¬ IsUnit f) :
    etaCounterexampleImageTriangle f hf ∉ distTriang KModA := sorry

theorem etaCounterexample_not_distinguished_of_nonunit (f : A) (hf : f ∈ nonZeroDivisors A)
    (hunit : ¬ IsUnit f) :
    etaCounterexampleTriangle f hf ∉
      distTriang
        (HomotopyCategory ((fTorsionFreeModuleProperty f).FullSubcategory) (ComplexShape.up ℤ)) :=
  by
  intro hT
  have hImage :
      etaCounterexampleImageTriangle f hf ∈ distTriang KModA := by
    simpa [etaCounterexampleImageTriangle] using
      (ftorsionFreeHomotopyInclusion f).map_distinguished (etaCounterexampleTriangle f hf) hT
  exact etaCounterexampleAmbient_not_distinguished_of_nonunit f hf hunit hImage

end
