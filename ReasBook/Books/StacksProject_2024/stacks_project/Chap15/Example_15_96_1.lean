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

instance fTorsionFreeModuleProperty_containsZero (f : A) :
    (fTorsionFreeModuleProperty f).ContainsZero where
  exists_zero := by
    let Z : ModuleCat A := ModuleCat.of A PUnit
    have hZ : IsZero Z := ModuleCat.isZero_of_subsingleton _
    have hprop : fTorsionFreeModuleProperty f Z := by
      change IsSMulRegular PUnit f
      rw [isSMulRegular_iff_right_eq_zero_of_smul]
      intro x _
      simp
    exact ⟨0, isZero_zero _, (fTorsionFreeModuleProperty f).prop_of_iso
      (hZ.iso (isZero_zero _)) hprop⟩


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

/-- Helper for Example 15.96.1: the zero object in the full subcategory of `f`-torsion-free
modules is represented by the ambient zero `A`-module. -/
instance (priority := 10000) ftorsionFreeModuleCat_zero (f : A) :
    Zero (FTorsionFreeModuleCat f) where
  zero := ⟨0, ObjectProperty.prop_zero (fTorsionFreeModuleProperty f)⟩

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

/-- Helper for Example 15.96.1: the chosen zero object of the full subcategory forgets to the
ambient zero object. -/
private theorem ftorsionFreeModuleCat_zero_obj_eq (f : A) :
    FullSubcategory.obj (0 : FTorsionFreeModuleCat f) = (0 : ModuleCat A) :=
  rfl

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

/-- Helper for Example 15.96.1: multiplication by a nonzerodivisor identifies `A` with the
principal ideal `(f)`. -/
private theorem principalIdealMul_bijective_of_mem_nonZeroDivisors
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    Function.Bijective (principalIdealMulToObject f).hom := by
  constructor
  · intro x y hxy
    -- Compare the underlying elements in `A` and use that `f` is a nonzerodivisor.
    have hxy_val :
        (((principalIdealMulToObject f).hom x : principalIdeal f) : A) =
          (((principalIdealMulToObject f).hom y : principalIdeal f) : A) := by
      exact congrArg Subtype.val hxy
    have hsub : (x - y) * f = 0 := by
      simpa [principalIdealMulToObject, LinearMap.toSpanSingleton, sub_mul] using
        sub_eq_zero.mpr hxy_val
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_right.mp hf) _ hsub)
  · intro x
    -- Every element of `(f)` is by definition a scalar multiple of `f`.
    rcases Submodule.mem_span_singleton.mp x.2 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    simpa [principalIdealMulToObject, LinearMap.toSpanSingleton] using ha

/-- The isomorphism `A ≅ (f)` induced by multiplication by a nonzerodivisor `f`. -/
private noncomputable def principalIdealMulIso (f : A) (hf : f ∈ nonZeroDivisors A) :
    ModuleCat.of A A ≅ principalIdealObject f :=
  (LinearEquiv.ofBijective (principalIdealMulToObject f).hom
    (principalIdealMul_bijective_of_mem_nonZeroDivisors f hf)).toModuleIso

/-- Helper for Example 15.96.1: the forward map of `principalIdealMulIso` is the explicit
multiplication map `A ⟶ (f)`. -/
private theorem principalIdealMulIso_hom
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    (principalIdealMulIso f hf).hom = principalIdealMulToObject f :=
  rfl

/-- Helper for Example 15.96.1: under the identification `A ≅ (f)`, multiplication by `f` on
`A` corresponds to multiplication by `f` on the principal ideal `(f)`. -/
private theorem principalIdealMulIso_naturality
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    ModuleCat.ofHom ((f : A) • (LinearMap.id : A →ₗ[A] A)) ≫ (principalIdealMulIso f hf).hom =
      (principalIdealMulIso f hf).hom ≫ principalIdealSelfMul f := by
  -- Reduce to the explicit `A ⟶ (f)` map and compare both sides on elements.
  rw [principalIdealMulIso_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp [principalIdealMulToObject, principalIdealSelfMul, mul_assoc]

/-- Helper for Example 15.96.1: the inverse of `A ≅ (f)` intertwines multiplication by `f` in the
opposite direction. -/
private theorem principalIdealMulIso_inv_naturality
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    (principalIdealMulIso f hf).inv ≫ ModuleCat.ofHom ((f : A) • (LinearMap.id : A →ₗ[A] A)) =
      principalIdealSelfMul f ≫ (principalIdealMulIso f hf).inv := by
  -- Cancel the isomorphism on the right and reuse the forward naturality identity.
  apply (cancel_mono (principalIdealMulIso f hf).hom).1
  calc
    ((principalIdealMulIso f hf).inv ≫
        ModuleCat.ofHom ((f : A) • (LinearMap.id : A →ₗ[A] A))) ≫
          (principalIdealMulIso f hf).hom
        = (principalIdealMulIso f hf).inv ≫
            (ModuleCat.ofHom ((f : A) • (LinearMap.id : A →ₗ[A] A)) ≫
              (principalIdealMulIso f hf).hom) := by
            simp [Category.assoc]
    _ = (principalIdealMulIso f hf).inv ≫
          ((principalIdealMulIso f hf).hom ≫ principalIdealSelfMul f) := by
          rw [principalIdealMulIso_naturality]
    _ = principalIdealSelfMul f := by
          simp
    _ = (principalIdealSelfMul f ≫ (principalIdealMulIso f hf).inv) ≫
          (principalIdealMulIso f hf).hom := by
          simp

/-- Helper for Example 15.96.1: if multiplication by `f` on `(f)` is an isomorphism and `f` is a
nonzerodivisor, then `f` is a unit. -/
private theorem isUnit_of_isIso_principalIdealSelfMul
    (f : A) (hf : f ∈ nonZeroDivisors A) [IsIso (principalIdealSelfMul f)] :
    IsUnit f := by
  let φ : ModuleCat.of A A ⟶ ModuleCat.of A A :=
    (principalIdealMulIso f hf).hom ≫ inv (principalIdealSelfMul f) ≫
      (principalIdealMulIso f hf).inv
  have hright : φ ≫ ModuleCat.ofHom ((f : A) • (LinearMap.id : A →ₗ[A] A)) = 𝟙 _ := by
    -- Conjugate the inverse of multiplication on `(f)` back to `A`.
    calc
      φ ≫ ModuleCat.ofHom ((f : A) • (LinearMap.id : A →ₗ[A] A))
          = (principalIdealMulIso f hf).hom ≫
              (inv (principalIdealSelfMul f) ≫
                ((principalIdealMulIso f hf).inv ≫
                  ModuleCat.ofHom ((f : A) • (LinearMap.id : A →ₗ[A] A)))) := by
              simp [φ, Category.assoc]
      _ = (principalIdealMulIso f hf).hom ≫
            (inv (principalIdealSelfMul f) ≫
              (principalIdealSelfMul f ≫ (principalIdealMulIso f hf).inv)) := by
            rw [principalIdealMulIso_inv_naturality]
      _ = (principalIdealMulIso f hf).hom ≫ (principalIdealMulIso f hf).inv := by
            simp
      _ = 𝟙 _ := by simp
  have hmul_linear :
      ((φ ≫ ModuleCat.ofHom ((f : A) • (LinearMap.id : A →ₗ[A] A))).hom) (1 : A) = 1 := by
    -- Evaluate the right-inverse identity at `1`.
    exact congrArg (fun g : A →ₗ[A] A ↦ g 1) (congrArg ModuleCat.Hom.hom hright)
  have hmul :
      f * (φ.hom (1 : A)) = 1 := by
    simpa [Category.assoc, LinearMap.smul_apply] using hmul_linear
  exact IsUnit.of_mul_eq_one_right (φ.hom (1 : A)) (by simpa [mul_comm] using hmul)

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

/-- Helper for Example 15.96.1: the degree-`0` term of the ambient cone complex is `A`. -/
private noncomputable abbrev etaCounterexampleConeDegreeZeroIso (f : A) :
    (etaCounterexampleConeComplex f).X 0 ≅ ModuleCat.of A A :=
  doubleXIso₀ (principalIdealMulToObject f) etaCounterexample_rel

/-- Helper for Example 15.96.1: the degree-`1` term of the ambient cone complex is `(f)`. -/
private noncomputable abbrev etaCounterexampleConeDegreeOneIso (f : A) :
    (etaCounterexampleConeComplex f).X 1 ≅ principalIdealObject f :=
  doubleXIso₁ (principalIdealMulToObject f) etaCounterexample_rel (by decide)

/-- Helper for Example 15.96.1: the unique nonzero differential of the ambient cone complex is
the explicit multiplication map `A ⟶ (f)`. -/
private theorem etaCounterexampleConeComplex_d_eq (f : A) :
    (etaCounterexampleConeDegreeZeroIso f).inv ≫
        (etaCounterexampleConeComplex f).d 0 1 ≫
        (etaCounterexampleConeDegreeOneIso f).hom =
      principalIdealMulToObject f := by
  -- The `double` owner places the chosen map in the unique active degree `0 → 1`.
  simp [etaCounterexampleConeComplex, etaCounterexampleConeDegreeZeroIso,
    etaCounterexampleConeDegreeOneIso, HomologicalComplex.double_d]

/-- Helper for Example 15.96.1: the identity of the ambient cone complex `A ⟶ (f)` is
null-homotopic via the inverse of the multiplication isomorphism `A ≅ (f)`. -/
private theorem etaCounterexampleCone_null_homotopy (f : A) (hf : f ∈ nonZeroDivisors A) :
    Nonempty (Homotopy (𝟙 (etaCounterexampleConeComplex f)) 0) := by
  -- Route correction: keep the source-faithful contraction, but package it directly with
  -- `Homotopy.mk` so the only active component is the inverse of the unique differential.
  let hom : (i j : ℤ) → (etaCounterexampleConeComplex f).X i ⟶ (etaCounterexampleConeComplex f).X j :=
    fun i j ↦
      if hi : i = 1 then
        if hj : j = 0 then by
          subst hi
          subst hj
          exact (etaCounterexampleConeDegreeOneIso f).hom ≫
            (principalIdealMulIso f hf).inv ≫
            (etaCounterexampleConeDegreeZeroIso f).inv
        else
          0
      else
        0
  refine ⟨Homotopy.mk hom ?_ ?_⟩
  · intro i j hij
    by_cases hi : i = 1
    · subst hi
      by_cases hj : j = 0
      · exfalso
        exact hij (by simpa [hj] using etaCounterexample_rel)
      · simp [hom, hj]
    · simp [hom, hi]
  · intro i
    by_cases hi0 : i = 0
    · subst hi0
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (0 : ℤ) 1 by simpa using etaCounterexample_rel),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1 : ℤ) 0 by simp)]
      -- In degree `0`, only the composite `d ≫ h` survives, and it is the identity.
      have hdeg0 :
          𝟙 ((etaCounterexampleConeComplex f).X 0) =
            (etaCounterexampleConeComplex f).d 0 1 ≫ hom 1 0 := by
        symm
        calc
          (etaCounterexampleConeComplex f).d 0 1 ≫ hom 1 0
              = ((etaCounterexampleConeComplex f).d 0 1 ≫
                  (etaCounterexampleConeDegreeOneIso f).hom) ≫
                    (principalIdealMulIso f hf).inv ≫
                      (etaCounterexampleConeDegreeZeroIso f).inv := by
                  simp [hom, Category.assoc]
          _ = ((etaCounterexampleConeDegreeZeroIso f).hom ≫ principalIdealMulToObject f) ≫
                (principalIdealMulIso f hf).inv ≫
                  (etaCounterexampleConeDegreeZeroIso f).inv := by
                simpa [Category.assoc] using congrArg
                  (fun k =>
                    (etaCounterexampleConeDegreeZeroIso f).hom ≫ k ≫
                      (principalIdealMulIso f hf).inv ≫
                        (etaCounterexampleConeDegreeZeroIso f).inv)
                  (etaCounterexampleConeComplex_d_eq f)
          _ = 𝟙 ((etaCounterexampleConeComplex f).X 0) := by
                rw [← principalIdealMulIso_hom f hf]
                simp [Category.assoc]
      simpa [hom] using hdeg0
    · by_cases hi1 : i = 1
      · subst hi1
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (1 : ℤ) 2 by simp),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (0 : ℤ) 1 by simpa using etaCounterexample_rel)]
        -- In degree `1`, the unsupported `2 → 1` component vanishes, so only `h ≫ d` remains.
        have hdeg1 :
            𝟙 ((etaCounterexampleConeComplex f).X 1) =
              hom 1 0 ≫ (etaCounterexampleConeComplex f).d 0 1 := by
          symm
          calc
            hom 1 0 ≫ (etaCounterexampleConeComplex f).d 0 1
                = (etaCounterexampleConeDegreeOneIso f).hom ≫
                    (principalIdealMulIso f hf).inv ≫
                      ((etaCounterexampleConeDegreeZeroIso f).inv ≫
                        (etaCounterexampleConeComplex f).d 0 1) := by
                    simp [hom, Category.assoc]
            _ = (etaCounterexampleConeDegreeOneIso f).hom ≫
                  (principalIdealMulIso f hf).inv ≫
                    (principalIdealMulToObject f ≫
                      (etaCounterexampleConeDegreeOneIso f).inv) := by
                  simpa [Category.assoc] using congrArg
                    (fun k =>
                      (etaCounterexampleConeDegreeOneIso f).hom ≫
                        (principalIdealMulIso f hf).inv ≫ k ≫
                          (etaCounterexampleConeDegreeOneIso f).inv)
                    (etaCounterexampleConeComplex_d_eq f)
            _ = 𝟙 ((etaCounterexampleConeComplex f).X 1) := by
                  rw [← principalIdealMulIso_hom f hf]
                  simp
        simpa [hom] using hdeg1
      -- Away from degrees `0` and `1`, the double complex is zero, so both sides vanish.
      let hzero : Limits.IsZero ((etaCounterexampleConeComplex f).X i) := by
        simpa [etaCounterexampleConeComplex] using
          (HomologicalComplex.isZero_double_X
            (principalIdealMulToObject f) etaCounterexample_rel i hi0 hi1)
      have hself_zero :
          ((𝟙 (etaCounterexampleConeComplex f) :
            etaCounterexampleConeComplex f ⟶ etaCounterexampleConeComplex f)).f i = 0 :=
        hzero.eq_of_tgt _ 0
      have hrhs_zero :
          (etaCounterexampleConeComplex f).d i (i + 1) ≫ hom (i + 1) i +
              hom i (i - 1) ≫ (etaCounterexampleConeComplex f).d (i - 1) i = 0 :=
        hzero.eq_of_tgt _ 0
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
      rw [hself_zero, hrhs_zero]
      simpa

/-- Helper for Example 15.96.1: the ambient cone complex `A ⟶ (f)` is contractible when `f` is a
nonzerodivisor. -/
private theorem etaCounterexampleCone_isZero (f : A) (hf : f ∈ nonZeroDivisors A) :
    IsZero (etaCounterexampleConeObj f) := by
  -- Pass from the explicit null-homotopy of the identity to vanishing in the quotient.
  exact (HomotopyCategory.isZero_quotient_obj_iff _).2 (etaCounterexampleCone_null_homotopy f hf)

/-- Helper for Example 15.96.1: if multiplication by `f` on the degree-`1` single complex is an
isomorphism in the homotopy category, then `f` is a unit. -/
private theorem etaCounterexampleFirstMap_isUnit_of_isIso (f : A)
    (hf : f ∈ nonZeroDivisors A)
    (hiso : IsIso ((HomotopyCategory.singleFunctor (ModuleCat A) (1 : ℤ)).map
      (principalIdealSelfMul f))) :
    IsUnit f := by
  -- Route correction: the old statement was false without `hf`; we need the comparison
  -- between homology of a single object in `K(A-mod)` and the underlying module.
  let H := HomotopyCategory.homologyFunctor (ModuleCat A) (ComplexShape.up ℤ) (1 : ℤ)
  let e :
      HomotopyCategory.singleFunctor (ModuleCat A) (1 : ℤ) ⋙ H ≅ 𝟭 (ModuleCat A) :=
    (Functor.isoWhiskerRight
      (HomotopyCategory.singleFunctorPostcompQuotientIso (ModuleCat A) (1 : ℤ)) H) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (HomotopyCategory.homologyFunctorFactors (ModuleCat A) (ComplexShape.up ℤ) (1 : ℤ)) ≪≫
      (HomologicalComplex.homologyFunctorSingleIso (ModuleCat A) (ComplexShape.up ℤ) (1 : ℤ))
  have hHiso :
      IsIso (H.map ((HomotopyCategory.singleFunctor (ModuleCat A) (1 : ℤ)).map
        (principalIdealSelfMul f))) := by
    infer_instance
  have hmulIso : IsIso (principalIdealSelfMul f) := by
    simpa using (NatIso.isIso_map_iff e (principalIdealSelfMul f)).1 hHiso
  letI : IsIso (principalIdealSelfMul f) := hmulIso
  -- The degree-`1` homology comparison reduces the ambient isomorphism to multiplication by `f`
  -- on the principal ideal itself.
  exact isUnit_of_isIso_principalIdealSelfMul f hf

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

/-- Helper for Example 15.96.1: the map from the degree-`1` single complex into the double
cone complex satisfies the chain-map commutativity relation. -/
private theorem etaCounterexampleFTorsionFreeSecondMap_comm
    (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ)
    (hi : (ComplexShape.up ℤ).Rel (1 : ℤ) i) :
    (doubleXIso₁ (principalIdealMulToFTorsionFreeModule f hf) etaCounterexample_rel
      (by decide)).inv ≫ (etaCounterexampleFTorsionFreeConeComplex f hf).d 1 i = 0 := by
  have hi' : i ≠ (1 : ℤ) := by
    intro h
    subst h
    simpa using hi
  have hd :
      (etaCounterexampleFTorsionFreeConeComplex f hf).d 1 i = 0 := by
    simpa [etaCounterexampleFTorsionFreeConeComplex] using
      (HomologicalComplex.double_d_eq_zero₁
        (principalIdealMulToFTorsionFreeModule f hf) etaCounterexample_rel 1 i hi')
  rw [hd]
  simp

private noncomputable abbrev etaCounterexampleFTorsionFreeSecondMap
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    etaCounterexampleFTorsionFreeIdealComplex f hf ⟶
      etaCounterexampleFTorsionFreeConeComplex f hf :=
  mkHomFromSingle
    ((doubleXIso₁ (principalIdealMulToFTorsionFreeModule f hf)
      etaCounterexample_rel (by decide)).inv)
    (etaCounterexampleFTorsionFreeSecondMap_comm f hf)

/-- Helper for Example 15.96.1: the map from the double cone complex to the shifted single
source complex satisfies the chain-map commutativity relation. -/
private theorem etaCounterexampleFTorsionFreeThirdMap_comm
    (f : A) (hf : f ∈ nonZeroDivisors A) (i : ℤ)
    (hi : (ComplexShape.up ℤ).Rel i (0 : ℤ)) :
    (etaCounterexampleFTorsionFreeConeComplex f hf).d i 0 ≫
      (-(doubleXIso₀ (principalIdealMulToFTorsionFreeModule f hf)
        etaCounterexample_rel).hom) = 0 := by
  have hi' : i ≠ (0 : ℤ) := by
    intro h
    subst h
    simpa using hi
  have hd :
      (etaCounterexampleFTorsionFreeConeComplex f hf).d i 0 = 0 := by
    simpa [etaCounterexampleFTorsionFreeConeComplex] using
      (HomologicalComplex.double_d_eq_zero₀
        (principalIdealMulToFTorsionFreeModule f hf) etaCounterexample_rel i 0 hi')
  rw [hd]
  simp

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

/-- Helper for Example 15.96.1: forgetting the full-subcategory structure on the explicit cone
complex identifies it with the ambient double complex. -/
private noncomputable def etaCounterexampleConeComplex_inclusion_iso (f : A)
    (hf : f ∈ nonZeroDivisors A) :
    ((ObjectProperty.ι (fTorsionFreeModuleProperty f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (etaCounterexampleFTorsionFreeConeComplex f hf) ≅
        etaCounterexampleConeComplex f := by
  classical
  refine HomologicalComplex.Hom.isoOfComponents (fun i ↦ ?_) ?_
  · by_cases hi0 : i = 0
    · subst hi0
      exact eqToIso (by
        unfold etaCounterexampleFTorsionFreeConeComplex etaCounterexampleConeComplex
          etaCounterexampleSourceModule etaCounterexampleIdealModule
        dsimp [HomologicalComplex.double]
        simp)
    · by_cases hi1 : i = 1
      · subst hi1
        exact eqToIso (by
          unfold etaCounterexampleFTorsionFreeConeComplex etaCounterexampleConeComplex
            etaCounterexampleSourceModule etaCounterexampleIdealModule
          dsimp [HomologicalComplex.double]
          simp)
      · have hleft :
            IsZero
              ((((ObjectProperty.ι (fTorsionFreeModuleProperty f)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj (etaCounterexampleFTorsionFreeConeComplex f hf)).X i) := by
          unfold etaCounterexampleFTorsionFreeConeComplex
          simpa [HomologicalComplex.double, hi0, hi1] using
            Functor.map_isZero (ObjectProperty.ι (fTorsionFreeModuleProperty f))
              (isZero_zero (FTorsionFreeModuleCat f))
        have hright : IsZero ((etaCounterexampleConeComplex f).X i) := by
          unfold etaCounterexampleConeComplex
          dsimp [HomologicalComplex.double]
          simpa [hi0, hi1] using (isZero_zero (ModuleCat A))
        exact hleft.isoZero ≪≫ (hright.isoZero).symm
  · intro i j hij
    by_cases hi0 : i = 0
    · subst hi0
      obtain rfl : j = 1 := (ComplexShape.up ℤ).next_eq hij etaCounterexample_rel
      unfold etaCounterexampleFTorsionFreeConeComplex etaCounterexampleConeComplex
        principalIdealMulToFTorsionFreeModule etaCounterexampleSourceModule
        etaCounterexampleIdealModule
      dsimp [HomologicalComplex.double]
      simp
    · have hd_left :
        (etaCounterexampleFTorsionFreeConeComplex f hf).d i j = 0 := by
        simpa [etaCounterexampleFTorsionFreeConeComplex] using
          (HomologicalComplex.double_d_eq_zero₀
            (principalIdealMulToFTorsionFreeModule f hf) etaCounterexample_rel i j hi0)
      have hd_right :
          (etaCounterexampleConeComplex f).d i j = 0 := by
        simpa [etaCounterexampleConeComplex] using
          (HomologicalComplex.double_d_eq_zero₀
            (principalIdealMulToObject f) etaCounterexample_rel i j hi0)
      simp [hd_left, hd_right]

/-- Helper for Example 15.96.1: forgetting the full-subcategory structure on the degree-`1`
single complex identifies it with the ambient single complex on `(f)`. -/
private noncomputable def etaCounterexampleSingleComplex_inclusion_iso (f : A)
    (hf : f ∈ nonZeroDivisors A) :
    ((ObjectProperty.ι (fTorsionFreeModuleProperty f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (etaCounterexampleFTorsionFreeIdealComplex f hf) ≅
        (CochainComplex.singleFunctor (ModuleCat A) (1 : ℤ)).obj (principalIdealObject f) := by
  classical
  refine HomologicalComplex.Hom.isoOfComponents (fun i ↦ ?_) ?_
  · by_cases hi : i = 1
    · subst hi
      exact eqToIso (by
        unfold etaCounterexampleFTorsionFreeIdealComplex etaCounterexampleIdealModule
        dsimp [CochainComplex.singleFunctor, HomologicalComplex.single]
        rfl)
    · have hleft :
          IsZero
            ((((ObjectProperty.ι (fTorsionFreeModuleProperty f)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (etaCounterexampleFTorsionFreeIdealComplex f hf)).X i) := by
        unfold etaCounterexampleFTorsionFreeIdealComplex CochainComplex.singleFunctor
          CochainComplex.singleFunctors
        delta HomologicalComplex.single
        simpa [hi] using
          Functor.map_isZero (ObjectProperty.ι (fTorsionFreeModuleProperty f))
            (isZero_zero (FTorsionFreeModuleCat f))
      have hright :
          IsZero
            (((CochainComplex.singleFunctor (ModuleCat A) (1 : ℤ)).obj
              (principalIdealObject f)).X i) := by
        unfold CochainComplex.singleFunctor CochainComplex.singleFunctors
        delta HomologicalComplex.single
        simpa [hi] using (isZero_zero (ModuleCat A))
      exact hleft.isoZero ≪≫ (hright.isoZero).symm
  · intro i j hij
    simp [etaCounterexampleFTorsionFreeIdealComplex, etaCounterexampleIdealModule]

/-- Helper for Example 15.96.1: the third vertex of the ambient image triangle is isomorphic to
the explicit ambient cone object `A ⟶ (f)`. -/
private noncomputable def etaCounterexampleImageTriangle_obj₃_iso_coneObj (f : A)
    (hf : f ∈ nonZeroDivisors A) :
    (etaCounterexampleImageTriangle f hf).obj₃ ≅ etaCounterexampleConeObj f := by
  change
    (ftorsionFreeHomotopyInclusion f).obj
        ((fTorsionFreeHomotopyQuotient f).obj (etaCounterexampleFTorsionFreeConeComplex f hf)) ≅
      etaCounterexampleConeObj f
  change
    moduleHomotopyQuotient.obj
        (((ObjectProperty.ι (fTorsionFreeModuleProperty f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (etaCounterexampleFTorsionFreeConeComplex f hf)) ≅
      etaCounterexampleConeObj f
  exact moduleHomotopyQuotient.mapIso (etaCounterexampleConeComplex_inclusion_iso f hf)

/-- Helper for Example 15.96.1: the inclusion on homotopy categories identifies the degree-`1`
single complex on `(f)` in the full subcategory with the ambient degree-`1` single complex. -/
private noncomputable def etaCounterexampleSingleFunctor_obj_under_inclusion_iso (f : A)
    (hf : f ∈ nonZeroDivisors A) :
    (ftorsionFreeHomotopyInclusion f).obj
        ((HomotopyCategory.singleFunctor (FTorsionFreeModuleCat f) (1 : ℤ)).obj
          (etaCounterexampleIdealModule f hf)) ≅
      (HomotopyCategory.singleFunctor (ModuleCat A) (1 : ℤ)).obj (principalIdealObject f) := by
  change
    moduleHomotopyQuotient.obj
        (((ObjectProperty.ι (fTorsionFreeModuleProperty f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (etaCounterexampleFTorsionFreeIdealComplex f hf)) ≅
      (HomotopyCategory.singleFunctor (ModuleCat A) (1 : ℤ)).obj (principalIdealObject f)
  exact
    (moduleHomotopyQuotient.mapIso (etaCounterexampleSingleComplex_inclusion_iso f hf)) ≪≫
      eqToIso
        (HomotopyCategory.quotient_obj_singleFunctors_obj (C := ModuleCat A) (n := (1 : ℤ))
          (X := principalIdealObject f))

/-- Helper for Example 15.96.1: forgetting the full-subcategory structure on the degree-`1`
single-complex self-map of `(f)` leaves the ambient single-complex self-map unchanged after
transporting along the comparison isomorphism. -/
private theorem etaCounterexampleSingleComplex_map_under_inclusion (f : A)
    (hf : f ∈ nonZeroDivisors A) :
    (etaCounterexampleSingleComplex_inclusion_iso f hf).inv ≫
        (((ObjectProperty.ι (fTorsionFreeModuleProperty f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
            ((CochainComplex.singleFunctor (FTorsionFreeModuleCat f) (1 : ℤ)).map
              (principalIdealSelfMulFTorsionFreeModule f hf))) ≫
      (etaCounterexampleSingleComplex_inclusion_iso f hf).hom =
        (CochainComplex.singleFunctor (ModuleCat A) (1 : ℤ)).map (principalIdealSelfMul f) := by
  classical
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = 1
  · subst hi
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    change ((etaCounterexampleSingleComplex_inclusion_iso f hf).inv.f 1) ≫
        ((((CochainComplex.singleFunctor (FTorsionFreeModuleCat f) (1 : ℤ)).map
          (principalIdealSelfMulFTorsionFreeModule f hf)).f 1).hom) ≫
      ((etaCounterexampleSingleComplex_inclusion_iso f hf).hom.f 1) =
        ((CochainComplex.singleFunctor (ModuleCat A) (1 : ℤ)).map (principalIdealSelfMul f)).f 1
    change 𝟙 _ ≫ (principalIdealSelfMulFTorsionFreeModule f hf).hom ≫ 𝟙 _ =
      principalIdealSelfMul f
    change (principalIdealSelfMulFTorsionFreeModule f hf).hom = principalIdealSelfMul f
    rfl
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    change ((etaCounterexampleSingleComplex_inclusion_iso f hf).inv.f i) ≫
        ((((CochainComplex.singleFunctor (FTorsionFreeModuleCat f) (1 : ℤ)).map
          (principalIdealSelfMulFTorsionFreeModule f hf)).f i).hom) ≫
      ((etaCounterexampleSingleComplex_inclusion_iso f hf).hom.f i) =
        ((CochainComplex.singleFunctor (ModuleCat A) (1 : ℤ)).map (principalIdealSelfMul f)).f i
    have hleft_zero :
        IsZero
          ((((ObjectProperty.ι (fTorsionFreeModuleProperty f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (etaCounterexampleFTorsionFreeIdealComplex f hf)).X i) := by
      unfold etaCounterexampleFTorsionFreeIdealComplex CochainComplex.singleFunctor
        CochainComplex.singleFunctors
      delta HomologicalComplex.single
      simpa [hi] using
        Functor.map_isZero (ObjectProperty.ι (fTorsionFreeModuleProperty f))
          (isZero_zero (FTorsionFreeModuleCat f))
    have hmid :
        ((((CochainComplex.singleFunctor (FTorsionFreeModuleCat f) (1 : ℤ)).map
          (principalIdealSelfMulFTorsionFreeModule f hf)).f i).hom) = 0 := by
      exact hleft_zero.eq_of_src _ _
    have hright_zero_obj :
        IsZero
          (((CochainComplex.singleFunctor (ModuleCat A) (1 : ℤ)).obj
            (principalIdealObject f)).X i) := by
      unfold CochainComplex.singleFunctor CochainComplex.singleFunctors
      delta HomologicalComplex.single
      simpa [hi] using (isZero_zero (ModuleCat A))
    have hright_zero :
        ((CochainComplex.singleFunctor (ModuleCat A) (1 : ℤ)).map (principalIdealSelfMul f)).f i =
          0 := by
      exact hright_zero_obj.eq_of_src _ _
    simp [hmid, hright_zero]

/-- Helper for Example 15.96.1: after transporting along the comparison isomorphism above, the
inclusion on homotopy categories sends the degree-`1` single-complex self-map of `(f)` to the
ambient degree-`1` single-complex self-map induced by multiplication by `f`. -/
private theorem etaCounterexampleSingleFunctor_map_under_inclusion (f : A)
    (hf : f ∈ nonZeroDivisors A) :
    (etaCounterexampleSingleFunctor_obj_under_inclusion_iso f hf).inv ≫
        (ftorsionFreeHomotopyInclusion f).map
          ((HomotopyCategory.singleFunctor (FTorsionFreeModuleCat f) (1 : ℤ)).map
            (principalIdealSelfMulFTorsionFreeModule f hf)) ≫
      (etaCounterexampleSingleFunctor_obj_under_inclusion_iso f hf).hom =
        ((HomotopyCategory.singleFunctor (ModuleCat A) (1 : ℤ)).map (principalIdealSelfMul f)) := by
  change
    (etaCounterexampleSingleFunctor_obj_under_inclusion_iso f hf).inv ≫
        moduleHomotopyQuotient.map
        (((ObjectProperty.ι (fTorsionFreeModuleProperty f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
            ((CochainComplex.singleFunctor (FTorsionFreeModuleCat f) (1 : ℤ)).map
              (principalIdealSelfMulFTorsionFreeModule f hf))) ≫
      (etaCounterexampleSingleFunctor_obj_under_inclusion_iso f hf).hom =
      ((HomotopyCategory.singleFunctor (ModuleCat A) (1 : ℤ)).map (principalIdealSelfMul f))
  change
    (etaCounterexampleSingleFunctor_obj_under_inclusion_iso f hf).inv ≫
        moduleHomotopyQuotient.map
        (((ObjectProperty.ι (fTorsionFreeModuleProperty f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
            ((CochainComplex.singleFunctor (FTorsionFreeModuleCat f) (1 : ℤ)).map
              (principalIdealSelfMulFTorsionFreeModule f hf))) ≫
      (etaCounterexampleSingleFunctor_obj_under_inclusion_iso f hf).hom =
      moduleHomotopyQuotient.map
        ((CochainComplex.singleFunctor (ModuleCat A) (1 : ℤ)).map (principalIdealSelfMul f))
  simpa [Category.assoc, etaCounterexampleSingleFunctor_obj_under_inclusion_iso,
    etaCounterexampleSingleComplex_inclusion_iso, eqToHom_map] using
    congrArg moduleHomotopyQuotient.map
      (etaCounterexampleSingleComplex_map_under_inclusion f hf)

/-- Helper for Example 15.96.1: the first morphism of the ambient image triangle is the ambient
single-complex map induced by multiplication by `f` on `(f)`, after transporting along the
ambient image triangle's first vertex identification. -/
private theorem etaCounterexampleImageTriangle_mor₁_eq_singleFunctor_map (f : A)
    (hf : f ∈ nonZeroDivisors A) :
    ∃ e : (etaCounterexampleImageTriangle f hf).obj₁ ≅
        (HomotopyCategory.singleFunctor (ModuleCat A) (1 : ℤ)).obj (principalIdealObject f),
      e.inv ≫ (etaCounterexampleImageTriangle f hf).mor₁ ≫ e.hom =
        ((HomotopyCategory.singleFunctor (ModuleCat A) (1 : ℤ)).map (principalIdealSelfMul f)) := by
  refine ⟨etaCounterexampleSingleFunctor_obj_under_inclusion_iso f hf, ?_⟩
  simpa [etaCounterexampleImageTriangle, etaCounterexampleTriangle] using
    etaCounterexampleSingleFunctor_map_under_inclusion f hf

/-- Example 15.96.1: if the ambient image triangle were distinguished, then `f` would have to be
a unit. -/
theorem etaCounterexample_distinguished_implies_isUnit (f : A) (hf : f ∈ nonZeroDivisors A)
    (hT : etaCounterexampleImageTriangle f hf ∈ distTriang KModA) :
    IsUnit f := by
  -- Identify the third vertex with the explicit contractible cone object.
  have hzero : IsZero ((etaCounterexampleImageTriangle f hf).obj₃) := by
    exact IsZero.of_iso (etaCounterexampleCone_isZero f hf)
      (etaCounterexampleImageTriangle_obj₃_iso_coneObj f hf)
  have hiso :
      IsIso
        (((HomotopyCategory.singleFunctor (ModuleCat A) (1 : ℤ)).map
          (principalIdealSelfMul f))) := by
    -- Distinguished triangles with zero third object have an isomorphism as first map.
    let hmor := etaCounterexampleImageTriangle_mor₁_eq_singleFunctor_map f hf
    obtain ⟨e, hmor_eq⟩ := hmor
    have hiso₀ : IsIso ((etaCounterexampleImageTriangle f hf).mor₁) :=
      (Triangle.isZero₃_iff_isIso₁ (etaCounterexampleImageTriangle f hf) hT).1 hzero
    have hiso_transport :
        IsIso (e.inv ≫ (etaCounterexampleImageTriangle f hf).mor₁ ≫ e.hom) := by
      infer_instance
    rw [hmor_eq] at hiso_transport
    exact hiso_transport
  -- Apply the homology-of-a-single-complex comparison to recover an inverse to multiplication
  -- by `f` on `(f)` and then on `A`.
  exact etaCounterexampleFirstMap_isUnit_of_isIso f hf hiso

/-- Example 15.96.1: if `f` is not a unit, the ambient comparison triangle cannot be
distinguished. -/
theorem etaCounterexampleAmbient_not_distinguished_of_nonunit (f : A) (hf : f ∈ nonZeroDivisors A)
    (hunit : ¬ IsUnit f) :
    etaCounterexampleImageTriangle f hf ∉ distTriang KModA := by
  intro hT
  exact hunit (etaCounterexample_distinguished_implies_isUnit f hf hT)

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
