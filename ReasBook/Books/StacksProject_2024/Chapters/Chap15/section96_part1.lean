import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Regular.IsSMulRegular

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_15_96_1 (from Chap15) -/
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

/-! ### Lemma_15_96_2 (from Chap15) -/
open CategoryTheory
open HomologicalComplex
open scoped nonZeroDivisors

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]
open LinearEquiv

/- Domain-style sampling:
- primary domain: the Berthelot-Ogus `η_f` operator on cochain complexes of `A`-modules and the
  induced comparison on cohomology modulo `f`-torsion;
- sampled chapter/project owner declarations in this domain:
  `CochainComplex (ModuleCat A) ℕ`,
  `CochainComplex.extend ComplexShape.embeddingUpNat`,
  `HomologicalComplex.cycles`,
  `HomologicalComplex.homology`;
- best owner abstraction:
  `source-facing`: the bounded-below Berthelot-Ogus complex `η_f M` for
    `M : NatModuleCochainComplex A`;
  `core/canonical`: `NatModuleCochainComplex A := CochainComplex (ModuleCat A) ℕ`;
  `bridge/view`: the `ℤ`-indexed extension-by-zero presentation
    `M.extend ComplexShape.embeddingUpNat`, together with the corresponding `ℤ`-indexed
    Berthelot-Ogus construction on `K : ModuleComplex A` under the support hypothesis
    `[K.IsStrictlyGE 0]`;
- primitive data vs derived API: the source-facing primitive data are the degreewise Berthelot-Ogus
  submodules and their restricted differentials for `NatModuleCochainComplex A`. The
  `ℤ`-indexed extension-by-zero construction is only a bounded-below bridge, and the homology
  comparison equivalence is derived API built from that bridge. -/

/-- A cochain complex of `A`-modules indexed by `ℤ`. -/
abbrev ModuleComplex (A : Type u) [CommRing A] := CochainComplex (ModuleCat A) ℤ

/-- A cochain complex of `A`-modules indexed by `ℕ`. This is the source-facing owner for
Lemma `15.96.2`. -/
abbrev NatModuleCochainComplex (A : Type u) [CommRing A] :=
  CochainComplex (ModuleCat A) ℕ

namespace BerthelotOgusInt

/-- A cochain complex is termwise `f`-torsion free if multiplication by `f` is injective in every
degree. -/
class IsTermwiseFTorsionFree (f : A) (K : ModuleComplex A) : Prop where
  /-- Multiplication by `f` is injective in each degree. -/
  isSMulRegular (i : ℤ) : IsSMulRegular (K.X i) f

/-- The owner class `IsTermwiseFTorsionFree` is equivalent to degreewise `f`-regularity. -/
theorem isTermwiseFTorsionFree_iff
    (f : A) (K : ModuleComplex A) :
    IsTermwiseFTorsionFree f K ↔ ∀ i : ℤ, IsSMulRegular (K.X i) f := by
  constructor
  · intro h i
    exact h.isSMulRegular i
  · intro h
    exact ⟨h⟩

instance (f : A) (K : ModuleComplex A) [h : IsTermwiseFTorsionFree f K] (i : ℤ) :
    IsSMulRegular (K.X i) f :=
  h.isSMulRegular i

/-- The degree-`i` Berthelot-Ogus term on the `ModuleComplex A` owner. -/
abbrev degreeSubmodule (f : A) (K : ModuleComplex A) (i : ℤ) :
    Submodule A (K.X i) :=
  LinearMap.range (LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)) ⊓
    (LinearMap.range
      (LinearMap.lsmul A (K.X (i + 1)) (f ^ Int.toNat (i + 1)))).comap (K.d i (i + 1)).hom

-- Proof sketch: if `x` lies in the defining intersection for degree `i`, then `d(x)` already
-- lies in the required range for degree `i + 1`; the second condition for `d(x)` is automatic
-- because `d ∘ d = 0`, and `0` belongs to every range.
/-- The differential of `K` sends the degree-`i` bridge term of `η_f K` into degree `i + 1`. -/
private theorem differential_mem
    (f : A) (K : ModuleComplex A) (i : ℤ) (x : degreeSubmodule f K i) :
    K.d i (i + 1) x ∈ degreeSubmodule f K (i + 1) := sorry

/-- The degree-`i` differential on the Berthelot-Ogus complex `η_f K`. -/
abbrev differentialLinear (f : A) (K : ModuleComplex A) (i : ℤ) :
    degreeSubmodule f K i →ₗ[A] degreeSubmodule f K (i + 1) :=
  ((K.d i (i + 1)).hom.comp (degreeSubmodule f K i).subtype).codRestrict
    (degreeSubmodule f K (i + 1))
    (differential_mem f K i)

-- Proof sketch: `η_f K` uses the same differentials as `K`, only codomain-restricted to the
-- defining submodules. Hence the square of two successive differentials is the restriction of
-- `d ∘ d = 0` on `K`.
/-- The successive differentials of `η_f K` compose to zero. -/
theorem differential_sq (f : A) (K : ModuleComplex A) (i : ℤ) :
    ModuleCat.ofHom (differentialLinear f K i) ≫
        ModuleCat.ofHom (differentialLinear f K (i + 1)) =
      0 := sorry

/-- The Berthelot-Ogus complex `η_f K` on the `ModuleComplex A` owner. -/
def complex (f : A) (K : ModuleComplex A) : ModuleComplex A :=
  CochainComplex.of
    (fun i ↦ ModuleCat.of A (degreeSubmodule f K i))
    (fun i ↦ ModuleCat.ofHom (differentialLinear f K i))
    (fun i ↦ differential_sq f K i)

instance complex_isStrictlyGE_zero
    (f : A) (K : ModuleComplex A) [K.IsStrictlyGE 0] :
    (complex f K).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  let hzero : CategoryTheory.Limits.IsZero (K.X i) := K.isZero_of_isStrictlyGE 0 i hi
  letI : Subsingleton (K.X i) := ModuleCat.subsingleton_of_isZero hzero
  letI : Subsingleton ((complex f K).X i) := by
    change Subsingleton (degreeSubmodule f K i)
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

scoped[BerthelotOgusInt] notation "η[" f "] " K:arg => complex f K

open scoped BerthelotOgusInt

/-- A morphism of bounded-below bridge complexes sends the degree-`i` Berthelot-Ogus term of `K`
into that of `L`. -/
theorem map_mem_degreeSubmodule
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) (i : ℤ) (x : degreeSubmodule f K i) :
    φ.f i x ∈ degreeSubmodule f L i := sorry

/-- The degree-`i` component of the morphism induced on Berthelot-Ogus complexes by `φ`. -/
abbrev mapLinear
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) (i : ℤ) :
    degreeSubmodule f K i →ₗ[A] degreeSubmodule f L i :=
  ((φ.f i).hom.comp (degreeSubmodule f K i).subtype).codRestrict
    (degreeSubmodule f L i)
    (map_mem_degreeSubmodule f φ i)

-- Proof sketch: both sides are restrictions of the commutative square defining the cochain map
-- `φ`; after forgetting the subtype codomains, the equality is exactly `φ.comm`.
/-- The induced Berthelot-Ogus component maps commute with the differentials. -/
theorem map_comm
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    CommSq
      (ModuleCat.ofHom (mapLinear f φ i))
      ((η[f] K).d i j)
      ((η[f] L).d i j)
      (ModuleCat.ofHom (mapLinear f φ j)) := sorry

/-- The morphism of Berthelot-Ogus complexes induced by a morphism `φ : K ⟶ L`. -/
def map (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) :
    η[f] K ⟶ η[f] L where
  f i := ModuleCat.ofHom (mapLinear f φ i)
  comm' i j hij := (map_comm f φ i j hij).w

-- Proof sketch: `BerthelotOgusInt.map f φ` is defined degreewise by `mapLinear f φ`, so its
-- `i`th component is the corresponding codomain-restricted map.
/-- The degree-`i` component of the Berthelot-Ogus map induced by `φ`. -/
theorem map_f
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) (i : ℤ) :
    (map f φ).f i = ModuleCat.ofHom (mapLinear f φ i) := sorry

-- Proof sketch: if `x` is a cocycle, then `f ^ Int.toNat i x` lies in the image of multiplication
-- by `f ^ Int.toNat i`, and its differential is zero, hence also lies in the image of
-- multiplication by `f ^ Int.toNat (i + 1)`. Therefore `f ^ Int.toNat i x` defines a term of
-- `η_f K` in degree `i`.
/-- Multiplication by `f ^ Int.toNat i` sends cocycles of `K` in degree `i` into the degree-`i`
term of `η_f K`. -/
private theorem cycleScale_mem_degreeSubmodule
    (f : A) (K : ModuleComplex A) (i : ℤ) (x : K.cycles i) :
    ((LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)).comp (K.iCycles i).hom) x ∈
      degreeSubmodule f K i := sorry

/-- Multiplication by `f ^ Int.toNat i` on cocycles, viewed as a morphism into the degree-`i`
term of `η_f K`. -/
abbrev cyclesToEtaXLinear (f : A) (K : ModuleComplex A) (i : ℤ) :
    K.cycles i →ₗ[A] degreeSubmodule f K i :=
  ((LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)).comp (K.iCycles i).hom).codRestrict
    (degreeSubmodule f K i) (cycleScale_mem_degreeSubmodule f K i)

-- Proof sketch: the source is already a cycle in `K`, so after multiplying by `f ^ Int.toNat i`
-- its differential is still zero. Since `η_f K` uses the restricted differential of `K`, the
-- image in degree `i` is a cocycle of `η_f K`.
/-- The scaled cocycle morphism lands in the cycles of `η_f K`. -/
theorem cyclesToEtaX_comp_d_eq_zero
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    ModuleCat.ofHom (cyclesToEtaXLinear f K i) ≫ (η[f] K).d i (i + 1) = 0 := sorry

/-- The cocycle-level comparison map from `K` to `η_f K` in degree `i`. -/
abbrev cyclesToEtaCycles (f : A) (K : ModuleComplex A) (i : ℤ) :
    K.cycles i ⟶ (η[f] K).cycles i :=
  (η[f] K).liftCycles'
    (ModuleCat.ofHom (cyclesToEtaXLinear f K i))
    (i + 1) (by simp) (cyclesToEtaX_comp_d_eq_zero f K i)

/-- The homology-class map induced on cocycles by multiplication by `f ^ Int.toNat i`. -/
abbrev cyclesToEtaHomology (f : A) (K : ModuleComplex A) (i : ℤ) :
    K.cycles i ⟶ (η[f] K).homology i :=
  cyclesToEtaCycles f K i ≫ (η[f] K).homologyπ i

-- Proof sketch: a boundary in degree `i` is represented by `d(y)` from degree `i - 1`. After
-- multiplying by `f ^ Int.toNat i`, this becomes the boundary of the corresponding scaled
-- predecessor in the subcomplex `η_f K`, so its class in `H^i(η_f K)` is zero.
/-- The cocycle-level comparison annihilates boundaries, so it descends to homology. -/
theorem toCycles_comp_cyclesToEtaHomology_eq_zero
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    (K.sc i).toCycles ≫ cyclesToEtaHomology f K i = 0 := sorry

/-- The homology comparison map `H^i(K) → H^i(η_f K)` induced by multiplication by
`f ^ Int.toNat i`. -/
abbrev homologyToEtaHomology (f : A) (K : ModuleComplex A) (i : ℤ) :
    K.homology i ⟶ (η[f] K).homology i :=
  (K.sc i).descHomology
    (cyclesToEtaHomology f K i)
    (toCycles_comp_cyclesToEtaHomology_eq_zero f K i)

-- Proof sketch: if a class in `H^i(K)` is killed by `f`, then multiplying a cocycle
-- representative by `f ^ Int.toNat i` becomes a boundary in `η_f K`; this is exactly the kernel
-- statement proved in the textbook argument.
/-- The homology comparison map kills the `f`-torsion in `H^i(K)`. -/
theorem torsionBy_le_ker_homologyToEtaHomology
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    Submodule.torsionBy A (K.homology i) f ≤
      LinearMap.ker (homologyToEtaHomology f K i).hom := sorry

/-- The canonical comparison map
`H^i(K) / H^i(K)[f] → H^i(η_f K)` induced by multiplication by `f ^ Int.toNat i`. -/
abbrev homologyComparison (f : A) (K : ModuleComplex A) (i : ℤ) :
    ((K.homology i) ⧸ Submodule.torsionBy A (K.homology i) f) →ₗ[A] (η[f] K).homology i :=
  (Submodule.torsionBy A (K.homology i) f).liftQ
    (homologyToEtaHomology f K i).hom
    (torsionBy_le_ker_homologyToEtaHomology f K i)

-- Proof sketch: surjectivity comes from the description of cocycles in `η_f K` as
-- `f ^ Int.toNat i` times cocycles of `K`. For injectivity, if `f ^ Int.toNat i z` is a boundary
-- in `η_f K`, the textbook argument rewrites it using the previous degree and the
-- `f`-torsion-free hypotheses together with the assumption that `f` is a nonzerodivisor to
-- conclude that the class of `z` is `f`-torsion. This bridge statement is valid only for
-- bounded-below `ℤ`-indexed complexes.
/-- The canonical comparison map `H^i(K) / H^i(K)[f] → H^i(η_f K)` is bijective for bounded-below
`ℤ`-indexed complexes under the nonzerodivisor and termwise `f`-torsion-free hypotheses. -/
theorem homologyComparison_bijective
    (f : A) (K : ModuleComplex A) (i : ℤ)
    [K.IsStrictlyGE 0]
    (hf : f ∈ nonZeroDivisors A) (hK : IsTermwiseFTorsionFree f K) :
    Function.Bijective (homologyComparison f K i) := sorry

/-- The canonical comparison
`H^i(K) / H^i(K)[f] ≃ H^i(η_f K)` for bounded-below `ℤ`-indexed complexes under the
nonzerodivisor and termwise `f`-torsion-free hypotheses. -/
noncomputable abbrev homologyComparisonEquiv
    (f : A) (K : ModuleComplex A) (i : ℤ)
    [K.IsStrictlyGE 0]
    (hf : f ∈ nonZeroDivisors A) (hK : IsTermwiseFTorsionFree f K) :
    ((K.homology i) ⧸ Submodule.torsionBy A (K.homology i) f) ≃ₗ[A] (η[f] K).homology i :=
  LinearEquiv.ofBijective
    (homologyComparison f K i)
    (homologyComparison_bijective f K i hf hK)

end BerthelotOgusInt

open BerthelotOgusInt

/-- A nonnegative cochain complex is termwise `f`-torsion free if multiplication by `f` is
injective in every degree. This is the source-facing owner predicate for Lemma `15.96.2`. -/
class IsTermwiseFTorsionFree (f : A) (M : NatModuleCochainComplex A) : Prop where
  /-- Multiplication by `f` is injective in degree `n`. -/
  isSMulRegular (n : ℕ) : IsSMulRegular (M.X n) f

/-- The source-facing owner predicate is equivalent to degreewise `f`-regularity. -/
theorem isTermwiseFTorsionFree_iff
    (f : A) (M : NatModuleCochainComplex A) :
    IsTermwiseFTorsionFree f M ↔ ∀ n : ℕ, IsSMulRegular (M.X n) f := by
  constructor
  · intro h n
    exact h.isSMulRegular n
  · intro h
    exact ⟨h⟩

instance (f : A) (M : NatModuleCochainComplex A) [h : IsTermwiseFTorsionFree f M] (n : ℕ) :
    IsSMulRegular (M.X n) f :=
  h.isSMulRegular n

namespace IsTermwiseFTorsionFree

/-- Passing to the extension by zero gives the bounded-below `ℤ`-indexed bridge predicate. -/
theorem toIsTermwiseFTorsionFree
    {f : A} {M : NatModuleCochainComplex A} (hM : IsTermwiseFTorsionFree f M) :
    BerthelotOgusInt.IsTermwiseFTorsionFree f (M.extend ComplexShape.embeddingUpNat) := by
  sorry

end IsTermwiseFTorsionFree

instance (f : A) (M : NatModuleCochainComplex A) [hM : IsTermwiseFTorsionFree f M] :
    BerthelotOgusInt.IsTermwiseFTorsionFree f (M.extend ComplexShape.embeddingUpNat) :=
  hM.toIsTermwiseFTorsionFree

/-- The degree-`n` Berthelot-Ogus term for a nonnegative complex. This is the source-facing owner
for the bounded-below Berthelot-Ogus construction. -/
abbrev etaFDegreeSubmodule (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    Submodule A (M.X n) :=
  LinearMap.range (LinearMap.lsmul A (M.X n) (f ^ n)) ⊓
    (LinearMap.range
      (LinearMap.lsmul A (M.X (n + 1)) (f ^ (n + 1)))).comap (M.d n (n + 1)).hom

-- Proof sketch: if `x` lies in the defining intersection for degree `n`, then `d(x)` already
-- lies in the required range for degree `n + 1`; the second condition for `d(x)` is automatic
-- because `d ∘ d = 0`, and `0` belongs to every range.
/-- The differential of `M` sends the degree-`n` Berthelot-Ogus term into degree `n + 1`. -/
private theorem etaFDifferential_mem
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) (x : etaFDegreeSubmodule f M n) :
    M.d n (n + 1) x ∈ etaFDegreeSubmodule f M (n + 1) := sorry

/-- The degree-`n` differential on the source-facing Berthelot-Ogus complex `η_f M`. -/
private abbrev etaFDifferentialLinear
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    etaFDegreeSubmodule f M n →ₗ[A] etaFDegreeSubmodule f M (n + 1) :=
  ((M.d n (n + 1)).hom.comp (etaFDegreeSubmodule f M n).subtype).codRestrict
    (etaFDegreeSubmodule f M (n + 1))
    (etaFDifferential_mem f M n)

-- Proof sketch: `η_f M` uses the same differentials as `M`, only codomain-restricted to the
-- defining submodules. Hence the square of two successive differentials is the restriction of
-- `d ∘ d = 0` on `M`.
/-- The successive differentials of `η_f M` compose to zero. -/
private theorem etaFDifferential_sq (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    ModuleCat.ofHom (etaFDifferentialLinear f M n) ≫
        ModuleCat.ofHom (etaFDifferentialLinear f M (n + 1)) =
      0 := sorry

/-- The source-facing Berthelot-Ogus complex `η_f M` on `NatModuleCochainComplex A`. -/
def etaFComplex (f : A) (M : NatModuleCochainComplex A) : NatModuleCochainComplex A :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of A (etaFDegreeSubmodule f M n))
    (fun n ↦ ModuleCat.ofHom (etaFDifferentialLinear f M n))
    (fun n ↦ etaFDifferential_sq f M n)

notation "η[" f "] " M:arg => etaFComplex f M

/-- The `ℤ`-indexed degree term on `M.extend embeddingUpNat` identifies with the source-facing
degree term on `M`. -/
private theorem etaFDegreeSubmodule_map_eq
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    (degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (n : ℤ)).map
        (M.extendXIso ComplexShape.embeddingUpNat rfl).toLinearEquiv.toLinearMap =
      etaFDegreeSubmodule f M n := by
  sorry

/-- The canonical linear equivalence from the bounded-below `ℤ`-indexed bridge term to the
source-facing degree term. -/
private noncomputable abbrev etaFDegreeSubmoduleLinearEquiv
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (n : ℤ) ≃ₗ[A]
      etaFDegreeSubmodule f M n :=
  (M.extendXIso ComplexShape.embeddingUpNat rfl).toLinearEquiv.ofSubmodules _ _
    (etaFDegreeSubmodule_map_eq f M n)

/-- The degreewise bridge equivalences commute with the `ℤ`-indexed and `ℕ`-indexed
Berthelot-Ogus differentials. -/
private theorem etaFDegreeSubmoduleLinearEquiv_comm
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    ModuleCat.ofHom (etaFDegreeSubmoduleLinearEquiv f M n) ≫ (η[f] M).d n (n + 1) =
      (η[f] (M.extend ComplexShape.embeddingUpNat)).d (n : ℤ) ((n + 1 : ℕ) : ℤ) ≫
        ModuleCat.ofHom (etaFDegreeSubmoduleLinearEquiv f M (n + 1)) := by
  sorry

/-- Restricting the `ℤ`-indexed Berthelot-Ogus complex on `M.extend ComplexShape.embeddingUpNat`
to nonnegative degrees recovers the source-facing complex `η[f] M`. -/
noncomputable def etaFExtendRestrictionIso
    (f : A) (M : NatModuleCochainComplex A) :
    (η[f] (M.extend ComplexShape.embeddingUpNat)).restriction (ComplexShape.embeddingUpIntGE 0) ≅
      η[f] M :=
  Hom.isoOfComponents
    (fun n ↦
      ((η[f] (M.extend ComplexShape.embeddingUpNat)).restrictionXIso
          (ComplexShape.embeddingUpIntGE 0) (by simp)) ≪≫
        (etaFDegreeSubmoduleLinearEquiv f M n).toModuleIso)
    (by
      rintro n _ rfl
      dsimp only
      have hn : (ComplexShape.embeddingUpIntGE 0).f n = (n : ℤ) := by simp
      have hn1 : (ComplexShape.embeddingUpIntGE 0).f (n + 1) = ((n + 1 : ℕ) : ℤ) := by simp
      rw [(η[f] (M.extend ComplexShape.embeddingUpNat)).restriction_d_eq
        (ComplexShape.embeddingUpIntGE 0) hn hn1]
      simpa using etaFDegreeSubmoduleLinearEquiv_comm f M n)

/-- The morphism of bounded-below Berthelot-Ogus complexes induced by a morphism of nonnegative
cochain complexes. This is the source-facing bridge obtained by transporting the owner-level
`BerthelotOgusInt.map` on `M.extend ComplexShape.embeddingUpNat` across
`etaFExtendRestrictionIso`. -/
def etaFMap (f : A) {M N : NatModuleCochainComplex A} (φ : M ⟶ N) :
    η[f] M ⟶ η[f] N :=
  (etaFExtendRestrictionIso f M).inv ≫
    restrictionMap
      (BerthelotOgusInt.map f (extendMap φ ComplexShape.embeddingUpNat))
      (ComplexShape.embeddingUpIntGE 0) ≫
    (etaFExtendRestrictionIso f N).hom

-- Proof sketch: if `x` is a cocycle, then `f ^ n x` lies in the image of multiplication by
-- `f ^ n`, and its differential is zero, hence also lies in the image of multiplication by
-- `f ^ (n + 1)`. Therefore `f ^ n x` defines a term of `η_f M` in degree `n`.
/-- Multiplication by `f ^ n` sends cocycles of `M` in degree `n` into the degree-`n` term of
`η_f M`. -/
private theorem cycleScale_mem_etaFDegreeSubmodule
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) (x : M.cycles n) :
    ((LinearMap.lsmul A (M.X n) (f ^ n)).comp (M.iCycles n).hom) x ∈
      etaFDegreeSubmodule f M n := sorry

/-- Multiplication by `f ^ n` on cocycles, viewed as a morphism into the degree-`n` term of
`η_f M`. -/
abbrev cyclesToEtaXLinear (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    M.cycles n →ₗ[A] etaFDegreeSubmodule f M n :=
  ((LinearMap.lsmul A (M.X n) (f ^ n)).comp (M.iCycles n).hom).codRestrict
    (etaFDegreeSubmodule f M n) (cycleScale_mem_etaFDegreeSubmodule f M n)

-- Proof sketch: the source is already a cycle in `M`, so after multiplying by `f ^ n` its
-- differential is still zero. Since `η_f M` uses the restricted differential of `M`, the image in
-- degree `n` is a cocycle of `η_f M`.
/-- The scaled cocycle morphism lands in the cycles of `η_f M`. -/
theorem cyclesToEtaX_comp_d_eq_zero
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    ModuleCat.ofHom (cyclesToEtaXLinear f M n) ≫ (η[f] M).d n (n + 1) = 0 := sorry

/-- The cocycle-level comparison map from `M` to `η_f M` in degree `n`. -/
abbrev cyclesToEtaCycles (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    M.cycles n ⟶ (η[f] M).cycles n :=
  (η[f] M).liftCycles'
    (ModuleCat.ofHom (cyclesToEtaXLinear f M n))
    (n + 1) (by simp) (cyclesToEtaX_comp_d_eq_zero f M n)

/-- The homology-class map induced on cocycles by multiplication by `f ^ n`. -/
abbrev cyclesToEtaHomology (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    M.cycles n ⟶ (η[f] M).homology n :=
  cyclesToEtaCycles f M n ≫ (η[f] M).homologyπ n

-- Proof sketch: a boundary in degree `n` is represented by `d(y)` from degree `n - 1`. After
-- multiplying by `f ^ n`, this becomes the boundary of the corresponding scaled predecessor in
-- the subcomplex `η_f M`, so its class in `H^n(η_f M)` is zero.
/-- The cocycle-level comparison annihilates boundaries, so it descends to homology. -/
theorem toCycles_comp_cyclesToEtaHomology_eq_zero
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    (M.sc n).toCycles ≫ cyclesToEtaHomology f M n = 0 := sorry

/-- The homology comparison map `H^n(M) → H^n(η_f M)` induced by multiplication by `f ^ n`. -/
abbrev homologyToEtaHomology (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    M.homology n ⟶ (η[f] M).homology n :=
  (M.sc n).descHomology
    (cyclesToEtaHomology f M n)
    (toCycles_comp_cyclesToEtaHomology_eq_zero f M n)

-- Proof sketch: if a class in `H^n(M)` is killed by `f`, then multiplying a cocycle
-- representative by `f ^ n` becomes a boundary in `η_f M`; this is exactly the kernel statement
-- proved in the textbook argument.
/-- The homology comparison map kills the `f`-torsion in `H^n(M)`. -/
theorem torsionBy_le_ker_homologyToEtaHomology
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    Submodule.torsionBy A (M.homology n) f ≤
      LinearMap.ker (homologyToEtaHomology f M n).hom := sorry

/-- The canonical comparison map
`H^n(M) / H^n(M)[f] → H^n(η_f M)` induced by multiplication by `f ^ n`. -/
abbrev homologyComparison (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    ((M.homology n) ⧸ Submodule.torsionBy A (M.homology n) f) →ₗ[A] (η[f] M).homology n :=
  (Submodule.torsionBy A (M.homology n) f).liftQ
    (homologyToEtaHomology f M n).hom
    (torsionBy_le_ker_homologyToEtaHomology f M n)

-- Proof sketch: surjectivity comes from the description of cocycles in `η_f M` as `f ^ n`
-- times cocycles of `M`. For injectivity, if `f ^ n z` is a boundary in `η_f M`, the textbook
-- argument rewrites it using the previous degree and the `f`-torsion-free hypotheses together
-- with the assumption that `f` is a nonzerodivisor to conclude that the class of `z` is
-- `f`-torsion.
/-- Lemma `15.96.2`: for an `ℕ`-indexed cochain complex of `A`-modules that is termwise
`f`-torsion free, the canonical Berthelot-Ogus comparison map
`H^n(M^\bullet) / H^n(M^\bullet)[f] → H^n(η_f M^\bullet)` is bijective under the nonzerodivisor
hypothesis. -/
theorem homologyComparison_bijective
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (hf : f ∈ nonZeroDivisors A) (hM : IsTermwiseFTorsionFree f M) :
    Function.Bijective (homologyComparison f M n) := sorry

/-- The canonical comparison
`H^n(M^\bullet) / H^n(M^\bullet)[f] ≃ H^n(η_f M^\bullet)` under the nonzerodivisor and termwise
`f`-torsion-free hypotheses. -/
noncomputable abbrev homologyComparisonEquiv
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (hf : f ∈ nonZeroDivisors A) (hM : IsTermwiseFTorsionFree f M) :
    ((M.homology n) ⧸ Submodule.torsionBy A (M.homology n) f) ≃ₗ[A] (η[f] M).homology n :=
  LinearEquiv.ofBijective
    (homologyComparison f M n)
    (homologyComparison_bijective f M n hf hM)

end

/-! ### Lemma_15_96_3 (from Chap15) -/
open CategoryTheory
open HomologicalComplex
open scoped nonZeroDivisors

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

/-
Domain-style sampling:
- primary domain: Berthelot-Ogus `η_f` on cochain complexes of `A`-modules and preservation of
  quasi-isomorphisms;
- sampled chapter/project owner declarations in this domain:
  `BerthelotOgusInt.complex`,
  `BerthelotOgusInt.map`,
  `NatModuleCochainComplex`,
  `etaFMap`;
- best owner abstraction:
  `source-facing`: Lemma `15.96.3` for arbitrary `ℤ`-indexed complexes of `f`-torsion-free
    `A`-modules;
  `core/canonical`: the Berthelot-Ogus owner layer `BerthelotOgusInt.complex` and
    `BerthelotOgusInt.map` on `ModuleComplex A`;
  `bridge/view`: the bounded-below transport `etaFMap` on `NatModuleCochainComplex A`;
- primitive data vs derived API: the primitive data are only the complexes, the morphism, the
  nonzerodivisor hypothesis, and the termwise `f`-torsion-free hypotheses. The bounded-below
  `ℕ`-indexed statement is derived by transporting the owner morphism across
  `etaFExtendRestrictionIso`, so it should remain a bridge corollary rather than the main owner.
-/

namespace BerthelotOgusInt

-- Proof sketch: identify the homology of `η[f] K` and `η[f] L` with the quotients
-- `H^i(K) / H^i(K)[f]` and `H^i(L) / H^i(L)[f]` by the Berthelot-Ogus comparison, observe that
-- the induced map on these quotients is an isomorphism because `φ` is a quasi-isomorphism, and
-- use naturality of the comparison maps to conclude that `map f φ` induces isomorphisms on every
-- cohomology group.
/-- Lemma 15.96.3, owner-level form: if `f` is a nonzerodivisor in `A`,
`φ : K^\bullet ⟶ L^\bullet` is a quasi-isomorphism, and both complexes are termwise
`f`-torsion free, then the induced map `η_f K^\bullet ⟶ η_f L^\bullet` is again a
quasi-isomorphism. -/
theorem map_quasiIso
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L)
    (hf : f ∈ nonZeroDivisors A) (hφ : QuasiIso φ)
    (hK : IsTermwiseFTorsionFree f K) (hL : IsTermwiseFTorsionFree f L) :
    QuasiIso (map f φ) := by
  sorry

end BerthelotOgusInt

-- Proof sketch: transport the owner-level quasi-isomorphism theorem
-- `BerthelotOgusInt.map_quasiIso` from `M.extend ComplexShape.embeddingUpNat` and
-- `N.extend ComplexShape.embeddingUpNat` across the canonical restriction isomorphisms
-- `etaFExtendRestrictionIso`.
/-- Lemma 15.96.3, bounded-below bridge/view: if `f` is a nonzerodivisor in `A`,
`φ : M^\bullet ⟶ N^\bullet` is a quasi-isomorphism, and both nonnegative complexes are termwise
`f`-torsion free, then the induced map `η_f M^\bullet ⟶ η_f N^\bullet` is again a
quasi-isomorphism. -/
theorem etaFMap_quasiIso
    (f : A) {M N : NatModuleCochainComplex A} (φ : M ⟶ N)
    (hf : f ∈ nonZeroDivisors A) (hφ : QuasiIso φ)
    (hM : IsTermwiseFTorsionFree f M) (hN : IsTermwiseFTorsionFree f N) :
    QuasiIso (etaFMap f φ) := by
  sorry

end

/-! ### Lemma_15_96_4 (from Chap15) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure
open scoped nonZeroDivisors

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: left-derived endofunctors on derived categories, built from the Berthelot-Ogus
  operator on bounded-below cochain complexes of `A`-modules;
- sampled owner declarations in the project:
  `fullSubcategoryLocalizationSystem`,
  `HomotopyCategory.Plus.quotient`,
  `mapBoundedBelowHomotopyToDerivedBelow`,
  `Functor.totalLeftDerived`,
  `Functor.ComputesLeftDerivedAt`;
- best owner abstraction:
  `source-facing`: Lemma `15.96.4`, asserting existence of a derived endofunctor whose
    representative-level action on termwise `f`-torsion-free nonnegative complexes is `η_f`;
  `core/canonical`: the restricted quasi-isomorphism system on the torsion-free full subcategory,
    the bounded-below localization chain
    `Comp⁺(A) ⥤ K⁺(A) ⥤ D⁺(A) ⥤ D(A)`, and the Chapter `13` owners
    `Functor.HasLeftDerivedFunctor` / `Functor.ComputesLeftDerivedAt`;
  `bridge/view`: the full subcategory of termwise `f`-torsion-free complexes and the comparison
    natural isomorphism on representatives.
- primitive data vs derived API: the primitive data are the source-facing `η_f` endofunctor on
  `NatModuleCochainComplex A`, the torsion-free full subcategory, the restricted quasi-isomorphism
  system, and the canonical functor from nonnegative complexes to the derived category through the
  bounded-below owner layer. The theorem-level existence statement is derived API and should be
  expressed through the Chapter `13` derived/localization owners, with the raw existential
  factorization kept only as a consequence.
-/

/-- The object property of being termwise `f`-torsion free for an `ℕ`-indexed cochain complex of
`A`-modules. -/
abbrev fTorsionFreeNatComplexProperty (f : A) : ObjectProperty (NatModuleCochainComplex A) :=
  IsTermwiseFTorsionFree f

/-- The full subcategory of `ℕ`-indexed cochain complexes of `A`-modules whose terms are
`f`-torsion free. -/
abbrev FTorsionFreeNatComplex (A : Type u) [CommRing A] (f : A) :=
  (fTorsionFreeNatComplexProperty f).FullSubcategory

/-- The quasi-isomorphism system on the full subcategory of termwise `f`-torsion-free
`ℕ`-indexed cochain complexes of `A`-modules. -/
abbrev fTorsionFreeNatComplexQuasiIso (f : A) :
    MorphismProperty (FTorsionFreeNatComplex A f) :=
  fullSubcategoryLocalizationSystem
    (fTorsionFreeNatComplexProperty f)
    (HomologicalComplex.quasiIso (ModuleCat A) (up ℕ))

-- Proof sketch: each term of `etaFComplex f M` is a submodule of the corresponding term of `M`,
-- so injectivity of multiplication by `f` on `M.X n` restricts to injectivity on the degree-`n`
-- term of `η_f M`.
/-- The Berthelot-Ogus complex of a termwise `f`-torsion-free complex is again termwise
`f`-torsion free. -/
theorem etaFComplex_preserves_termwiseFTorsionFree
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M) :
    IsTermwiseFTorsionFree f (η[f] M) := sorry

-- Proof sketch: `etaFMap f (𝟙 M)` is obtained by conjugating the owner-level identity morphism
-- `BerthelotOgusInt.map f (extendMap (𝟙 M) _)` by the canonical restriction isomorphisms from
-- `Lemma_15_96_2`, so it is itself the identity.
/-- The Berthelot-Ogus construction sends identity morphisms of complexes to identity morphisms. -/
theorem etaFMap_id (f : A) (M : NatModuleCochainComplex A) :
    etaFMap f (𝟙 M) = 𝟙 (η[f] M) := sorry

-- Proof sketch: `etaFMap` is the bounded-below bridge of the owner-level functorial map
-- `BerthelotOgusInt.map`. Functoriality of `extendMap`, `BerthelotOgusInt.map`, and
-- `restrictionMap` gives the composite formula after conjugating by the canonical restriction
-- isomorphisms.
/-- The Berthelot-Ogus construction sends composites of morphisms of complexes to composites. -/
theorem etaFMap_comp (f : A) {M N K : NatModuleCochainComplex A}
    (φ : M ⟶ N) (ψ : N ⟶ K) :
    etaFMap f (φ ≫ ψ) = etaFMap f φ ≫ etaFMap f ψ := sorry

/-- The Berthelot-Ogus operator as an endofunctor on `ℕ`-indexed cochain complexes. -/
def etaFEndofunctor (f : A) : NatModuleCochainComplex A ⥤ NatModuleCochainComplex A where
  obj M := η[f] M
  map φ := etaFMap f φ
  map_id M := etaFMap_id f M
  map_comp φ ψ := etaFMap_comp f φ ψ

/-- The Berthelot-Ogus operator on the full subcategory of termwise `f`-torsion-free
`ℕ`-indexed cochain complexes. -/
def etaFTorsionFreeEndofunctor (f : A) :
    FTorsionFreeNatComplex A f ⥤ FTorsionFreeNatComplex A f :=
  (fTorsionFreeNatComplexProperty f).lift
    ((fTorsionFreeNatComplexProperty f).ι ⋙ etaFEndofunctor f)
    (fun M ↦ etaFComplex_preserves_termwiseFTorsionFree f M.obj M.property)

/-- The extension of an `ℕ`-indexed cochain complex of `A`-modules to a bounded below
`ℤ`-indexed cochain complex. -/
noncomputable def natComplexToPlus :
    NatModuleCochainComplex A ⥤ CochainComplex.Plus (ModuleCat A) :=
  (CochainComplex.plus (ModuleCat A)).lift
    (embeddingUpNat.extendFunctor (ModuleCat A))
    (fun M ↦ ⟨0, by
      change CochainComplex.IsStrictlyGE (M.extend embeddingUpNat) 0
      infer_instance⟩)

/-- The functor from `ℕ`-indexed cochain complexes of `A`-modules to the derived category,
obtained by passing through the canonical bounded-below homotopy and derived owners from
Chapter `13`. -/
noncomputable def natComplexToDerived :
    NatModuleCochainComplex A ⥤ DerivedCategory (ModuleCat A) :=
  natComplexToPlus ⋙
    HomotopyCategory.Plus.quotient (ModuleCat A) ⋙
    mapBoundedBelowHomotopyToDerivedBelow ⋙
    (t.plus : ObjectProperty (DerivedCategory (ModuleCat A))).ι

-- Proof sketch: let `𝒯` be the full subcategory of termwise `f`-torsion-free complexes.
-- Flat resolutions give quasi-isomorphic representatives in `𝒯`, so the localization of `𝒯`
-- by quasi-isomorphisms identifies with `D(A)`. Lemma `15.96.3` shows that `η_f` preserves
-- quasi-isomorphisms on `𝒯`, hence it descends through this localization to the required
-- additive endofunctor, and every torsion-free representative computes this left derived functor.
/-- Lemma 15.96.4, canonical Chapter `13` form: for a ring `A` and a nonzerodivisor `f : A`,
the functor on termwise `f`-torsion-free representatives obtained by applying `η_f` and then
passing to the derived category admits a left derived functor along the canonical representative
functor from the torsion-free full subcategory to `D(A)`, and every torsion-free representative
computes that left derived functor. -/
theorem exists_left_derived_etaF_functor
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    let L : FTorsionFreeNatComplex A f ⥤ DerivedCategory (ModuleCat A) :=
      (fTorsionFreeNatComplexProperty f).ι ⋙ natComplexToDerived
    let ηL : FTorsionFreeNatComplex A f ⥤ DerivedCategory (ModuleCat A) :=
      etaFTorsionFreeEndofunctor f ⋙ L
    ∃ hL : Functor.IsLocalization L (fTorsionFreeNatComplexQuasiIso f),
      let _ : Functor.IsLocalization L (fTorsionFreeNatComplexQuasiIso f) := hL
      ηL.HasLeftDerivedFunctor (fTorsionFreeNatComplexQuasiIso f) ∧
        ∀ X : FTorsionFreeNatComplex A f,
          ηL.ComputesLeftDerivedAt (fTorsionFreeNatComplexQuasiIso f) X := sorry

-- Proof sketch: once the localization instance and left-derived existence statement above are in
-- place, take the canonical total left derived functor and use that each torsion-free
-- representative computes it. Definition `13.14.10` upgrades objectwise computation to
-- invertibility of the total counit components, yielding a natural isomorphism on representatives.
/-- Lemma 15.96.4, existential corollary: the canonical Chapter `13` derived-functor statement
implies the traditional formulation that there exists an additive endofunctor on `D(A)` whose
value on a termwise `f`-torsion-free representative is `η_f` of that representative. -/
theorem exists_left_derived_etaF_functor_iso
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    let L : FTorsionFreeNatComplex A f ⥤ DerivedCategory (ModuleCat A) :=
      (fTorsionFreeNatComplexProperty f).ι ⋙ natComplexToDerived
    let ηL : FTorsionFreeNatComplex A f ⥤ DerivedCategory (ModuleCat A) :=
      etaFTorsionFreeEndofunctor f ⋙ L
    ∃ (F : DerivedCategory (ModuleCat A) ⥤ DerivedCategory (ModuleCat A)) (_ : F.Additive),
      Nonempty (L ⋙ F ≅ ηL) := sorry

end

/-! ### Remark_15_96_5 (from Chap15) -/
open CategoryTheory
open HomologicalComplex
open CochainComplex
open scoped BerthelotOgusInt

universe u v w

noncomputable section

variable {A : Type u} [CommRing A]

/- Domain-style sampling for the reduction owner:
- primary domain: reduction modulo an ideal of cochain complexes of `A`-modules, and the
  source-facing Berthelot-Ogus reduction `η_f(K^\bullet) / f η_f(K^\bullet)`;
- sampled owner declarations:
  `CochainComplex (ModuleCat A) ι`,
  `LinearMap.reduceModIdeal`,
  `ModuleCat.restrictScalars`,
  `BerthelotOgusInt.complex`;
- best owner abstraction:
  `core/canonical`: reduction modulo an ideal of a cochain complex, owned once by
    `CochainComplex.reduceModIdeal` together with its induced map
    `CochainComplex.reduceModIdealMap` and scalar-restricted view
    `CochainComplex.reduceModIdealA`;
  `source-facing`: the Berthelot-Ogus reduction owners
    `BerthelotOgusEtaReduction.complex` together with the quotient-ring comparison map
    `BerthelotOgusEtaReduction.toHomology`;
  `bridge/view`: the scalar-restricted `A`-linear view, the nonnegative-degree restriction and
  homology identifications for `CochainComplex.reduceModIdealA`, and the bounded-below
    comparison map `BerthelotOgusEtaReduction.Nat.toHomology`;
  `primitive data vs derived API`: the primitive data are the quotient terms and induced
  differentials. The Berthelot-Ogus reduction and the quotient-to-homology maps are derived from
  that owner construction, so the file should not keep parallel local bounded-below copies of the
  quotient-ring reduction complex or cocycle map. -/

namespace CochainComplex

/-- The degree-`i` differential on the reduction of a cochain complex modulo `I`. -/
private abbrev reduceModIdealDifferential
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) (i : ι) :
    ModuleCat.of (A ⧸ I) (K.X i ⧸ I • (⊤ : Submodule A (K.X i))) ⟶
      ModuleCat.of (A ⧸ I) (K.X (i + 1) ⧸ I • (⊤ : Submodule A (K.X (i + 1)))) :=
  ModuleCat.ofHom <| (K.d i (i + 1)).hom.reduceModIdeal I

-- Proof sketch: the reduced differential is induced from the differential of `K`, so two
-- successive reduced differentials factor through the quotient of `d ≫ d = 0`.
/-- Two successive reduced differentials compose to zero. -/
private theorem reduceModIdealDifferential_sq
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) (i : ι) :
    reduceModIdealDifferential I K i ≫ reduceModIdealDifferential I K (i + 1) = 0 := sorry

/-- The cochain complex obtained by reducing every term of `K` modulo `I`, viewed over the
quotient ring `A ⧸ I`. -/
abbrev reduceModIdeal
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) :
    CochainComplex (ModuleCat.{v} (A ⧸ I)) ι :=
  let _ : DecidableEq ι := Classical.decEq ι
  CochainComplex.of
    (fun i ↦ ModuleCat.of (A ⧸ I) (K.X i ⧸ I • (⊤ : Submodule A (K.X i))))
    (fun i ↦ reduceModIdealDifferential I K i)
    (fun i ↦ reduceModIdealDifferential_sq I K i)

/-- The scalar-restricted `A`-linear view of `K / IK`. -/
abbrev reduceModIdealA
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) :
    CochainComplex (ModuleCat.{v} A) ι :=
  ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ι)).obj
    (reduceModIdeal I K)

/-- The morphism induced on reduced complexes by a morphism of cochain complexes. -/
abbrev reduceModIdealMap
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    {K L : CochainComplex (ModuleCat.{v} A) ι} (I : Ideal A) (φ : K ⟶ L) :
    reduceModIdeal I K ⟶ reduceModIdeal I L where
  f i := ModuleCat.ofHom <| (φ.f i).hom.reduceModIdeal I
  comm' i j hij := by
    rcases hij with rfl
    sorry

/-- The scalar-restricted `A`-linear view of the morphism induced on reduced complexes. -/
abbrev reduceModIdealAMap
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    {K L : CochainComplex (ModuleCat.{v} A) ι} (I : Ideal A) (φ : K ⟶ L) :
    reduceModIdealA I K ⟶ reduceModIdealA I L :=
  ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ι)).map
    (reduceModIdealMap I φ)

/-- The quotient submodule `IM` is preserved by the standard degree identification
`(M.extend embeddingUpNat).X i ≅ M.X i`. -/
private theorem smul_top_extendXIso_map
    (I : Ideal A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (I • (⊤ : Submodule A ((M.extend ComplexShape.embeddingUpNat).X (i : ℤ)))).map
        (M.extendXIso ComplexShape.embeddingUpNat (by simp)).toLinearEquiv.toLinearMap =
      I • (⊤ : Submodule A (M.X i)) := by
  sorry

/-- Restricting the reduction of `M.extend ComplexShape.embeddingUpNat` to nonnegative degrees
recovers the reduction of `M`. -/
private noncomputable def reduceModIdealARestrictionIso
    (I : Ideal A) (M : NatModuleCochainComplex A) :
    (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).restriction
        (ComplexShape.embeddingUpIntGE 0) ≅
      reduceModIdealA I M :=
  Hom.isoOfComponents
    (fun i ↦
      ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).restrictionXIso
          (ComplexShape.embeddingUpIntGE 0) (by simp)) ≪≫
        LinearEquiv.toModuleIso
          (Submodule.Quotient.equiv
            (I • (⊤ : Submodule A ((M.extend ComplexShape.embeddingUpNat).X (i : ℤ))))
            (I • (⊤ : Submodule A (M.X i)))
            (M.extendXIso ComplexShape.embeddingUpNat (by simp)).toLinearEquiv
            (smul_top_extendXIso_map I M i)))
    (by
      sorry)

/-- The degree `-1` term of the reduction of an extended nonnegative cochain complex is zero. -/
private theorem reduceModIdealA_isZero_negOne
    (I : Ideal A) (M : NatModuleCochainComplex A) :
    CategoryTheory.Limits.IsZero
      ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).X (-1)) := by
  let hzero : CategoryTheory.Limits.IsZero ((M.extend ComplexShape.embeddingUpNat).X (-1 : ℤ)) :=
    M.isZero_extend_X ComplexShape.embeddingUpNat (-1) (by
      intro i hi
      change (i : ℤ) = -1 at hi
      have h : (0 : ℤ) ≤ (i : ℤ) := by
        exact_mod_cast Nat.zero_le i
      rw [hi] at h
      norm_num at h)
  letI : Subsingleton ((M.extend ComplexShape.embeddingUpNat).X (-1 : ℤ)) :=
    ModuleCat.subsingleton_of_isZero hzero
  letI : Subsingleton ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).X (-1)) := by
    change Subsingleton
      (((M.extend ComplexShape.embeddingUpNat).X (-1 : ℤ)) ⧸
        I • (⊤ : Submodule A ((M.extend ComplexShape.embeddingUpNat).X (-1 : ℤ))))
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

/-- The canonical homology identification between the reduction of
`M.extend ComplexShape.embeddingUpNat` and the reduction of `M`. -/
noncomputable abbrev reduceModIdealAHomologyIso
    (I : Ideal A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).homology (i : ℤ) ≅
      (reduceModIdealA I M).homology i :=
  match i with
  | 0 =>
      have h0 : (ComplexShape.embeddingUpIntGE 0).f 0 = (0 : ℤ) := by
        simp [ComplexShape.embeddingUpIntGE]
      have h1 : (ComplexShape.embeddingUpIntGE 0).f 1 = (1 : ℤ) := by
        simp [ComplexShape.embeddingUpIntGE]
      have hnext : (ComplexShape.up ℤ).next (0 : ℤ) = (1 : ℤ) := by
        simpa using (CochainComplex.next ℤ (0 : ℤ))
      let e₀ :
          (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).homology (0 : ℤ) ≅
            ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).restriction
              (ComplexShape.embeddingUpIntGE 0)).homology 0 :=
        (((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).isoHomologyπ
              (-1) 0 (by simpa using (CochainComplex.prev ℤ (0 : ℤ)))
              (by
                simpa using
                  (reduceModIdealA_isZero_negOne I M).eq_of_src
                    ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).d (-1) 0) 0)).symm ≪≫
            ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).restrictionCyclesIso
              (ComplexShape.embeddingUpIntGE 0) 0 1 (by simp) h0 h1 hnext).symm) ≪≫
          CochainComplex.isoHomologyπ₀
            ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).restriction
              (ComplexShape.embeddingUpIntGE 0))
      e₀ ≪≫ homologyMapIso (reduceModIdealARestrictionIso I M) 0
  | n + 1 =>
      have hi : (ComplexShape.embeddingUpIntGE 0).f n = (n : ℤ) := by
        simp [ComplexShape.embeddingUpIntGE]
      have hj : (ComplexShape.embeddingUpIntGE 0).f (n + 1) = ((n + 1 : ℕ) : ℤ) := by
        simp [ComplexShape.embeddingUpIntGE]
      have hk : (ComplexShape.embeddingUpIntGE 0).f (n + 2) = ((n + 2 : ℕ) : ℤ) := by
        simp [ComplexShape.embeddingUpIntGE]
      have hprev : (ComplexShape.up ℤ).prev (((n + 1 : ℕ) : ℤ)) = (n : ℤ) := by
        simp
      have hnext : (ComplexShape.up ℤ).next (((n + 1 : ℕ) : ℤ)) = ((n + 2 : ℕ) : ℤ) := by
        calc
          (ComplexShape.up ℤ).next (((n + 1 : ℕ) : ℤ)) = (((n + 1 : ℕ) : ℤ) + 1) :=
            CochainComplex.next ℤ (((n + 1 : ℕ) : ℤ))
          _ = ((n + 2 : ℕ) : ℤ) := by
            exact_mod_cast (show n + 1 + 1 = n + 2 by omega)
      ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).restrictionHomologyIso
          (ComplexShape.embeddingUpIntGE 0) n (n + 1) (n + 2) (by simp) (by simp)
          hi hj hk hprev hnext
        ).symm ≪≫
        homologyMapIso (reduceModIdealARestrictionIso I M) (n + 1)

end CochainComplex

namespace BerthelotOgusEtaReduction

open BerthelotOgusInt

/-- The canonical inclusion `η_f(K^\bullet) ⟶ K^\bullet`. -/
private def etaInclusion (f : A) (K : ModuleComplex A) :
    η[f] K ⟶ K where
  f i := ModuleCat.ofHom (degreeSubmodule f K i).subtype
  comm' i j hij := by
    rcases hij with rfl
    sorry

/-- The bounded-below `ℤ`-indexed bridge reduction
`η_f(K^\bullet) / f η_f(K^\bullet)` over `A ⧸ (f)`. -/
abbrev complex (f : A) (K : ModuleComplex A) :
    ModuleComplex (A ⧸ principalIdeal f) :=
  reduceModIdeal (principalIdeal f) (BerthelotOgusInt.complex f K)

private abbrev toRawReductionLinear
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    (complex f K).X i →ₗ[A ⧸ principalIdeal f]
      (reduceModIdeal (principalIdeal f) K).X i :=
  ((reduceModIdealMap (principalIdeal f) (etaInclusion f K)).f i).hom

-- Proof sketch: an element of `η_f(K)^i` reduces to a cocycle in `K^i / fK^i` because its
-- differential is already divisible by `f` in degree `i + 1`.
/-- The canonical quotient map from the reduced Berthelot-Ogus term to the reduced complex lands in
cycles. -/
private theorem toRawReductionLinear_comp_d_eq_zero
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    ModuleCat.ofHom (toRawReductionLinear f K i) ≫
        (reduceModIdeal (principalIdeal f) K).d i (i + 1) =
      0 := sorry

/-- The canonical map
`(η_f(K^\bullet)^i / f η_f(K^\bullet)^i) ⟶ Z^i(K^\bullet / f K^\bullet)`. -/
abbrev toCycles (f : A) (K : ModuleComplex A) (i : ℤ) :
    (complex f K).X i ⟶ (reduceModIdeal (principalIdeal f) K).cycles i :=
  (reduceModIdeal (principalIdeal f) K).liftCycles'
    (ModuleCat.ofHom (toRawReductionLinear f K i))
    (i + 1) (by simp) (toRawReductionLinear_comp_d_eq_zero f K i)

/-- The canonical map
`(η_f(K^\bullet)^i / f η_f(K^\bullet)^i) ⟶ H^i(K^\bullet / f K^\bullet)`. -/
abbrev toHomology (f : A) (K : ModuleComplex A) (i : ℤ) :
    (complex f K).X i ⟶ (reduceModIdeal (principalIdeal f) K).homology i :=
  toCycles f K i ≫ (reduceModIdeal (principalIdeal f) K).homologyπ i

namespace Nat

/-- The canonical inclusion `η_f(M^\bullet) ⟶ M^\bullet`. -/
private def etaInclusion (f : A) (M : NatModuleCochainComplex A) :
    η[f] M ⟶ M where
  f i := ModuleCat.ofHom (etaFDegreeSubmodule f M i).subtype
  comm' i j hij := by
    rcases hij with rfl
    sorry

private abbrev toRawReduction
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (reduceModIdealA (principalIdeal f) (η[f] M)).X i ⟶
      (reduceModIdealA (principalIdeal f) M).X i :=
  (reduceModIdealAMap (principalIdeal f) (etaInclusion f M)).f i

/-- The scalar-restricted `A`-linear quotient map induced by the canonical inclusion
`η_f(M^\bullet) ⟶ M^\bullet`. -/
private abbrev toRawReductionLinear
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (reduceModIdealA (principalIdeal f) (η[f] M)).X i →ₗ[A]
      (reduceModIdealA (principalIdeal f) M).X i :=
  (toRawReduction f M i).hom

/-- The canonical bounded-below map
`(η_f(M^\bullet)^i / f η_f(M^\bullet)^i) ⟶ H^i(M^\bullet / f M^\bullet)`. -/
abbrev toHomology (f : A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (reduceModIdealA (principalIdeal f) (η[f] M)).X i ⟶
      (reduceModIdealA (principalIdeal f) M).homology i :=
  let _ : Module A ↑((reduceModIdeal (principalIdeal f) (η[f] M)).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
  let _ : Module A ↑((reduceModIdeal (principalIdeal f) M).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
  (reduceModIdealA (principalIdeal f) M).liftCycles'
      (toRawReduction f M i)
      (i + 1) (by simp)
      (by
        -- This is the scalar-restricted bounded-below form of the owner cocycle calculation.
        sorry) ≫
    (reduceModIdealA (principalIdeal f) M).homologyπ i

end Nat

end BerthelotOgusEtaReduction

/-! ### Lemma_15_96_6 (from Chap15) -/
noncomputable section

open CategoryTheory
open CochainComplex
open ModFSquared.Nat

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: the Berthelot-Ogus reduction complex from Remark `15.96.5` and its comparison
  with the canonical Bockstein cohomology complex;
- sampled owner declarations:
  `BerthelotOgusEtaReduction.Nat.toHomology`,
  `bockstein_factorization_naturality`,
  `modfCohomologyBocksteinComplex`,
  `QuasiIso`;
- best owner abstraction:
  `source-facing`: the scalar-restricted bounded-below bridge reduction complex
    `CochainComplex.reduceModIdealA (principalIdeal f) (η[f] M)`;
  `core/canonical`: the target complex `modfCohomologyBocksteinComplex f M hM`;
  `bridge/view`: the source-owned comparison map
    `BerthelotOgusEtaReduction.Nat.toModfCohomologyBocksteinComplex` and its quasi-isomorphism;
- primitive data vs derived API: the primitive source data are the owner declarations from Remark
  `15.96.5`. The target Bockstein complex is derived, so this file should state only the canonical
  comparison map to that target. -/

namespace BerthelotOgusEtaReduction
namespace Nat

-- Proof sketch: use the canonical reduction complex from Remark `15.96.5`. The quotient by its
-- acyclic boundary subcomplex identifies degreewise with the homology of `K^\bullet / fK^\bullet`,
-- and the induced differential on those quotients is the canonical Bockstein differential from
-- `15.96.5.2`; equivalently, this is the bounded-below source-facing specialization of the
-- factorization square from `15.96.5.1`. Hence the quotient map gives a quasi-isomorphism from
-- the canonical reduction complex to `modfCohomologyBocksteinComplex f M hM`.
/-- The canonical quotient maps
`(η_f M)^i / f(η_f M)^i ⟶ H^i(M^\bullet / fM^\bullet)` intertwine the differential on the
reduced Berthelot-Ogus complex with the Berthelot-Ogus Bockstein differential. -/
theorem toHomology_comm_bockstein
    (f : A) (M : NatModuleCochainComplex A)
    (hM : IsTermwiseFTorsionFree f M) (i : ℕ) :
    CommSq
      (toHomology f M i)
      ((reduceModIdealA (principalIdeal f) (η[f] M)).d i (i + 1))
      (bockstein f M i hM)
      (toHomology f M (i + 1)) := by
  sorry

/-- The canonical comparison morphism from the Berthelot-Ogus reduction complex to the Bockstein
cohomology complex. -/
def toModfCohomologyBocksteinComplex
    (f : A) (M : NatModuleCochainComplex A)
    (hM : IsTermwiseFTorsionFree f M) :
    reduceModIdealA (principalIdeal f) (η[f] M) ⟶ modfCohomologyBocksteinComplex f M hM where
  f i := by
    simpa only [modfCohomologyBocksteinComplex_X] using toHomology f M i
  comm' i j hij := by
    rcases hij with rfl
    simpa only [modfCohomologyBocksteinComplex_d] using
      (toHomology_comm_bockstein f M hM i).w

/-- Lemma 15.96.6: let `A` be a ring, let `f ∈ A`, and let `K^\bullet` be a cochain complex of
`A`-modules on which multiplication by `f` is injective in every degree. Then
the scalar-restricted `A`-linear view of the canonical Berthelot-Ogus reduction complex
`η_f K^\bullet / f(η_f K^\bullet)` from Remark `15.96.5` is quasi-isomorphic to the canonical
Bockstein cohomology complex `H^\bullet(K^\bullet / fK^\bullet)` of `15.96.5.2`, via the
canonical comparison map. -/
theorem toModfCohomologyBocksteinComplex_quasiIso
    (f : A) (M : NatModuleCochainComplex A)
    (hM : IsTermwiseFTorsionFree f M) :
    QuasiIso (toModfCohomologyBocksteinComplex f M hM) := by
  sorry

end Nat
end BerthelotOgusEtaReduction

end
