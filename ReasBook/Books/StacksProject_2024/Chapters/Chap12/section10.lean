import Mathlib
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_10_1 (from Chap12) -/
universe u v

namespace CategoryTheory.ObjectProperty

open Limits ZeroObject

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Definition 12.10.1:
- primary domain: object properties on abelian categories defined by stability in exact
  five-term sequences;
- inspected canonical declarations:
  `ComposableArrows.Exact`,
  `ObjectProperty.IsSerreClass`,
  `ObjectProperty.IsClosedUnderKernels`,
  `ObjectProperty.IsClosedUnderCokernels`,
  and `ObjectProperty.IsClosedUnderExtensions`;
- owner abstraction: `ObjectProperty A`, with the source-facing weak-LinearRepresentations_Serre_1977 notion recorded by the
  owner predicate `IsWeakSerreClass P`;
- primitive data: a nonempty object property together with the four-out-of-five exactness
  criterion on exact `ComposableArrows A 4`;
- derived API: containment of a zero object, closure under kernels, cokernels, and extensions, and
  the bridge from the later closure characterization back to the source-facing owner.

Source/core/bridge triage:
- `source-facing`: the Stacks four-out-of-five exactness criterion for a nonempty full
  subcategory;
- `core/canonical`: the ambient owner `ObjectProperty A`;
- `bridge/view`: the derived closure-package bridge
  `isWeakSerreClass_of_closure`, together with the LinearRepresentations_Serre_1977-to-weak implication below. -/

/-- Definition 12.10.1 (2): a weak LinearRepresentations_Serre_1977 subcategory is a nonempty full subcategory such that in
every exact sequence `A₀ ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄`, membership of `A₀`, `A₁`, `A₃`, and `A₄`
forces membership of `A₂`. This is formalized on the canonical owner `ObjectProperty A`. -/
class IsWeakSerreClass (P : ObjectProperty A) : Prop extends P.Nonempty where
  prop_X₂_of_exact₄ {S : ComposableArrows A 4} (hS : S.Exact)
      (h₀ : P (S.obj 0)) (h₁ : P (S.obj 1)) (h₃ : P (S.obj 3)) (h₄ : P (S.obj 4)) :
      P (S.obj 2)

variable (P : ObjectProperty A)

private lemma mk₄_exact {X₀ X₁ X₂ X₃ X₄ : A} {f : X₀ ⟶ X₁} {g : X₁ ⟶ X₂} {h : X₂ ⟶ X₃}
    {i : X₃ ⟶ X₄} (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) (hhi : h ≫ i = 0)
    (hex₀ : (ShortComplex.mk f g hfg).Exact) (hex₁ : (ShortComplex.mk g h hgh).Exact)
    (hex₂ : (ShortComplex.mk h i hhi).Exact) :
    (ComposableArrows.mk₄ f g h i).Exact := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_⟩
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl
    · dsimp [ComposableArrows.mk₄, ComposableArrows.mk₃, ComposableArrows.mk₂]
      exact hfg
    · dsimp [ComposableArrows.mk₄, ComposableArrows.mk₃, ComposableArrows.mk₂]
      exact hgh
    · dsimp [ComposableArrows.mk₄, ComposableArrows.mk₃, ComposableArrows.mk₂]
      exact hhi
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl
    · simpa using hex₀
    · simpa using hex₁
    · simpa using hex₂

/-- Closure under extensions together with one zero object already implies closure under
isomorphisms. This is the standard strictly-fullness bridge used repeatedly below. -/
theorem isClosedUnderIsomorphisms_of_containsZero_of_closedUnderExtensions
    [P.ContainsZero] [P.IsClosedUnderExtensions] :
    P.IsClosedUnderIsomorphisms := by
  refine ⟨fun {X Y} e hX ↦ ?_⟩
  obtain ⟨Z, hZ, hPZ⟩ := P.exists_prop_of_containsZero
  let S : ShortComplex A := ShortComplex.mk e.hom (0 : Y ⟶ Z) (by simp)
  have hS : S.ShortExact := by
    exact (ShortComplex.Splitting.ofIsIsoOfIsZero S inferInstance hZ).shortExact
  exact P.prop_X₂_of_shortExact hS hX hPZ

instance [IsWeakSerreClass P] : P.ContainsZero := by
  obtain ⟨X, hX⟩ := P.exists_prop_of_nonempty
  refine ⟨(0 : A), isZero_zero _, ?_⟩
  have hS :
      (ComposableArrows.mk₄ (𝟙 X) (0 : X ⟶ (0 : A)) (0 : (0 : A) ⟶ X) (𝟙 X)).Exact := by
    refine mk₄_exact ?_ ?_ ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simpa using
        ((ShortComplex.mk (𝟙 X) (0 : X ⟶ (0 : A)) (by simp)).exact_iff_epi (by simp)).2
          (inferInstance : Epi (𝟙 X))
    · simpa using
        ((ShortComplex.mk (0 : X ⟶ (0 : A)) (0 : (0 : A) ⟶ X) (by simp)).exact_iff_epi
          (by simp)).2 (inferInstance : Epi (0 : X ⟶ (0 : A)))
    · simpa using
        ((ShortComplex.mk (0 : (0 : A) ⟶ X) (𝟙 X) (by simp)).exact_iff_mono (by simp)).2
          (inferInstance : Mono (𝟙 X))
  exact IsWeakSerreClass.prop_X₂_of_exact₄ hS hX hX hX hX

instance [IsWeakSerreClass P] : P.IsClosedUnderKernels where
  kernels_le := by
    intro _ ⟨f, k, hk, hXY⟩
    obtain ⟨Z, hZ, hPZ⟩ := P.exists_prop_of_containsZero
    letI := Fork.IsLimit.mono hk
    have hk' : IsLimit (KernelFork.ofι k.ι (show k.ι ≫ f = 0 from k.condition)) :=
      KernelFork.IsLimit.ofι' k.ι k.condition fun s hs ↦
        ⟨hk.lift (KernelFork.ofι s hs), hk.fac (KernelFork.ofι s hs) WalkingParallelPair.zero⟩
    have hS :
        (ComposableArrows.mk₄ (𝟙 Z) (0 : Z ⟶ k.pt) k.ι f).Exact := by
      refine mk₄_exact ?_ ?_ ?_ ?_ ?_ ?_
      · simp
      · simp
      · exact k.condition
      · simpa using
          ((ShortComplex.mk (𝟙 Z) (0 : Z ⟶ k.pt) (by simp)).exact_iff_epi (by simp)).2
            (inferInstance : Epi (𝟙 Z))
      · simpa using
          ((ShortComplex.mk (0 : Z ⟶ k.pt) k.ι (by simp)).exact_iff_mono (by simp)).2
            (inferInstance : Mono k.ι)
      · simpa using ShortComplex.exact_of_f_is_kernel _ hk'
    exact IsWeakSerreClass.prop_X₂_of_exact₄ hS hPZ hPZ hXY.1 hXY.2

instance [IsWeakSerreClass P] : P.IsClosedUnderCokernels where
  cokernels_le := by
    intro _ ⟨f, k, hk, hXY⟩
    obtain ⟨Z, hZ, hPZ⟩ := P.exists_prop_of_containsZero
    letI := Cofork.IsColimit.epi hk
    have hk' : IsColimit (CokernelCofork.ofπ k.π (show f ≫ k.π = 0 from k.condition)) :=
      CokernelCofork.IsColimit.ofπ' k.π k.condition fun s hs ↦
        ⟨hk.desc (CokernelCofork.ofπ s hs), hk.fac (CokernelCofork.ofπ s hs) WalkingParallelPair.one⟩
    have hS :
        (ComposableArrows.mk₄ f k.π (0 : k.pt ⟶ Z) (𝟙 Z)).Exact := by
      refine mk₄_exact ?_ ?_ ?_ ?_ ?_ ?_
      · exact k.condition
      · simp
      · simp
      · simpa using ShortComplex.exact_of_g_is_cokernel _ hk'
      · simpa using
          ((ShortComplex.mk k.π (0 : k.pt ⟶ Z) (by simp)).exact_iff_epi (by simp)).2
            (inferInstance : Epi k.π)
      · simpa using
          ((ShortComplex.mk (0 : k.pt ⟶ Z) (𝟙 Z) (by simp)).exact_iff_mono (by simp)).2
            (inferInstance : Mono (𝟙 Z))
    exact IsWeakSerreClass.prop_X₂_of_exact₄ hS hXY.1 hXY.2 hPZ hPZ

instance [IsWeakSerreClass P] : P.IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    letI := hS.mono_f
    letI := hS.epi_g
    obtain ⟨Z, hZ, hPZ⟩ := P.exists_prop_of_containsZero
    have hR :
        (ComposableArrows.mk₄ (0 : Z ⟶ S.X₁) S.f S.g (0 : S.X₃ ⟶ Z)).Exact := by
      refine mk₄_exact ?_ ?_ ?_ ?_ ?_ ?_
      · simp
      · exact S.zero
      · simp
      · simpa using
          ((ShortComplex.mk (0 : Z ⟶ S.X₁) S.f (by simp)).exact_iff_mono (by simp)).2
            (inferInstance : Mono S.f)
      · exact hS.exact
      · simpa using
          ((ShortComplex.mk S.g (0 : S.X₃ ⟶ Z) (by simp)).exact_iff_epi (by simp)).2
            (inferInstance : Epi S.g)
    exact IsWeakSerreClass.prop_X₂_of_exact₄ hR hPZ h₁ h₃ hPZ

/-- The later closure-package characterization of weak LinearRepresentations_Serre_1977 subcategories implies the original
source-facing four-out-of-five exactness criterion. This is the canonical bridge back to
Definition 12.10.1. -/
theorem isWeakSerreClass_of_closure [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] :
    IsWeakSerreClass P := by
  letI : P.Nonempty := inferInstance
  letI : P.IsClosedUnderIsomorphisms :=
    isClosedUnderIsomorphisms_of_containsZero_of_closedUnderExtensions P
  refine
    { toNonempty := inferInstance
      prop_X₂_of_exact₄ := ?_ }
  intro S hS h₀ h₁ h₃ h₄
  let S₀ : ShortComplex A := S.sc hS.toIsComplex 0
  let S₁ : ShortComplex A := S.sc hS.toIsComplex 1
  let S₂ : ShortComplex A := S.sc hS.toIsComplex 2
  have hS₀ : S₀.Exact := hS.exact 0
  have hS₁ : S₁.Exact := hS.exact 1
  have hS₂ : S₂.Exact := hS.exact 2
  have hcoim₁ : P (Abelian.coimage S₀.g) := by
    have hk :
        IsColimit
          (CokernelCofork.ofπ (Abelian.coimage.π S₀.g)
            (Abelian.comp_coimage_π_eq_zero S₀.zero)) :=
      hS₀.isColimitCoimage
    simpa using
      (P.prop_of_isColimit_cokernelCofork hk h₀ h₁ :
        P
          (CokernelCofork.ofπ (Abelian.coimage.π S₀.g)
            (Abelian.comp_coimage_π_eq_zero S₀.zero)).pt)
  have himage₂ : P (Abelian.image S₁.g) := by
    simpa [S₁, S₂] using P.prop_of_isLimit_kernelFork hS₂.isLimitImage h₃ h₄
  have hcoim₂ : P (Abelian.coimage S₁.g) := by
    exact P.prop_of_iso (Abelian.coimageIsoImage S₁.g).symm himage₂
  let T : ShortComplex A :=
    ShortComplex.mk (Abelian.factorThruCoimage S₀.g) (Abelian.coimage.π S₁.g) (by
      have hfac : Abelian.factorThruCoimage S₀.g ≫ S₁.g = 0 := by
        apply (cancel_epi (Abelian.coimage.π S₀.g)).1
        have hzero : S₀.g ≫ S₁.g = 0 := by simpa [S₀, S₁] using S₁.zero
        simpa [Category.assoc, Abelian.coimage.fac] using hzero
      exact Abelian.comp_coimage_π_eq_zero hfac)
  have hT : T.Exact := by
    let T' : ShortComplex A :=
      ShortComplex.mk S₁.f (Abelian.coimage.π S₁.g) (Abelian.comp_coimage_π_eq_zero S₁.zero)
    have hT' : T'.Exact := (S₁.exact_iff_exact_coimage_π).1 hS₁
    let φ : T' ⟶ T :=
      { τ₁ := Abelian.coimage.π S₁.f
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [S₀, S₁, T, T']
        comm₂₃ := by simp [T', T] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hT'
  exact
    P.prop_X₂_of_shortExact (ShortComplex.ShortExact.mk' hT inferInstance inferInstance)
      hcoim₁ hcoim₂

/- Definition 12.10.1 (1): a LinearRepresentations_Serre_1977 subcategory of an abelian category is the canonical
object-property predicate `IsSerreClass`, i.e. containing zero and closed under subobjects,
quotients, and extensions. -/
recall IsSerreClass

/-- Every LinearRepresentations_Serre_1977 subcategory is in particular a weak LinearRepresentations_Serre_1977 subcategory. -/
instance instIsWeakSerreClassOfIsSerreClass [P.IsSerreClass] : IsWeakSerreClass P :=
  isWeakSerreClass_of_closure P

end Abelian

end CategoryTheory.ObjectProperty

/-! ### Lemma_12_10_2 (from Chap12) -/
open CategoryTheory

universe u v

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C]

section

variable (P : ObjectProperty C) [P.IsSerreClass]

/- Lemma 12.10.2 is a `bridge/view` item: a LinearRepresentations_Serre_1977 subcategory is, via the chapter owner
abstraction from Definition 12.10.1, a weak LinearRepresentations_Serre_1977 subcategory. The primitive source-facing data
remain `P.IsSerreClass`; strict fullness and exactness are derived later from
`P.IsWeakSerreClass`. -/
recall instIsWeakSerreClassOfIsSerreClass (P : ObjectProperty C) [P.IsSerreClass] :
    P.IsWeakSerreClass

end

end CategoryTheory.ObjectProperty

/-! ### Lemma_12_10_3 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace CategoryTheory.ObjectProperty

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] (P : ObjectProperty 𝒜)

/- Domain-style sampling for Lemma 12.10.3:
- primary domain: weak LinearRepresentations_Serre_1977 object properties in abelian categories and the induced exact
  full-subcategory formalism;
- sampled owner declarations:
  `ObjectProperty.IsWeakSerreClass`,
  `ObjectProperty.isWeakSerreClass_of_closure`,
  `ObjectProperty.IsClosedUnderBinaryProducts`,
  `ObjectProperty.IsClosedUnderFiniteProducts`,
  `ObjectProperty.FullSubcategory`;
- best owner abstraction: an object property `P : ObjectProperty 𝒜` equipped with
  `[P.IsWeakSerreClass]`;
- primitive data: the source-facing weak-LinearRepresentations_Serre_1977 four-out-of-five exactness criterion from
  Definition 12.10.1;
- derived API: containing zero, closure under kernels/cokernels/extensions and then closure under
  isomorphisms and finite products, the abelian structure on `P.FullSubcategory`, and exactness
  of the inclusion `P.ι`.

Source/core/bridge triage:
- `source-facing`: the Stacks consequences for a weak LinearRepresentations_Serre_1977 subcategory;
- `core/canonical`: the `ObjectProperty` owner `P`, together with `P.FullSubcategory` and `P.ι`;
- `bridge/view`: the exactness statement for the inclusion functor, derived from the canonical
  kernel/cokernel preservation API. -/

/- Companion bridge: `isWeakSerreClass_of_closure` recovers the source-facing owner abstraction
from the later closure-package characterization. -/
#check isWeakSerreClass_of_closure

/- Definition 12.10.1 stores the primitive four-out-of-five exactness criterion directly. -/
#check IsWeakSerreClass.prop_X₂_of_exact₄

/-- A weak LinearRepresentations_Serre_1977 subcategory is closed under isomorphisms. -/
instance [IsWeakSerreClass P] :
    P.IsClosedUnderIsomorphisms :=
  isClosedUnderIsomorphisms_of_containsZero_of_closedUnderExtensions P

/-- A weak LinearRepresentations_Serre_1977 subcategory is closed under binary products. -/
instance [IsWeakSerreClass P] :
    P.IsClosedUnderBinaryProducts := by
  refine IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  have hXY : P (X ⊞ Y) := P.prop_biprod (hF _) (hF _)
  let hPair :
      IsLimit ((Cone.postcompose (diagramIsoPair F).hom).obj (limit.cone F)) :=
    (IsLimit.postcomposeHomEquiv (diagramIsoPair F) _).2 (limit.isLimit F)
  exact P.prop_of_iso (IsLimit.conePointUniqueUpToIso hPair (BinaryBiproduct.isLimit X Y)).symm
    hXY

/-- A weak LinearRepresentations_Serre_1977 subcategory is closed under finite products. -/
instance [IsWeakSerreClass P] : P.IsClosedUnderFiniteProducts := by
  exact .mk'

section

variable [IsWeakSerreClass P]

/- Lemma 12.10.3 (1): a weak LinearRepresentations_Serre_1977 subcategory contains a zero object. -/
#synth P.ContainsZero

/- Lemma 12.10.3 (2): a weak LinearRepresentations_Serre_1977 subcategory is strictly full, i.e. closed under
isomorphisms. -/
#synth P.IsClosedUnderIsomorphisms

/- Lemma 12.10.3 (3): kernels and cokernels in `𝒜` of morphisms between objects of the weak
LinearRepresentations_Serre_1977 subcategory again belong to the subcategory. -/
#synth P.IsClosedUnderKernels
#synth P.IsClosedUnderCokernels

/- Lemma 12.10.3 (4): an extension of two objects of a weak LinearRepresentations_Serre_1977 subcategory again belongs
to the subcategory. -/
#synth P.IsClosedUnderExtensions

/- Lemma 12.10.3 (Moreover): the full subcategory cut out by a weak LinearRepresentations_Serre_1977 subcategory of an
abelian category is itself abelian. This is the canonical mathlib instance on
`P.FullSubcategory`, derived from zero, kernel, cokernel, and finite-product closure. -/
#synth Abelian P.FullSubcategory

/-- Lemma 12.10.3 (Moreover): the inclusion functor of a weak LinearRepresentations_Serre_1977 subcategory into the ambient
abelian category is exact. -/
theorem weakSerreSubcategory_inclusion_exact :
    exactFunctor P.FullSubcategory 𝒜 P.ι := by
  rw [exactFunctor_iff]
  constructor
  · letI : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) P.ι :=
      fun {_ _} f ↦ P.preservesKernels_ι f
    exact P.ι.preservesFiniteLimits_of_preservesKernels
  · letI : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) P.ι :=
      fun {_ _} f ↦ P.preservesCokernels_ι f
    exact P.ι.preservesFiniteColimits_of_preservesCokernels

/-- The inclusion functor of a weak LinearRepresentations_Serre_1977 subcategory preserves finite limits. -/
theorem weakSerreSubcategory_inclusion_preservesFiniteLimits :
    PreservesFiniteLimits P.ι :=
  (exactFunctor_iff P.ι).1 (weakSerreSubcategory_inclusion_exact P) |>.1

/-- The inclusion functor of a weak LinearRepresentations_Serre_1977 subcategory preserves finite colimits. -/
theorem weakSerreSubcategory_inclusion_preservesFiniteColimits :
    PreservesFiniteColimits P.ι :=
  (exactFunctor_iff P.ι).1 (weakSerreSubcategory_inclusion_exact P) |>.2

end

end CategoryTheory.ObjectProperty

/-! ### Lemma_12_10_4 (from Chap12) -/
universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace ExactFunctor

section

open Functor (kernel)

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ₑ B)

/- Lemma 12.10.4: for an exact functor `F : \mathcal A ⥤ₑ \mathcal B` between abelian
categories, the kernel object property `kernel F.obj` is a LinearRepresentations_Serre_1977 class.

Domain-style sampling:
- primary domain: exact functors and LinearRepresentations_Serre_1977 classes of object properties in abelian categories;
- sampled owner declarations: `Functor.kernel`, `ObjectProperty.IsSerreClass`, and the generic
  inverse-image instance giving `IsSerreClass (P.inverseImage F)` when `F` preserves finite limits
  and finite colimits;
- owner abstraction: `Functor.kernel` on the underlying functor `F.obj`;
- primitive data: the object property `IsZero (F.obj.obj X)`;
- derived API: the LinearRepresentations_Serre_1977-class structure on that inverse image.

Source/core/bridge triage:
- `source-facing`: the kernel of an exact functor is a LinearRepresentations_Serre_1977 class;
- `core/canonical`: the owner `kernel F.obj`;
- `bridge/view`: the exact-functor bundle supplies the preservation instances needed to invoke the
  generic inverse-image LinearRepresentations_Serre_1977-class instance.
-/
#synth (kernel F.obj).IsSerreClass

end

end ExactFunctor

end CategoryTheory

/-! ### Definition_12_10_5 (from Chap12) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace ExactFunctor

section

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable (F : A ⥤ₑ B)

/- Definition 12.10.5:
- source-facing: the kernel of an exact functor is the full subcategory of objects sent to zero
- primary domain: exact functors and full subcategories cut out by an object property
- sampled owner declarations: `Functor.kernel`, `ObjectProperty.FullSubcategory`,
  `ObjectProperty.ι`
- core/canonical owner: `Functor.kernel`, specialized here to `F.obj.kernel`
- bridge/view: the associated full subcategory `F.obj.kernel.FullSubcategory`

The primitive data are the object property `IsZero (F.obj X)`; the subcategory is derived API. -/
recall Functor.kernel
#check F.obj.kernel.FullSubcategory

end

end ExactFunctor

end CategoryTheory

/-! ### Lemma_12_10_6 (from Chap12) -/
open CategoryTheory

universe uA vA uB vB

namespace _root_.CategoryTheory.ObjectProperty

open _root_.CategoryTheory.ObjectProperty.SerreClassLocalization
open CategoryTheory.Functor (kernel)
open CategoryTheory.Limits
open CategoryTheory.Localization

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

noncomputable section

local notation "Q" => P.isoModSerre.Q

/- Domain-style sampling for Lemma 12.10.6:
- primary domain: LinearRepresentations_Serre_1977 quotients of abelian categories and exact functors out of them;
- sampled canonical declarations:
  `ObjectProperty.SerreClassLocalization.isZero_obj_iff`,
  `ObjectProperty.SerreClassLocalization.exactFunctor_comp_iff`,
  `ObjectProperty.SerreClassLocalization.essImage_whiskeringLeft`,
  `Localization.essSurj`;
- owner abstraction: the localization functor `Q`, the exact-functor whiskering owner
  `whiskeringLeft Q P B`, together with the canonical localization interface;
- primitive data: the LinearRepresentations_Serre_1977 class `P`, the exact functor `G`, and the kernel-containment witness
  `P ≤ G.obj.kernel`;
- derived API in this file: exactness of `Q`, identification of its kernel, the source-facing
  essential surjectivity of `Q`, and the source-facing essential-image criterion for exact
  functors out of the LinearRepresentations_Serre_1977 quotient;
- source/core/bridge triage:
  `source-facing`: essential surjectivity of `Q` and the kernel criterion for exact factorization
    through the LinearRepresentations_Serre_1977 quotient;
  `core/canonical`: `Q`, `whiskeringLeft Q P B`, `Localization.essSurj`, `Localization.lift`,
    and `essImage_whiskeringLeft Q P B`;
  `bridge/view`: `P.isoModSerre_isInvertedBy_iff`, which rewrites inversion of
    `P.isoModSerre` as containment in the kernel.
-/

local instance : Abelian P.isoModSerre.Localization :=
  abelian Q P

-- Proof sketch: the localization of an abelian category at the morphisms that are isomorphisms
-- modulo a LinearRepresentations_Serre_1977 class preserves finite limits and finite colimits, hence is exact.
/-- The canonical functor to the LinearRepresentations_Serre_1977 quotient is exact. -/
theorem toSerreQuotient_exact :
    exactFunctor A P.isoModSerre.Localization Q :=
  ⟨preservesFiniteLimits Q P, preservesFiniteColimits Q P⟩

-- Proof sketch: an object maps to zero in the LinearRepresentations_Serre_1977 quotient exactly when its identity morphism
-- becomes an isomorphism modulo `P`, and this is equivalent to the object lying in `P`.
/-- The kernel of the canonical functor to the LinearRepresentations_Serre_1977 quotient is the original LinearRepresentations_Serre_1977 class. -/
theorem toSerreQuotient_kernel_eq :
    kernel Q = P := by
  ext X
  simpa using isZero_obj_iff Q P X

-- Proof sketch: every object of the LinearRepresentations_Serre_1977 quotient has the canonical localization-preimage
-- supplied by `Localization.essSurj`.
/-- Lemma 12.10.6: the quotient functor to the LinearRepresentations_Serre_1977 quotient is essentially surjective. -/
theorem toSerreQuotient_essSurj :
    Functor.EssSurj Q :=
  Localization.essSurj Q P.isoModSerre

-- Proof sketch: combine the canonical essential-image theorem for whiskering by a LinearRepresentations_Serre_1977
-- localization functor with the canonical criterion that exact functors invert `P.isoModSerre`
-- exactly when their kernels contain `P`.
/-- Lemma 12.10.6: an exact functor `G : A ⥤ₑ B` lies in the essential image of precomposition
with the quotient functor exactly when its kernel contains `P`. -/
theorem exactFunctor_mem_essImage_whiskeringLeft_iff
    (B : Type uB) [Category.{vB} B] [Abelian B] (G : A ⥤ₑ B) :
    (whiskeringLeft Q P B).essImage G ↔ P ≤ G.obj.kernel := by
  simpa [essImage_whiskeringLeft Q P B] using P.isoModSerre_isInvertedBy_iff G.obj

/-- Any exact functor whose kernel contains `P` factors through the LinearRepresentations_Serre_1977 quotient. -/
theorem exactFunctor_factors_through_toSerreQuotient
    (B : Type uB) [Category.{vB} B] [Abelian B]
    (G : A ⥤ₑ B) (hG : P ≤ G.obj.kernel) :
    (whiskeringLeft Q P B).essImage G :=
  (exactFunctor_mem_essImage_whiskeringLeft_iff P B G).2 hG

end

end _root_.CategoryTheory.ObjectProperty

/-! ### Lemma_12_10_7 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Localization

universe uA vA uB vB

namespace CategoryTheory.Functor

open Abelian Limits

/-- An exact functor between abelian categories is faithful if its kernel consists only of zero
objects. -/
theorem faithful_of_exact_of_kernel_le_isZero
    {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : F.kernel ≤ IsZero) :
    F.Faithful := by
  let hExact : ∀ S : ShortComplex C, S.Exact → (S.map F).Exact := fun _ hS ↦ hS.map F
  letI : F.PreservesMonomorphisms := preservesMonomorphisms_of_map_exact F hExact
  letI : F.PreservesEpimorphisms := preservesEpimorphisms_of_map_exact F hExact
  letI : F.Additive := additive_of_preserves_binary_products F
  refine ⟨fun {X Y} f g hfg ↦ ?_⟩
  apply sub_eq_zero.mp
  have hmap : F.map (f - g) = 0 := by
    simp [map_sub, hfg]
  have hι :
      F.map (Abelian.image.ι (f - g)) = 0 := by
    apply zero_of_epi_comp (F.map (Abelian.factorThruImage (f - g)))
    rw [← F.map_comp, Abelian.image.fac]
    exact hmap
  have himageF : IsZero (F.obj (Abelian.image (f - g))) :=
    IsZero.of_mono_eq_zero (F.map (Abelian.image.ι (f - g))) hι
  have himage : IsZero (Abelian.image (f - g)) := hF _ himageF
  have hzero : Abelian.image.ι (f - g) = 0 := himage.eq_of_src _ _
  calc
    f - g = Abelian.factorThruImage (f - g) ≫ Abelian.image.ι (f - g) := by
      symm
      exact Abelian.image.fac (f - g)
    _ = 0 := by simp [hzero]

end CategoryTheory.Functor

namespace _root_.CategoryTheory.ObjectProperty

open _root_.CategoryTheory.ObjectProperty.SerreClassLocalization

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable (P : ObjectProperty A) [P.IsSerreClass]

local notation "Q" => P.isoModSerre.Q

noncomputable section

local instance : Abelian P.isoModSerre.Localization :=
  abelian Q P

-- Proof sketch: if the induced functor is faithful, then any object annihilated by `G` has zero
-- identity in the LinearRepresentations_Serre_1977 quotient, hence belongs to `P`. Conversely, if `P = G.obj.kernel`, then
-- a morphism in the quotient mapped to zero has image object in the kernel of `G`, hence in `P`,
-- so the morphism itself is zero.
/-- Lemma 12.10.7: let `G : A ⥤ₑ B` be an exact functor between abelian categories, and let `P`
be a LinearRepresentations_Serre_1977 subcategory of `A` contained in the kernel of `G`. Then `P` equals the kernel of `G`
if and only if the induced functor from the LinearRepresentations_Serre_1977 quotient `A/P` to `B` is faithful. -/
theorem kernel_eq_iff_inducedFunctorToSerreQuotient_faithful
    (G : A ⥤ₑ B) (hPker : P ≤ G.obj.kernel) :
    P = G.obj.kernel ↔
      (lift G.obj ((P.isoModSerre_isInvertedBy_iff G.obj).2 hPker) Q).Faithful := by
  let hG : P.isoModSerre.IsInvertedBy G.obj := (P.isoModSerre_isInvertedBy_iff G.obj).2 hPker
  let H := lift G.obj hG Q
  change P = G.obj.kernel ↔ H.Faithful
  have hHexact : exactFunctor _ _ H := by
    rw [← exactFunctor_comp_iff Q P]
    exact ObjectProperty.prop_of_iso _ (Localization.fac G.obj hG Q).symm G.property
  letI : PreservesFiniteLimits H := (exactFunctor_iff H).1 hHexact |>.1
  letI : PreservesFiniteColimits H := (exactFunctor_iff H).1 hHexact |>.2
  constructor
  · intro hker
    have := Localization.essSurj (P.isoModSerre.Q) P.isoModSerre
    exact Functor.faithful_of_exact_of_kernel_le_isZero H <| show H.kernel ≤ IsZero from
      fun Y hY ↦ by
        have hpre :
            IsZero (H.obj ((P.isoModSerre.Q).obj ((P.isoModSerre.Q).objPreimage Y))) := by
          simpa using ((H.mapIso ((P.isoModSerre.Q).objObjPreimageIso Y)).isZero_iff).2 hY
        have hkernel :
            G.obj.kernel ((P.isoModSerre.Q).objPreimage Y) := by
          simpa using
            ((Localization.fac G.obj hG Q).app ((P.isoModSerre.Q).objPreimage Y)).isZero_iff.1 hpre
        have hPpre : P ((P.isoModSerre.Q).objPreimage Y) := by
          simpa [hker] using hkernel
        have hQpre : IsZero ((P.isoModSerre.Q).obj ((P.isoModSerre.Q).objPreimage Y)) :=
          (isZero_obj_iff Q P _).2 hPpre
        exact (((P.isoModSerre.Q).objObjPreimageIso Y).isZero_iff).1 hQpre
  · intro hfaithful
    ext X
    constructor
    · exact hPker X
    · intro hkernel
      have hQX :
          IsZero (H.obj ((P.isoModSerre.Q).obj X)) := by
        simpa using ((Localization.fac G.obj hG Q).app X).isZero_iff.2 hkernel
      have hQid : 𝟙 ((P.isoModSerre.Q).obj X) = 0 := by
        apply H.zero_of_map_zero
        simpa [IsZero.iff_id_eq_zero] using hQX
      exact (isZero_obj_iff Q P X).1 <| (IsZero.iff_id_eq_zero _).2 hQid

end

end _root_.CategoryTheory.ObjectProperty
