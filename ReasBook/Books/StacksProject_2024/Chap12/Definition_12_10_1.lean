import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

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
