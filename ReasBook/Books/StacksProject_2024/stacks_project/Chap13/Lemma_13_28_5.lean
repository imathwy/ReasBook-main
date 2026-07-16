import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_11_1
import StacksProject_2024.stacks_project.Chap12.Lemma_12_11_3
import StacksProject_2024.stacks_project.Chap12.Lemma_12_10_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_17_1
import StacksProject_2024.stacks_project.Chap13.Definition_13_28_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_6_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure
open scoped DerivedCategoryWithCohomologyIn
open scoped ZeroObject

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

local notation "H" => DerivedCategory.homologyFunctor A
local notation "single₀" => singleFunctor A (0 : ℤ)

section LocalEulerInfrastructure

/-- Helper for Lemma 13.28.5: the degree-zero complex of an object of `A` is bounded. -/
theorem singleFunctor_obj_mem_boundedDerivedCategory (X : A) :
    t.bounded ((single₀).obj X) := by
  -- The degree-zero complex has no cohomology outside degree `0`.
  rw [derivedCategory_t_bounded_iff]
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩
  · intro i hi
    let _ : ((single₀).obj X).IsGE 0 := inferInstance
    exact DerivedCategory.isZero_of_isGE _ 0 i hi
  · intro i hi
    let _ : ((single₀).obj X).IsLE 0 := inferInstance
    exact DerivedCategory.isZero_of_isLE _ 0 i hi

/-- Helper for Lemma 13.28.5: the canonical degree-zero embedding `A ⥤ Dᵇ(A)`. -/
abbrev singleFunctorToBoundedDerived :
    A ⥤ Dᵇ(A) :=
  ObjectProperty.lift
    t.bounded
    single₀
    (singleFunctor_obj_mem_boundedDerivedCategory (A := A))

/-- Helper for Lemma 13.28.5: the cohomology of a degree-zero complex vanishes away from degree
`0`. -/
theorem single_zero_complex_homology_isZero_of_ne
    (X : A) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((H i).obj ((single₀).obj X)) := by
  -- Proof comment: a degree-zero complex is bounded both below and above by `0`, so all other
  -- cohomology groups vanish by the standard `t`-structure bounds.
  by_cases hlt : i < 0
  · let _ : ((single₀).obj X).IsGE 0 := inferInstance
    exact DerivedCategory.isZero_of_isGE _ 0 i hlt
  · have hgt : 0 < i := by
      omega
    let _ : ((single₀).obj X).IsLE 0 := inferInstance
    exact DerivedCategory.isZero_of_isLE _ 0 i hgt

end LocalEulerInfrastructure

namespace Functor

section LocalEulerK0Map

universe u₁ u₂ v₁ v₂

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : D ⥤ B) [F.IsHomological] [F.ShiftSequence ℤ]

/-- Helper for Lemma 13.28.5: the alternating Euler class attached to a shifted homological
functor. -/
def eulerClass (X : D) : AbelianK0 B :=
  ∑ᶠ i : ℤ, i.negOnePow • K₀[(F.shift i).obj X]

/-- Helper for Lemma 13.28.5: the zero object has trivial class in the abelian Grothendieck
group of the target category. -/
private theorem abelian_k0_zero_eq :
    K₀[(0 : B)] = 0 := by
  -- Proof comment: evaluate the Grothendieck relation for the zero short exact sequence and
  -- cancel one copy of the zero class.
  let S : ShortComplex B := ShortComplex.mk (0 : (0 : B) ⟶ 0) (0 : (0 : B) ⟶ 0) (by simp)
  have hExact : S.Exact := by
    exact (S.exact_iff_epi (by simp [S])).2 inferInstance
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  have hK0 : K₀[(0 : B)] = K₀[(0 : B)] + K₀[(0 : B)] := by
    simpa [S] using (AbelianK0.of_shortExact S hShort)
  have hSub := congrArg (fun z : AbelianK0 B ↦ z - K₀[(0 : B)]) hK0
  have hZero : (0 : AbelianK0 B) = K₀[(0 : B)] := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub
  simpa using hZero.symm

/-- Helper for Lemma 13.28.5: isomorphic objects define the same class in the abelian
Grothendieck group of the target category. -/
private theorem abelian_k0_eq_of_iso {X Y : B} (e : X ≅ Y) :
    K₀[X] = K₀[Y] := by
  -- Proof comment: delegate to the canonical Chapter 12 `K₀` invariance under isomorphism.
  exact _root_.CategoryTheory.ObjectProperty.k0_eq_of_iso (A := B) e

/-- Helper for Lemma 13.28.5: the difference of target and source classes equals the difference
of cokernel and kernel classes. -/
private theorem k0_sub_eq_cokernel_sub_kernel {X Y : B} (f : X ⟶ Y) :
    K₀[Y] - K₀[X] = K₀[Limits.cokernel f] - K₀[Limits.kernel f] := by
  -- Proof comment: this is the canonical Chapter 12 kernel-cokernel identity in `K₀(B)`.
  exact _root_.CategoryTheory.ObjectProperty.k0_sub_eq_cokernel_sub_kernel (A := B) f

/-- Helper for Lemma 13.28.5: composing with the lift into `kernel f` preserves the kernel class
in `K₀(B)`. -/
private theorem k0_kernel_of_kernel_lift
    {X Y Z : B} (f : Y ⟶ Z) (g : X ⟶ Y) (h : g ≫ f = 0) :
    K₀[Limits.kernel (Limits.kernel.lift f g h)] = K₀[Limits.kernel g] := by
  -- Proof comment: use the Chapter 12 comparison between the two kernels attached to
  -- `kernel.lift`.
  exact _root_.CategoryTheory.ObjectProperty.k0_kernel_of_kernel_lift (A := B) f g h

/-- Helper for Lemma 13.28.5: if the source of a morphism in the abelian target is zero, then
the class of its kernel vanishes in `K₀(B)`. -/
private lemma k0_kernel_eq_zero_of_isZero_source {X Y : B} (f : X ⟶ Y) (hX : IsZero X) :
    K₀[Limits.kernel f] = 0 := by
  -- Proof comment: a morphism out of a zero object is mono, so its kernel is zero.
  let e : X ≅ 0 := hX.isoZero
  let _ : Mono f := Limits.mono_of_source_iso_zero f e
  calc
    K₀[Limits.kernel f] = K₀[(0 : B)] := by
      exact abelian_k0_eq_of_iso (kernel.ofMono f)
    _ = 0 := abelian_k0_zero_eq (B := B)

/-- Helper for Lemma 13.28.5: exactness at two consecutive spots expresses the middle class as
the sum of the adjacent kernel classes. -/
private lemma k0_eq_kernel_add_kernel_of_exact
    {X₀ X₁ X₂ X₃ : B} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0)
    (hex₁ : (ShortComplex.mk f g hfg).Exact) (hex₂ : (ShortComplex.mk g h hgh).Exact) :
    K₀[X₁] = K₀[Limits.kernel g] + K₀[Limits.kernel h] := by
  -- Proof comment: identify `X₁ ⟶ kernel h` with a kernel-cokernel presentation and then
  -- replace its kernel by `kernel g`.
  let u : X₁ ⟶ Limits.kernel h := Limits.kernel.lift h g hgh
  haveI : Epi u := (ShortComplex.Exact.epi_kernelLift (S := ShortComplex.mk g h hgh) hex₂)
  have hcokernel :
      K₀[Limits.cokernel u] = 0 := by
    calc
      K₀[Limits.cokernel u] = K₀[(0 : B)] := by
        exact abelian_k0_eq_of_iso (Limits.cokernel.ofEpi u)
      _ = 0 := abelian_k0_zero_eq (B := B)
  have hkernel :
      K₀[Limits.kernel u] = K₀[Limits.kernel g] := by
    simpa [u] using
      (k0_kernel_of_kernel_lift (f := h) (g := g) hgh)
  have hsub :
      K₀[Limits.kernel h] - K₀[X₁] = -K₀[Limits.kernel g] := by
    rw [k0_sub_eq_cokernel_sub_kernel u, hcokernel, hkernel]
    abel
  have hsum := congrArg (fun z : AbelianK0 B ↦ z + K₀[X₁] + K₀[Limits.kernel g]) hsub
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum.symm

/-- Helper for Lemma 13.28.5: once the shifted values of `F` vanish outside a finite interval,
the Euler `finsum` reduces to the corresponding finite sum. -/
private lemma eulerClass_eq_sum_of_vanishingOutside (X : D) {a b : ℤ}
    (hX : ∀ n : ℤ, n ∉ Set.Icc a b → IsZero ((F.shift n).obj X)) :
    F.eulerClass X =
      Finset.sum (Finset.Icc a b) (fun i ↦ i.negOnePow • K₀[(F.shift i).obj X]) := by
  -- Proof comment: outside the interval every Euler summand is zero, so the `finsum`
  -- collapses to the finite interval sum.
  let f : ℤ → AbelianK0 B := fun i ↦ i.negOnePow • K₀[(F.shift i).obj X]
  change ∑ᶠ i : ℤ, f i = Finset.sum (Finset.Icc a b) f
  have hsupp : Function.support f ⊆ ↑(Finset.Icc a b) := by
    intro i hi
    by_contra hnot
    have hzeroObj : IsZero ((F.shift i).obj X) := hX i <| by simpa using hnot
    have hk0 :
        K₀[(F.shift i).obj X] = 0 := by
      calc
        K₀[(F.shift i).obj X] = K₀[(0 : B)] := by
          exact abelian_k0_eq_of_iso hzeroObj.isoZero
        _ = 0 := abelian_k0_zero_eq (B := B)
    have hfi : f i = 0 := by
      rw [show f i = i.negOnePow • K₀[(F.shift i).obj X] by rfl, hk0, smul_zero]
    exact hi hfi
  rw [finsum_eq_sum_of_support_subset (s := Finset.Icc a b) f hsupp]

/-- Helper for Lemma 13.28.5: the distinguished-triangle relations are killed by the local
Euler-class map. -/
private theorem relations_le_ker_eulerClass
    (hF : ∀ X : D, F.shiftVanishingBounded X) :
    TriangulatedK0.relations D ≤
      (FreeAbelianGroup.lift fun X ↦ F.eulerClass X).ker := by
  -- TODO: reuse the telescoping proof from `Lemma_13_28_4` after the local weak-Serre
  -- transport layer is stabilized; the current bottleneck is elaboration time rather than a
  -- concrete goal mismatch.
  sorry

/-- Helper for Lemma 13.28.5: the induced Euler-characteristic map on the triangulated `K₀`. -/
def eulerK0Map (hF : ∀ X : D, F.shiftVanishingBounded X) :
    TriangulatedK0 D →+ AbelianK0 B :=
  TriangulatedK0.lift
    (fun X ↦ F.eulerClass X)
    (relations_le_ker_eulerClass F hF)

/-- Helper for Lemma 13.28.5: evaluation of the Euler-characteristic map on a generator. -/
@[simp] theorem eulerK0Map_apply_of
    (hF : ∀ X : D, F.shiftVanishingBounded X) (X : D) :
    F.eulerK0Map hF (TriangulatedK0.of X) = F.eulerClass X := by
  simpa using
    TriangulatedK0.lift_of
      (fun Y ↦ F.eulerClass Y)
      (relations_le_ker_eulerClass F hF)
      X

end LocalEulerK0Map

end Functor

section WeakSerreSingleBridge

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/- Domain-style sampling for Lemma 13.28.5:
- primary domain: the bounded derived subcategory cut out by a weak Serre object property and the
  induced Grothendieck-group comparison map;
- sampled owner declarations:
  `derivedCategoryCohomologyInProperty`,
  `derivedCategoryBoundedCohomologyInProperty`,
  `Dᵇ_{P}`,
  `ObjectProperty.IsTriangulated`,
  `Functor.eulerK0Map`,
  `Functor.shiftVanishingBounded`;
- best owner abstraction: the Chapter 13 owner object property on `DerivedCategory A` together
  with its canonical full subcategory `Dᵇ_{P}`; the Euler map on `K₀(Dᵇ_{P})` should be routed
  through the owner-functor construction
  `(derivedBoundedWithCohomologyInZeroHomologyFunctor P).eulerK0Map`;
- primitive-vs-derived split:
  primitive data: the object property `P`, its zero-object and iso-stability owners used by the
    degree-zero bridge, and the chapter owner
    `derivedCategoryBoundedCohomologyInProperty P`, whose full subcategory owner is the chapter
    notation `Dᵇ_{P}`;
  derived API: the degree-zero embedding obtained by restricting the Chapter 13 owner
    `singleFunctorToBoundedDerived A` along `P.ι`, the induced maps on `K₀`, and the Euler
    characteristic inverse;
- source/core/bridge triage:
  `source-facing`: the `K₀` comparison between `P` and `Dᵇ_{P}`;
  `core/canonical`: the owner declarations from `Lemma_13_17_1`;
  `bridge/view`: the restricted degree-zero functor
    `P.FullSubcategory ⥤ Dᵇ(A) ⥤ Dᵇ_{P}` and the resulting additive maps.

This file therefore reuses the Chapter 13 owner API rather than redeclaring a second bounded
cohomology-in-`P` object property. -/

/-- The degree-zero complex attached to an object of `P.FullSubcategory` lies in
`Dᵇ_{P}`. -/
theorem weakSerreSingle_obj_mem_derivedCategoryBoundedCohomologyInProperty
    (X : P.FullSubcategory) :
    derivedCategoryBoundedCohomologyInProperty P
      ((P.ι ⋙ singleFunctorToBoundedDerived (A := A)).obj X) := by
  intro i
  by_cases hi : i = 0
  · subst hi
    simpa [derivedCategoryBoundedCohomologyInProperty, derivedCategoryCohomologyInProperty,
      Functor.comp_obj] using
        P.prop_of_iso ((singleFunctorCompHomologyFunctorIso A 0).app X.obj).symm X.property
  · have hzero :
        IsZero
          ((H i).obj
            ((ObjectProperty.ι t.bounded).obj
              ((P.ι ⋙ singleFunctorToBoundedDerived (A := A)).obj X))) := by
      by_cases hlt : i < 0
      · change IsZero ((H i).obj ((singleFunctor A 0).obj X.obj))
        letI : ((singleFunctor A 0).obj X.obj).IsGE 0 := inferInstance
        exact DerivedCategory.isZero_of_isGE _ 0 i hlt
      · have hgt : 0 < i := by omega
        change IsZero ((H i).obj ((singleFunctor A 0).obj X.obj))
        letI : ((singleFunctor A 0).obj X.obj).IsLE 0 := inferInstance
        exact DerivedCategory.isZero_of_isLE _ 0 i hgt
    simpa [derivedCategoryBoundedCohomologyInProperty, derivedCategoryCohomologyInProperty,
      Functor.comp_obj] using P.prop_of_isZero hzero

/-- The canonical functor `P.FullSubcategory ⥤ Dᵇ_{P}` sending `X` to the degree-zero object
`X[0]` in the ambient derived category. -/
abbrev weakSerreSingleFunctorToDerivedBounded :
    P.FullSubcategory ⥤ Dᵇ_{P} :=
  ObjectProperty.lift
    (derivedCategoryBoundedCohomologyInProperty P)
    (P.ι ⋙ singleFunctorToBoundedDerived (A := A))
    (weakSerreSingle_obj_mem_derivedCategoryBoundedCohomologyInProperty P)

end WeakSerreSingleBridge

section WeakSerreBoundedDerivedBridge

variable (P : ObjectProperty A)

/-- The `i`-th cohomology functor on `Dᵇ_{P}` lifted to the weak Serre full subcategory
`P.FullSubcategory`. -/
abbrev derivedBoundedWithCohomologyInHomologyFunctor (i : ℤ) :
    Dᵇ_{P} ⥤ P.FullSubcategory :=
  P.lift
    ((derivedCategoryBoundedCohomologyInProperty P).ι ⋙
      ObjectProperty.ι (t.bounded : ObjectProperty (D(A))) ⋙ H i)
    (fun X ↦ X.property i)

/-- The degree-zero cohomology functor on `Dᵇ_{P}` lifted to `P.FullSubcategory`. -/
abbrev derivedBoundedWithCohomologyInZeroHomologyFunctor :
    Dᵇ_{P} ⥤ P.FullSubcategory :=
  derivedBoundedWithCohomologyInHomologyFunctor P 0

end WeakSerreBoundedDerivedBridge

section WeakSerreBoundedDerivedK0

variable (P : ObjectProperty A) [P.IsWeakSerreClass]

noncomputable local instance derivedBoundedWithCohomologyInZeroHomologyFunctor_shiftSequence :
    (derivedBoundedWithCohomologyInZeroHomologyFunctor P).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

/-- Helper for Lemma 13.28.5: exactness of a mapped short complex is unchanged under a natural
isomorphism of functors. -/
private theorem shortComplex_exact_iff_of_functor_iso
    {C B : Type*} [Category C] [Category B]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms B]
    {F G : C ⥤ B} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (e : F ≅ G) (S : ShortComplex C) :
    (S.map F).Exact ↔ (S.map G).Exact := by
  -- Proof comment: compare the mapped short complexes degreewise using the components of `e`,
  -- and then transport exactness across the resulting isomorphism.
  let i : S.map F ≅ S.map G :=
    ShortComplex.isoMk (e.app S.X₁) (e.app S.X₂) (e.app S.X₃)
      (by simp)
      (by simp)
  exact ShortComplex.exact_iff_of_iso i

/-- Helper for Lemma 13.28.5: mapping a short exact sequence in `P.FullSubcategory` along the
inclusion `P.ι` keeps it short exact in `A`. -/
private theorem weakSerreSingleFunctor_mapped_shortExact
    {S : ShortComplex P.FullSubcategory} (hS : S.ShortExact) :
    (S.map P.ι).ShortExact := by
  -- The weak Serre inclusion is exact, so the ambient sequence remains short exact after
  -- forgetting from `P.FullSubcategory` to `A`.
  letI : PreservesFiniteLimits P.ι :=
    ObjectProperty.weakSerreSubcategory_inclusion_preservesFiniteLimits P
  letI : PreservesFiniteColimits P.ι :=
    ObjectProperty.weakSerreSubcategory_inclusion_preservesFiniteColimits P
  simpa using hS.map_of_exact P.ι

/-- Helper for Lemma 13.28.5: after forgetting from `Dᵇ_{P}` to `Dᵇ(A)`, the weak-Serre
degree-zero embedding is the usual degree-zero bounded-derived embedding. -/
private noncomputable def weakSerreSingleFunctorToBoundedDerivedCompIso :
    weakSerreSingleFunctorToDerivedBounded P ⋙
      (derivedCategoryBoundedCohomologyInProperty P).ι ≅
    P.ι ⋙ singleFunctorToBoundedDerived (A := A) :=
  (derivedCategoryBoundedCohomologyInProperty P).liftCompιIso
    (P.ι ⋙ singleFunctorToBoundedDerived (A := A))
    (weakSerreSingle_obj_mem_derivedCategoryBoundedCohomologyInProperty (A := A) P)

/-- Helper for Lemma 13.28.5: the ambient bounded-derived triangle attached to the mapped short
exact sequence `S.map P.ι`. -/
private def weakSerreSingleFunctor_mappedBoundedDerivedTriangle
    {S : ShortComplex P.FullSubcategory} (hS : S.ShortExact) :
    Triangle (Dᵇ(A)) :=
  Triangle.mk
    ((singleFunctorToBoundedDerived (A := A)).map (S.map P.ι).f)
    ((singleFunctorToBoundedDerived (A := A)).map (S.map P.ι).g)
    ((ObjectProperty.ι t.bounded).preimage
      ((weakSerreSingleFunctor_mapped_shortExact (P := P) hS).singleδ ≫
        ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app
          ((singleFunctorToBoundedDerived (A := A)).obj S.X₁.obj)))

/-- Helper for Lemma 13.28.5: the mapped short exact sequence gives the canonical distinguished
triangle in `Dᵇ(A)`. -/
private theorem weakSerreSingleFunctor_mappedBoundedDerivedTriangle_distinguished
    {S : ShortComplex P.FullSubcategory} (hS : S.ShortExact) :
    weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A) (P := P) hS ∈
      distTriang (Dᵇ(A)) := by
  -- Proof comment: this is exactly the bounded-derived short-exact-sequence triangle of
  -- `S.map P.ι`, so the proof is the same as in `Lemma_13_28_2`.
  rw [← (ObjectProperty.ι t.bounded).map_distinguished_iff]
  change
    Triangle.mk
        ((ObjectProperty.ι t.bounded).map
          ((singleFunctorToBoundedDerived (A := A)).map (S.map P.ι).f))
        ((ObjectProperty.ι t.bounded).map
          ((singleFunctorToBoundedDerived (A := A)).map (S.map P.ι).g))
        ((ObjectProperty.ι t.bounded).map
            ((ObjectProperty.ι t.bounded).preimage
              ((weakSerreSingleFunctor_mapped_shortExact (P := P) hS).singleδ ≫
                ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app
                  ((singleFunctorToBoundedDerived (A := A)).obj S.X₁.obj))) ≫
          ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).hom.app
            ((singleFunctorToBoundedDerived (A := A)).obj S.X₁.obj)) ∈
      distTriang (D(A))
  rw [(ObjectProperty.ι t.bounded).map_preimage]
  refine isomorphic_distinguished _
    (weakSerreSingleFunctor_mapped_shortExact (P := P) hS).singleTriangle_distinguished _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp [singleFunctorToBoundedDerived]
  · simp [singleFunctorToBoundedDerived]
  · simpa [Category.assoc] using
      congrArg (fun k ↦ (weakSerreSingleFunctor_mapped_shortExact (P := P) hS).singleδ ≫ k)
        (((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv_hom_id_app
          ((singleFunctorToBoundedDerived (A := A)).obj S.X₁.obj))

/-- Helper for Lemma 13.28.5: the degree-zero images of a short exact sequence in
`P.FullSubcategory` form the canonical triangle in `Dᵇ_{P}`. -/
private def weakSerreSingleFunctorToDerivedBoundedTriangle {S : ShortComplex P.FullSubcategory}
    (hS : S.ShortExact) :
    Triangle (Dᵇ_{P}) :=
  -- TODO: reinsert the transported short-exact-sequence triangle once the comparison morphism is
  -- stabilized definitionally inside `Dᵇ_{P}`.
  sorry

/-- Helper for Lemma 13.28.5: the canonical triangle attached to a short exact sequence in the
weak Serre subcategory is distinguished in `Dᵇ_{P}`. -/
private theorem weakSerreSingleFunctorToDerivedBoundedTriangle_distinguished
    {S : ShortComplex P.FullSubcategory} (hS : S.ShortExact) :
    weakSerreSingleFunctorToDerivedBoundedTriangle P hS ∈ distTriang (Dᵇ_{P}) := by
  -- TODO: prove distinguishedness by comparing the forgotten triangle with the ambient
  -- bounded-derived short-exact-sequence triangle.
  sorry

-- Proof sketch: a short exact sequence in `P.FullSubcategory` gives the canonical distinguished
-- triangle of degree-zero objects in `D(A)`, and each vertex lies in `Dᵇ_{P}`. Hence the
-- corresponding Grothendieck relation vanishes in the triangulated `K₀`.
private theorem relations_le_ker_weakSerreToDerivedBoundedK0 :
    AbelianK0.relations P.FullSubcategory ≤
      (FreeAbelianGroup.lift fun X ↦
        TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj X)).ker := by
  -- TODO: descend the short-exact-sequence relations once the transported triangle API above is
  -- re-established.
  sorry

/-- The canonical map `K₀(P) → K₀(Dᵇ_{P})` induced by `X ↦ X[0]`. -/
def weakSerreToDerivedBoundedK0 :
    AbelianK0 P.FullSubcategory →+ TriangulatedK0 (Dᵇ_{P}) :=
  AbelianK0.lift
    (fun X ↦ TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj X))
    (relations_le_ker_weakSerreToDerivedBoundedK0 P)

-- Proof sketch: `weakSerreToDerivedBoundedK0` is the owner lift `AbelianK0.lift` applied to the
-- object-level formula `X ↦ [X[0]]`, so evaluation on `AbelianK0.of X` is the canonical owner
-- lemma `AbelianK0.lift_of`.
/-- The canonical map on `K₀` sends `[X]` to the class of `X[0]` in `Dᵇ_{P}`. -/
@[simp] theorem weakSerreToDerivedBoundedK0_apply_of
    (X : P.FullSubcategory) :
    weakSerreToDerivedBoundedK0 P K₀[X] =
      TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj X) := by
  simpa using
    AbelianK0.lift_of
      (fun Y : P.FullSubcategory ↦
        TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj Y))
      (relations_le_ker_weakSerreToDerivedBoundedK0 P)
      X

-- Proof sketch: `Dᵇ_P(A)` inherits its triangulated structure from the ambient derived category,
-- and the lifted degree-zero cohomology functor is the source-facing `H⁰` functor valued in the
-- weak Serre full subcategory. Exactness is therefore the same long exact cohomology sequence as
-- for `DerivedCategory.homologyFunctor A 0`, viewed inside `P.FullSubcategory`.
local instance derivedBoundedWithCohomologyInZeroHomologyFunctor_isHomological :
    (derivedBoundedWithCohomologyInZeroHomologyFunctor P).IsHomological := by
  -- Proof comment: compare the lifted `H⁰` functor with the ambient homological composite after
  -- forgetting to `A`, then reflect exactness back along the faithful weak-Serre inclusion.
  let F : Dᵇ_{P} ⥤ P.FullSubcategory :=
    derivedBoundedWithCohomologyInZeroHomologyFunctor P
  let G : Dᵇ_{P} ⥤ A :=
    (derivedCategoryBoundedCohomologyInProperty P).ι ⋙
      ObjectProperty.ι (t.bounded : ObjectProperty (D(A))) ⋙ H 0
  let e : F ⋙ P.ι ≅ G :=
    P.liftCompιIso G (fun X ↦ X.property 0)
  letI : P.ι.Faithful := inferInstance
  letI : P.ι.PreservesZeroMorphisms := by
    infer_instance
  letI : PreservesFiniteLimits P.ι :=
    ObjectProperty.weakSerreSubcategory_inclusion_preservesFiniteLimits P
  letI : PreservesFiniteColimits P.ι :=
    ObjectProperty.weakSerreSubcategory_inclusion_preservesFiniteColimits P
  refine ⟨fun T hT ↦ ?_⟩
  have hG : ((Pretriangulated.shortComplexOfDistTriangle T hT).map G).Exact := by
    exact (inferInstance : G.IsHomological).exact T hT
  have hFG : ((Pretriangulated.shortComplexOfDistTriangle T hT).map (F ⋙ P.ι)).Exact := by
    exact (shortComplex_exact_iff_of_functor_iso e
      (Pretriangulated.shortComplexOfDistTriangle T hT)).2 hG
  exact P.ι.reflects_exact_of_faithful _ hFG

/-- Helper for Lemma 13.28.5: on a shifted object of `Dᵇ_{P}`, the lifted degree-zero cohomology
functor computes the ambient `i`-th cohomology object. -/
noncomputable def derivedBoundedWithCohomologyIn_zero_homology_shift_obj_iso
    (X : Dᵇ_{P}) (i : ℤ) :
    ((derivedBoundedWithCohomologyInZeroHomologyFunctor P).obj
      ((shiftFunctor (Dᵇ_{P}) i).obj X)) ≅
      ((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X) := by
  -- Proof comment: commute both inclusion functors past the shift, then rewrite `H⁰(X[i])` as
  -- `Hⁱ(X)` using the canonical shift comparison for derived-category cohomology.
  dsimp [derivedBoundedWithCohomologyInZeroHomologyFunctor,
    derivedBoundedWithCohomologyInHomologyFunctor]
  refine P.isoMk ?_
  refine ((H 0).mapIso ?_) ≪≫ (((H 0).isoShift i).app X.obj.obj) ≪≫ ?_
  · exact
      ((ObjectProperty.ι t.bounded).mapIso
        ((((derivedCategoryBoundedCohomologyInProperty P).ι).commShiftIso i).app X)) ≪≫
          (((ObjectProperty.ι t.bounded).commShiftIso i).app X.obj)
  · exact
      eqToIso
        (congrArg (fun F : DerivedCategory A ⥤ A => F.obj X.obj.obj)
          (DerivedCategory.shift_homologyFunctor A i))

/-- On generators, the Euler-characteristic map sends a bounded derived object with cohomology in
`P` to the alternating sum of the classes of its cohomology objects in `K₀(P)`. -/
noncomputable abbrev derivedBoundedWithCohomologyInEulerClass
    (X : Dᵇ_{P}) :
    AbelianK0 P.FullSubcategory :=
  ∑ᶠ i : ℤ, i.negOnePow •
    K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)]

/-- Helper for Lemma 13.28.5: any zero object of `P.FullSubcategory` has trivial class in
`K₀(P)`. -/
private theorem weakSerre_k0_zero_eq (Z : P.FullSubcategory) (hZ : IsZero Z) :
    K₀[Z] = 0 := by
  -- Proof comment: evaluate the Grothendieck relation for the zero short exact sequence in the
  -- weak Serre full subcategory and cancel one copy of the zero class.
  let S : ShortComplex P.FullSubcategory :=
    ShortComplex.mk (0 : (0 : P.FullSubcategory) ⟶ 0) (0 : (0 : P.FullSubcategory) ⟶ 0) (by simp)
  have hExact : S.Exact := by
    exact (S.exact_iff_epi (by simp [S])).2 inferInstance
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  have hK0 : K₀[(0 : P.FullSubcategory)] = K₀[(0 : P.FullSubcategory)] + K₀[(0 : P.FullSubcategory)] := by
    simpa [S] using (AbelianK0.of_shortExact S hShort)
  have hSub := congrArg (fun z : AbelianK0 P.FullSubcategory ↦ z - K₀[(0 : P.FullSubcategory)]) hK0
  have hZero : (0 : AbelianK0 P.FullSubcategory) = K₀[(0 : P.FullSubcategory)] := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub
  let S' : ShortComplex P.FullSubcategory :=
    ShortComplex.mk hZ.isoZero.hom (0 : (0 : P.FullSubcategory) ⟶ 0) (by simp)
  have hExact' : S'.Exact := by
    exact (S'.exact_iff_epi (by simp [S'])).2 inferInstance
  have hShort' : S'.ShortExact := ShortComplex.ShortExact.mk' hExact' inferInstance inferInstance
  have hEq : K₀[Z] = K₀[(0 : P.FullSubcategory)] := by
    simpa [S', hZero.symm, add_comm] using
      (AbelianK0.of_shortExact S' hShort').symm
  calc
    K₀[Z] = K₀[(0 : P.FullSubcategory)] := hEq
    _ = 0 := by
      simpa using hZero.symm

/-- Helper for Lemma 13.28.5: isomorphic objects in `P.FullSubcategory` define the same
Grothendieck class. -/
private theorem weakSerre_k0_eq_of_iso {X Y : P.FullSubcategory} (e : X ≅ Y) :
    K₀[X] = K₀[Y] := by
  -- Proof comment: route the isomorphism through the short exact sequence `0 → X → Y → 0` in
  -- the weak Serre full subcategory.
  let S : ShortComplex P.FullSubcategory := ShortComplex.mk e.hom (0 : Y ⟶ 0) (by simp)
  have hExact : S.Exact := by
    exact (S.exact_iff_epi (by simp [S])).2 inferInstance
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  simpa [S, weakSerre_k0_zero_eq (P := P) 0 (isZero_zero _), add_comm] using
    (AbelianK0.of_shortExact S hShort).symm

/-- Helper for Lemma 13.28.5: an object of the weak Serre full subcategory is zero whenever its
underlying ambient object is zero. -/
private theorem weakSerre_isZero_of_underlying_isZero
    (X : P.FullSubcategory) (hX : IsZero X.obj) :
    IsZero X := by
  -- Proof comment: lift the ambient isomorphism `X.obj ≅ 0` into the full subcategory `P`.
  have hzero_obj : (0 : A) ≅ (0 : P.FullSubcategory).obj := by
    simpa using (P.ι.mapZeroObject).symm
  let e : X ≅ (0 : P.FullSubcategory) := P.isoMk (hX.isoZero ≪≫ hzero_obj)
  exact IsZero.of_iso (isZero_zero _) e

/-- Helper for Lemma 13.28.5: the degree-zero cohomology of the degree-zero object `X[0]` in
`Dᵇ_{P}` is canonically `X`. -/
private noncomputable def derivedBoundedWithCohomologyInHomology_zero_single_iso
    (X : P.FullSubcategory) :
    ((derivedBoundedWithCohomologyInHomologyFunctor P (0 : ℤ)).obj
      ((weakSerreSingleFunctorToDerivedBounded P).obj X)) ≅ X := by
  -- Proof comment: forget to the ambient bounded derived category, compare with the usual degree-
  -- zero embedding, and then apply the standard derived-category identification `H⁰(X[0]) ≅ X`.
  refine P.isoMk ?_
  exact
    ((H 0).mapIso
      ((ObjectProperty.ι (t.bounded : ObjectProperty (D(A)))).mapIso
        ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).app X))) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A (0 : ℤ)).app X.obj

/-- Helper for Lemma 13.28.5: the Euler class of a degree-zero object is its original class in
`K₀(P)`. -/
theorem derivedBoundedWithCohomologyInEulerClass_single_zero
    (X : P.FullSubcategory) :
    derivedBoundedWithCohomologyInEulerClass P
        ((weakSerreSingleFunctorToDerivedBounded P).obj X) =
      K₀[X] := by
  -- Proof comment: only the degree-zero cohomology term survives for the degree-zero object
  -- `X[0]`; the surviving term is identified with `X` by the canonical `H⁰(X[0]) ≅ X`.
  let Y := (weakSerreSingleFunctorToDerivedBounded P).obj X
  let f : ℤ → AbelianK0 P.FullSubcategory :=
    fun i ↦ i.negOnePow • K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj Y)]
  have hsupport :
      ∀ i : ℤ, i ∉ Set.Icc (0 : ℤ) 0 → f i = 0 := by
    intro i hi
    have hi0 : i ≠ 0 := by
      simpa using hi
    have hzeroHomology :
        IsZero ((derivedBoundedWithCohomologyInHomologyFunctor P i).obj Y) := by
      refine weakSerre_isZero_of_underlying_isZero (P := P) _ ?_
      change IsZero ((H i).obj ((single₀).obj X.obj))
      exact single_zero_complex_homology_isZero_of_ne (A := A) X.obj i hi0
    have hk0 :
        K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj Y)] = 0 := by
      calc
        K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj Y)] =
            K₀[(0 : P.FullSubcategory)] := by
              exact weakSerre_k0_eq_of_iso (P := P) hzeroHomology.isoZero
        _ = 0 := weakSerre_k0_zero_eq (P := P) 0 (isZero_zero _)
    change i.negOnePow • K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj Y)] = 0
    rw [hk0]
    simp
  have hsum :
      derivedBoundedWithCohomologyInEulerClass P Y =
        Finset.sum (Finset.Icc (0 : ℤ) 0) f := by
    have hsupp :
        Function.support f ⊆ ↑(Finset.Icc (0 : ℤ) 0) := by
      intro i hi
      by_contra hnot
      exact hi (hsupport i (by simpa using hnot))
    simpa [derivedBoundedWithCohomologyInEulerClass, f] using
      (finsum_eq_sum_of_support_subset (s := Finset.Icc (0 : ℤ) 0) f hsupp)
  have hzero :
      K₀[((derivedBoundedWithCohomologyInHomologyFunctor P (0 : ℤ)).obj Y)] = K₀[X] := by
    -- Proof comment: the unique surviving degree-zero cohomology object is canonically `X`.
    exact weakSerre_k0_eq_of_iso (P := P)
      (derivedBoundedWithCohomologyInHomology_zero_single_iso (A := A) P X)
  calc
    derivedBoundedWithCohomologyInEulerClass P Y = Finset.sum (Finset.Icc (0 : ℤ) 0) f := hsum
    _ = f 0 := by simp
    _ = K₀[X] := by simpa [f, hzero]

-- Proof sketch: boundedness gives integers `a ≤ b` such that `H^i(X) = 0` outside `[a, b]`.
-- Since the tautological shift sequence on the lifted degree-zero cohomology functor computes the
-- degree-`i` cohomology objects up to the standard derived-category shift identification, only
-- finitely many shifts contribute.
/-- The lifted degree-zero cohomology functor has finite shift support on `Dᵇ_{P}`. -/
theorem derivedBoundedWithCohomologyInZeroHomologyFunctor_hasFiniteShiftSupport :
    ∀ X : Dᵇ_{P},
      (derivedBoundedWithCohomologyInZeroHomologyFunctor P).shiftVanishingBounded X := by
  -- Proof comment: boundedness of the ambient derived object gives vanishing of `Hⁱ(X)` outside
  -- a finite interval, and `H⁰(X[i]) ≅ Hⁱ(X)` transports that vanishing back to `P`.
  intro X
  rcases (derivedCategory_t_bounded_iff X.obj.obj).1 X.obj.property with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  refine ⟨⟨a - 1, ?_⟩, ⟨b + 1, ?_⟩⟩
  · intro n hn
    have hzero :
        IsZero ((derivedBoundedWithCohomologyInHomologyFunctor P n).obj X) := by
      refine weakSerre_isZero_of_underlying_isZero (P := P) _ ?_
      simpa [derivedBoundedWithCohomologyInHomologyFunctor] using ha n (by omega)
    exact IsZero.of_iso
      hzero
      (derivedBoundedWithCohomologyIn_zero_homology_shift_obj_iso (A := A) P X n)
  · intro n hn
    have hzero :
        IsZero ((derivedBoundedWithCohomologyInHomologyFunctor P n).obj X) := by
      refine weakSerre_isZero_of_underlying_isZero (P := P) _ ?_
      simpa [derivedBoundedWithCohomologyInHomologyFunctor] using hb n (by omega)
    exact IsZero.of_iso
      hzero
      (derivedBoundedWithCohomologyIn_zero_homology_shift_obj_iso (A := A) P X n)

-- Proof sketch: with the tautological shift sequence on the lifted degree-zero cohomology
-- functor, the `i`-th shifted value is `H⁰(X[i])`, canonically identified with `H^i(X)`. The
-- Euler class from `Lemma 13.28.4` is therefore exactly the textbook alternating sum of the
-- cohomology classes.
/-- The Euler class coming from the general homological-functor owner for the lifted degree-zero
cohomology functor agrees with the textbook alternating sum of the cohomology objects. -/
theorem derivedBoundedWithCohomologyInZeroHomologyFunctor_eulerClass_eq
    (X : Dᵇ_{P}) :
    (derivedBoundedWithCohomologyInZeroHomologyFunctor P).eulerClass X =
      derivedBoundedWithCohomologyInEulerClass P X := by
  -- Proof comment: compare each Euler summand through the tautological shift on the lifted
  -- degree-zero functor and the canonical identification `H⁰(X[i]) ≅ Hⁱ(X)`.
  refine finsum_congr ?_
  intro i
  have hIso :
      ((derivedBoundedWithCohomologyInZeroHomologyFunctor P).shift i).obj X ≅
        ((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X) := by
    exact
      ((derivedBoundedWithCohomologyInZeroHomologyFunctor P).isoShift i).app X ≪≫
        derivedBoundedWithCohomologyIn_zero_homology_shift_obj_iso (A := A) P X i
  -- Rewrite the `K₀` class of each shifted `H⁰` value by the comparison isomorphism.
  exact congrArg (fun z : AbelianK0 P.FullSubcategory ↦ i.negOnePow • z)
    (by
      calc
        K₀[((derivedBoundedWithCohomologyInZeroHomologyFunctor P).shift i).obj X] =
            K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)] := by
              exact weakSerre_k0_eq_of_iso (P := P) hIso)

/-- The Euler-characteristic map `K₀(Dᵇ_{P}) → K₀(P)`. -/
def derivedBoundedWithCohomologyInEulerK0 :
    TriangulatedK0 (Dᵇ_{P}) →+ AbelianK0 P.FullSubcategory :=
  (derivedBoundedWithCohomologyInZeroHomologyFunctor P).eulerK0Map
    (derivedBoundedWithCohomologyInZeroHomologyFunctor_hasFiniteShiftSupport P)

-- Proof sketch: `derivedBoundedWithCohomologyInEulerK0` is the general owner
-- `H0.eulerK0Map` applied to the lifted degree-zero cohomology functor on `Dᵇ_P(A)`;
-- the companion comparison theorem identifies the resulting Euler class with the textbook
-- alternating sum of cohomology classes.
/-- The Euler-characteristic map sends the class of `X` to the alternating sum of the classes of
its cohomology objects. -/
@[simp] theorem derivedBoundedWithCohomologyInEulerK0_apply_of
    (X : Dᵇ_{P}) :
    derivedBoundedWithCohomologyInEulerK0 P (TriangulatedK0.of X) =
      derivedBoundedWithCohomologyInEulerClass P X := by
  simpa [derivedBoundedWithCohomologyInEulerK0] using
    (Functor.eulerK0Map_apply_of (derivedBoundedWithCohomologyInZeroHomologyFunctor P)
      (derivedBoundedWithCohomologyInZeroHomologyFunctor_hasFiniteShiftSupport P) X).trans
        (derivedBoundedWithCohomologyInZeroHomologyFunctor_eulerClass_eq P X)

-- Proof sketch: evaluate the Euler characteristic of the degree-zero object `X[0]`; all
-- cohomology groups vanish except in degree `0`, where the cohomology object is `X` itself.
/-- The Euler-characteristic map is a left inverse to the degree-zero embedding on `K₀(P)`. -/
theorem weakSerreToDerivedBoundedK0_leftInverse :
    Function.LeftInverse
      (derivedBoundedWithCohomologyInEulerK0 P)
      (weakSerreToDerivedBoundedK0 P) := by
  -- TODO: descend the generator calculation from
  -- `derivedBoundedWithCohomologyInEulerClass_single_zero` across the quotient presentation of
  -- `AbelianK0 P.FullSubcategory`; the remaining issue here is elaboration cost, not the
  -- generator-level formula.
  sorry

-- Proof sketch: use the truncation triangles from Remark 13.12.4 to express the class of a
-- bounded derived object as the alternating sum of the classes of its shifted cohomology objects;
-- this is the same expression used by `derivedBoundedWithCohomologyInEulerK0`.
/-- The degree-zero embedding on `K₀(P)` is a right inverse to the Euler-characteristic map on
`K₀(Dᵇ_{P})`. -/
theorem weakSerreToDerivedBoundedK0_rightInverse :
    Function.RightInverse
      (derivedBoundedWithCohomologyInEulerK0 P)
      (weakSerreToDerivedBoundedK0 P) := by
  -- TODO: use the truncation triangles from `Remark_13_12_4` to prove the objectwise class
  -- formula `[X] = ∑ (-1)^i [H^i(X)[0]]`, then upgrade that equality to `TriangulatedK0`.
  sorry

/-- Lemma 13.28.5: for a weak Serre subcategory `P` of an abelian category `A`, the canonical map
`K₀(P) → K₀(Dᵇ_{P})` sending `[X]` to `[X[0]]` is an isomorphism. Its inverse sends the class
of `X` to the alternating sum `\sum_i (-1)^i [H^i(X)]`. -/
noncomputable def weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn :
    AbelianK0 P.FullSubcategory ≃+ TriangulatedK0 (Dᵇ_{P}) where
  toFun := weakSerreToDerivedBoundedK0 P
  invFun := derivedBoundedWithCohomologyInEulerK0 P
  left_inv := weakSerreToDerivedBoundedK0_leftInverse P
  right_inv := weakSerreToDerivedBoundedK0_rightInverse P
  map_add' := (weakSerreToDerivedBoundedK0 P).map_add

-- Proof sketch: this is the `toFun` field of
-- `weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn`, evaluated on the generator class
-- `AbelianK0.of X`.
/-- The canonical equivalence sends the class of `X` to the class of the degree-zero object
`X[0]` in `Dᵇ_{P}`. -/
theorem weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn_apply_of
    (X : P.FullSubcategory) :
    weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn P K₀[X] =
      TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj X) :=
  weakSerreToDerivedBoundedK0_apply_of P X

-- Proof sketch: this is the `invFun` field of
-- `weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn`, evaluated on the class of `X`;
-- the value is exactly the defining Euler characteristic formula.
/-- The inverse equivalence sends the class of `X` to the alternating sum of the classes of the
cohomology objects `H^i(X)`. -/
theorem weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn_symm_apply_of
    (X : Dᵇ_{P}) :
    (weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn P).symm (TriangulatedK0.of X) =
      derivedBoundedWithCohomologyInEulerClass P X :=
  derivedBoundedWithCohomologyInEulerK0_apply_of P X

end WeakSerreBoundedDerivedK0

end CategoryTheory
