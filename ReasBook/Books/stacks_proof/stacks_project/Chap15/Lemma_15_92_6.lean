import Mathlib
import stacks_proof.stacks_project.Chap12.Lemma_12_10_3
import stacks_proof.stacks_project.Chap13.Lemma_13_17_1
import stacks_proof.stacks_project.Chap13.Remark_13_12_4
import stacks_proof.stacks_project.Chap15.Definition_15_92_4
import stacks_proof.stacks_project.Chap15.Lemma_15_92_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] (I : Ideal A)

namespace DerivedCategory

local notation "DMod" => DerivedCategory (ModuleCat A)

/-- Helper for Lemma 15.92.6: derived completeness is stable under the shift by `1` in `D(A)`.
-/
lemma isDerivedCompleteWithRespectTo_shift
    {K : DMod} (hK : K.IsDerivedCompleteWithRespectTo I) :
    K⟦(1 : ℤ)⟧.IsDerivedCompleteWithRespectTo I := by
  intro f hf E
  -- Proof comment: shift the target back by `-1`, then commute restriction of scalars with that
  -- shift so the source returns to the original derived-complete object `K`.
  let F :
      DerivedCategory (ModuleCat (Localization.Away f)) ⥤ DMod :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
  let hsub : Subsingleton (F.obj (E⟦(-1 : ℤ)⟧) ⟶ K) := hK f hf (E⟦(-1 : ℤ)⟧)
  let eK : ((K⟦(1 : ℤ)⟧)⟦(-1 : ℤ)⟧) ≅ K :=
    (shiftFunctorCompIsoId DMod (1 : ℤ) (-1 : ℤ) (by simp)).app K
  refine ⟨fun u v ↦ ?_⟩
  let u' : F.obj (E⟦(-1 : ℤ)⟧) ⟶ K :=
    ((F.commShiftIso (-1 : ℤ)).hom.app E) ≫ u⟦(-1 : ℤ)⟧' ≫ eK.hom
  let v' : F.obj (E⟦(-1 : ℤ)⟧) ⟶ K :=
    ((F.commShiftIso (-1 : ℤ)).hom.app E) ≫ v⟦(-1 : ℤ)⟧' ≫ eK.hom
  have hu'v' : u' = v' := hsub.elim _ _
  have huv :
      ((F.commShiftIso (-1 : ℤ)).hom.app E) ≫ u⟦(-1 : ℤ)⟧' ≫ eK.hom =
        ((F.commShiftIso (-1 : ℤ)).hom.app E) ≫ v⟦(-1 : ℤ)⟧' ≫ eK.hom := by
    simpa [u', v'] using hu'v'
  have hshift :
      u⟦(-1 : ℤ)⟧' = v⟦(-1 : ℤ)⟧' := by
    apply (cancel_epi ((F.commShiftIso (-1 : ℤ)).hom.app E)).1
    exact (cancel_mono eK.hom).1 huv
  exact (shiftFunctor DMod (-1 : ℤ)).map_injective hshift

/-- Helper for Lemma 15.92.6: in `D(A)`, derived completeness with respect to `I` is closed
under extensions, i.e. under the middle term of a distinguished triangle. -/
lemma isDerivedCompleteWithRespectTo_of_distinguished
    {K L M : DMod} {a : K ⟶ L} {b : L ⟶ M} {c : M ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk a b c ∈ distTriang DMod)
    (hK : K.IsDerivedCompleteWithRespectTo I)
    (hM : M.IsDerivedCompleteWithRespectTo I) :
    L.IsDerivedCompleteWithRespectTo I := by
  intro f hf E
  -- Proof comment: for a map into `L`, its composite with `b` vanishes because maps into `M`
  -- are already subsingleton; distinguished-triangle exactness then factors it through `a`,
  -- and maps into `K` are also subsingleton.
  let E' :
      DMod :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
  have hsubK : Subsingleton (E' ⟶ K) := hK f hf E
  have hsubM : Subsingleton (E' ⟶ M) := hM f hf E
  refine ⟨fun u v ↦ ?_⟩
  have hcomp : (u - v) ≫ b = 0 := by
    have huv : u ≫ b = v ≫ b := hsubM.elim _ _
    rw [sub_comp, huv, sub_self]
  obtain ⟨w, hw⟩ := Triangle.coyoneda_exact₂ (T := Triangle.mk a b c) hT (u - v) hcomp
  have hw_zero : w = 0 := hsubK.elim _ _
  apply sub_eq_zero.mp
  calc
    u - v = w ≫ a := hw
    _ = 0 := by simpa [hw_zero]

end DerivedCategory

namespace ModuleCat

/-- Helper for Lemma 15.92.6: the kernel of a morphism from a derived-complete module is again
derived complete. -/
lemma isDerivedCompleteWithRespectTo_kernel
    {M N : ModuleCat A} (u : M ⟶ N)
    (hM : M.IsDerivedCompleteWithRespectTo I) :
    (kernel u).IsDerivedCompleteWithRespectTo I := by
  intro f hf E
  -- Proof comment: any map into the kernel becomes a map into `M`, and the kernel inclusion is
  -- monic, so the source Hom set injects into a subsingleton one.
  let E' :
      DerivedCategory (ModuleCat A) :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
  let single₀ : ModuleCat A ⥤ DerivedCategory (ModuleCat A) := ModuleCat.single0Functor
  have hsubM : Subsingleton (E' ⟶ (ModuleCat.single0Functor : ModuleCat A ⥤
      DerivedCategory (ModuleCat A)).obj M) := hM f hf E
  refine ⟨fun x y ↦ ?_⟩
  apply (cancel_mono (single₀.map (kernel.ι u))).1
  exact hsubM.elim _ _

/-- Helper for Lemma 15.92.6: the cokernel of a monomorphism between derived-complete modules is
again derived complete. -/
lemma isDerivedCompleteWithRespectTo_cokernel_of_mono
    {M N : ModuleCat A} (u : M ⟶ N) [Mono u]
    (hM : M.IsDerivedCompleteWithRespectTo I)
    (hN : N.IsDerivedCompleteWithRespectTo I) :
    (cokernel u).IsDerivedCompleteWithRespectTo I := by
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  have hS : S.ShortExact := by
    -- Proof comment: a monomorphism together with its cokernel projection is the canonical short
    -- exact row `0 → M → N → cokernel u → 0`.
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel u))
      inferInstance inferInstance
  let T : Triangle (DerivedCategory (ModuleCat A)) := hS.singleTriangle
  have hsubObj₂ :
      ∀ f ∈ I, ∀ E : DerivedCategory (ModuleCat (Localization.Away f)),
        Subsingleton
          (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ⟶
            T.obj₂) := by
    intro f hf E
    simpa [T, S] using hN f hf E
  have hsubShiftObj₁ :
      ∀ f ∈ I, ∀ E : DerivedCategory (ModuleCat (Localization.Away f)),
        Subsingleton
          (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ⟶
            T.obj₁⟦(1 : ℤ)⟧) := by
    intro f hf E
    simpa [T, S] using
      (DerivedCategory.isDerivedCompleteWithRespectTo_shift (A := A) (I := I)
        (K := (ModuleCat.single0Functor : ModuleCat A ⥤ DerivedCategory (ModuleCat A)).obj M)
        (by simpa [ModuleCat.IsDerivedCompleteWithRespectTo] using hM)) f hf E
  intro f hf E
  let E' :
      DerivedCategory (ModuleCat A) :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
  have hsub₂ : Subsingleton (E' ⟶ T.obj₂) := hsubObj₂ f hf E
  have hsub₁shift : Subsingleton (E' ⟶ T.obj₁⟦(1 : ℤ)⟧) := hsubShiftObj₁ f hf E
  -- Proof comment: the five-term exactness for the short exact row says every map into the
  -- cokernel factors through `T.mor₂`, and any two such factors agree because the middle term is
  -- already derived complete.
  refine ⟨fun x y ↦ ?_⟩
  have hxy_zero : (x - y) ≫ T.mor₃ = 0 := by
    have hxy : x ≫ T.mor₃ = y ≫ T.mor₃ := hsub₁shift.elim _ _
    rw [sub_comp, hxy, sub_self]
  obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₃ (T := T) hS.singleTriangle_distinguished (x - y) hxy_zero
  have hz_zero : z = 0 := hsub₂.elim _ _
  apply sub_eq_zero.mp
  calc
    x - y = z ≫ T.mor₂ := hz
    _ = 0 := by simpa [hz_zero]

/-- Helper for Lemma 15.92.6: a short exact sequence of derived-complete modules has
derived-complete middle term. -/
lemma isDerivedCompleteWithRespectTo_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact)
    (h₁ : S.X₁.IsDerivedCompleteWithRespectTo I)
    (h₃ : S.X₃.IsDerivedCompleteWithRespectTo I) :
    S.X₂.IsDerivedCompleteWithRespectTo I := by
  -- Proof comment: pass to the canonical distinguished triangle on degree-zero objects and apply
  -- derived-category extension closure to its middle term.
  exact
    DerivedCategory.isDerivedCompleteWithRespectTo_of_distinguished (A := A) (I := I)
      hS.singleTriangle_distinguished h₁ h₃

end ModuleCat

/- Domain-style sampling:
- primary domain: object properties on `ModuleCat A` and the generic derived-category owner
  `derivedCategoryCohomologyInProperty`;
- sampled owner-side declarations:
  `ObjectProperty.IsWeakSerreClass`,
  `ObjectProperty.weakSerreSubcategory_inclusion_exact`,
  `derivedCategoryCohomologyInProperty`,
  `DerivedCategory.derivedCompleteObjectProperty`,
  `ModuleCat.derivedCompleteObjectProperty`;
- best owner abstraction: the object-property owners
  `ModuleCat.derivedCompleteObjectProperty I` and
  `DerivedCategory.derivedCompleteObjectProperty I`;
- primitive data: the module and derived derived-complete predicates from
  `Definition_15_92_4`;
- derived API: the weak-Serre structure on the module owner and the identification of the
  derived owner with the generic cohomology-in-property owner.

Layer triage:
- `source-facing`: derived-complete modules and derived-complete objects with respect to `I`;
- `core/canonical`: `ModuleCat.derivedCompleteObjectProperty I`,
  `DerivedCategory.derivedCompleteObjectProperty I`, and
  `derivedCategoryCohomologyInProperty`;
- `bridge/view`: the pointwise iff restatement below, derived from the owner-level equality. -/

-- Proof sketch: Lemma 15.92.1 identifies derived completeness with vanishing of
-- `Ext^n_A(A_f, -)` for every `f ∈ I`; the associated long exact sequences show closure under
-- kernels, cokernels, and extensions, and Lemma 12.10.3 packages these closures into the weak
-- Serre structure.
/-- Lemma 15.92.6: the derived complete `A`-modules with respect to `I` form a weak Serre
subcategory of `Mod_A`. -/
@[stacks 091U]
theorem derivedCompleteObjectProperty_isWeakSerreClass :
    IsWeakSerreClass (ModuleCat.derivedCompleteObjectProperty I) := by
  let P : ObjectProperty (ModuleCat A) := ModuleCat.derivedCompleteObjectProperty I
  letI : P.ContainsZero := by
    refine ⟨0, isZero_zero _, ?_⟩
    -- Proof comment: the degree-zero derived object on the zero module is itself zero, so every
    -- Hom set into it is subsingleton.
    intro f hf E
    have hzero :
        IsZero ((ModuleCat.single0Functor : ModuleCat A ⥤ DerivedCategory (ModuleCat A)).obj
          (0 : ModuleCat A)) := by
      exact IsZero.of_iso (isZero_zero _) (ModuleCat.single0Functor.mapZeroObject).symm
    exact ⟨fun u v ↦ hzero.eq_of_tgt u v⟩
  letI : P.IsClosedUnderExtensions where
    prop_X₂_of_shortExact {S} hS h₁ h₃ := by
      exact ModuleCat.isDerivedCompleteWithRespectTo_of_shortExact (A := A) (I := I) hS h₁ h₃
  letI : P.IsClosedUnderIsomorphisms :=
    CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_of_containsZero_of_closedUnderExtensions P
  letI : P.IsClosedUnderKernels where
    kernels_le := by
      intro X hX
      rcases hX with ⟨u, k, hk, hMN⟩
      -- Proof comment: a map into the kernel becomes a map into the source object, so the kernel
      -- inherits derived completeness directly from that source.
      exact
        P.prop_of_iso
          (IsLimit.conePointUniqueUpToIso hk (kernelIsKernel u)).symm
          (ModuleCat.isDerivedCompleteWithRespectTo_kernel (A := A) (I := I) u hMN.1)
  letI : P.IsClosedUnderCokernels where
    cokernels_le := by
      intro X hX
      rcases hX with ⟨u, q, hq, hMN⟩
      have hker : P (kernel u) :=
        ModuleCat.isDerivedCompleteWithRespectTo_kernel (A := A) (I := I) u hMN.1
      have hcoim : P (Abelian.coimage u) := by
        -- Proof comment: first take the cokernel of the monomorphism `kernel.ι u`.
        simpa [Abelian.coimage] using
          (ModuleCat.isDerivedCompleteWithRespectTo_cokernel_of_mono (A := A) (I := I)
            (kernel.ι u) hker hMN.1)
      have himage : P (Abelian.image u) := by
        -- Proof comment: in an abelian category, coimage and image are canonically isomorphic.
        exact P.prop_of_iso (Abelian.coimageIsoImage u) hcoim
      have hcokerImage : P (cokernel (Abelian.image.ι u)) := by
        -- Proof comment: the remaining quotient is now the cokernel of a monomorphism.
        exact
          ModuleCat.isDerivedCompleteWithRespectTo_cokernel_of_mono (A := A) (I := I)
            (Abelian.image.ι u) himage hMN.2
      have hcoker : P (cokernel u) := by
        -- Proof comment: `u` and its image inclusion have canonically isomorphic cokernels.
        exact
          P.prop_of_iso
            (asIso (cokernel.map u (Abelian.image.ι u) (Abelian.factorThruImage u) (𝟙 N)
              (by simp))).symm
            hcokerImage
      exact P.prop_of_iso (IsColimit.coconePointUniqueUpToIso hq (cokernelIsCokernel u)).symm hcoker
  exact ObjectProperty.isWeakSerreClass_of_closure P

namespace DerivedCategory

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/-- Helper for Lemma 15.92.6: the degree-`n` single object is canonically the shift by `-n` of
the degree-zero single object. -/
private noncomputable def singleFunctor_obj_iso_shifted_single0_neg
    (M : ModuleCat A) (n : ℤ) :
    (DerivedCategory.singleFunctor (ModuleCat A) n).obj M ≅ ((single₀).obj M)⟦-n⟧ :=
  -- Proof comment: package the standard `shiftIso` comparison into the source-facing form used by
  -- the localization-away vanishing criterion.
  (shiftShiftNeg ((DerivedCategory.singleFunctor (ModuleCat A) n).obj M) n).symm ≪≫
    (shiftFunctor DMod (-n)).mapIso
      (((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso n 0 n (by simp)).app M)

/-- Helper for Lemma 15.92.6: vanishing of `T(M[n], f)` is the same as vanishing of `T(M[0], f)`,
so the fixed-`f` criterion for a single object is independent of the cohomological degree. -/
lemma isZero_localizationAwayT_singleFunctor_iff_moduleLocalizationAwayTVanishing
    (f : A) (M : ModuleCat A) (n : ℤ) :
    IsZero
      (CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f
        ((DerivedCategory.singleFunctor (ModuleCat A) n).obj M)) ↔
      ModuleCat.moduleLocalizationAwayTVanishing M f := by
  let F : DMod ⥤ DMod :=
    CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f
  letI : F.CommShift ℤ := inferInstance
  let eSingle :
      (DerivedCategory.singleFunctor (ModuleCat A) n).obj M ≅ ((single₀).obj M)⟦-n⟧ :=
    singleFunctor_obj_iso_shifted_single0_neg (A := A) M n
  let eF :
      F.obj ((DerivedCategory.singleFunctor (ModuleCat A) n).obj M) ≅
        (F.obj ((single₀).obj M))⟦-n⟧ :=
    (F.mapIso eSingle) ≪≫ asIso ((F.commShiftIso (-n)).hom.app ((single₀).obj M))
  constructor
  · intro hsingle
    have hshift :
        IsZero ((F.obj ((single₀).obj M))⟦-n⟧) :=
      eF.isZero_iff.1 hsingle
    have hshift_back :
        IsZero (((F.obj ((single₀).obj M))⟦-n⟧)⟦n⟧) :=
      (shiftFunctor DMod n).map_isZero hshift
    have hzero :
        IsZero (F.obj ((single₀).obj M)) := by
      -- Proof comment: shift back by `n` and cancel the resulting `(-n, n)` shift pair.
      exact IsZero.of_iso hshift_back (shiftShiftNeg (F.obj ((single₀).obj M)) (-n))
    simpa [F] using (ModuleCat.moduleLocalizationAwayTVanishing_iff (H := inferInstance) M f).2 hzero
  · intro hmodule
    have hzero :
        IsZero (F.obj ((single₀).obj M)) := by
      simpa [F] using (ModuleCat.moduleLocalizationAwayTVanishing_iff (H := inferInstance) M f).1
        hmodule
    have hshift :
        IsZero ((F.obj ((single₀).obj M))⟦-n⟧) :=
      (shiftFunctor DMod (-n)).map_isZero hzero
    -- Proof comment: transport the degree-zero vanishing statement across the canonical single
    -- object comparison and the commutation of `localizationAwayT` with shifts.
    exact eF.symm.isZero_iff.2 hshift

/-- Helper for Lemma 15.92.6: the lower truncation step gives the forward implication needed in
the fixed-`f` bridge. If the isolated degree-`n` cohomology term and the next truncation already
vanish after applying `localizationAwayT`, then the current lower truncation also vanishes. -/
lemma localizationAwayT_truncGE_step_zero_of_outer_zero
    (f : A) (K : DMod) (n : ℤ)
    (h_head : ModuleCat.moduleLocalizationAwayTVanishing ((H n).obj K) f)
    (h_tail :
      IsZero
        (CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f
          ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj K))) :
    IsZero
      (CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f
        ((DerivedCategory.TStructure.t.truncGE n).obj K)) := by
  let F : DMod ⥤ DMod :=
    CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f
  letI : F.CommShift ℤ := inferInstance
  letI : F.IsTriangulated := inferInstance
  let T : Triangle DMod := _root_.truncGE_step_homologyTriangle K n
  have hT : T ∈ distTriang DMod := _root_.truncGE_step_homology_triangle K n
  have h_head_zero : IsZero (F.obj T.obj₁) := by
    -- Proof comment: the first vertex is the isolated degree-`n` cohomology object.
    simpa [T, _root_.truncGE_step_homologyTriangle] using
      (isZero_localizationAwayT_singleFunctor_iff_moduleLocalizationAwayTVanishing
        (A := A) f ((H n).obj K) n).2 h_head
  have h_tail_zero : IsZero (F.obj T.obj₃) := by
    -- Proof comment: the third vertex is the next lower truncation `τ_{\ge n + 1}K`.
    simpa [T, _root_.truncGE_step_homologyTriangle] using h_tail
  have hFT : F.mapTriangle.obj T ∈ distTriang DMod := by
    -- Proof comment: `localizationAwayT` is triangulated, so it preserves the truncation-step
    -- distinguished triangle.
    simpa [F, T] using F.map_distinguished T hT
  have h_mid_zero :
      IsZero ((F.mapTriangle.obj T).obj₂) :=
    Triangle.isZero₂_of_isZero₁₃ (F.mapTriangle.obj T) hFT h_head_zero h_tail_zero
  simpa [F, T, _root_.truncGE_step_homologyTriangle] using h_mid_zero

/-- Helper for Lemma 15.92.6: the upper truncation step gives the forward implication needed in
the fixed-`f` bridge. If the previous upper truncation and the isolated degree-`n` cohomology term
already vanish after applying `localizationAwayT`, then the next upper truncation also vanishes.
-/
lemma localizationAwayT_truncLT_step_zero_of_outer_zero
    (f : A) (K : DMod) (n : ℤ)
    (h_prev :
      IsZero
        (CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f
          ((DerivedCategory.TStructure.t.truncLT n).obj K)))
    (h_head : ModuleCat.moduleLocalizationAwayTVanishing ((H n).obj K) f) :
    IsZero
      (CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f
        ((DerivedCategory.TStructure.t.truncLT (n + 1)).obj K)) := by
  let F : DMod ⥤ DMod :=
    CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f
  letI : F.CommShift ℤ := inferInstance
  letI : F.IsTriangulated := inferInstance
  let T : Triangle DMod := _root_.truncLE_step_homologyTriangle K (n - 1)
  have hT : T ∈ distTriang DMod := _root_.truncLE_step_homology_triangle K (n - 1)
  have h_prev_zero : IsZero (F.obj T.obj₁) := by
    -- Proof comment: for `a = n - 1`, the first vertex is `τ_{< n}K`.
    simpa [T, _root_.truncLE_step_homologyTriangle, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using h_prev
  have h_head_zero : IsZero (F.obj T.obj₃) := by
    -- Proof comment: for `a = n - 1`, the third vertex is the isolated degree-`n` cohomology
    -- object.
    simpa [T, _root_.truncLE_step_homologyTriangle, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using
      (isZero_localizationAwayT_singleFunctor_iff_moduleLocalizationAwayTVanishing
        (A := A) f ((H n).obj K) n).2 h_head
  have hFT : F.mapTriangle.obj T ∈ distTriang DMod := by
    -- Proof comment: exactness transports the source truncation triangle through
    -- `localizationAwayT`.
    simpa [F, T] using F.map_distinguished T hT
  have h_mid_zero :
      IsZero ((F.mapTriangle.obj T).obj₂) :=
    Triangle.isZero₂_of_isZero₁₃ (F.mapTriangle.obj T) hFT h_prev_zero h_head_zero
  simpa [F, T, _root_.truncLE_step_homologyTriangle, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using h_mid_zero

/-- Helper for Lemma 15.92.6: the degree-`n` homology of the textbook object `T(K, f)` vanishes
exactly the constant `f`-tower on the module `M`. -/
abbrev localizationAwayModuleTower (f : A) (M : ModuleCat A) :
    SequentialInverseSystem (ModuleCat A) :=
  let X : ℕ → ModuleCat A := fun _ ↦ M
  let step : (n : ℕ) → X (n + 1) ⟶ X n := fun _ ↦ f • 𝟙 M
  Functor.ofOpSequence step

/-- Helper for Lemma 15.92.6: an isomorphism of modules induces an isomorphism of the associated
constant localization-away towers. -/
private def localizationAwayModuleTower_iso_of_iso
    (f : A) {M N : ModuleCat A} (e : M ≅ N) :
    localizationAwayModuleTower (A := A) f M ≅ localizationAwayModuleTower (A := A) f N := by
  let stageHom : ∀ n : ℕ, M ⟶ N := fun _ ↦ e.hom
  have hstageHom_naturality :
      ∀ n : ℕ,
        (localizationAwayModuleTower (A := A) f M).map (homOfLE (Nat.le_succ n)).op ≫
            stageHom (n + 1) =
          stageHom n ≫
            (localizationAwayModuleTower (A := A) f N).map (homOfLE (Nat.le_succ n)).op := by
    intro n
    ext x
    simp [localizationAwayModuleTower]
  let stageInv : ∀ n : ℕ, N ⟶ M := fun _ ↦ e.inv
  have hstageInv_naturality :
      ∀ n : ℕ,
        (localizationAwayModuleTower (A := A) f N).map (homOfLE (Nat.le_succ n)).op ≫
            stageInv (n + 1) =
          stageInv n ≫
            (localizationAwayModuleTower (A := A) f M).map (homOfLE (Nat.le_succ n)).op := by
    intro n
    ext x
    simp [localizationAwayModuleTower]
  let α :
      localizationAwayModuleTower (A := A) f M ⟶
        localizationAwayModuleTower (A := A) f N :=
    NatTrans.ofOpSequence stageHom hstageHom_naturality
  let β :
      localizationAwayModuleTower (A := A) f N ⟶
        localizationAwayModuleTower (A := A) f M :=
    NatTrans.ofOpSequence stageInv hstageInv_naturality
  refine ⟨α, β, ?_, ?_⟩
  · ext n x
    simp [α, β, stageHom, stageInv]
  · ext n x
    simp [α, β, stageHom, stageInv]

/-- Helper for Lemma 15.92.6: applying cohomology in degree `n` to the derived localization-away
tower gives the constant `f`-tower on the cohomology module `H^n(K)`. -/
lemma homology_localizationAwayTower_iso_module_tower
    (f : A) (K : DMod) (n : ℤ) :
    ((CategoryTheory.DerivedCategory.localizationAwayTower (A := A) f K) ⋙ H n) ≅
      localizationAwayModuleTower (A := A) f ((H n).obj K) := by
  let stageHom : ∀ m : ℕ, ((H n).obj K) ⟶ ((H n).obj K) := fun _ ↦ 𝟙 _
  have hstageHom_naturality :
      ∀ m : ℕ,
        (((CategoryTheory.DerivedCategory.localizationAwayTower (A := A) f K) ⋙ H n).map
            (homOfLE (Nat.le_succ m)).op) ≫ stageHom (m + 1) =
          stageHom m ≫
            (localizationAwayModuleTower (A := A) f ((H n).obj K)).map
              (homOfLE (Nat.le_succ m)).op := by
    intro m
    -- Proof comment: both successor maps are multiplication by `f` on the same cohomology
    -- module, one before and one after identifying the tower object.
    simp [localizationAwayModuleTower,
      CategoryTheory.DerivedCategory.localizationAwayTower]
  let stageInv : ∀ m : ℕ, ((H n).obj K) ⟶ ((H n).obj K) := fun _ ↦ 𝟙 _
  have hstageInv_naturality :
      ∀ m : ℕ,
        (localizationAwayModuleTower (A := A) f ((H n).obj K)).map
            (homOfLE (Nat.le_succ m)).op ≫ stageInv (m + 1) =
          stageInv m ≫
            (((CategoryTheory.DerivedCategory.localizationAwayTower (A := A) f K) ⋙ H n).map
              (homOfLE (Nat.le_succ m)).op) := by
    intro m
    -- Proof comment: this is the same successor-map comparison in the reverse direction.
    simp [localizationAwayModuleTower,
      CategoryTheory.DerivedCategory.localizationAwayTower]
  let α :
      ((CategoryTheory.DerivedCategory.localizationAwayTower (A := A) f K) ⋙ H n) ⟶
        localizationAwayModuleTower (A := A) f ((H n).obj K) :=
    NatTrans.ofOpSequence stageHom hstageHom_naturality
  let β :
      localizationAwayModuleTower (A := A) f ((H n).obj K) ⟶
        ((CategoryTheory.DerivedCategory.localizationAwayTower (A := A) f K) ⋙ H n) :=
    NatTrans.ofOpSequence stageInv hstageInv_naturality
  refine ⟨α, β, ?_, ?_⟩
  · ext m x
    simp [α, β, stageHom, stageInv]
  · ext m x
    simp [α, β, stageHom, stageInv]

/-- Helper for Lemma 15.92.6: a natural isomorphism of sequential module towers induces an
isomorphism on the Milnor term `R^1 \!\varprojlim`. -/
private theorem sequentialModule_firstDerivedLimit_iso_of_natIso
    {Msys Nsys : SequentialInverseSystem (ModuleCat A)} (e : Msys ≅ Nsys) :
    SequentialInverseSystem.firstDerivedLimit Msys ≅
      SequentialInverseSystem.firstDerivedLimit Nsys := by
  -- Proof comment: `R^1 lim` is the Milnor cokernel, so the inverse natural transformation gives
  -- the inverse map on cokernels and both identities reduce to `simp`.
  refine ⟨SequentialInverseSystem.firstDerivedLimitMap e.hom,
    SequentialInverseSystem.firstDerivedLimitMap e.inv, ?_, ?_⟩
  · apply (cancel_epi (cokernel.π (CategoryTheory.derivedLimitDifferenceMap Msys))).1
    simp [SequentialInverseSystem.firstDerivedLimitMap, Category.assoc]
  · apply (cancel_epi (cokernel.π (CategoryTheory.derivedLimitDifferenceMap Nsys))).1
    simp [SequentialInverseSystem.firstDerivedLimitMap, Category.assoc]

/-- Helper for Lemma 15.92.6: the inverse limit and first derived inverse limit of a sequential
module tower vanish when each stage is already zero. -/
private theorem sequentialModule_limit_and_firstDerivedLimit_isZero_of_stagewise_isZero
    (Msys : SequentialInverseSystem (ModuleCat A))
    (hMsys : ∀ n : ℕ, IsZero (Msys.obj (Opposite.op n))) :
    IsZero (limit Msys) ∧ IsZero (SequentialInverseSystem.firstDerivedLimit Msys) := by
  constructor
  · -- Proof comment: every projection from the limit lands in a zero stage, so the identity on
    -- the limit is zero.
    refine (IsZero.iff_id_eq_zero _).2 ?_
    apply limit.hom_ext
    intro n
    simpa using (hMsys n.unop).eq_of_tgt (limit.π Msys n) 0
  · -- Proof comment: the defining product object for `R^1 lim` is zero, so the Milnor
    -- difference map is epi and its cokernel vanishes.
    have hprod : IsZero (∏ᶜ CategoryTheory.inverseSystemFamily Msys) := by
      refine (IsZero.iff_id_eq_zero _).2 ?_
      apply Pi.hom_ext
      intro n
      simpa using (hMsys n).eq_of_tgt (Pi.π (CategoryTheory.inverseSystemFamily Msys) n) 0
    have hEpi : Epi (CategoryTheory.derivedLimitDifferenceMap Msys) := by
      refine ⟨fun g h _ ↦ hprod.eq_of_src g h⟩
    let _ : Epi (CategoryTheory.derivedLimitDifferenceMap Msys) := hEpi
    simpa [SequentialInverseSystem.firstDerivedLimit] using
      (isZero_cokernel_of_epi (CategoryTheory.derivedLimitDifferenceMap Msys))

/-- Helper for Lemma 15.92.6: in a short exact sequence of modules, if the outer terms are zero
then the middle term is zero. -/
private theorem shortComplex_X₂_isZero_of_outer_isZero
    {X₁ X₂ X₃ : ModuleCat A} {ι : X₁ ⟶ X₂} {π : X₂ ⟶ X₃} {h : ι ≫ π = 0}
    (hS : (ShortComplex.mk ι π h).ShortExact)
    (h₁ : IsZero X₁) (h₃ : IsZero X₃) :
    IsZero X₂ := by
  have hπ_zero : π = 0 := h₃.eq_of_tgt π 0
  have hπ_mono : Mono π := by
    -- Proof comment: exactness plus a zero left term forces the right map to be monic.
    exact ((ShortComplex.mk ι π h).exact_iff_mono (h₁.eq_of_src ι 0)).1 hS.exact
  let _ : Mono π := hπ_mono
  exact IsZero.of_mono_eq_zero π hπ_zero

/-- Helper for Lemma 15.92.6: the Milnor short exact sequence for `T(K, f)` identifies its
degree-`n` cohomology with the `R^1 lim` and `lim` of the constant `f`-towers on the neighboring
cohomology modules of `K`. -/
lemma localizationAwayT_cohomology_shortExact
    (f : A) (K : DMod) (n : ℤ) :
    ∃ (ι :
        SequentialInverseSystem.firstDerivedLimit
            (localizationAwayModuleTower (A := A) f ((H (n - 1)).obj K)) ⟶
          (H n).obj
            (CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f K))
      (π :
        (H n).obj
            (CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f K) ⟶
          limit (localizationAwayModuleTower (A := A) f ((H n).obj K)))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  -- TODO: prove the Milnor short exact sequence by specializing
  -- `CategoryTheory.derivedLimit_cohomology_shortExact` to
  -- `CategoryTheory.DerivedCategory.localizationAwayTower f K`, then transport the outer terms
  -- along `homology_localizationAwayTower_iso_module_tower`. This is blocked here because the
  -- current upstream file that should supply `derivedLimit_cohomology_shortExact` does not
  -- compile in the workspace snapshot.
  sorry

/-- Helper for Lemma 15.92.6: the cohomology of a degree-zero module object vanishes away from
degree `0`. -/
private theorem isZero_homology_single0_obj_of_ne
    (M : ModuleCat A) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((H n).obj ((single₀).obj M)) := by
  by_cases hlt : n < 0
  · -- Proof comment: a degree-zero object is concentrated in nonnegative degrees.
    exact DerivedCategory.isZero_of_isGE ((single₀).obj M) 0 n hlt
  · have hgt : 0 < n := by
      omega
    -- Proof comment: the same degree-zero object is also concentrated in nonpositive degrees.
    exact DerivedCategory.isZero_of_isLE ((single₀).obj M) 0 n hgt

/-- Helper for Lemma 15.92.6: for a module `M`, the localization-away vanishing criterion is
equivalent to vanishing of both `lim` and `R^1 lim` of the constant `f`-tower on `M`. -/
lemma moduleLocalizationAwayTVanishing_iff_limit_and_firstDerivedLimit_isZero
    (f : A) (M : ModuleCat A) :
    ModuleCat.moduleLocalizationAwayTVanishing M f ↔
      IsZero (limit (localizationAwayModuleTower (A := A) f M)) ∧
        IsZero (SequentialInverseSystem.firstDerivedLimit
          (localizationAwayModuleTower (A := A) f M)) := by
  let T :
      DMod :=
    CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f ((single₀).obj M)
  let eZero :
      ((H (0 : ℤ)).obj ((single₀).obj M)) ≅ M :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app M
  let eTowerZero :
      localizationAwayModuleTower (A := A) f ((H (0 : ℤ)).obj ((single₀).obj M)) ≅
        localizationAwayModuleTower (A := A) f M :=
    localizationAwayModuleTower_iso_of_iso (A := A) f eZero
  constructor
  · intro hM
    have hzeroT : IsZero T := by
      simpa [T] using
        (ModuleCat.moduleLocalizationAwayTVanishing_iff (H := inferInstance) M f).1 hM
    have hzeroHomology :
        ∀ n : ℤ, IsZero ((H n).obj T) :=
      (isZero_iff_homologyFunctor_obj_isZero (A := A) T).1 hzeroT
    have hnegOne :
        IsZero ((H (-1 : ℤ)).obj ((single₀).obj M)) :=
      isZero_homology_single0_obj_of_ne (A := A) M (-1) (by omega)
    have hone :
        IsZero ((H (1 : ℤ)).obj ((single₀).obj M)) :=
      isZero_homology_single0_obj_of_ne (A := A) M 1 (by omega)
    have hnegOnePair :
        IsZero
            (limit
              (localizationAwayModuleTower (A := A) f
                ((H (-1 : ℤ)).obj ((single₀).obj M)))) ∧
          IsZero
            (SequentialInverseSystem.firstDerivedLimit
              (localizationAwayModuleTower (A := A) f
                ((H (-1 : ℤ)).obj ((single₀).obj M)))) := by
      -- Proof comment: every stage of the degree `-1` tower is already zero.
      apply sequentialModule_limit_and_firstDerivedLimit_isZero_of_stagewise_isZero (A := A)
      intro n
      simpa [localizationAwayModuleTower] using hnegOne
    have honePair :
        IsZero
            (limit
              (localizationAwayModuleTower (A := A) f
                ((H (1 : ℤ)).obj ((single₀).obj M)))) ∧
          IsZero
            (SequentialInverseSystem.firstDerivedLimit
              (localizationAwayModuleTower (A := A) f
                ((H (1 : ℤ)).obj ((single₀).obj M)))) := by
      -- Proof comment: the same stagewise-zero argument applies in degree `1`.
      apply sequentialModule_limit_and_firstDerivedLimit_isZero_of_stagewise_isZero (A := A)
      intro n
      simpa [localizationAwayModuleTower] using hone
    obtain ⟨ι₀, π₀, h₀, hShort₀⟩ :=
      localizationAwayT_cohomology_shortExact (A := A) f ((single₀).obj M) 0
    have hlimZero' :
        IsZero
          (limit
            (localizationAwayModuleTower (A := A) f
              ((H (0 : ℤ)).obj ((single₀).obj M)))) := by
      have hπ₀_zero : π₀ = 0 := (hzeroHomology 0).eq_of_tgt π₀ 0
      let _ : Epi π₀ := hShort₀.epi_g
      exact IsZero.of_epi_eq_zero π₀ hπ₀_zero
    have hlimZero :
        IsZero (limit (localizationAwayModuleTower (A := A) f M)) := by
      -- Proof comment: identify `H^0(M[0])` with `M` itself and transport the limit vanishing.
      exact IsZero.of_iso hlimZero' (HasLimit.isoOfNatIso eTowerZero).symm
    obtain ⟨ι₁, π₁, h₁, hShort₁⟩ :=
      localizationAwayT_cohomology_shortExact (A := A) f ((single₀).obj M) 1
    have hfdlZero' :
        IsZero
          (SequentialInverseSystem.firstDerivedLimit
            (localizationAwayModuleTower (A := A) f
              ((H (0 : ℤ)).obj ((single₀).obj M)))) := by
      have hι₁_zero : ι₁ = 0 := (hzeroHomology 1).eq_of_tgt ι₁ 0
      let _ : Mono ι₁ := hShort₁.mono_f
      exact IsZero.of_mono_eq_zero ι₁ hι₁_zero
    have hfdlZero :
        IsZero
          (SequentialInverseSystem.firstDerivedLimit
            (localizationAwayModuleTower (A := A) f M)) := by
      -- Proof comment: the same `H^0(M[0]) ≅ M` comparison transports the `R^1 lim` vanishing.
      exact IsZero.of_iso hfdlZero'
        (sequentialModule_firstDerivedLimit_iso_of_natIso (A := A) eTowerZero).symm
    exact ⟨hlimZero, hfdlZero⟩
  · rintro ⟨hlimM, hfdlM⟩
    have hlimZero :
        IsZero
          (limit
            (localizationAwayModuleTower (A := A) f
              ((H (0 : ℤ)).obj ((single₀).obj M)))) := by
      exact IsZero.of_iso hlimM (HasLimit.isoOfNatIso eTowerZero)
    have hfdlZero :
        IsZero
          (SequentialInverseSystem.firstDerivedLimit
            (localizationAwayModuleTower (A := A) f
              ((H (0 : ℤ)).obj ((single₀).obj M)))) := by
      exact IsZero.of_iso hfdlM
        (sequentialModule_firstDerivedLimit_iso_of_natIso (A := A) eTowerZero)
    have hzeroHomology : ∀ n : ℤ, IsZero ((H n).obj T) := by
      intro n
      by_cases hzero : n = 0
      · subst n
        obtain ⟨ι, π, h, hShort⟩ :=
          localizationAwayT_cohomology_shortExact (A := A) f ((single₀).obj M) 0
        have hleft :
            IsZero
              (SequentialInverseSystem.firstDerivedLimit
                (localizationAwayModuleTower (A := A) f
                  ((H (-1 : ℤ)).obj ((single₀).obj M)))) := by
          have hnegOne :
              IsZero ((H (-1 : ℤ)).obj ((single₀).obj M)) :=
            isZero_homology_single0_obj_of_ne (A := A) M (-1) (by omega)
          exact
            (sequentialModule_limit_and_firstDerivedLimit_isZero_of_stagewise_isZero
              (A := A)
              (localizationAwayModuleTower (A := A) f
                ((H (-1 : ℤ)).obj ((single₀).obj M)))
              (fun m ↦ by simpa [localizationAwayModuleTower] using hnegOne)).2
        exact shortComplex_X₂_isZero_of_outer_isZero (A := A) hShort hleft hlimZero
      · by_cases hone : n = 1
        · subst n
          obtain ⟨ι, π, h, hShort⟩ :=
            localizationAwayT_cohomology_shortExact (A := A) f ((single₀).obj M) 1
          have hright :
              IsZero
                (limit
                  (localizationAwayModuleTower (A := A) f
                    ((H (1 : ℤ)).obj ((single₀).obj M)))) := by
            have hone' :
                IsZero ((H (1 : ℤ)).obj ((single₀).obj M)) :=
              isZero_homology_single0_obj_of_ne (A := A) M 1 (by omega)
            exact
              (sequentialModule_limit_and_firstDerivedLimit_isZero_of_stagewise_isZero
                (A := A)
                (localizationAwayModuleTower (A := A) f
                  ((H (1 : ℤ)).obj ((single₀).obj M)))
                (fun m ↦ by simpa [localizationAwayModuleTower] using hone')).1
          exact shortComplex_X₂_isZero_of_outer_isZero (A := A) hShort hfdlZero hright
        · obtain ⟨ι, π, h, hShort⟩ :=
            localizationAwayT_cohomology_shortExact (A := A) f ((single₀).obj M) n
          have hprevZero :
              IsZero ((H (n - 1)).obj ((single₀).obj M)) :=
            isZero_homology_single0_obj_of_ne (A := A) M (n - 1) (by omega)
          have hcurrZero :
              IsZero ((H n).obj ((single₀).obj M)) :=
            isZero_homology_single0_obj_of_ne (A := A) M n hzero
          have hleft :
              IsZero
                (SequentialInverseSystem.firstDerivedLimit
                  (localizationAwayModuleTower (A := A) f
                    ((H (n - 1)).obj ((single₀).obj M)))) := by
            exact
              (sequentialModule_limit_and_firstDerivedLimit_isZero_of_stagewise_isZero
                (A := A)
                (localizationAwayModuleTower (A := A) f
                  ((H (n - 1)).obj ((single₀).obj M)))
                (fun m ↦ by simpa [localizationAwayModuleTower] using hprevZero)).2
          have hright :
              IsZero
                (limit
                  (localizationAwayModuleTower (A := A) f
                    ((H n).obj ((single₀).obj M)))) := by
            exact
              (sequentialModule_limit_and_firstDerivedLimit_isZero_of_stagewise_isZero
                (A := A)
                (localizationAwayModuleTower (A := A) f
                  ((H n).obj ((single₀).obj M)))
                (fun m ↦ by simpa [localizationAwayModuleTower] using hcurrZero)).1
          exact shortComplex_X₂_isZero_of_outer_isZero (A := A) hShort hleft hright
    have hzeroT : IsZero T :=
      (isZero_iff_homologyFunctor_obj_isZero (A := A) T).2 hzeroHomology
    simpa [T] using
      (ModuleCat.moduleLocalizationAwayTVanishing_iff (H := inferInstance) M f).2 hzeroT

/-- Helper for Lemma 15.92.6: a derived object is zero exactly when all of its cohomology objects
vanish. -/
lemma isZero_iff_homologyFunctor_obj_isZero
    (L : DMod) :
    IsZero L ↔ ∀ n : ℤ, IsZero ((H n).obj L) := by
  constructor
  · intro hL n
    -- Proof comment: each cohomology functor preserves zero objects.
    exact (H n).map_isZero hL
  · intro hHomology
    -- Proof comment: vanishing of every cohomology object places `L` in both halves of the
    -- standard t-structure with an empty interval, hence `L` is zero.
    have hLE : L.IsLE 0 := by
      rw [DerivedCategory.isLE_iff]
      intro i hi
      exact hHomology i
    have hGE : L.IsGE 1 := by
      rw [DerivedCategory.isGE_iff]
      intro i hi
      exact hHomology i
    letI : L.IsLE 0 := hLE
    letI : L.IsGE 1 := hGE
    exact t.isZero L 0 1 (by omega)

/-- Helper for Lemma 15.92.6: the fixed-`f` derived-Hom vanishing condition is equivalent to the
degreewise module localization-away criterion on all cohomology objects. -/
lemma localizationAwayDerivedHomVanishingCondition_iff_homology_moduleLocalizationAwayTVanishing
    (f : A) (K : DMod) :
    CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f K ↔
      ∀ n : ℤ, ModuleCat.moduleLocalizationAwayTVanishing ((H n).obj K) f := by
  constructor
  · intro hvanish n
    -- Proof comment: from `T(K,f)=0`, degrees `n` and `n + 1` of the Milnor short exact
    -- sequence force both `lim` and `R^1 lim` for the constant tower on `H^n(K)` to vanish.
    have hzeroT :
        IsZero (CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f K) :=
      (CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition_iff
        (H := inferInstance) f K).1 hvanish
    have hzeroHomology :
        ∀ m : ℤ,
          IsZero
            ((H m).obj
              (CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f K)) :=
      (isZero_iff_homologyFunctor_obj_isZero (A := A)
        (L := CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f K)).1
        hzeroT
    obtain ⟨ιₙ, πₙ, hₙ, hShortₙ⟩ :=
      localizationAwayT_cohomology_shortExact (A := A) f K n
    have hlim :
        IsZero
          (limit (localizationAwayModuleTower (A := A) f ((H n).obj K))) := by
      have hπₙ_zero : πₙ = 0 := (hzeroHomology n).eq_of_tgt πₙ 0
      let _ : Epi πₙ := hShortₙ.epi_g
      exact IsZero.of_epi_eq_zero πₙ hπₙ_zero
    obtain ⟨ιsucc, πsucc, hsucc, hShortsucc⟩ :=
      localizationAwayT_cohomology_shortExact (A := A) f K (n + 1)
    have hfdl :
        IsZero
          (SequentialInverseSystem.firstDerivedLimit
            (localizationAwayModuleTower (A := A) f ((H n).obj K))) := by
      have hιsucc_zero : ιsucc = 0 := (hzeroHomology (n + 1)).eq_of_tgt ιsucc 0
      let _ : Mono ιsucc := hShortsucc.mono_f
      exact IsZero.of_mono_eq_zero ιsucc hιsucc_zero
    exact
      (moduleLocalizationAwayTVanishing_iff_limit_and_firstDerivedLimit_isZero
        (A := A) f ((H n).obj K)).2 ⟨hlim, hfdl⟩
  · intro hmodules
    -- Proof comment: the module criterion kills the two Milnor outer terms in every degree, so
    -- the short exact sequence forces all cohomology of `T(K,f)` to vanish.
    have hzeroHomology :
        ∀ n : ℤ,
          IsZero
            ((H n).obj
              (CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f K)) := by
      intro n
      obtain ⟨ι, π, h, hShort⟩ :=
        localizationAwayT_cohomology_shortExact (A := A) f K n
      have hleft :
          IsZero
            (SequentialInverseSystem.firstDerivedLimit
              (localizationAwayModuleTower (A := A) f ((H (n - 1)).obj K))) := by
        exact
          ((moduleLocalizationAwayTVanishing_iff_limit_and_firstDerivedLimit_isZero
            (A := A) f ((H (n - 1)).obj K)).1 (hmodules (n - 1))).2
      have hright :
          IsZero
            (limit (localizationAwayModuleTower (A := A) f ((H n).obj K))) := by
        exact
          ((moduleLocalizationAwayTVanishing_iff_limit_and_firstDerivedLimit_isZero
            (A := A) f ((H n).obj K)).1 (hmodules n)).1
      exact shortComplex_X₂_isZero_of_outer_isZero (A := A) hShort hleft hright
    have hzeroT :
        IsZero (CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f K) :=
      (isZero_iff_homologyFunctor_obj_isZero (A := A)
        (L := CategoryTheory.DerivedCategory.localizationAwayT (H := inferInstance) f K)).2
        hzeroHomology
    exact
      (CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition_iff
        (H := inferInstance) f K).2 hzeroT

/-- Helper for Lemma 15.92.6: once the fixed-`f` localization-away criterion is known degreewise
on cohomology, derived completeness of a complex is equivalent to derived completeness of all its
cohomology modules. -/
lemma isDerivedCompleteWithRespectTo_iff_homology_isDerivedComplete_of_fixed_f_bridge
    (hbridge :
      ∀ f : A, ∀ K : DMod,
        CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f K ↔
          ∀ n : ℤ, ModuleCat.moduleLocalizationAwayTVanishing ((H n).obj K) f)
    (K : DMod) :
    K.IsDerivedCompleteWithRespectTo I ↔
      ∀ n : ℤ, ((H n).obj K).IsDerivedCompleteWithRespectTo I := by
  constructor
  · intro hK n
    -- Proof comment: specialize the fixed-`f` bridge at each `f ∈ I` and then read off the
    -- degree-`n` module statement.
    intro f hf
    simpa [ModuleCat.moduleLocalizationAwayTVanishing] using
      ((hbridge f K).1 (hK f hf)) n
  · intro hK
    -- Proof comment: conversely, the fixed-`f` bridge is recovered degreewise from the assumed
    -- derived completeness of all cohomology modules, and then reassembled over `f ∈ I`.
    intro f hf
    refine (hbridge f K).2 ?_
    intro n
    simpa [ModuleCat.moduleLocalizationAwayTVanishing] using hK n f hf

/-- Helper for Lemma 15.92.6: after the fixed-`f` bridge is proved, the owner equality is just
the pointwise cohomology reformulation. -/
lemma derivedCompleteObjectProperty_eq_derivedCategoryCohomologyInProperty_of_fixed_f_bridge
    (hbridge :
      ∀ f : A, ∀ K : DMod,
        CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f K ↔
          ∀ n : ℤ, ModuleCat.moduleLocalizationAwayTVanishing ((H n).obj K) f) :
    DerivedCategory.derivedCompleteObjectProperty I =
      derivedCategoryCohomologyInProperty (ModuleCat.derivedCompleteObjectProperty I) := by
  ext K
  -- Proof comment: expand the owner `derivedCategoryCohomologyInProperty` and apply the
  -- degreewise cohomology criterion proved just above.
  change K.IsDerivedCompleteWithRespectTo I ↔
    ∀ n : ℤ, ((H n).obj K).IsDerivedCompleteWithRespectTo I
  exact
    isDerivedCompleteWithRespectTo_iff_homology_isDerivedComplete_of_fixed_f_bridge
      (A := A) (I := I) hbridge K

-- Proof sketch: use Lemma 15.92.1 to pass between derived completeness of a complex and the
-- vanishing criterion after localizing at each `f ∈ I`. The long exact cohomology sequences show
-- that this criterion holds degreewise on the cohomology modules of `K`.
/-- The derived-complete owner on `D(A)` is exactly the generic cohomology-in-property owner
attached to derived-complete modules. -/
theorem derivedCompleteObjectProperty_eq_derivedCategoryCohomologyInProperty :
    DerivedCategory.derivedCompleteObjectProperty I =
      derivedCategoryCohomologyInProperty (ModuleCat.derivedCompleteObjectProperty I) := by
  -- Route correction: the previous proof left the whole owner equality opaque. We now isolate the
  -- single missing source-faithful fixed-`f` bridge and prove the quantifier/owner assembly
  -- separately.
  -- Proof comment: the main theorem is now reduced to the fixed-`f` bridge proved just above.
  exact
    derivedCompleteObjectProperty_eq_derivedCategoryCohomologyInProperty_of_fixed_f_bridge
      (A := A) (I := I)
      (fun f K ↦
        localizationAwayDerivedHomVanishingCondition_iff_homology_moduleLocalizationAwayTVanishing
          (A := A) f K)

/-- Companion pointwise restatement of
`derivedCompleteObjectProperty_eq_derivedCategoryCohomologyInProperty`. -/
theorem isDerivedCompleteWithRespectTo_iff_mem_derivedCategoryCohomologyInProperty
    (K : DMod) :
    K.IsDerivedCompleteWithRespectTo I ↔
      derivedCategoryCohomologyInProperty (ModuleCat.derivedCompleteObjectProperty I) K := by
  change DerivedCategory.derivedCompleteObjectProperty I K ↔
    derivedCategoryCohomologyInProperty (ModuleCat.derivedCompleteObjectProperty I) K
  exact
    (congrArg (fun P : ObjectProperty DMod ↦ P K)
      (derivedCompleteObjectProperty_eq_derivedCategoryCohomologyInProperty I)).to_iff


end DerivedCategory

end
