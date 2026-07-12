import Mathlib
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Definition_15_92_4
import StacksProject_2024.Chap15.Lemma_15_92_6
import StacksProject_2024.Chap15.Lemma_15_92_3.Transport

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

namespace ModuleCat

variable {I : Ideal A} {M : ModuleCat.{u, u} A}

local notation "IM" => I • (⊤ : Submodule A M)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat A ⥤ DerivedCategory (ModuleCat A))

/- Domain-style sampling:
- primary domain: derived-complete modules over a commutative ring, with quotient-vanishing and
  submodule-saturation criteria for zero modules;
- sampled owner-side declarations:
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `derivedCompleteObjectProperty_isWeakSerreClass`,
  `surjective_adicCompletion_of_isDerivedCompleteWithRespectTo`,
  `subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson`;
- best owner abstraction: the project owner predicate `ModuleCat.IsDerivedCompleteWithRespectTo`,
  with the primitive zero-criterion expressed by the owner-level equality
  `I • (⊤ : Submodule A M) = ⊤`;
- primitive data: the ideal `I`, the module `M`, derived completeness of `M`, and the submodule
  equality `I • ⊤ = ⊤`;
- derived API: the source-facing quotient formulation
  `Subsingleton (M ⧸ I • (⊤ : Submodule A M))`.

Layer triage:
- `source-facing`: the quotient-vanishing statement `M / IM = 0`;
- `core/canonical`: `M.IsDerivedCompleteWithRespectTo I` together with `I • ⊤ = ⊤`;
- `bridge/view`: the quotient-subsingleton companion theorem below. -/

namespace DerivedCategory

/-- Helper for Lemma 15.92.7: derived completeness is stable under the shift by `1` in `D(A)`. -/
lemma isDerivedCompleteWithRespectTo_shift_local
    {K : DerivedCategory (ModuleCat A)} (hK : K.IsDerivedCompleteWithRespectTo I) :
    K⟦(1 : ℤ)⟧.IsDerivedCompleteWithRespectTo I := by
  intro f hf E
  -- Proof comment: shift the target back by `-1`, then commute restriction of scalars with that
  -- shift so the source returns to the original derived-complete object `K`.
  let F :
      DerivedCategory (ModuleCat (Localization.Away f)) ⥤ DerivedCategory (ModuleCat A) :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
  let hsub : Subsingleton (F.obj (E⟦(-1 : ℤ)⟧) ⟶ K) := hK f hf (E⟦(-1 : ℤ)⟧)
  let eK : ((K⟦(1 : ℤ)⟧)⟦(-1 : ℤ)⟧) ≅ K :=
    (shiftFunctorCompIsoId (DerivedCategory (ModuleCat A)) (1 : ℤ) (-1 : ℤ) (by simp)).app K
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
    have huv' :
        (((F.commShiftIso (-1 : ℤ)).hom.app E) ≫ u⟦(-1 : ℤ)⟧') ≫ eK.hom =
          (((F.commShiftIso (-1 : ℤ)).hom.app E) ≫ v⟦(-1 : ℤ)⟧') ≫ eK.hom := by
      simpa [Category.assoc] using huv
    exact (cancel_mono eK.hom).1 huv'
  exact (shiftFunctor (DerivedCategory (ModuleCat A)) (-1 : ℤ)).map_injective hshift

end DerivedCategory

/-- Helper for Lemma 15.92.7: the kernel of a morphism from a derived-complete module is again
derived complete. -/
lemma isDerivedCompleteWithRespectTo_kernel_local
    {I : Ideal A} {M N : ModuleCat.{u, u} A} (u : M ⟶ N)
    (hM : M.IsDerivedCompleteWithRespectTo I) :
    (kernel u).IsDerivedCompleteWithRespectTo I := by
  exact ModuleCat.isDerivedCompleteWithRespectTo_kernel (I := I) u hM

/-- Helper for Lemma 15.92.7: the cokernel of a monomorphism between derived-complete modules is
again derived complete. -/
lemma isDerivedCompleteWithRespectTo_cokernel_of_mono_local
    {I : Ideal A} {M N : ModuleCat.{u, u} A} (u : M ⟶ N) [Mono u]
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
      (DerivedCategory.isDerivedCompleteWithRespectTo_shift_local (A := A) (I := I)
        (K := (ModuleCat.single0Functor : ModuleCat A ⥤ DerivedCategory (ModuleCat A)).obj M)
        (by simpa [ModuleCat.IsDerivedCompleteWithRespectTo] using hM)) f hf E
  intro f hf E
  let E' :
      DerivedCategory (ModuleCat A) :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
  have hsub₂ : Subsingleton (E' ⟶ T.obj₂) := hsubObj₂ f hf E
  have hsub₁shift : Subsingleton (E' ⟶ T.obj₁⟦(1 : ℤ)⟧) := hsubShiftObj₁ f hf E
  -- Proof comment: exactness in the distinguished triangle forces maps into the cokernel to
  -- factor through `T.mor₂`, and those factors agree because the middle term is derived complete.
  refine ⟨fun x y ↦ ?_⟩
  have hxy_zero : (x - y) ≫ T.mor₃ = 0 := by
    have hxy : x ≫ T.mor₃ = y ≫ T.mor₃ := hsub₁shift.elim _ _
    rw [Preadditive.sub_comp, hxy, sub_self]
  obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₃ (T := T) hS.singleTriangle_distinguished (x - y) hxy_zero
  have hz_zero : z = 0 := hsub₂.elim _ _
  apply sub_eq_zero.mp
  calc
    x - y = z ≫ T.mor₂ := hz
    _ = 0 := by simpa [hz_zero]

/-- Helper for Lemma 15.92.7: module-level derived completeness is invariant under module
isomorphism. -/
private lemma module_isDerivedCompleteWithRespectTo_iff_of_iso
    {I : Ideal A} {M N : ModuleCat.{u, u} A} (e : M ≅ N) :
    M.IsDerivedCompleteWithRespectTo I ↔ N.IsDerivedCompleteWithRespectTo I := by
  -- Proof comment: transport the module statement through the degree-zero embedding into the
  -- derived category.
  constructor
  · intro hM f hf E
    have hSub :
        Subsingleton
          ((((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory).obj
              E) ⟶
            (single₀).obj M) :=
      hM f hf E
    refine ⟨fun g₁ g₂ ↦ ?_⟩
    have hEq :
        g₁ ≫ ((single₀).mapIso e).inv =
          g₂ ≫ ((single₀).mapIso e).inv :=
      @Subsingleton.elim _ hSub _ _
    simpa [Category.assoc] using
      congrArg (fun h ↦ h ≫ ((single₀).mapIso e).hom) hEq
  · intro hN f hf E
    have hSub :
        Subsingleton
          ((((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory).obj
              E) ⟶
            (single₀).obj N) :=
      hN f hf E
    refine ⟨fun g₁ g₂ ↦ ?_⟩
    have hEq :
        g₁ ≫ ((single₀).mapIso e).hom =
          g₂ ≫ ((single₀).mapIso e).hom :=
      @Subsingleton.elim _ hSub _ _
    simpa [Category.assoc] using
      congrArg (fun h ↦ h ≫ ((single₀).mapIso e).inv) hEq

/-- Helper for Lemma 15.92.7: multiplication by `f` has image exactly `fM`. -/
lemma range_lsmul_eq_principalIdeal_smul_top
    {M : Type u} [AddCommGroup M] [Module A M] (f : A) :
    LinearMap.range (LinearMap.lsmul A M f) =
      Ideal.span ({f} : Set A) • (⊤ : Submodule A M) := by
  ext x
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
    -- Proof comment: an explicit `f`-multiple is, by definition, in the principal ideal multiple.
    exact
      Submodule.smul_mem_smul
        (Ideal.subset_span (by simp : f ∈ ({f} : Set A)))
        (show y ∈ (⊤ : Submodule A M) by simp)
  · intro hx
    -- Proof comment: every generator of `fM` is hit by the scalar-multiplication map.
    have hle :
        Ideal.span ({f} : Set A) • (⊤ : Submodule A M) ≤
          LinearMap.range (LinearMap.lsmul A M f) := by
      rw [Submodule.smul_le]
      intro r hr y hy
      rcases Ideal.mem_span_singleton.mp hr with ⟨a, rfl⟩
      refine LinearMap.mem_range.mpr ⟨a • y, ?_⟩
      simp [LinearMap.lsmul_apply, smul_smul, mul_comm]
    exact hle hx

/-- Helper for Lemma 15.92.7: an element of `fM` has an explicit `f`-divisibility witness. -/
lemma exists_eq_smul_of_mem_span_singleton_smul_top
    {M : Type u} [AddCommGroup M] [Module A M] (f : A) {x : M}
    (hx : x ∈ Ideal.span ({f} : Set A) • (⊤ : Submodule A M)) :
    ∃ y, x = f • y := by
  -- Proof comment: rewrite `fM` as the range of multiplication by `f` and choose a preimage.
  have hx' : x ∈ LinearMap.range (LinearMap.lsmul A M f) := by
    simpa [range_lsmul_eq_principalIdeal_smul_top (A := A) (M := M) f] using hx
  rcases LinearMap.mem_range.mp hx' with ⟨y, hy⟩
  exact ⟨y, by simpa [LinearMap.lsmul_apply] using hy.symm⟩

/-- Helper for Lemma 15.92.7: a localization-away vanishing condition kills the initial term of a
principal recursive sequence. -/
lemma principal_recursive_sequence_zero_of_localizationAwayDerivedHomVanishingCondition
    (f : A) (M : ModuleCat.{u, u} A)
    (hvanish : CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f
      ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M))
    (y : ℕ → M) (hy : ∀ n : ℕ, y n = f • y (n + 1)) :
    y 0 = 0 := by
  -- Route correction: the `A_f[0]` transport now comes from the stabilized helper in
  -- `Lemma_15_92_3`, so this proof only builds the source-faithful recursive-sequence map.
  let Y : Submodule A (ℕ → M) :=
    { carrier := {z | ∀ n : ℕ, z n = f • z (n + 1)}
      zero_mem' := by
        intro n
        simp
      add_mem' := by
        intro z w hz hw n
        simp [hz n, hw n, smul_add]
      smul_mem' := by
        intro a z hz n
        simp [hz n, smul_smul, mul_comm] }
  let shift : Y →ₗ[A] Y :=
    { toFun := fun z ↦ ⟨fun n ↦ z.1 (n + 1), by
        intro n
        exact z.2 (n + 1)⟩
      map_add' := by
        intro z w
        ext n
        rfl
      map_smul' := by
        intro a z
        ext n
        rfl }
  have hpowers :
      ∀ s : Submonoid.powers f, IsUnit ((algebraMap A (Module.End A Y)) s.1) := by
    have hfunit : IsUnit ((algebraMap A (Module.End A Y)) f) := by
      -- Proof comment: shifting one step backward is inverse to multiplication by `f` on
      -- recursive sequences.
      refine ⟨⟨algebraMap A (Module.End A Y) f, shift, ?_, ?_⟩, rfl⟩
      · ext z n
        change f • z.1 (n + 1) = z.1 n
        simpa using (z.2 n).symm
      · ext z n
        cases n with
        | zero =>
            change f • z.1 1 = z.1 0
            simpa using (z.2 0).symm
        | succ n =>
            change f • z.1 (n + 1 + 1) = z.1 (n + 1)
            simpa using (z.2 (n + 1)).symm
    intro s
    rcases s with ⟨s, ⟨n, rfl⟩⟩
    simpa [map_pow] using hfunit.pow n
  let y₀ : Y := ⟨y, hy⟩
  let base : A →ₗ[A] Y :=
    { toFun := fun a ↦ a • y₀
      map_add' := by
        intro a b
        simp [add_smul]
      map_smul' := by
        intro a b
        simp [mul_smul] }
  let lifted : LocalizedModule.Away f A →ₗ[A] Y :=
    IsLocalizedModule.lift (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) A) base hpowers
  let evalZero : Y →ₗ[A] M :=
    { toFun := fun z ↦ z.1 0
      map_add' := by
        intro z w
        rfl
      map_smul' := by
        intro a z
        rfl }
  let e : LocalizedModule.Away f A ≃ₗ[A] Localization.Away f :=
    IsLocalizedModule.linearEquiv (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) A)
      (Algebra.linearMap A (Localization.Away f))
  let φ : Localization.Away f →ₗ[A] M :=
    evalZero.comp (lifted.comp e.symm.toLinearMap)
  have he' :
      e.symm (algebraMap A (Localization.Away f) 1) =
        LocalizedModule.mkLinearMap (Submonoid.powers f) A 1 := by
    -- Proof comment: compare the denominator-`1` generator across the canonical localization
    -- equivalence.
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    simpa using
      (IsLocalizedModule.linearEquiv_apply (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) A)
        (Algebra.linearMap A (Localization.Away f)) 1).symm
  have hφ_apply_one : φ (algebraMap A (Localization.Away f) 1) = y 0 := by
    -- Proof comment: evaluating the localized map at `1` recovers the initial recursive term.
    change evalZero (lifted (e.symm (algebraMap A (Localization.Away f) 1))) = y 0
    calc
      evalZero (lifted (e.symm (algebraMap A (Localization.Away f) 1)))
          = evalZero (lifted (LocalizedModule.mkLinearMap (Submonoid.powers f) A 1)) := by
              simpa using congrArg (fun z ↦ evalZero (lifted z)) he'
      _ = evalZero (base 1) := by
            simpa [lifted] using congrArg evalZero
              (IsLocalizedModule.lift_apply (Submonoid.powers f)
                (LocalizedModule.mkLinearMap (Submonoid.powers f) A) base hpowers 1)
      _ = y 0 := by
            simp [evalZero, base, y₀]
  letI : Subsingleton (Localization.Away f →ₗ[A] M) :=
    ModuleCat.subsingleton_linearMap_from_localizationAway_of_localizationAwayDerivedHomVanishingCondition
      (A := A) f M hvanish
  have hφ : φ = 0 := Subsingleton.elim _ _
  have happly :
      φ (algebraMap A (Localization.Away f) 1) = 0 := by
    simpa using congrArg
      (fun ψ : Localization.Away f →ₗ[A] M ↦ ψ (algebraMap A (Localization.Away f) 1)) hφ
  -- Proof comment: rewrite the evaluation at `1` back to the initial recursive term.
  rwa [hφ_apply_one] at happly

/-- Helper for Lemma 15.92.7: derived completeness descends along smaller ideals. -/
lemma isDerivedCompleteWithRespectTo_of_le {J I : Ideal A} {M : ModuleCat A}
    (hM : M.IsDerivedCompleteWithRespectTo I) (hJI : J ≤ I) :
    M.IsDerivedCompleteWithRespectTo J := by
  -- Proof comment: the defining localization-away vanishing condition for `J` is a subset of the
  -- one already available for `I`.
  intro f hf E
  exact hM f (hJI hf) E

/-- Helper for Lemma 15.92.7: quotients by submodules of the form `J M` remain derived complete. -/
lemma isDerivedCompleteWithRespectTo_quotient_smul_top
    {I J : Ideal A} {M : ModuleCat.{u, u} A}
    (hM : M.IsDerivedCompleteWithRespectTo I) :
    (ModuleCat.of A (M ⧸ J • (⊤ : Submodule A M))).IsDerivedCompleteWithRespectTo I := by
  let K : Submodule A M := J • (⊤ : Submodule A M)
  have hKker :
      (kernel (ModuleCat.ofHom (Submodule.mkQ K))).IsDerivedCompleteWithRespectTo I := by
    -- Proof comment: the submodule `K = J M` is the kernel object of the quotient map `M → M / K`.
    exact
      isDerivedCompleteWithRespectTo_kernel_local (A := A) (I := I)
        (u := ModuleCat.ofHom (Submodule.mkQ K)) hM
  have hK : (ModuleCat.of A K).IsDerivedCompleteWithRespectTo I := by
    have hK' : (ModuleCat.of A ((Submodule.mkQ K).ker)).IsDerivedCompleteWithRespectTo I := by
      exact
        (module_isDerivedCompleteWithRespectTo_iff_of_iso
          (I := I) (ModuleCat.kernelIsoKer (ModuleCat.ofHom (Submodule.mkQ K)))).1 hKker
    let eK : ModuleCat.of A ((Submodule.mkQ K).ker) ≅ ModuleCat.of A K :=
      (LinearEquiv.ofEq _ _ (Submodule.ker_mkQ K)).toModuleIso
    exact (module_isDerivedCompleteWithRespectTo_iff_of_iso (I := I) eK).1 hK'
  have hQcoker :
      (cokernel (ModuleCat.ofHom K.subtype)).IsDerivedCompleteWithRespectTo I := by
    exact
      isDerivedCompleteWithRespectTo_cokernel_of_mono_local (A := A) (I := I)
        (u := ModuleCat.ofHom K.subtype) hK hM
  -- Proof comment: the quotient `M / K` is the cokernel of the inclusion `K ↪ M`.
  have hQ' :
      (ModuleCat.of A (M ⧸ (K.subtype : K →ₗ[A] M).range)).IsDerivedCompleteWithRespectTo I := by
    exact
      (module_isDerivedCompleteWithRespectTo_iff_of_iso
        (I := I) (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom K.subtype))).1 hQcoker
  let eQ : ModuleCat.of A (M ⧸ (K.subtype : K →ₗ[A] M).range) ≅ ModuleCat.of A (M ⧸ K) :=
    (Submodule.quotEquivOfEq (K.subtype.range) K (Submodule.range_subtype K)).toModuleIso
  exact (module_isDerivedCompleteWithRespectTo_iff_of_iso (I := I) eQ).1 hQ'

/-- Helper for Lemma 15.92.7: a derived-complete module on which one element of the ideal acts
surjectively is subsingleton. -/
lemma subsingleton_of_isDerivedCompleteWithRespectTo_of_span_singleton_smul_top_eq_top
    {I : Ideal A} {M : ModuleCat.{u, u} A} (f : A) (hf : f ∈ I)
    (hM : M.IsDerivedCompleteWithRespectTo I)
    (hspan : Ideal.span ({f} : Set A) • (⊤ : Submodule A M) = ⊤) :
    Subsingleton M := by
  classical
  refine ⟨fun x y ↦ ?_⟩
  have hdivisible : ∀ z : M, ∃ w, z = f • w := by
    intro z
    have hz_top : z ∈ (⊤ : Submodule A M) := by simp
    have hz_span : z ∈ Ideal.span ({f} : Set A) • (⊤ : Submodule A M) := by
      simpa [hspan] using hz_top
    exact exists_eq_smul_of_mem_span_singleton_smul_top (A := A) (M := M) f hz_span
  have hx_zero : x = 0 := by
    let seq : ℕ → M := Nat.rec x (fun _ prev => Classical.choose (hdivisible prev))
    have hseq : ∀ n : ℕ, seq n = f • seq (n + 1) := by
      intro n
      cases n with
      | zero =>
          simpa [seq] using Classical.choose_spec (hdivisible x)
      | succ n =>
          simpa [seq] using Classical.choose_spec (hdivisible (seq (n + 1)))
    have hzero :
        seq 0 = 0 :=
      principal_recursive_sequence_zero_of_localizationAwayDerivedHomVanishingCondition
        (A := A) f M (hM f hf) seq hseq
    simpa [seq] using hzero
  have hy_zero : y = 0 := by
    let seq : ℕ → M := Nat.rec y (fun _ prev => Classical.choose (hdivisible prev))
    have hseq : ∀ n : ℕ, seq n = f • seq (n + 1) := by
      intro n
      cases n with
      | zero =>
          simpa [seq] using Classical.choose_spec (hdivisible y)
      | succ n =>
          simpa [seq] using Classical.choose_spec (hdivisible (seq (n + 1)))
    have hzero :
        seq 0 = 0 :=
      principal_recursive_sequence_zero_of_localizationAwayDerivedHomVanishingCondition
        (A := A) f M (hM f hf) seq hseq
    simpa [seq] using hzero
  rw [hx_zero, hy_zero]

/-- Helper for Lemma 15.92.7: if the quotient by `J M` is subsingleton, then `J M = M`. -/
lemma smul_top_eq_top_of_subsingleton_quotient
    {J : Ideal A} {M : ModuleCat A}
    (hquot : Subsingleton (M ⧸ J • (⊤ : Submodule A M))) :
    J • (⊤ : Submodule A M) = ⊤ := by
  -- Proof comment: every element has zero residue class in the quotient, so every element already
  -- belongs to `J M`.
  refine Submodule.eq_top_iff'.2 ?_
  intro x
  have hx : Submodule.mkQ (J • (⊤ : Submodule A M)) x = 0 := Subsingleton.elim _ _
  simpa [Submodule.Quotient.mk_eq_zero] using hx

/-- Helper for Lemma 15.92.7: after quotienting by the tail-generated submodule, the head
generator acts surjectively. -/
lemma span_singleton_smul_top_eq_top_of_cons_smul_top_eq_top
    {M : ModuleCat A} (a : A) (rs : List A)
    (htop : Ideal.ofList (a :: rs) • (⊤ : Submodule A M) = ⊤) :
    Ideal.span ({a} : Set A) •
        (⊤ : Submodule A (M ⧸ Ideal.ofList rs • (⊤ : Submodule A M))) = ⊤ := by
  let S : Submodule A M := Ideal.span ({a} : Set A) • (⊤ : Submodule A M)
  let T : Submodule A M := Ideal.ofList rs • (⊤ : Submodule A M)
  have htopMap : (S ⊔ T).map T.mkQ = (⊤ : Submodule A (M ⧸ T)) := by
    -- Proof comment: map the global equality `(a, rs) M = M` to the quotient by `T`.
    have hmap := congrArg (Submodule.map T.mkQ) htop
    simpa [S, T, Ideal.ofList_cons, Submodule.sup_smul, Submodule.map_top,
      Submodule.range_mkQ] using hmap
  have htop' : S.map T.mkQ = (⊤ : Submodule A (M ⧸ T)) := by
    -- Proof comment: the tail-generated summand dies after quotienting by `T`.
    calc
      S.map T.mkQ = S.map T.mkQ ⊔ T.map T.mkQ := by rw [Submodule.mkQ_map_self, sup_bot_eq]
      _ = (S ⊔ T).map T.mkQ := by rw [Submodule.map_sup]
      _ = ⊤ := htopMap
  -- Proof comment: identify the image of `S = aM` in the quotient with `a(M / T)`.
  calc
    Ideal.span ({a} : Set A) • (⊤ : Submodule A (M ⧸ T)) = S.map T.mkQ := by
      simp [S, T, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    _ = ⊤ := htop'

/-- Helper for Lemma 15.92.7: the ideal generated by a list is the span of the corresponding
indexed range. -/
lemma ideal_ofList_eq_span_range_get (rs : List A) :
    Ideal.ofList rs = Ideal.span (Set.range rs.get) := by
  induction rs with
  | nil =>
      -- Proof comment: both sides are the zero ideal for the empty list.
      ext x
      simp [Ideal.ofList]
  | cons a rs ih =>
      have hRange : Set.range (List.get (a :: rs)) = insert a (Set.range rs.get) := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          cases i using Fin.cases with
          | zero =>
              simp
          | succ i =>
              right
              exact ⟨i, by simp⟩
        · intro hx
          rcases hx with rfl | hx
          · exact ⟨0, by simp⟩
          · rcases hx with ⟨i, hi⟩
            exact ⟨i.succ, by simpa using hi⟩
      -- Proof comment: adjoining the head on the list side matches inserting it in the range.
      rw [Ideal.ofList_cons, ih, hRange, Ideal.span_insert]

/-- Helper for Lemma 15.92.7: the list-generated zero criterion is proved by induction on the
ordered generator list. -/
lemma subsingleton_of_isDerivedCompleteWithRespectTo_of_ofList_smul_top_eq_top
    {M : ModuleCat.{u, u} A} :
    ∀ rs : List A,
      M.IsDerivedCompleteWithRespectTo (Ideal.ofList rs) →
        Ideal.ofList rs • (⊤ : Submodule A M) = ⊤ →
          Subsingleton M
  | [] => by
      intro hM htop
      have hbot : (⊥ : Submodule A M) = ⊤ := by
        -- Proof comment: `Ideal.ofList [] = 0`, so `0 ⋅ M = M`.
        simpa [Ideal.ofList] using htop
      refine ⟨?_⟩
      intro x y
      have hx : x = 0 := by
        have hxmem : x ∈ (⊤ : Submodule A M) := by simp
        have hxbot : x ∈ (⊥ : Submodule A M) := by simpa [hbot] using hxmem
        simpa using hxbot
      have hy : y = 0 := by
        have hymem : y ∈ (⊤ : Submodule A M) := by simp
        have hybot : y ∈ (⊥ : Submodule A M) := by simpa [hbot] using hymem
        simpa using hybot
      rw [hx, hy]
  | a :: rs => by
      intro hM htop
      let J : Ideal A := Ideal.ofList rs
      let Q : ModuleCat.{u, u} A := ModuleCat.of A (M ⧸ J • (⊤ : Submodule A M))
      have hQ : Q.IsDerivedCompleteWithRespectTo (Ideal.ofList (a :: rs)) := by
        -- Proof comment: quotienting by the tail-generated submodule preserves derived
        -- completeness.
        simpa [Q, J] using
          isDerivedCompleteWithRespectTo_quotient_smul_top
            (A := A) (I := Ideal.ofList (a :: rs)) (J := J) (M := M) hM
      have hQtop : Ideal.span ({a} : Set A) • (⊤ : Submodule A Q) = ⊤ := by
        -- Proof comment: modulo the tail generators, only the head generator survives.
        simpa [Q, J] using
          span_singleton_smul_top_eq_top_of_cons_smul_top_eq_top
            (A := A) (M := M) a rs htop
      have ha : a ∈ Ideal.ofList (a :: rs) := by
        rw [Ideal.ofList_cons]
        exact
          (show Ideal.span ({a} : Set A) ≤ Ideal.span ({a} : Set A) ⊔ Ideal.ofList rs from
            le_sup_left)
            (Ideal.subset_span (by simp : a ∈ ({a} : Set A)))
      have hQsub : Subsingleton Q :=
        subsingleton_of_isDerivedCompleteWithRespectTo_of_span_singleton_smul_top_eq_top
          (A := A) (I := Ideal.ofList (a :: rs)) (M := Q) a ha hQ hQtop
      have hJtop : J • (⊤ : Submodule A M) = ⊤ := by
        -- Proof comment: the quotient by `J M` is now zero, so `J M = M`.
        exact smul_top_eq_top_of_subsingleton_quotient (A := A) (J := J) (M := M) hQsub
      have hJ : M.IsDerivedCompleteWithRespectTo J := by
        -- Proof comment: every tail generator already lies in the full ideal `(a, rs)`.
        exact
          isDerivedCompleteWithRespectTo_of_le (A := A)
            (I := Ideal.ofList (a :: rs)) (J := J) hM <| by
              simpa [J, Ideal.ofList_cons] using
                (le_sup_right : J ≤ Ideal.span ({a} : Set A) ⊔ J)
      exact
        subsingleton_of_isDerivedCompleteWithRespectTo_of_ofList_smul_top_eq_top
          (M := M) rs hJ hJtop

-- Proof sketch: write `I = (f₁, …, f_r)` and choose the largest `i` such that
-- `M / (f₁, …, fᵢ) M` is nonzero. Lemma `15.92.6` shows this quotient is still derived complete.
-- Then `fᵢ₊₁` acts surjectively on it because `(M ⧸ I • ⊤)` is zero, producing the source
-- principal contradiction; the implementation packages this as induction on a generator list.
/-- Lemma 15.92.7, owner-level form: if `I` is finitely generated and a derived-complete module
`M` satisfies `IM = M`, then `M` is zero. -/
@[stacks 09B9]
lemma subsingleton_of_isDerivedCompleteWithRespectTo_of_smul_top_eq_top
    (hI : I.FG) (hM : M.IsDerivedCompleteWithRespectTo I) (hIM : IM = ⊤) :
    Subsingleton M := by
  classical
  obtain ⟨s, hsfin, hsI⟩ := Submodule.fg_def.mp hI
  let rs : List A := hsfin.toFinset.toList
  have hrs : Ideal.ofList rs = I := by
    -- Proof comment: replace the finitely generated ideal by an explicit list of generators.
    calc
      Ideal.ofList rs = Ideal.span (Set.range rs.get) :=
        ideal_ofList_eq_span_range_get (A := A) rs
      _ = Ideal.span (↑hsfin.toFinset : Set A) := by
          congr 1
          ext x
          simp [rs]
      _ = Ideal.span s := by
          congr 1
          ext x
          simpa using hsfin.mem_toFinset
      _ = I := hsI
  have hM' : M.IsDerivedCompleteWithRespectTo (Ideal.ofList rs) := by
    simpa [hrs] using hM
  have hIM' : Ideal.ofList rs • (⊤ : Submodule A M) = ⊤ := by
    simpa [hrs] using hIM
  -- Proof comment: the source proof is now the induction on the ordered generator list.
  exact
    subsingleton_of_isDerivedCompleteWithRespectTo_of_ofList_smul_top_eq_top
      (M := M) rs hM' hIM'

/-- Lemma 15.92.7: if `I` is finitely generated and an `A`-module `M` is derived complete with
respect to `I`, then the vanishing condition `M / I M = 0`, formalized by the quotient
`M ⧸ I • (⊤ : Submodule A M)` being subsingleton, forces `M` itself to be zero. -/
@[stacks 09B9]
lemma subsingleton_of_isDerivedCompleteWithRespectTo_of_subsingleton_quotient_smul_top
    (hI : I.FG) (hM : M.IsDerivedCompleteWithRespectTo I) (hquot : Subsingleton (M ⧸ IM)) :
    Subsingleton M := by
  apply subsingleton_of_isDerivedCompleteWithRespectTo_of_smul_top_eq_top hI hM
  -- Proof comment: a zero quotient means every element of `M` already lies in `I M`.
  refine Submodule.eq_top_iff'.2 ?_
  intro x
  have hx : Submodule.mkQ IM x = 0 := Subsingleton.elim _ _
  simpa [Submodule.Quotient.mk_eq_zero] using hx

end ModuleCat

end
