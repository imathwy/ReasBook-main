import Mathlib
import StacksProject_2024.Chap15.Definition_15_92_4
import StacksProject_2024.Chap15.Lemma_15_90_1
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

namespace ModuleCat

/-- Helper for Lemma 15.94.9: restricting scalars identifies the degree-zero localization object
with the degree-zero object of the restricted `A`-module. This inlines the tiny owner bridge from
Lemma `15.92.3` so the current item does not depend on its unavailable `.olean`. -/
noncomputable def restrictScalars_localizationAway_single_iso_for_principalPowerIntersection
    (f : A) :
    ((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u, u} (Localization.Away f)) (0 : ℤ)).obj
        (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f)))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u, u} A) (0 : ℤ)).obj
        (((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).obj
          (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f)))) := by
  -- Proof comment: normalize the restricted degree-zero object through `Q` and the standard
  -- single-complex compatibility isomorphisms.
  exact
    (((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).mapDerivedCategory).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
        (ModuleCat.{u, u} (Localization.Away f)) (0 : ℤ)).app
          (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f)))) ≪≫
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (ModuleCat.{u, u} (Localization.Away f)) (0 : ℤ)).obj
        (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f))) ≪≫
    DerivedCategory.Q.mapIso
      ((CategoryTheory.Functor.mapCochainComplexSingleFunctor
        (ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f)))
        (0 : ℤ)).app (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f)))

/-- Helper for Lemma 15.94.9: the degree-zero localization-away vanishing condition forces every
`A`-linear map `A_f → M` to be zero. This is the exact upstream bridge from Lemma `15.92.3`,
inlined locally because the canonical compiled owner module is unavailable in this run. -/
lemma subsingleton_linearMap_from_localizationAway_of_localizationAwayDerivedHomVanishingCondition_for_principalPowerIntersection
    (f : A) (M : ModuleCat.{u, u} A)
    (hvanish : CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f
      ((DerivedCategory.singleFunctor (ModuleCat.{u, u} A) (0 : ℤ)).obj M)) :
    Subsingleton (Localization.Away f →ₗ[A] M) := by
  -- Route correction: the source-faithful bridge is already known from Lemma `15.92.3`; after
  -- removing the missing import, only the local universe alignment between `singleFunctor`,
  -- `restrictScalars`, and `ModuleCat.of` remains.
  let singleA := DerivedCategory.singleFunctor (ModuleCat.{u, u} A) (0 : ℤ)
  let singleAway := DerivedCategory.singleFunctor (ModuleCat.{u, u} (Localization.Away f)) (0 : ℤ)
  let source : ModuleCat.{u, u} A :=
    ((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).obj
      (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f)))
  let sourceIso :
      ((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u, u} (Localization.Away f)) (0 : ℤ)).obj
          (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f)))) ≅
      singleA.obj source :=
    restrictScalars_localizationAway_single_iso_for_principalPowerIntersection (A := A) f
  have hDerived :
      Subsingleton ((singleA.obj source) ⟶ singleA.obj M) := by
    let E := singleAway.obj (ModuleCat.of.{u, u} (Localization.Away f) (Localization.Away f))
    have hE :
        Subsingleton
          (((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
            E) ⟶ singleA.obj M) :=
      hvanish E
    letI := hE
    -- Proof comment: `homCongr` transports the subsingleton hom-space across the source
    -- isomorphism, avoiding any further transport algebra in the main proof.
    let e :
        (((ModuleCat.restrictScalars.{u, u, u} (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
          E) ⟶ singleA.obj M) ≃ ((singleA.obj source) ⟶ singleA.obj M) :=
      sourceIso.homCongr (CategoryTheory.eqToIso rfl)
    exact e.symm.injective.subsingleton
  let hFaithful : singleA.Faithful := inferInstance
  have hSource : Subsingleton (source ⟶ M) := by
    letI := hDerived
    refine ⟨fun φ ψ ↦ ?_⟩
    -- Proof comment: faithfulness of `single₀` descends the derived-category subsingleton to
    -- honest morphisms out of the restricted source module.
    exact hFaithful.map_injective (Subsingleton.elim _ _)
  let eLinear : source ≃ₗ[A] Localization.Away f :=
    restrictScalars_selfLinearEquiv (A := A) (B := Localization.Away f)
  let eSource : source ≅ ModuleCat.of A (Localization.Away f) := eLinear.toModuleIso
  have hCanonical : Subsingleton (ModuleCat.of A (Localization.Away f) ⟶ M) := by
    letI := hSource
    -- Proof comment: transport the source-level subsingleton to the canonical localization owner.
    let e : (source ⟶ M) ≃ (ModuleCat.of A (Localization.Away f) ⟶ M) :=
      eSource.homCongr (CategoryTheory.eqToIso rfl)
    exact e.symm.injective.subsingleton
  letI := hCanonical
  refine ⟨fun φ ψ ↦ ?_⟩
  -- Proof comment: once the canonical source hom-set is subsingleton, the original linear maps
  -- are equal because `ModuleCat.ofHom` is injective on the underlying linear map.
  have hEqCanonical : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := Subsingleton.elim _ _
  simpa using congrArg ModuleCat.Hom.hom hEqCanonical

end ModuleCat

/- Domain-style sampling:
- primary domain: principal-adic completion kernels for derived-complete modules over a
  commutative ring;
- sampled owner-side declarations:
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `principalIdeal`,
  `principalPowerIdeal`,
  `AdicCompletion.of`;
- best owner abstraction: the source-facing principal-power intersection ideal
  `⨅ n : ℕ, principalPowerIdeal f n`, acting on the canonical completion-kernel owner
  `LinearMap.ker (AdicCompletion.of (principalIdeal f) M)`;
- primitive data: `f : A`, `M : ModuleCat A`, the derived-completeness hypothesis with respect to
  `(f)`, and the principal completion map;
- derived API: the ring specialization where the same ideal acts on its own completion kernel.

Layer triage:
- `source-facing`: the annihilation statement for the kernel of the principal completion map;
- `core/canonical`: `AdicCompletion.of`, `LinearMap.ker`, and
  `ModuleCat.IsDerivedCompleteWithRespectTo`;
- `bridge/view`: the ring specialization yielding the square-zero conclusion. -/

local notation "J(" f ")" => ⨅ n : ℕ, principalPowerIdeal f n

/-- Helper for Lemma 15.94.9: the degree-zero specialization of the localization-away vanishing
predicate from Definition `15.92.4`. -/
abbrev moduleLocalizationAwayTVanishing (M : ModuleCat.{u, u} A) (f : A) : Prop :=
  CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f
    ((DerivedCategory.singleFunctor (ModuleCat.{u, u} A) (0 : ℤ)).obj M)

-- Proof sketch: let `x` lie in the kernel of the principal-adic completion map and let
-- `g ∈ ⋂ n, (f)^n`. For each `n`, the kernel condition identifies `x` with an element divisible by
-- `f ^ n`, and since `g` lies in `(f)^n`, the products define a compatible sequence over the
-- localization `A_f`. Lemma `15.92.1` says every map from `A_f` into a derived-complete module
-- vanishes, so these products are all zero. Hence every element of `⋂ n, (f)^n` annihilates the
-- completion kernel.
/-- Helper for Lemma 15.94.9: an element of the completion kernel maps to zero in every principal
power quotient, hence it lies in every principal-power multiple of `⊤`. -/
lemma completionKernel_mem_principalPower_smul_top
    (f : A) (M : ModuleCat.{u, u} A) {x : M}
    (hx : x ∈ LinearMap.ker (AdicCompletion.of (principalIdeal f) M)) (n : ℕ) :
    x ∈ principalPowerIdeal f n • (⊤ : Submodule A M) := by
  -- Evaluate the kernel equation in the `n`th quotient of the adic completion.
  rw [LinearMap.mem_ker] at hx
  have hx_eval :
      AdicCompletion.eval (principalIdeal f) M n
          (AdicCompletion.of (principalIdeal f) M x) = 0 := by
    simpa using congrArg (AdicCompletion.eval (principalIdeal f) M n) hx
  -- Rewrite the vanishing quotient class as membership in `(f)^n M`.
  rw [AdicCompletion.eval_of] at hx_eval
  simpa [principalPowerIdeal] using hx_eval

/-- Helper for Lemma 15.94.9: if `g ∈ (f)^n`, then `g • u` depends only on the common value of
`(f^n) • u`. -/
lemma principal_power_smul_desc_well_defined
    (f : A) {M : Type*} [AddCommGroup M] [Module A M]
    {g : A} {x : M} {n : ℕ} {u v : M}
    (hg : g ∈ principalPowerIdeal f n)
    (hxu : x = (f ^ n) • u)
    (hxv : x = (f ^ n) • v) :
    g • u = g • v := by
  -- Express `g` as a multiple of `f^n`.
  rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hg
  rcases hg with ⟨a, rfl⟩
  -- The two chosen divisibility witnesses for `x` then give the same image after multiplying by
  -- `g`.
  have huv : (f ^ n) • u = (f ^ n) • v := by
    rw [← hxu, hxv]
  simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun m : M ↦ a • m) huv

/-- Helper for Lemma 15.94.9: multiplication by `a` has image exactly `aM`. -/
lemma range_lsmul_eq_principalIdeal_smul_top
    {M : Type*} [AddCommGroup M] [Module A M] (a : A) :
    LinearMap.range (LinearMap.lsmul A M a) =
      principalIdeal a • (⊤ : Submodule A M) := by
  ext x
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
    -- A visible `a`-multiple lands in `aM` by construction.
    simpa [principalIdeal, LinearMap.lsmul_apply] using
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a)
        (show y ∈ (⊤ : Submodule A M) by simp))
  · intro hx
    -- Conversely, every generator of `aM` is hit by multiplication by `a`.
    have hle : principalIdeal a • (⊤ : Submodule A M) ≤ LinearMap.range (LinearMap.lsmul A M a) := by
      rw [Submodule.smul_le]
      intro r hr y hy
      rcases Ideal.mem_span_singleton.mp hr with ⟨b, rfl⟩
      refine LinearMap.mem_range.mpr ⟨b • y, ?_⟩
      simp [LinearMap.lsmul_apply, smul_smul, mul_comm]
    exact hle hx

/-- Helper for Lemma 15.94.9: membership in `fM` gives an explicit `f`-divisibility witness. -/
lemma exists_eq_smul_of_mem_principalIdeal_smul_top
    {M : Type*} [AddCommGroup M] [Module A M] (f : A) {x : M}
    (hx : x ∈ principalIdeal f • (⊤ : Submodule A M)) :
    ∃ y, x = f • y := by
  -- Rewrite `fM` as the range of multiplication by `f`.
  have hx' : x ∈ LinearMap.range (LinearMap.lsmul A M f) := by
    simpa [range_lsmul_eq_principalIdeal_smul_top (A := A) (M := M) f] using hx
  rcases LinearMap.mem_range.mp hx' with ⟨y, hy⟩
  exact ⟨y, by simpa [LinearMap.lsmul_apply] using hy.symm⟩

/-- Helper for Lemma 15.94.9: membership in `(f)^n M` gives an explicit `f^n`-divisibility
witness. -/
lemma exists_eq_smul_of_mem_principalPower_smul_top
    {M : Type*} [AddCommGroup M] [Module A M] (f : A) {n : ℕ} {x : M}
    (hx : x ∈ principalPowerIdeal f n • (⊤ : Submodule A M)) :
    ∃ y, x = (f ^ n) • y := by
  -- Identify `(f)^n` with the principal ideal generated by `f^n`.
  have hx' : x ∈ principalIdeal (f ^ n) • (⊤ : Submodule A M) := by
    simpa [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] using hx
  exact exists_eq_smul_of_mem_principalIdeal_smul_top (A := A) (M := M) (f := f ^ n) hx'

/-- Helper for Lemma 15.94.9: a principal-recursive sequence vanishes at its initial term once
every map `A_f → M` vanishes. -/
lemma principal_recursive_sequence_zero_of_moduleLocalizationAwayTVanishing
    (f : A) (M : ModuleCat.{u, u} A)
    (hvanish : moduleLocalizationAwayTVanishing M f)
    (y : ℕ → M) (hy : ∀ n : ℕ, y n = f • y (n + 1)) :
    y 0 = 0 := by
  -- Route correction: the main proof now delegates the textbook `A_f → M` construction and its
  -- vanishing consequence to this single helper, keeping the outer argument source-faithful and
  -- flat.
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
      -- Multiplication by `f` on recursive sequences is inverted by shifting the sequence.
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
    -- Every power of `f` is therefore a unit on the recursive-sequence object.
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
    -- Compare the denominator-`1` generator through the canonical localization equivalence.
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    simpa using
      (IsLocalizedModule.linearEquiv_apply (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) A)
        (Algebra.linearMap A (Localization.Away f)) 1).symm
  have hφ_apply_one : φ (algebraMap A (Localization.Away f) 1) = y 0 := by
    -- Evaluate the localized recursive-sequence map at `1`, where the lift recovers the initial
    -- recursive sequence `y`.
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
    ModuleCat.subsingleton_linearMap_from_localizationAway_of_localizationAwayDerivedHomVanishingCondition_for_principalPowerIntersection
      (A := A) f M hvanish
  have hφ : φ = 0 := Subsingleton.elim _ _
  -- Since every `A_f → M` map is zero, evaluating our source-faithful map at `1` forces `y₀ = 0`.
  have happly :
      φ (algebraMap A (Localization.Away f) 1) = 0 := by
    simpa using congrArg
      (fun ψ : Localization.Away f →ₗ[A] M ↦ ψ (algebraMap A (Localization.Away f) 1)) hφ
  -- Proof comment: rewrite the evaluation at `1` to the initial recursive term and conclude.
  rw [hφ_apply_one] at happly
  exact happly

/-- Helper for Lemma 15.94.9: for the ring module, the kernel of the principal completion map is
exactly the intersection of the principal powers. -/
lemma completionKernel_eq_principalPowerIntersection
    (f : A) :
    LinearMap.ker (AdicCompletion.of (principalIdeal f) (ModuleCat.of A A)) = (J(f) : Ideal A) := by
  ext x
  constructor
  · intro hx
    -- A kernel element is divisible by every power of `f`.
    rw [Submodule.mem_iInf]
    intro n
    simpa using
      completionKernel_mem_principalPower_smul_top
        (f := f) (M := ModuleCat.of A A) hx n
  · intro hx
    -- If every principal-power quotient class vanishes, then the completion element is zero.
    rw [LinearMap.mem_ker]
    apply AdicCompletion.ext
    intro n
    rw [← AdicCompletion.eval_apply, AdicCompletion.eval_of]
    have hx_n : x ∈ (principalIdeal f ^ n • ⊤ : Submodule A A) := by
      simpa [principalPowerIdeal] using
        (Submodule.mem_iInf (p := fun n : ℕ ↦ (principalPowerIdeal f n : Ideal A))).1 hx n
    exact (Submodule.Quotient.mk_eq_zero (p := (principalIdeal f ^ n • ⊤ : Submodule A A))
      (x := x)).2 hx_n

/-- Helper for Lemma 15.94.9: an element of `J(f)` annihilates each completion-kernel element of a
derived-complete module. -/
lemma principalPowerIntersection_smul_mem_completionKernel_eq_zero
    (f : A) (M : ModuleCat.{u, u} A)
    (hM : M.IsDerivedCompleteWithRespectTo (principalIdeal f))
    {g : A} (hg : g ∈ J(f)) {x : M}
    (hx : x ∈ LinearMap.ker (AdicCompletion.of (principalIdeal f) M)) :
    g • x = 0 := by
  classical
  have hvanish : moduleLocalizationAwayTVanishing M f := by
    -- Specialize derived completeness to the generator `f ∈ (f)`.
    simpa [moduleLocalizationAwayTVanishing] using
      hM f (by simpa [principalIdeal] using (Ideal.mem_span_singleton_self f))
  have hxpow_exists : ∀ n : ℕ, ∃ u : M, x = (f ^ (n + 1)) • u := by
    intro n
    -- Each completion-kernel stage provides one divisibility witness for `x`.
    exact
      exists_eq_smul_of_mem_principalPower_smul_top (A := A) (M := M) (f := f)
        (completionKernel_mem_principalPower_smul_top (f := f) (M := M) hx (n + 1))
  choose xpow hxpow using hxpow_exists
  let y : ℕ → M := fun n ↦ g • xpow n
  have hy : ∀ n : ℕ, y n = f • y (n + 1) := by
    intro n
    have hgpow : g ∈ principalPowerIdeal f (n + 1) := by
      exact
        (Submodule.mem_iInf
          (p := fun m : ℕ ↦ (principalPowerIdeal f m : Ideal A))).1 hg (n + 1)
    have hnext : x = (f ^ (n + 1)) • (f • xpow (n + 1)) := by
      -- The next-stage witness also witnesses divisibility by `f^(n+1)` after one extra factor of
      -- `f`, so the descended `g`-multiple is independent of the chosen witness.
      calc
        x = (f ^ (n + 2)) • xpow (n + 1) := hxpow (n + 1)
        _ = (f ^ (n + 1)) • (f • xpow (n + 1)) := by
            simp [pow_succ, smul_smul, mul_assoc]
    have hdesc :
        g • xpow n = g • (f • xpow (n + 1)) := by
      exact
        principal_power_smul_desc_well_defined
          (f := f) (g := g) (x := x) (n := n + 1) hgpow
          (hxpow n) hnext
    calc
      y n = g • (f • xpow (n + 1)) := by simpa [y] using hdesc
      _ = f • y (n + 1) := by
          simp [y, smul_smul, mul_comm]
  have hy0 :
      y 0 = 0 :=
    principal_recursive_sequence_zero_of_moduleLocalizationAwayTVanishing
      (A := A) (f := f) (M := M) hvanish y hy
  -- The first divisibility witness rewrites `g • x` as `f • y₀`, and the recursive-sequence
  -- vanishing kills `y₀`.
  calc
    g • x = g • ((f ^ (0 + 1)) • xpow 0) := by
      simpa using congrArg (fun z : M ↦ g • z) (hxpow 0)
    _ = g • (f • xpow 0) := by simp
    _ = f • y 0 := by
        simp [y, smul_smul, mul_comm]
    _ = 0 := by simp [hy0]

/-- Lemma 15.94.9: if an `A`-module `M` is derived complete with respect to the principal ideal
`(f)`, then the intersection `J = ⋂ n, (f)^n` annihilates the kernel of the completion map
`M → lim_n M / (f)^n M`, modeled in Lean as `AdicCompletion.of (principalIdeal f) M`. -/
theorem principalPowerIntersection_smul_completionKernel_eq_bot_of_isDerivedComplete
    (f : A) (M : ModuleCat.{u, u} A)
    (hM : M.IsDerivedCompleteWithRespectTo (principalIdeal f)) :
    J(f) • LinearMap.ker (AdicCompletion.of (principalIdeal f) M) = ⊥ := by
  -- Reduce the submodule statement to pointwise annihilation by elements of `J(f)`.
  rw [eq_bot_iff]
  exact Submodule.smul_le.2 fun g hg x hx ↦ by
    -- The source-faithful localization argument kills each scalar action separately.
    simpa using
      principalPowerIntersection_smul_mem_completionKernel_eq_zero
        (f := f) (M := M) hM hg hx

-- Proof sketch: apply the previous theorem to the `A`-module `A` itself. The kernel of the
-- completion map `A → lim_n A / (f)^n` is exactly `⋂ n, (f)^n`, so the annihilation statement
-- becomes `J * J = 0`, i.e. `J ^ 2 = ⊥`.
/-- If the ring `A`, viewed as an `A`-module, is derived complete with respect to `(f)`, then the
intersection `⋂ n, (f)^n` is an ideal of square zero. -/
theorem principalPowerIntersection_sq_eq_bot_of_ring_isDerivedComplete
    (f : A)
    (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo (principalIdeal f)) :
    J(f) ^ 2 = ⊥ := by
  -- Specialize the module statement to the ring module.
  have hsmul :
      J(f) • LinearMap.ker (AdicCompletion.of (principalIdeal f) (ModuleCat.of A A)) = ⊥ :=
    principalPowerIntersection_smul_completionKernel_eq_bot_of_isDerivedComplete
      (f := f) (M := ModuleCat.of A A) hA
  -- Identify the completion kernel with the principal-power intersection.
  rw [completionKernel_eq_principalPowerIntersection (f := f)] at hsmul
  -- For the ring module, this smul is ideal multiplication, so we get `J(f)^2 = 0`.
  simpa [pow_two] using hsmul

end
