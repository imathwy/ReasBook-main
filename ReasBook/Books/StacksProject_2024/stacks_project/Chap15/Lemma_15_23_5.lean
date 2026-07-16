import StacksProject_2024.stacks_project.Chap15.Lemma_15_23_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

/-
Domain-style sampling:
- primary domain: duality and reflexivity of finite modules over a commutative domain;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.Dual.eval`,
  `Module.evalEquiv`,
  `Module.IsReflexive.to_isTorsionFree`,
  `Module.Finite.of_injective`,
  `Module.Finite.range`;
- best owner abstraction: the canonical owner is the reflexivity class `Module.IsReflexive`,
  with the evaluation map `Module.Dual.eval` supplying the intrinsic comparison to the double
  dual; finiteness of the source and of the quotient object is derived API from the ambient finite
  middle term together with the exact pair;
- source/core/bridge triage:
  - `source-facing`: this closure lemma for reflexive modules under kernels with torsion-free
    quotient;
  - `core/canonical`: `Module.IsReflexive`, `Module.Dual.eval`, `Module.IsTorsionFree`,
    `Module.Finite`;
  - `bridge/view`: the quotient seen here is the canonical submodule `LinearMap.range g`, not an
    auxiliary wrapper around the ambient codomain.

Primitive data are the exact pair `f, g`, the injectivity of `f`, the reflexivity of the middle
term, and the torsion-freeness of the actual quotient object `LinearMap.range g`. The finiteness
of `M` is derived from `Module.Finite.of_injective hf`, and the finiteness of `LinearMap.range g`
is derived from the canonical range instance on linear maps out of finite modules. Requiring the
ambient codomain `M''` or the source `M` themselves to be finite as primitive public assumptions is
therefore redundant.
-/

section

open Function Module
open scoped nonZeroDivisors

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} {M' : Type w} {M'' : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M'] [Module R M'] [Module.Finite R M']
variable [AddCommGroup M''] [Module R M'']

/-- Helper for Lemma 15.23.5: a finitely generated submodule of the fraction field has one common
nonzero denominator. -/
private theorem fractionRing_finite_submodule_has_common_denominator
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (I : Submodule R (FractionRing R)) (hI : I.FG) :
    ∃ c : R, c ≠ 0 ∧ ∀ z ∈ I,
      c • z ∈ LinearMap.range (Algebra.linearMap R (FractionRing R)) := by
  classical
  let aMap : R →ₗ[R] FractionRing R := Algebra.linearMap R (FractionRing R)
  let num : FractionRing R → R := fun z ↦ (IsLocalization.exists_mk'_eq (R⁰) z).choose
  let den : FractionRing R → R⁰ := fun z ↦
    ((IsLocalization.exists_mk'_eq (R⁰) z).choose_spec).choose
  have hfrac : ∀ z : FractionRing R, IsLocalization.mk' (FractionRing R) (num z) (den z) = z := by
    intro z
    exact ((IsLocalization.exists_mk'_eq (R⁰) z).choose_spec).choose_spec
  obtain ⟨t, ht⟩ := hI
  let c : R := ∏ z ∈ t, (den z : R)
  have hc : c ≠ 0 := by
    -- Every chosen denominator is nonzero, so their finite product is nonzero.
    refine Finset.prod_ne_zero_iff.mpr fun z hz ↦ ?_
    exact mem_nonZeroDivisors_iff_ne_zero.mp (den z).2
  let J : Submodule R (FractionRing R) :=
    { carrier := {z | c • z ∈ LinearMap.range aMap}
      zero_mem' := by
        refine ⟨0, ?_⟩
        simp
      add_mem' := by
        intro z w hz hw
        simpa [smul_add] using (LinearMap.range aMap).add_mem hz hw
      smul_mem' := by
        intro r z hz
        simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
          (LinearMap.range aMap).smul_mem r hz }
  have hgen : ∀ z ∈ (↑t : Set (FractionRing R)), z ∈ J := by
    intro z hz
    change c • z ∈ LinearMap.range aMap
    let d : R := ∏ w ∈ t.erase z, (den w : R)
    have hden :
        (den z : R) • z = aMap (num z) := by
      -- Rewrite the chosen fraction as a numerator divided by its denominator.
      have hz' :
          aMap (num z) = z * aMap (den z : R) := by
        exact
          (IsLocalization.mk'_eq_iff_eq_mul (M := R⁰) (S := FractionRing R)
            (x := num z) (y := den z) (z := z)).mp (hfrac z)
      simpa [aMap, Algebra.smul_def, mul_comm] using hz'.symm
    have hc' : d * (den z : R) = c := by
      simpa [c, d] using
        (Finset.prod_erase_mul (s := t) (f := fun w ↦ (den w : R)) (a := z) (h := hz))
    refine ⟨d * num z, ?_⟩
    calc
      aMap (d * num z) = d • aMap (num z) := by
        simp [aMap, Algebra.smul_def]
      _ = d • ((den z : R) • z) := by rw [hden]
      _ = (d * (den z : R)) • z := by rw [smul_smul]
      _ = c • z := by rw [hc']
  have hI_le : I ≤ J := by
    -- The generators belong to the denominator-cleared submodule, so the whole submodule does.
    rw [← ht]
    exact Submodule.span_le.mpr hgen
  refine ⟨c, hc, ?_⟩
  intro z hz
  exact hI_le hz

/-- Helper for Lemma 15.23.5: after multiplying by one nonzero scalar, a fraction-field-valued
linear form on a finite module descends to an `R`-valued linear form. -/
private theorem exists_smul_eq_algebraMap_comp_fractionRing
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (ℓ : N →ₗ[R] FractionRing R) :
    ∃ c : R, c ≠ 0 ∧ ∃ ℓ0 : N →ₗ[R] R,
      (Algebra.linearMap R (FractionRing R)).comp ℓ0 = c • ℓ := by
  let I : Submodule R (FractionRing R) := LinearMap.range ℓ
  have hI : I.FG := by
    -- The image of a finite module is finitely generated.
    change (LinearMap.range ℓ).FG
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map ℓ Module.Finite.fg_top
  obtain ⟨c, hc, hclear⟩ :=
    fractionRing_finite_submodule_has_common_denominator (R := R) (N := N) I hI
  let aMap : R →ₗ[R] FractionRing R := Algebra.linearMap R (FractionRing R)
  have haMap_inj : Function.Injective aMap := IsFractionRing.injective R (FractionRing R)
  let e : R ≃ₗ[R] LinearMap.range aMap := LinearEquiv.ofInjective aMap haMap_inj
  have hcod : ∀ x : N, (c • ℓ) x ∈ LinearMap.range aMap := by
    intro x
    exact hclear (ℓ x) ⟨x, rfl⟩
  let ℓrange : N →ₗ[R] LinearMap.range aMap :=
    LinearMap.codRestrict (LinearMap.range aMap) (c • ℓ) hcod
  let ℓ0 : N →ₗ[R] R := e.symm.toLinearMap.comp ℓrange
  refine ⟨c, hc, ℓ0, ?_⟩
  -- Evaluate inside the range of the algebra map and then forget the subtype.
  ext x
  change ((e (ℓ0 x) : LinearMap.range aMap) : FractionRing R) = (ℓrange x : FractionRing R)
  exact congrArg Subtype.val (e.apply_symm_apply (ℓrange x))

/-- Helper for Lemma 15.23.5: localizing `Dual R M` gives fraction-field-valued functionals on
the generic fiber. -/
private noncomputable def localized_dual_raw_map
    {N : Type*} [AddCommGroup N] [Module R N] :
    Dual R N →ₗ[R] (LocalizedModule R⁰ N →ₗ[R] FractionRing R) :=
  IsLocalizedModule.map R⁰ (LocalizedModule.mkLinearMap R⁰ N)
    (Algebra.linearMap R (FractionRing R))

/-- Helper for Lemma 15.23.5: on numerator generators, the raw localized dual map is ordinary
scalar extension of the original functional. -/
private theorem localized_dual_raw_map_comp
    {N : Type*} [AddCommGroup N] [Module R N] (φ : Dual R N) :
    (localized_dual_raw_map (R := R) (N := N) φ).comp (LocalizedModule.mkLinearMap R⁰ N) =
      (Algebra.linearMap R (FractionRing R)).comp φ := by
  -- This is exactly the defining localization square.
  simpa [localized_dual_raw_map] using
    (IsLocalizedModule.map_comp (S := R⁰)
      (f := LocalizedModule.mkLinearMap R⁰ N)
      (g := Algebra.linearMap R (FractionRing R))
      (h := φ))

/-- Helper for Lemma 15.23.5: the raw map from `Dual R M` to fraction-field-valued functionals on
the generic fiber is itself a localization map. -/
private theorem localized_dual_raw_map_isLocalizedModule
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] :
    IsLocalizedModule R⁰ (localized_dual_raw_map (R := R) (N := N)) := by
  classical
  letI : Module (FractionRing R) (LocalizedModule R⁰ N →ₗ[R] FractionRing R) := inferInstance
  letI : IsScalarTower R (FractionRing R) (LocalizedModule R⁰ N →ₗ[R] FractionRing R) :=
    inferInstance
  refine
    { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro s
    letI :
        IsLocalizedModule R⁰
          (.id (R := R) (M := LocalizedModule R⁰ N →ₗ[R] FractionRing R)) :=
      isLocalizedModule_id
        (S := R⁰) (M := LocalizedModule R⁰ N →ₗ[R] FractionRing R) (R' := FractionRing R)
    -- Multiplication by a nonzero denominator is invertible on this vector space.
    simpa using
      (IsLocalizedModule.map_units
        (S := R⁰)
        (f := (.id (R := R) (M := LocalizedModule R⁰ N →ₗ[R] FractionRing R))) s)
  · intro ψ
    obtain ⟨c, hc, ℓ₀, hℓ₀⟩ :=
      exists_smul_eq_algebraMap_comp_fractionRing (R := R) (N := N)
        (ψ.comp (LocalizedModule.mkLinearMap R⁰ N))
    refine ⟨⟨ℓ₀, ⟨c, mem_nonZeroDivisors_iff_ne_zero.mpr hc⟩⟩, ?_⟩
    -- Compare the two candidate localized functionals after precomposing with the numerator map.
    apply IsLocalizedModule.linearMap_ext (S := R⁰)
      (LocalizedModule.mkLinearMap R⁰ N)
      (Algebra.linearMap R (FractionRing R))
    ext n
    calc
      ((((⟨c, mem_nonZeroDivisors_iff_ne_zero.mpr hc⟩ : R⁰) • ψ).comp
          (LocalizedModule.mkLinearMap R⁰ N)) n)
          = (((c : R) • (ψ.comp (LocalizedModule.mkLinearMap R⁰ N))) n) := by
              simp [LinearMap.comp_apply]
      _ = (((Algebra.linearMap R (FractionRing R)).comp ℓ₀) n) := by
            simpa [LinearMap.comp_apply] using
              (congrArg (fun f : N →ₗ[R] FractionRing R => f n) hℓ₀).symm
      _ = (((localized_dual_raw_map (R := R) (N := N) ℓ₀).comp
            (LocalizedModule.mkLinearMap R⁰ N)) n) := by
            rw [localized_dual_raw_map_comp]
  · intro φ₁ φ₂ h
    have hcomp :
        (localized_dual_raw_map (R := R) (N := N) φ₁).comp (LocalizedModule.mkLinearMap R⁰ N) =
          (localized_dual_raw_map (R := R) (N := N) φ₂).comp
            (LocalizedModule.mkLinearMap R⁰ N) := by
      simpa using congrArg
        (fun ψ : LocalizedModule R⁰ N →ₗ[R] FractionRing R =>
          ψ.comp (LocalizedModule.mkLinearMap R⁰ N)) h
    have hφ : φ₁ = φ₂ := by
      ext n
      have hn :
          algebraMap R (FractionRing R) (φ₁ n) = algebraMap R (FractionRing R) (φ₂ n) := by
        simpa [localized_dual_raw_map_comp, LinearMap.comp_apply] using
          congrArg (fun f : N →ₗ[R] FractionRing R => f n) hcomp
      exact (IsFractionRing.injective R (FractionRing R)) hn
    exact ⟨1, by simpa [hφ]⟩

/-- Helper for Lemma 15.23.5: after upgrading the codomain to genuine fraction-field duals, the
dual localization comparison is still a localization map. -/
private noncomputable def dual_localization_map
    {N : Type*} [AddCommGroup N] [Module R N] :
    Dual R N →ₗ[R] Dual (FractionRing R) (LocalizedModule R⁰ N) :=
  (((LinearMap.extendScalarsOfIsLocalizationEquiv (R⁰) (FractionRing R)
      (M := LocalizedModule R⁰ N) (N := FractionRing R)).restrictScalars R).toLinearMap) ∘ₗ
    localized_dual_raw_map (R := R) (N := N)

/-- Helper for Lemma 15.23.5: the genuine dual localization comparison inherits the localization
universal property from the raw localized dual map. -/
private theorem dual_localization_map_isLocalizedModule
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] :
    IsLocalizedModule R⁰ (dual_localization_map (R := R) (N := N)) := by
  let e : (LocalizedModule R⁰ N →ₗ[R] FractionRing R) ≃ₗ[R]
      Dual (FractionRing R) (LocalizedModule R⁰ N) :=
    (LinearMap.extendScalarsOfIsLocalizationEquiv (R⁰) (FractionRing R)
      (M := LocalizedModule R⁰ N) (N := FractionRing R)).restrictScalars R
  letI : IsLocalizedModule R⁰ (localized_dual_raw_map (R := R) (N := N)) :=
    localized_dual_raw_map_isLocalizedModule (R := R) (N := N)
  -- The codomain change is a linear equivalence, so the localization structure transports.
  simpa [dual_localization_map, e] using
    (show IsLocalizedModule R⁰ (e.toLinearMap ∘ₗ localized_dual_raw_map (R := R) (N := N))
      from inferInstance)

/-- Helper for Lemma 15.23.5: the localization of the dual identifies with the dual of the
generic fiber. -/
private noncomputable abbrev dual_localization_linearEquiv
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] :
    LocalizedModule R⁰ (Dual R N) ≃ₗ[R] Dual (FractionRing R) (LocalizedModule R⁰ N) :=
  letI : IsLocalizedModule R⁰ (dual_localization_map (R := R) (N := N)) :=
    dual_localization_map_isLocalizedModule (R := R) (N := N)
  IsLocalizedModule.linearEquiv R⁰
    (LocalizedModule.mkLinearMap R⁰ (Dual R N))
    (dual_localization_map (R := R) (N := N))

/-- Helper for Lemma 15.23.5: if a localized submodule is all of the generic fiber, then the
localized quotient is trivial. -/
private theorem localized_quotient_subsingleton_of_localized_eq_top
    {N : Type*} [AddCommGroup N] [Module R N]
    (P : Submodule R N) (hP : Submodule.localized (p := R⁰) P = ⊤) :
    Subsingleton (LocalizedModule R⁰ (N ⧸ P)) := by
  let e :
      (LocalizedModule R⁰ N ⧸ Submodule.localized (p := R⁰) P) ≃ₗ[FractionRing R]
        LocalizedModule R⁰ (N ⧸ P) :=
    localizedQuotientEquiv R⁰ P
  have hquot :
      Subsingleton (LocalizedModule R⁰ N ⧸ Submodule.localized (p := R⁰) P) := by
    rw [hP]
    infer_instance
  -- Once the localized submodule is everything, the localized quotient is the quotient by `⊤`.
  letI : Subsingleton (LocalizedModule R⁰ N ⧸ Submodule.localized (p := R⁰) P) := hquot
  exact e.symm.toEquiv.subsingleton

/-- Helper for Lemma 15.23.5: dual localization intertwines restriction along `f` with
restriction along the localized map. -/
private theorem dual_localization_lcomp_transport
    [Module.Finite R M] {f : M →ₗ[R] M'} :
    let β₀ : Dual R M' →ₗ[R] Dual R M := LinearMap.lcomp R R f
    let eM : LocalizedModule R⁰ (Dual R M) ≃ₗ[R] Dual (FractionRing R) (LocalizedModule R⁰ M) :=
      dual_localization_linearEquiv (R := R) (N := M)
    let eM' : LocalizedModule R⁰ (Dual R M') ≃ₗ[R] Dual (FractionRing R) (LocalizedModule R⁰ M') :=
      dual_localization_linearEquiv (R := R) (N := M')
    let fK : LocalizedModule R⁰ M →ₗ[FractionRing R] LocalizedModule R⁰ M' :=
      LocalizedModule.map R⁰ f
    eM.toLinearMap.comp (LinearMap.restrictScalars R (LocalizedModule.map R⁰ β₀)) =
      ((LinearMap.lcomp (FractionRing R) (FractionRing R) fK).restrictScalars R).comp
        eM'.toLinearMap := by
  -- TODO: prove the localization transport identity on numerator generators and extend by
  -- `IsLocalizedModule.linearMap_ext`. The current blocker is the same generic-fiber comparison
  -- needed below to turn localized surjectivity of the fraction-field dual map back into the
  -- localized image computation for `range (lcomp f)`.
  sorry

/-- Helper for Lemma 15.23.5: the cokernel of the restriction map on duals has zero generic
fiber. -/
private theorem dual_cokernel_localized_subsingleton
    [Module.Finite R M] {f : M →ₗ[R] M'} (hf : Injective f) :
    let β₀ : Dual R M' →ₗ[R] Dual R M := LinearMap.lcomp R R f
    let C : Submodule R (Dual R M) := LinearMap.range β₀
    let Q : Type max u v := Dual R M ⧸ C
    Subsingleton (LocalizedModule R⁰ Q) := by
  -- TODO: after the transport lemma above is available, use a left inverse to the localized map
  -- `LocalizedModule.map R⁰ f` to make the localized dual restriction map surjective, identify its
  -- range with `Submodule.localized C`, and conclude that the localized quotient is trivial.
  sorry

/-- Helper for Lemma 15.23.5: the cokernel of the restriction map on duals is torsion. -/
private theorem dual_cokernel_isTorsion
    [Module.Finite R M] {f : M →ₗ[R] M'} (hf : Injective f) :
    let β₀ : Dual R M' →ₗ[R] Dual R M := LinearMap.lcomp R R f
    let C : Submodule R (Dual R M) := LinearMap.range β₀
    let Q : Type max u v := Dual R M ⧸ C
    IsTorsion R Q := by
  -- TODO: once `dual_cokernel_localized_subsingleton` is proved, rewrite by
  -- `LocalizedModule.subsingleton_iff` to extract the required denominator-killing witness.
  sorry

/-- Helper for Lemma 15.23.5: the dual of a torsion module over a domain is trivial. -/
private theorem dual_of_torsion_subsingleton
    {T : Type*} [AddCommGroup T] [Module R T] (hTors : IsTorsion R T) :
    Subsingleton (Dual R T) := by
  -- TODO: evaluate a functional on a torsion element and cancel the nonzero annihilator in the
  -- torsion-free module `R`.
  sorry

/-- Helper for Lemma 15.23.5: replacing `g` by its canonical map to `range g` preserves the
exactness of the sequence. -/
private theorem exact_rangeRestrict
    {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Function.Exact f g) :
    Function.Exact f g.rangeRestrict := by
  -- The only change is the codomain, and `g.rangeRestrict` has the same kernel as `g`.
  rw [LinearMap.exact_iff] at hfg ⊢
  simpa using hfg

/-- Helper for Lemma 15.23.5: dualizing the exact sequence
`0 → M → M' → range g → 0` gives a short exact row ending in the range of `lcomp f`. -/
private theorem dual_range_sequence_short_exact
    {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Function.Exact f g) :
    let Q := LinearMap.range g
    let π : M' →ₗ[R] Q := g.rangeRestrict
    let α : Dual R Q →ₗ[R] Dual R M' := LinearMap.lcomp R R π
    let β₀ : Dual R M' →ₗ[R] Dual R M := LinearMap.lcomp R R f
    let β : Dual R M' →ₗ[R] LinearMap.range β₀ := β₀.rangeRestrict
    Function.Exact α β ∧ Function.Injective α ∧ Function.Surjective β := by
  let Q := LinearMap.range g
  let π : M' →ₗ[R] Q := g.rangeRestrict
  let α : Dual R Q →ₗ[R] Dual R M' := LinearMap.lcomp R R π
  let β₀ : Dual R M' →ₗ[R] Dual R M := LinearMap.lcomp R R f
  let β : Dual R M' →ₗ[R] LinearMap.range β₀ := β₀.rangeRestrict
  have hExactπ : Function.Exact f π := exact_rangeRestrict (R := R) hfg
  have hπsurj : Function.Surjective π := g.surjective_rangeRestrict
  have hExactβ₀ : Function.Exact α β₀ :=
    LinearMap.exact_lcomp_of_exact_of_surjective R hExactπ hπsurj
  have hExactβ : Function.Exact α β := by
    intro φ
    constructor
    · intro hβ
      -- Forgetting the range wrapper reduces the vanishing condition to the usual dual map.
      have hβ₀ : β₀ φ = 0 := by
        ext m
        simpa [β] using LinearMap.congr_fun (congrArg Subtype.val hβ) m
      exact (hExactβ₀ φ).1 hβ₀
    · rintro ⟨ψ, rfl⟩
      -- Exactness of the original sequence gives `π (f m) = 0`, so the range-restricted map
      -- vanishes on the image of `α`.
      apply Subtype.ext
      ext m
      have hcomp : π (f m) = 0 := by
        exact (hExactπ (f m)).2 ⟨m, rfl⟩
      simp [α, β, β₀, hcomp]
  have hInjα : Function.Injective α :=
    LinearMap.lcomp_injective_of_surjective π hπsurj
  have hSurjβ : Function.Surjective β := β₀.surjective_rangeRestrict
  exact ⟨hExactβ, hInjα, hSurjβ⟩

/-- Helper for Lemma 15.23.5: evaluation on extendable functionals identifies `M` with the dual of
`range (lcomp f)`. -/
private theorem restricted_dual_eval_bijective
    {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Function.Exact f g) (hf : Injective f)
    [IsReflexive R M'] [IsTorsionFree R (LinearMap.range g)] :
    let C := LinearMap.range (LinearMap.lcomp R R f)
    let ρ : Dual R (Dual R M) →ₗ[R] Dual R C := LinearMap.lcomp R R C.subtype
    Function.Bijective (ρ.comp (Module.Dual.eval R M)) := by
  let Q := LinearMap.range g
  let π : M' →ₗ[R] Q := g.rangeRestrict
  let α : Dual R Q →ₗ[R] Dual R M' := LinearMap.lcomp R R π
  let β₀ : Dual R M' →ₗ[R] Dual R M := LinearMap.lcomp R R f
  let C := LinearMap.range β₀
  let β : Dual R M' →ₗ[R] C := β₀.rangeRestrict
  let ρ : Dual R (Dual R M) →ₗ[R] Dual R C := LinearMap.lcomp R R C.subtype
  let μ : M →ₗ[R] Dual R C := ρ.comp (Module.Dual.eval R M)
  obtain ⟨hExactαβ, hInjα, hSurjβ⟩ :=
    dual_range_sequence_short_exact (R := R) (M := M) (M' := M') (M'' := M'') hfg
  have hExactDual : Function.Exact (LinearMap.lcomp R R β) (LinearMap.lcomp R R α) :=
    LinearMap.exact_lcomp_of_exact_of_surjective R hExactαβ hSurjβ
  constructor
  · intro m₁ m₂ hμ
    -- Testing against all extendable functionals identifies `f m₁` and `f m₂` in the reflexive
    -- middle term, and then injectivity of `f` recovers `m₁ = m₂`.
    have hEval : Module.Dual.eval R M' (f m₁) = Module.Dual.eval R M' (f m₂) := by
      ext φ
      have happly := congrArg
        (fun ν => ν ⟨β₀ φ, ⟨φ, rfl⟩⟩) hμ
      simpa [μ, ρ, β₀] using happly
    exact hf ((Module.evalEquiv R M').injective hEval)
  · intro ψ
    -- Dualizing the short exact row gives a bidual element of `M'`; exactness then forces it
    -- into `ker π = range f`.
    let m' : M' := (Module.evalEquiv R M').symm ((LinearMap.lcomp R R β) ψ)
    have hm' :
        Module.Dual.eval R M' m' = (LinearMap.lcomp R R β) ψ := by
      change (Module.evalEquiv R M') m' = (LinearMap.lcomp R R β) ψ
      exact LinearEquiv.apply_symm_apply (Module.evalEquiv R M') ((LinearMap.lcomp R R β) ψ)
    have hβψ :
        (LinearMap.lcomp R R α) ((LinearMap.lcomp R R β) ψ) = 0 := by
      exact (hExactDual ((LinearMap.lcomp R R β) ψ)).2 ⟨ψ, rfl⟩
    have hnat := Module.Dual.eval_naturality (R := R) (M₁ := M') (M₂ := Q) π
    have hπeval :
        (LinearMap.lcomp R R α) (Module.Dual.eval R M' m') =
          Module.Dual.eval R Q (π m') := by
      simpa [α] using LinearMap.congr_fun hnat m'
    have hEvalZero : Module.Dual.eval R Q (π m') = 0 := by
      rw [← hπeval, hm']
      exact hβψ
    have hEvalQInj : Function.Injective (Module.Dual.eval R Q) := by
      exact (eval_injective_iff_isTorsionFree (R := R) (M := Q)).2 inferInstance
    have hπzero : π m' = 0 := by
      apply hEvalQInj
      simpa using hEvalZero
    have hExactπ : Function.Exact f π := exact_rangeRestrict (R := R) hfg
    obtain ⟨m, hm⟩ := (hExactπ m').1 hπzero
    refine ⟨m, ?_⟩
    ext c
    obtain ⟨φ, hφ⟩ := c.2
    have hc : β φ = c := Subtype.ext hφ
    have hψφ : φ m' = ψ (β φ) := by
      simpa [β] using LinearMap.congr_fun hm' φ
    -- On generators of the range, `μ` is just evaluation at `f m = m'`.
    calc
      μ m c = μ m (β φ) := by rw [← hc]
      _ = φ m' := by simpa [μ, ρ, β, β₀, hm]
      _ = ψ (β φ) := hψφ
      _ = ψ c := by rw [hc]

/-- Helper for Lemma 15.23.5: the bidual restriction map to extendable functionals is injective. -/
private theorem bidual_restrict_injective
    {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Function.Exact f g) (hf : Injective f)
    [IsReflexive R M'] [IsTorsionFree R (LinearMap.range g)] :
    let C := LinearMap.range (LinearMap.lcomp R R f)
    let ρ : Dual R (Dual R M) →ₗ[R] Dual R C := LinearMap.lcomp R R C.subtype
    Function.Injective ρ := by
  -- TODO: derive `Module.Finite R M` from the already-bijective restricted evaluation map, prove
  -- the torsion statement for `Q := (Dual R M) ⧸ range (lcomp f)`, then dualize
  -- `0 → C → Dual R M → Q → 0` to kill `Dual R Q` and conclude that `ρ` has trivial kernel.
  sorry

-- Proof sketch: replace `g` by the canonical surjection `M' → range g`, so the exact pair
-- becomes `0 → M → M' → range g → 0`. Dualize this short exact sequence to compare the
-- evaluation maps into the double duals. Reflexivity of `M'` identifies the middle vertical map
-- with an isomorphism, while torsion-freeness of `range g` makes the right evaluation map
-- injective by Lemma `15.23.2`. The remaining diagram chase shows the evaluation map for `M` is
-- bijective.
/-- Lemma 15.23.5: if `0 → M → M' → M''` is exact over a domain, `M'` is finite and
reflexive, and the quotient `M'/M` identified with `LinearMap.range g` is torsion free, then `M`
is reflexive. -/
theorem isReflexive_of_exact_of_isReflexive_of_isTorsionFree
    {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Function.Exact f g) (hf : Injective f)
    [IsReflexive R M'] [IsTorsionFree R (LinearMap.range g)] :
    IsReflexive R M := by
  -- TODO: once `bidual_restrict_injective` is available, combine it with the already-bijective
  -- map to extendable functionals from `restricted_dual_eval_bijective` to cancel the restriction
  -- map and recover bijectivity of `Module.Dual.eval R M`.
  sorry

end
