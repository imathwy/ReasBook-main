import Mathlib
import StacksProject_2024.Chap15.Lemma_15_29_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open AlgebraicTopology
open CategoryTheory.Limits
open LocalizedModule
open ModuleCat
open MonoidalCategory
open scoped TensorProduct

/-
Domain-style sampling:
- primary domain: homology of the extended alternating Čech complex of a finite family in a
  commutative ring;
- sampled owner declarations:
  `extendedAlternatingCechComplex`
  `extendedAlternatingCechComplex_homotopyEquivalent_zero_of_exists_isUnit`
  `extendedAlternatingCechComplex_homology_isZero_of_isKoszulRegularSequence`
  `Module.support`;
- best owner abstraction: the cohomology modules in this lemma are already canonically the
  homology objects `(extendedAlternatingCechComplex f M).homology q`, so no parallel local
  cohomology owner should be introduced here.

Primitive data is only the finite family `f`, the `R`-module `M`, and the canonical owner
`extendedAlternatingCechComplex f M`. The cohomology objects, their support, and the annihilation
properties are derived API of that owner.

Source/core/bridge triage:
- `source-facing`: the four cohomology consequences stated in Lemma 15.29.5;
- `core/canonical`: homology of the owner complex `(extendedAlternatingCechComplex f M).homology q`;
- `bridge/view`: support and annihilation reformulations of those homology objects.
-/

section

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {r : ℕ}

/-- Helper for Lemma 15.29.5: the tensor-description comparison for the extended alternating Čech
complex, restated at the ambient module universe used in this file. -/
noncomputable abbrev extendedAlternatingCechComplex_iso_tensorObj_universe
    (f : Fin r → R) :
    extendedAlternatingCechComplex f M ≅
      (((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (extendedAlternatingCechComplex f R)) :=
  sorry

/-- Helper for Lemma 15.29.5: the scalar-extension comparison for the extended alternating Čech
complex, restated at the ambient module universe used in this file. -/
noncomputable abbrev extendedAlternatingCechComplex_iso_extendScalars_universe
    {S : Type u} [CommRing S] [Algebra R S]
    (f : Fin r → R) :
    extendedAlternatingCechComplex (fun i ↦ algebraMap R S (f i)) (S ⊗[R] M) ≅
      (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (extendedAlternatingCechComplex f M)) :=
  sorry

/-- Helper for Lemma 15.29.5: once the away-localization of a module is trivial, every element is
killed by a positive power of the localized scalar. -/
lemma exists_pos_pow_smul_eq_zero_of_away_subsingleton
    {a : R} {H : Type u} [AddCommGroup H] [Module R H]
    (hH : Subsingleton (LocalizedModule.Away a H)) (x : H) :
    ∃ n : ℕ, 1 ≤ n ∧ a ^ n • x = 0 := by
  -- Extract a denominator in the powers of `a` that annihilates `x`.
  rcases (LocalizedModule.subsingleton_iff (S := Submonoid.powers a) (M := H)).mp hH x with
    ⟨s, hs, hsx⟩
  rcases hs with ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst hn
    refine ⟨1, le_rfl, ?_⟩
    -- If `x = 0`, then the first power also kills `x`.
    have hx0 : x = 0 := by simpa using hsx
    simpa [hx0]
  · exact ⟨n, Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn), hsx⟩

/-- Helper for Lemma 15.29.5: restricting scalars on `R[1 / a]` does not change the underlying
localized ring. -/
private noncomputable def restrictScalars_away_self_equiv (a : R) :
    ↑((ModuleCat.restrictScalars (algebraMap R (Localization.Away a))).obj
      (ModuleCat.of (Localization.Away a) (Localization.Away a))) ≃ₗ[Localization.Away a]
        Localization.Away a :=
  { __ := AddEquiv.refl (Localization.Away a)
    map_smul' := fun _ _ ↦ rfl }

/-- Helper for Lemma 15.29.5: the restricted `R`-action and the ambient localized action on
`R[1 / a]` form the expected scalar tower. -/
private instance restrictScalars_away_self_isScalarTower (a : R) :
    IsScalarTower R (Localization.Away a)
      ↑((ModuleCat.restrictScalars (algebraMap R (Localization.Away a))).obj
        (ModuleCat.of (Localization.Away a) (Localization.Away a))) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

/-- Helper for Lemma 15.29.5: scalar extension to `R[1 / a]` is the canonical tensor product with
`R[1 / a]`. -/
private noncomputable def away_extendScalars_tensor_iso (a : R) (H : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away a))).obj H ≅
      ModuleCat.of (Localization.Away a) ((Localization.Away a) ⊗[R] ↑H) := by
  -- Expand scalar extension and collapse the restricted-scalar factor on the localized ring.
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      (restrictScalars_away_self_equiv (R := R) a)
      (LinearEquiv.refl R ↑H)).toModuleIso

/-- Helper for Lemma 15.29.5: scalar extension to `R[1 / a]` agrees with away localization. -/
private noncomputable def away_extendScalars_iso (a : R) (H : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away a))).obj H ≅
      ModuleCat.of (Localization.Away a) (LocalizedModule.Away a ↑H) :=
  away_extendScalars_tensor_iso (R := R) a H ≪≫
    ((LocalizedModule.equivTensorProduct (Submonoid.powers a) (↑H)).symm).toModuleIso

/-- Helper for Lemma 15.29.5: the away localization of the `q`th cohomology module, viewed as an
object over `R[1 / f i]`. -/
private abbrev away_localized_extendedAlternatingCechCohomology
    {f : Fin r → R} (q : ℕ) (i : Fin r) :
    ModuleCat.{u} (Localization.Away (f i)) :=
  ModuleCat.of (Localization.Away (f i))
    (LocalizedModule.Away (f i) ((extendedAlternatingCechComplex f M).homology q))

/-- Helper for Lemma 15.29.5: the `q`th homology object after extending scalars to `R[1 / f i]`.
-/
private abbrev extendedAlternatingCechComplex_baseChange_homology
    {f : Fin r → R} (q : ℕ) (i : Fin r) :
    ModuleCat.{u} (Localization.Away (f i)) :=
  ((((ModuleCat.extendScalars
      (algebraMap R (Localization.Away (f i)))).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
    (extendedAlternatingCechComplex f M)).homology q)

/-- Helper for Lemma 15.29.5: away localization of the `q`th cohomology agrees with first
extending scalars to `R[1 / f i]` and then taking `q`th homology. -/
noncomputable def localized_extendedAlternatingCechCohomology_iso_away_generator
    {f : Fin r → R} (q : ℕ) (i : Fin r) :
    (away_localized_extendedAlternatingCechCohomology
        (R := R) (M := M) (f := f) q i) ≅
      (extendedAlternatingCechComplex_baseChange_homology
        (R := R) (M := M) (f := f) q i) := by
  let S := Localization.Away (f i)
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := ModuleCat.extendScalars (algebraMap R S)
  have hflat : (algebraMap R S).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr (show Module.Flat R S from inferInstance)
  letI : PreservesFiniteLimits F := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  letI : F.PreservesHomology := inferInstance
  let K := extendedAlternatingCechComplex f M
  -- First identify away localization with exact scalar extension of the homology object.
  let eAway :
      F.obj (ModuleCat.of R (K.homology q)) ≅
        away_localized_extendedAlternatingCechCohomology
          (R := R) (M := M) (f := f) q i :=
    away_extendScalars_iso (R := R) (f i) (ModuleCat.of R (K.homology q))
  -- Then commute homology past scalar extension.
  exact eAway.symm ≪≫ ((K.sc q).mapHomologyIso F).symm

/-- Helper for Lemma 15.29.5: localizing away from one generator kills the corresponding extended
alternating Čech cohomology module. -/
lemma localized_extendedAlternatingCechCohomology_subsingleton_away_generator
    {f : Fin r → R} (q : ℕ) (i : Fin r) :
    Subsingleton (LocalizedModule.Away (f i) ((extendedAlternatingCechComplex f M).homology q)) := by
  let S := Localization.Away (f i)
  let fS : Fin r → S := fun j ↦ algebraMap R S (f j)
  have hunit : ∃ j : Fin r, IsUnit (fS j) := by
    refine ⟨i, ?_⟩
    simpa [fS] using (IsLocalization.Away.algebraMap_isUnit (f i))
  obtain ⟨e⟩ :=
    extendedAlternatingCechComplex_homotopyEquivalent_zero_of_exists_isUnit
      (R := S) (M := S ⊗[R] M) (r := r) fS hunit
  have hzeroLocalized :
      IsZero ((extendedAlternatingCechComplex fS (S ⊗[R] M)).homology q) := by
    -- The localized extended alternating Čech complex is homotopy equivalent to zero.
    -- TODO: identify the homology of the zero cochain complex with the zero object in this
    -- `ℕ`-indexed setting, then transport that zero statement across `e.toHomologyIso q`.
    sorry
  have hzeroBaseChange :
      IsZero
        (extendedAlternatingCechComplex_baseChange_homology
          (R := R) (M := M) (f := f) q i) := by
    -- Transport the zero homology statement across the base-change comparison from Lemma `15.29.3`.
    exact IsZero.of_iso hzeroLocalized
      (HomologicalComplex.homologyMapIso
        (extendedAlternatingCechComplex_iso_extendScalars_universe
          (R := R) (S := S) (M := M) (r := r) f) q).symm
  have hzeroAway :
      IsZero
        (away_localized_extendedAlternatingCechCohomology
          (R := R) (M := M) (f := f) q i) := by
    -- Finally compare the localized homology object with away localization of the homology module.
    exact IsZero.of_iso hzeroBaseChange
      (localized_extendedAlternatingCechCohomology_iso_away_generator
        (R := R) (M := M) (f := f) q i)
  simpa [ModuleCat.isZero_iff_subsingleton] using hzeroAway

/-- Helper for Lemma 15.29.5: support in `V(a)` together with invertibility of `a` forces a module
to be zero. -/
lemma isZero_of_support_subset_zeroLocus_singleton_of_scalar_isUnit
    {a : R} {H : Type u} [AddCommGroup H] [Module R H]
    (hsupp : Module.support R H ⊆ PrimeSpectrum.zeroLocus ({a} : Set R))
    (hunit : IsUnit (algebraMap R (Module.End R H) a)) :
    IsZero (ModuleCat.of R H) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  rw [subsingleton_iff_forall_eq 0]
  intro x
  have hsub : Subsingleton (LocalizedModule.Away a H) := by
    rw [LocalizedModule.subsingleton_iff_support_subset]
    exact hsupp
  -- Local support in `V(a)` provides a power of `a` annihilating `x`.
  rcases (LocalizedModule.subsingleton_iff (S := Submonoid.powers a) (M := H)).mp hsub x with
    ⟨s, hs, hsx⟩
  rcases hs with ⟨n, rfl⟩
  let u : Module.End R H := algebraMap R (Module.End R H) a
  have hu : IsUnit u := by simpa [u] using hunit
  have hunitpow : IsUnit (u ^ n) := hu.pow n
  have hbijpow : Function.Bijective ⇑(u ^ n) := (Module.End.isUnit_iff (u ^ n)).1 hunitpow
  have hpow_apply : ∀ m : ℕ, ∀ y : H, (u ^ m) y = a ^ m • y := by
    intro m y
    induction m with
    | zero =>
        simp [u]
    | succ m ihm =>
        simp [pow_succ, ihm, u, Module.algebraMap_end_apply, smul_smul, mul_comm]
  have hsx' : (u ^ n) x = 0 := by
    rw [hpow_apply n x]
    exact hsx
  -- An invertible scalar endomorphism cannot send a nonzero vector to zero.
  apply hbijpow.1
  simpa using hsx'

/-- Helper for Lemma 15.29.5: once the `q`th term of a cochain complex is zero, the `q`th
homology vanishes because the middle object of the defining short complex is zero. -/
private theorem isZero_homology_of_isZero_term
    {K : CochainComplex (ModuleCat.{u} R) ℕ} (q : ℕ)
    (hX : IsZero (K.X q)) :
    IsZero (K.homology q) := by
  -- The degree-`q` short complex computing homology has zero middle term.
  simpa using
    (ShortComplex.isZero_homology_of_isZero_X₂
      (S := K.sc q)
      (by simpa using hX))

/-- Helper for Lemma 15.29.5: on the tensor-model presentation of the extended alternating Čech
complex, the `q`th homology vanishes for `q > r`. -/
private lemma tensor_model_extendedAlternatingCechComplex_homology_isZero_of_gt
    {f : Fin r → R} {q : ℕ} (hq : r < q) :
    IsZero
      ((((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (extendedAlternatingCechComplex f R)).homology q) := by
  -- Route correction: the source proof must run through the bounded powered-Koszul or normalized
  -- Moore model, because the unnormalized extended Čech complex has nonzero terms in arbitrarily
  -- high degrees. The remaining gap is therefore a homology-level boundedness bridge, not a
  -- term-level vanishing lemma.
  -- TODO: compare the tensor-model extended alternating Čech complex with the public bounded model
  -- coming from Lemma `15.29.6` (or an equivalent normalized-Moore owner), then transport the
  -- degree bound `q > r` through that comparison.
  sorry

-- Proof sketch: the extended alternating Čech complex is concentrated in degrees `0, ..., r`, so
-- the homology object in degree `q` is zero once `q > r`.
/-- Lemma 15.29.5 (1): the extended alternating Čech cohomology vanishes in degrees above `r`,
which is the `q ∉ [0, r]` vanishing statement in the natural `ℕ`-indexed model of the complex. -/
@[stacks 0G6K]
theorem extendedAlternatingCechCohomology_isZero_of_gt
    {f : Fin r → R} {q : ℕ} (hq : r < q) :
    IsZero ((extendedAlternatingCechComplex f M).homology q) := by
  let eTensor := extendedAlternatingCechComplex_iso_tensorObj_universe
    (R := R) (M := M) (r := r) f
  have hzeroTensorHomology :
      IsZero
        ((((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (extendedAlternatingCechComplex f R)).homology q) :=
    tensor_model_extendedAlternatingCechComplex_homology_isZero_of_gt
      (R := R) (M := M) (r := r) hq
  -- Pull the tensor-model vanishing statement back across the tensor-description comparison.
  exact IsZero.of_iso hzeroTensorHomology (HomologicalComplex.homologyMapIso eTensor q)

-- Proof sketch: localize the extended alternating Čech complex at `f i`; by Lemma 15.29.3 this
-- localized complex is again an extended alternating Čech complex, and by Lemma 15.29.4 it is
-- contractible because `f i` becomes a unit. Hence the localized cohomology vanishes, which means
-- some positive power of `f i` kills the class `x`.
/-- Lemma 15.29.5 (2): every cohomology class in the extended alternating Čech complex is
annihilated by a positive power of each generator `f i`. -/
@[stacks 0G6K]
theorem exists_pow_smul_eq_zero_of_mem_extendedAlternatingCechCohomology
    {f : Fin r → R} (q : ℕ) (i : Fin r)
    (x : (extendedAlternatingCechComplex f M).homology q) :
    ∃ n : ℕ, 1 ≤ n ∧ f i ^ n • x = 0 := by
  -- After localizing away from `f i`, the cohomology vanishes, so some power of `f i` kills `x`.
  exact exists_pos_pow_smul_eq_zero_of_away_subsingleton
    (localized_extendedAlternatingCechCohomology_subsingleton_away_generator
      (R := R) (M := M) q i)
    x

-- Proof sketch: by the previous clause, localizing the cohomology module at any `f i` gives zero.
-- The support criterion for localization then places the support inside the common zero locus of
-- the ideal generated by the family `f`.
/-- Lemma 15.29.5 (3): the support of the `q`th extended alternating Čech cohomology module is
contained in the closed subset `V(f₁, ..., fᵣ)`. -/
@[stacks 0G6K]
theorem support_extendedAlternatingCechCohomology_subset_zeroLocus
    {f : Fin r → R} (q : ℕ) :
    Module.support R ((extendedAlternatingCechComplex f M).homology q) ⊆
      PrimeSpectrum.zeroLocus (Ideal.span (Set.range f)) := by
  intro p hp
  rw [PrimeSpectrum.mem_zeroLocus]
  refine Ideal.span_le.mpr ?_
  intro x hx
  rcases hx with ⟨i, rfl⟩
  have hsingle :
      Module.support R ((extendedAlternatingCechComplex f M).homology q) ⊆
        PrimeSpectrum.zeroLocus ({f i} : Set R) := by
    rw [← LocalizedModule.subsingleton_iff_support_subset]
    exact localized_extendedAlternatingCechCohomology_subsingleton_away_generator
      (R := R) (M := M) q i
  -- Every prime in the support contains each generator separately.
  have hpzero : p ∈ PrimeSpectrum.zeroLocus ({f i} : Set R) := hsingle hp
  rw [PrimeSpectrum.mem_zeroLocus] at hpzero
  exact hpzero (by simp)

/-- Helper for Lemma 15.29.5: an invertible scalar endomorphism of `M` defines a module
automorphism of `M`. -/
private noncomputable def module_iso_of_scalar_isUnit
    {a : R} (hunit : IsUnit (algebraMap R (Module.End R M) a)) :
    ModuleCat.of R M ≅ ModuleCat.of R M := by
  have hbij : Function.Bijective (algebraMap R (Module.End R M) a) := by
    -- `Module.End.isUnit_iff` turns the source hypothesis into bijectivity of scalar
    -- multiplication on the underlying module.
    exact (Module.End.isUnit_iff _).1 hunit
  exact (LinearEquiv.ofBijective (algebraMap R (Module.End R M) a) hbij).toModuleIso

/-- Helper for Lemma 15.29.5: the module automorphism built from an invertible scalar is exactly
scalar multiplication by that element. -/
private theorem module_iso_of_scalar_isUnit_hom_eq
    {a : R} (hunit : IsUnit (algebraMap R (Module.End R M) a)) :
    (module_iso_of_scalar_isUnit (R := R) (M := M) hunit).hom =
      ModuleCat.ofHom (algebraMap R (Module.End R M) a) := by
  -- `LinearEquiv.ofBijective` keeps the same underlying linear map.
  rfl

/-- Helper for Lemma 15.29.5: cochain-complex homology maps are linear in the chain map. -/
private theorem cochain_homologyMap_smul
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L) (a : R) (q : ℕ)
    [K.HasHomology q] [L.HasHomology q] :
    HomologicalComplex.homologyMap (a • φ) q =
      a • HomologicalComplex.homologyMap φ q := by
  -- Reduce to the linearity statement for the short-complex homology map at degree `q`.
  change
    ShortComplex.homologyMap
        (a • (HomologicalComplex.shortComplexFunctor
          (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map φ) =
      a • ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor
          (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map φ)
  rw [ShortComplex.homologyMap_smul]
  rfl

/-- Helper for Lemma 15.29.5: the homology map induced by scalar multiplication on a cochain
complex is scalar multiplication on homology. -/
private theorem cochain_homologyMap_smul_id
    {K : CochainComplex (ModuleCat.{u} R) ℕ} (a : R) (q : ℕ) [K.HasHomology q] :
    HomologicalComplex.homologyMap (a • 𝟙 K) q = a • 𝟙 (K.homology q) := by
  -- Specialize the linearity statement to the identity chain map.
  rw [cochain_homologyMap_smul, HomologicalComplex.homologyMap_id]

/-- Helper for Lemma 15.29.5: tensoring an isomorphism on the left acts on pure tensors by
applying that isomorphism to the first tensor factor. -/
private theorem tensoringLeft_mapIso_hom_apply_tmul
    {N : Type u} [AddCommGroup N] [Module R N]
    (e : ModuleCat.of R M ≅ ModuleCat.of R M) (x : M) (y : N) :
    (((tensoringLeft (ModuleCat.{u} R)).mapIso e).app (ModuleCat.of R N)).hom.hom
        (x ⊗ₜ[R] y) =
      e.hom.hom x ⊗ₜ[R] y :=
  rfl

/-- Helper for Lemma 15.29.5: on the tensor-model extended alternating Čech complex, the mapped
scalar automorphism is literally scalar multiplication by `a`. -/
private theorem tensor_model_scalar_hom_eq_smul_id
    {f : Fin r → R} {a : R}
    (hunit : IsUnit (algebraMap R (Module.End R M) a)) :
    (((NatIso.mapHomologicalComplex
        ((tensoringLeft (ModuleCat.{u} R)).mapIso
          (module_iso_of_scalar_isUnit (R := R) (M := M) hunit))
        (ComplexShape.up ℕ)).app (extendedAlternatingCechComplex f R)).hom =
      a • 𝟙 (((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (extendedAlternatingCechComplex f R))) := by
  -- TODO: this transport equality should be reintroduced through a dedicated componentwise tensor
  -- lemma; the current direct extensional proof times out during elaboration.
  sorry

/-- Helper for Lemma 15.29.5: if scalar multiplication by `a` is invertible on `M`, then the same
scalar endomorphism is an isomorphism of the entire extended alternating Čech complex. -/
private lemma extendedAlternatingCechComplex_smul_isIso_of_module_scalar_isUnit
    {f : Fin r → R} {a : R}
    (hunit : IsUnit (algebraMap R (Module.End R M) a)) :
    IsIso (a • 𝟙 (extendedAlternatingCechComplex f M)) := by
  -- TODO: once the tensor-model scalar comparison is available, this isomorphism follows by
  -- transport across `extendedAlternatingCechComplex_iso_tensorObj_universe`.
  sorry

-- TODO: transport invertibility of scalar multiplication by `a` on `M` to invertibility on the
-- homology module by functoriality of the extended alternating Čech complex and homology.
/-- Helper for Lemma 15.29.5: an invertible scalar action on `M` induces an invertible scalar
action on extended alternating Čech cohomology. -/
lemma homology_scalar_isUnit_of_module_scalar_isUnit
    {f : Fin r → R} (q : ℕ) {a : R}
    (hunit : IsUnit (algebraMap R (Module.End R M) a)) :
    IsUnit
      (algebraMap R
        (Module.End R ((extendedAlternatingCechComplex f M).homology q)) a) := by
  -- TODO: after the complex-side scalar automorphism is reinstated, functoriality of homology
  -- transports it to an invertible scalar action on the cohomology module.
  sorry

-- Proof sketch: an element `a ∈ (f₁, ..., fᵣ)` acting invertibly on `M` also acts invertibly on
-- every term of the extended alternating Čech complex and hence on its cohomology. Clause (3)
-- shows that the support of the cohomology is contained in `V(a)`, so invertibility of `a`
-- forces the cohomology module to vanish.
/-- Lemma 15.29.5 (4): if some element of the ideal `(f₁, ..., fᵣ)` acts invertibly on `M`, then
every extended alternating Čech cohomology module vanishes. -/
@[stacks 0G6K]
theorem extendedAlternatingCechCohomology_isZero_of_exists_isUnit_span
    {f : Fin r → R} (q : ℕ)
    (hunit : ∃ a ∈ Ideal.span (Set.range f), IsUnit (algebraMap R (Module.End R M) a)) :
    IsZero ((extendedAlternatingCechComplex f M).homology q) := by
  rcases hunit with ⟨a, ha, hunita⟩
  have hsupp :
      Module.support R ((extendedAlternatingCechComplex f M).homology q) ⊆
        PrimeSpectrum.zeroLocus ({a} : Set R) := by
    intro p hp
    have hp' := support_extendedAlternatingCechCohomology_subset_zeroLocus
      (R := R) (M := M) (f := f) q hp
    rw [PrimeSpectrum.mem_zeroLocus] at ⊢
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hp' ha
  have hunitH :
      IsUnit
        (algebraMap R
          (Module.End R ((extendedAlternatingCechComplex f M).homology q)) a) :=
    homology_scalar_isUnit_of_module_scalar_isUnit
      (R := R) (M := M) (f := f) q hunita
  -- Support in `V(a)` and invertibility of `a` on cohomology force the module to vanish.
  simpa using
    isZero_of_support_subset_zeroLocus_singleton_of_scalar_isUnit
      (R := R)
      (H := ((extendedAlternatingCechComplex f M).homology q))
      hsupp
      hunitH

end
