import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Ideal.Over

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_126_1 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/- Domain-style sampling:
- primary domain: finite-type algebras under tensor-product base change and faithfully flat descent;
- sampled owner declarations:
  `RingHom.FaithfullyFlat`,
  `RingHom.faithfullyFlat_algebraMap_iff`,
  `Algebra.FiniteType`,
  `Algebra.FiniteType.baseChange`,
  `Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat`,
  `RingHom.FiniteType.codescendsAlong_faithfullyFlat`;
- best owner abstractions: `Algebra.FiniteType` for the finite-type property and
  `(algebraMap R R').FaithfullyFlat` for the faithfully flat base-change hypothesis;
- primitive data: the two algebra structures `R → S` and `R → R'`, together with faithful
  flatness of the canonical ring map `R → R'`;
- derived API: the textbook equivalence between finite type for `S/R` and for the base change
  `R' ⊗[R] S / R'`.

Source/core/bridge triage:
- `source-facing`: the textbook iff statement of Lemma 10.126.1;
- `core/canonical`: `Algebra.FiniteType.baseChange` and
  `Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat` together with the canonical
  faithful-flatness owner `(algebraMap R R').FaithfullyFlat`;
- `bridge/view`: `RingHom.faithfullyFlat_algebraMap_iff` and the tensor-product presentation
  `R' ⊗[R] S` of the base-changed algebra.
-/

/-- Lemma 10.126.1: for a faithfully flat base change `R → R'`, the `R`-algebra `S` is of finite
type over `R` if and only if the base-changed algebra `R' ⊗[R] S` is of finite type over `R'`. -/
theorem finiteType_iff_finiteType_baseChange_of_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat) :
    Algebra.FiniteType R S ↔ Algebra.FiniteType R' (R' ⊗[R] S) := by
  letI : Module.FaithfullyFlat R R' :=
    (RingHom.faithfullyFlat_algebraMap_iff : (algebraMap R R').FaithfullyFlat ↔
      Module.FaithfullyFlat R R').mp hff
  exact ⟨fun _ ↦ inferInstance,
    fun _ ↦ Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat R'⟩

end

/-! ### Lemma_10_126_2 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/- Domain-style sampling:
- primary domain: faithfully flat descent and base-change stability for finite-presentation of
  commutative algebras;
- sampled canonical declarations of the same kind:
  `Algebra.FinitePresentation.baseChange`,
  `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`,
  `RingHom.FinitePresentation.codescendsAlong_faithfullyFlat`;
- best owner abstraction: the predicate `Algebra.FinitePresentation R S`;
- primitive data: the commutative rings `R`, `S`, `R'`, the algebra structures `R → S` and
  `R → R'`, and the faithfully flat base change `R → R'`;
- derived API: base-change stability and faithfully flat descent for that owner predicate.

Layering:
- this numbered item is `source-facing`: it packages the canonical forward base-change instance and
  reverse descent theorem into the textbook `iff`, without introducing any parallel owner API.
-/

-- Proof sketch: the forward implication is the standard base-change stability of finite
-- presentation. For the reverse implication, apply the canonical faithfully flat descent theorem
-- `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` to the
-- base-changed algebra `R' ⊗[R] S`.
/-- Lemma 10.126.2: for a faithfully flat base change `R → R'`, the `R`-algebra `S` is of finite
presentation over `R` if and only if the base-changed `R'`-algebra `R' ⊗[R] S` is of finite
presentation over `R'`. -/
theorem finitePresentation_iff_finitePresentation_baseChange_of_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat) :
    Algebra.FinitePresentation R S ↔ Algebra.FinitePresentation R' (R' ⊗[R] S) := by
  letI : Module.FaithfullyFlat R R' :=
    (RingHom.faithfullyFlat_algebraMap_iff : (algebraMap R R').FaithfullyFlat ↔
      Module.FaithfullyFlat R R').mp hff
  constructor
  · intro _
    infer_instance
  · intro _
    simpa using Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat R'

end

/-! ### Lemma_10_126_3 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R) (S : Submonoid R)

local notation "Sbar" => Algebra.algebraMapSubmonoid (R ⧸ I) S
local notation "R'" => Localization Sbar

open scoped Pointwise

/-- Helper for Lemma 10.126.3: an `R ⧸ I`-module is annihilated by `I` after restricting scalars
along `R → R ⧸ I`. -/
lemma quotient_module_smul_top_eq_bot
    {Q : Type v} [AddCommGroup Q] [Module (R ⧸ I) Q] [Module R Q]
    [IsScalarTower R (R ⧸ I) Q] :
    I • (⊤ : Submodule R Q) = ⊥ := by
  -- Every element of `I` maps to zero in `R ⧸ I`, so it acts trivially on `Q`.
  rw [← Submodule.le_annihilator_iff, Submodule.annihilator_top]
  intro r hr
  exact Module.mem_annihilator.mpr fun x ↦ by
    have hzero : ((Ideal.Quotient.mk I r : R ⧸ I) • x) = 0 := by
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    rw [← algebraMap_smul (A := R ⧸ I) r x]
    exact hzero

/-- Helper for Lemma 10.126.3: the quotient map by `I • ⊤` is an isomorphism for modules already
defined over `R ⧸ I`. -/
noncomputable def quotient_module_quotient_equiv
    {Q : Type v} [AddCommGroup Q] [Module (R ⧸ I) Q] [Module R Q]
    [IsScalarTower R (R ⧸ I) Q] :
    (Q ⧸ (I • ⊤ : Submodule R Q)) ≃ₗ[R] Q :=
  Submodule.quotEquivOfEqBot _ (quotient_module_smul_top_eq_bot (I := I))

/-- Helper for Lemma 10.126.3: after clearing denominators on a finite set of localized relations,
localizing the resulting span over `R ⧸ I` recovers the original localized span. -/
lemma localized_span_of_cleared_relation_generators
    {Fbar : Type v} [AddCommGroup Fbar] [Module (R ⧸ I) Fbar] [DecidableEq Fbar]
    {F' : Type v} [AddCommGroup F'] [Module (R ⧸ I) F'] [Module R' F']
    [IsScalarTower (R ⧸ I) R' F']
    (locMap : Fbar →ₗ[(R ⧸ I)] F') [IsLocalizedModule Sbar locMap]
    (T : Finset F') :
    (Submodule.span (R ⧸ I)
      (IsLocalizedModule.finsetIntegerMultiple Sbar locMap T : Set Fbar)).localized' R' Sbar
        locMap = Submodule.span R' (T : Set F') := by
  -- Localizing the cleared numerators multiplies the original generators by a common unit.
  rw [Submodule.localized'_span]
  rw [IsLocalizedModule.finsetIntegerMultiple_image]
  have hs :
      algebraMap (R ⧸ I) R' (IsLocalizedModule.commonDenomOfFinset Sbar locMap T : R ⧸ I) •
        (T : Set F') =
      IsLocalizedModule.commonDenomOfFinset Sbar locMap T • (T : Set F') := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp⟩
  rw [← hs]
  exact Submodule.span_smul_eq_of_isUnit _ _
    (IsLocalization.map_units R' (IsLocalizedModule.commonDenomOfFinset Sbar locMap T))

/-- Helper for Lemma 10.126.3: the coordinatewise reduction map `R^n → (R/I)^n` has kernel
`I • ⊤`. -/
lemma pi_reduce_mod_ideal_ker_eq_smul_top (n : ℕ) :
    LinearMap.ker (((Ideal.Quotient.mkₐ R I).toLinearMap).compLeft (Fin n)) =
      I • (⊤ : Submodule R (Fin n → R)) := by
  let modMap : (Fin n → R) →ₗ[R] (Fin n → R ⧸ I) :=
    ((Ideal.Quotient.mkₐ R I).toLinearMap).compLeft (Fin n)
  -- One inclusion is coordinatewise: a vector in the kernel has every coordinate in `I`.
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have hcoord : ∀ i, x i ∈ I := by
      intro i
      have hx0 : modMap x i = 0 := by
        simpa using congrFun hx i
      simpa [modMap, Ideal.Quotient.eq_zero_iff_mem] using hx0
    -- Reassemble the vector from the standard basis after checking each coefficient lies in `I`.
    rw [show x = ∑ i, Pi.single i (x i) by
      simpa using (LinearMap.sum_single_apply (v := x)).symm]
    exact Submodule.sum_mem _ fun i _ => by
      have hsingle :
          (x i : R) • (Pi.single i (1 : R) : Fin n → R) = (Pi.single i (x i) : Fin n → R) := by
        ext j
        by_cases h : j = i
        · subst h
          simp
        · simp [Pi.single_eq_of_ne h]
      rw [← hsingle]
      exact Submodule.smul_mem_smul (hcoord i)
        (by simp : Pi.single i (1 : R) ∈ (⊤ : Submodule R (Fin n → R)))
  · intro hx
    rw [LinearMap.mem_ker]
    ext i
    -- Reduction modulo `I` kills every element of `I • ⊤`.
    have hxproj : ((LinearMap.proj i : (Fin n → R) →ₗ[R] R) x) ∈ I • (⊤ : Submodule R R) :=
      (Submodule.smul_top_le_comap_smul_top (I := I)
        (f := (LinearMap.proj i : (Fin n → R) →ₗ[R] R))) hx
    simpa [modMap, Ideal.Quotient.eq_zero_iff_mem] using hxproj

/-- Helper for Lemma 10.126.3: spanning by chosen lifts in `R^n` maps onto the span of the cleared
relations in `(R/I)^n`. -/
lemma lifted_relation_span_maps_to_cleared_relation_span
    {n : ℕ} (Tbar : Finset (Fin n → R ⧸ I))
    (lift : Tbar → Fin n → R)
    (hlift : ∀ t : Tbar,
      (((Ideal.Quotient.mkₐ R I).toLinearMap).compLeft (Fin n)) (lift t) = t) :
    (Submodule.span R (Set.range lift)).map (((Ideal.Quotient.mkₐ R I).toLinearMap).compLeft
      (Fin n)) =
      (Submodule.span (R ⧸ I) (Tbar : Set (Fin n → R ⧸ I))).restrictScalars R := by
  rw [Submodule.restrictScalars_span (R := R) (A := R ⧸ I) Ideal.Quotient.mk_surjective]
  apply le_antisymm
  · -- Every lifted generator reduces to the corresponding cleared relation.
    rw [Submodule.map_span_le]
    intro x hx
    rcases hx with ⟨t, rfl⟩
    exact Submodule.subset_span (by simpa [hlift t] using t.property)
  · -- Conversely, each cleared relation is the image of its chosen lift.
    refine Submodule.span_le.mpr ?_
    intro x hx
    refine ⟨lift ⟨x, hx⟩, Submodule.subset_span (by exact Set.mem_range_self _), ?_⟩
    simpa [hlift ⟨x, hx⟩]

/-- Helper for Lemma 10.126.3: after quotienting the lifted presentation by `I`, one recovers the
presentation over `R ⧸ I`. -/
theorem quotient_by_lifted_relations_reduce_mod_ideal_equiv
    {n : ℕ} (K : Submodule R (Fin n → R))
    (Kbar : Submodule (R ⧸ I) (Fin n → R ⧸ I))
    (hKmap : K.map (((Ideal.Quotient.mkₐ R I).toLinearMap).compLeft (Fin n)) =
      Kbar.restrictScalars R) :
    Nonempty ((((Fin n → R) ⧸ K) ⧸ (I • (⊤ : Submodule R ((Fin n → R) ⧸ K)))) ≃ₗ[R ⧸ I]
      (Fin n → R ⧸ I) ⧸ Kbar) := by
  let modMap : (Fin n → R) →ₗ[R] (Fin n → R ⧸ I) :=
    ((Ideal.Quotient.mkₐ R I).toLinearMap).compLeft (Fin n)
  have hmod_surj : Function.Surjective modMap := by
    -- Lift each coordinate independently along the quotient map.
    intro y
    choose x hx using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨fun i => x i, ?_⟩
    ext i
    exact hx i
  let q : ((Fin n → R) ⧸ K) →ₗ[R] ((Fin n → R ⧸ I) ⧸ Kbar.restrictScalars R) :=
    Submodule.mapQ K (Kbar.restrictScalars R) modMap (by
      rw [← hKmap]
      exact Submodule.map_le_iff_le_comap.mp le_rfl)
  have hsurj : Function.Surjective q := by
    -- Surjectivity descends from the coordinatewise quotient map.
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (Kbar.restrictScalars R) y
    obtain ⟨x, rfl⟩ := hmod_surj y
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    simp [q, modMap]
  have hkerq : LinearMap.ker q = I • (⊤ : Submodule R ((Fin n → R) ⧸ K)) := by
    -- The only extra relations introduced by reduction are exactly the `I`-multiples.
    rw [Submodule.ker_mapQ]
    rw [← hKmap, Submodule.comap_map_eq, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
    rw [pi_reduce_mod_ideal_ker_eq_smul_top (I := I), Submodule.map_smul'']
    simp
  let eR :
      (((Fin n → R) ⧸ K) ⧸ (I • (⊤ : Submodule R ((Fin n → R) ⧸ K)))) ≃ₗ[R]
        ((Fin n → R ⧸ I) ⧸ Kbar) :=
    (Submodule.quotEquivOfEq _ _ hkerq.symm ≪≫ₗ q.quotKerEquivOfSurjective hsurj) ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv R Kbar
  exact ⟨eR.extendScalarsOfSurjective Ideal.Quotient.mk_surjective⟩

/-- Helper for Lemma 10.126.3: quotienting by `I • ⊤` commutes with the universe lift `ULift`. -/
lemma ulift_quotient_mod_ideal_equiv
    {M : Type u} [AddCommGroup M] [Module R M] :
    Nonempty ((((ULift.{v} M) ⧸ (I • ⊤ : Submodule R (ULift.{v} M))) ≃ₗ[R ⧸ I]
      (M ⧸ (I • ⊤ : Submodule R M)))) := by
  let eR :
      ((ULift.{v} M) ⧸ (I • ⊤ : Submodule R (ULift.{v} M))) ≃ₗ[R]
        (M ⧸ (I • ⊤ : Submodule R M)) :=
    Submodule.Quotient.equiv
      (I • ⊤ : Submodule R (ULift.{v} M))
      (I • ⊤ : Submodule R M)
      (ULift.moduleEquiv : ULift.{v} M ≃ₗ[R] M)
      (by
        -- `ULift.moduleEquiv` preserves both scalar multiplication and the top submodule.
        simpa [Submodule.map_smul''])
  -- The quotient by `I • ⊤` naturally carries an `R ⧸ I`-module structure, and `eR` respects it.
  exact ⟨eR.extendScalarsOfSurjective Ideal.Quotient.mk_surjective⟩

/-- Helper for Lemma 10.126.3: passing from an `R`-module to its `ULift` does not change the
localized quotient modulo `I`. -/
theorem localized_quotient_ulift_equiv
    {M : Type u} [AddCommGroup M] [Module R M] :
    Nonempty (LocalizedModule Sbar
      ((ULift.{v} M) ⧸ (I • ⊤ : Submodule R (ULift.{v} M))) ≃ₗ[R']
        LocalizedModule Sbar (M ⧸ (I • ⊤ : Submodule R M))) := by
  rcases ulift_quotient_mod_ideal_equiv (I := I) (M := M) with ⟨e⟩
  -- Localizing the quotient-level equivalence gives the required `R'`-linear transport.
  exact ⟨IsLocalizedModule.mapEquiv Sbar
    (LocalizedModule.mkLinearMap Sbar
      ((ULift.{v} M) ⧸ (I • ⊤ : Submodule R (ULift.{v} M))))
    (LocalizedModule.mkLinearMap Sbar (M ⧸ (I • ⊤ : Submodule R M)))
    R' e⟩

/-- Helper for Lemma 10.126.3: the coordinatewise algebra map from `(R ⧸ I)^n` to `(R')^n`
is the concrete finite-free localization map used in both source clauses. -/
noncomputable abbrev free_pi_localizedMap (n : ℕ) :
    (Fin n → R ⧸ I) →ₗ[(R ⧸ I)] (Fin n → R') :=
  (Algebra.linearMap (R ⧸ I) R').compLeft (Fin n)

/-- Helper for Lemma 10.126.3: the coordinatewise algebra map on a finite free module is a
localization map because localization commutes with finite products. -/
instance free_pi_algebraMap_isLocalizedModule (n : ℕ) :
    IsLocalizedModule Sbar (free_pi_localizedMap (I := I) (S := S) n) := by
  rw [isLocalizedModule_iff_isBaseChange Sbar R']
  -- The scalar localization map is a base change, and finite powers preserve base change.
  simpa [free_pi_localizedMap] using
    (show IsBaseChange R' ((Algebra.linearMap (R ⧸ I) R').compLeft (Fin n)) from
      (show IsBaseChange R' (Algebra.linearMap (R ⧸ I) R') by
        rw [← isLocalizedModule_iff_isBaseChange Sbar R']
        infer_instance).finitePow (Fin n))

/-- Helper for Lemma 10.126.3: localizing a quotient of a finite free `(R ⧸ I)`-module gives the
corresponding quotient over `R'` once the localized relation submodule is identified. -/
lemma localized_free_pi_quotient_equiv
    {n : ℕ}
    (locMap : (Fin n → R ⧸ I) →ₗ[(R ⧸ I)] (Fin n → R')) [IsLocalizedModule Sbar locMap]
    (Kbar : Submodule (R ⧸ I) (Fin n → R ⧸ I))
    (K' : Submodule R' (Fin n → R'))
    (hKmap : (Kbar.localized Sbar).map
      (((IsLocalizedModule.iso Sbar locMap).extendScalarsOfIsLocalization Sbar R').toLinearMap) =
        K') :
    Nonempty (LocalizedModule Sbar ((Fin n → R ⧸ I) ⧸ Kbar) ≃ₗ[R'] ((Fin n → R') ⧸ K')) := by
  let locIso : LocalizedModule Sbar (Fin n → R ⧸ I) ≃ₗ[R'] (Fin n → R') :=
    (IsLocalizedModule.iso Sbar locMap).extendScalarsOfIsLocalization Sbar R'
  let eQuot :
      LocalizedModule Sbar ((Fin n → R ⧸ I) ⧸ Kbar) ≃ₗ[R']
        (LocalizedModule Sbar (Fin n → R ⧸ I) ⧸ (Kbar.localized Sbar)) :=
    (localizedQuotientEquiv Sbar Kbar).symm
  let eRel :
      (LocalizedModule Sbar (Fin n → R ⧸ I) ⧸ (Kbar.localized Sbar)) ≃ₗ[R']
        (Fin n → R') ⧸ K' :=
    Submodule.Quotient.equiv
      (Kbar.localized Sbar)
      K'
      locIso
      (by simpa [locIso] using hKmap)
  -- First rewrite localization of the quotient as a quotient of the localization, then descend
  -- the canonical localization equivalence of free modules to the quotient.
  exact ⟨eQuot.trans eRel⟩

/-- Helper for Lemma 10.126.3: the canonical localized submodule and the concrete `localized'`
submodule agree after transporting along the comparison equivalence of localized free modules. -/
lemma canonical_localized_submodule_image_eq_concrete_localized
    {Fbar : Type v} [AddCommGroup Fbar] [Module (R ⧸ I) Fbar]
    {F' : Type v} [AddCommGroup F'] [Module (R ⧸ I) F'] [Module R' F']
    [IsScalarTower (R ⧸ I) R' F']
    (locMap : Fbar →ₗ[(R ⧸ I)] F') [IsLocalizedModule Sbar locMap]
    (Kbar : Submodule (R ⧸ I) Fbar) :
    (Kbar.localized Sbar).map
        (((IsLocalizedModule.iso Sbar locMap).extendScalarsOfIsLocalization Sbar R').toLinearMap) =
      Kbar.localized' R' Sbar locMap := by
  let locIso : LocalizedModule Sbar Fbar ≃ₗ[R'] F' :=
    (IsLocalizedModule.iso Sbar locMap).extendScalarsOfIsLocalization Sbar R'
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases (Submodule.mem_localized' (S := Localization Sbar) (p := Sbar)
        (f := LocalizedModule.mkLinearMap Sbar Fbar) (M' := Kbar) y).mp hy with
      ⟨m, hm, s, rfl⟩
    -- The comparison equivalence sends the canonical fraction `m / s` to the same concrete
    -- fraction computed by `locMap`.
    exact (Submodule.mem_localized' (S := R') (p := Sbar) (f := locMap) (M' := Kbar) _).2
      ⟨m, hm, s, by
        rw [← IsLocalizedModule.mk_eq_mk' (S := Sbar) (m := m) (s := s)]
        change IsLocalizedModule.mk' locMap m s =
          ((IsLocalizedModule.iso Sbar locMap).toLinearMap.extendScalarsOfIsLocalization
            Sbar R') (LocalizedModule.mk m s)
        rfl⟩
  · intro hx
    rcases (Submodule.mem_localized' (S := R') (p := Sbar) (f := locMap) (M' := Kbar) x).mp hx with
      ⟨m, hm, s, rfl⟩
    -- Conversely, the same numerator/denominator pair defines a point of the canonical localized
    -- submodule whose image under the comparison map is the prescribed concrete fraction.
    refine Submodule.mem_map.mpr ?_
    refine ⟨LocalizedModule.mk m s, ?_, ?_⟩
    · exact (Submodule.mem_localized' (S := Localization Sbar) (p := Sbar)
        (f := LocalizedModule.mkLinearMap Sbar Fbar) (M' := Kbar) _).2
        ⟨m, hm, s, (IsLocalizedModule.mk_eq_mk' (S := Sbar) (m := m) (s := s)).symm⟩
    · change ((IsLocalizedModule.iso Sbar locMap).toLinearMap.extendScalarsOfIsLocalization
        Sbar R') (LocalizedModule.mk m s) = IsLocalizedModule.mk' locMap m s
      rfl

/-- Helper for Lemma 10.126.3: localizing the inverse-image relation submodule recovers the
original relation submodule over `R'`. -/
lemma restricted_comap_localized_eq_original
    {n : ℕ}
    (locMap : (Fin n → R ⧸ I) →ₗ[(R ⧸ I)] (Fin n → R')) [IsLocalizedModule Sbar locMap]
    (K' : Submodule R' (Fin n → R')) :
    (((K'.restrictScalars (R ⧸ I)).comap locMap).localized' R' Sbar locMap) = K' := by
  -- The localization/comap adjunction already identifies the localized inverse image with the
  -- original submodule, so no new denominator-clearing argument is needed here.
  simpa using (Submodule.localized'gi R' Sbar locMap).l_u_eq K'

/-- Helper for Lemma 10.126.3: the inverse-image relation submodule in `R^n` reduces modulo `I`
to the inverse-image relation submodule in `(R ⧸ I)^n`. -/
lemma inverse_image_relation_map_reduce_mod_eq
    {n : ℕ}
    (locMap : (Fin n → R ⧸ I) →ₗ[(R ⧸ I)] (Fin n → R')) [IsLocalizedModule Sbar locMap]
    (K' : Submodule R' (Fin n → R')) :
    let reduce : (Fin n → R) →ₗ[R] (Fin n → R ⧸ I) :=
      ((Ideal.Quotient.mkₐ R I).toLinearMap).compLeft (Fin n)
    let Kbar : Submodule (R ⧸ I) (Fin n → R ⧸ I) :=
      (K'.restrictScalars (R ⧸ I)).comap locMap
    let K : Submodule R (Fin n → R) :=
      (K'.restrictScalars R).comap ((locMap.restrictScalars R).comp reduce)
    K.map reduce = Kbar.restrictScalars R := by
  dsimp
  let reduce : (Fin n → R) →ₗ[R] (Fin n → R ⧸ I) :=
    ((Ideal.Quotient.mkₐ R I).toLinearMap).compLeft (Fin n)
  have hreduce_surj : Function.Surjective reduce := by
    -- The coordinatewise quotient map is surjective because each component quotient map is.
    intro y
    choose x hx using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨fun i => x i, ?_⟩
    ext i
    exact hx i
  have hK :
      Submodule.comap ((locMap.restrictScalars R).comp reduce) (K'.restrictScalars R) =
        (Submodule.restrictScalars R (Submodule.comap locMap (K'.restrictScalars (R ⧸ I)))).comap
          reduce := by
    -- Both submodules are defined by the same membership test after unfolding the two scalar
    -- restrictions on `K'`.
    ext x
    simp [reduce]
  -- Once the inverse-image description is aligned, surjectivity of `reduce` gives `map_comap`.
  calc
    Submodule.map reduce (Submodule.comap ((locMap.restrictScalars R).comp reduce)
        (K'.restrictScalars R)) =
      Submodule.map reduce
        (((Submodule.comap locMap (K'.restrictScalars (R ⧸ I))).restrictScalars R).comap reduce) := by
          rw [hK]
    _ = (Submodule.comap locMap (K'.restrictScalars (R ⧸ I))).restrictScalars R :=
      Submodule.map_comap_eq_of_surjective hreduce_surj _

/-- Helper for Lemma 10.126.3: for the inverse-image relation submodule, the canonical localized
submodule maps to the original relation submodule over `R'`. -/
lemma comap_relation_localized_hKmap
    {n : ℕ}
    (locMap : (Fin n → R ⧸ I) →ₗ[(R ⧸ I)] (Fin n → R')) [IsLocalizedModule Sbar locMap]
    (K' : Submodule R' (Fin n → R')) :
    (((K'.restrictScalars (R ⧸ I)).comap locMap).localized Sbar).map
        (((IsLocalizedModule.iso Sbar locMap).extendScalarsOfIsLocalization Sbar R').toLinearMap) =
      K' := by
  -- Route correction: pass through the concrete `localized'` submodule, then apply the canonical
  -- Galois-insertion identity `l_u_eq` for submodule localization.
  rw [canonical_localized_submodule_image_eq_concrete_localized
    (I := I) (S := S) (locMap := locMap) (Kbar := (K'.restrictScalars (R ⧸ I)).comap locMap)]
  -- The inverse-image relation localizes back to the original relation by the owner adjunction.
  simpa using restricted_comap_localized_eq_original (I := I) (S := S) (locMap := locMap) K'

/-- Helper for Lemma 10.126.3: any denominator-clearing equality for the concrete `localized'`
relation submodule upgrades to the canonical `hKmap` equality needed for quotient localization. -/
lemma lifted_relation_span_hKmap
    {n : ℕ}
    (locMap : (Fin n → R ⧸ I) →ₗ[(R ⧸ I)] (Fin n → R')) [IsLocalizedModule Sbar locMap]
    (Kbar : Submodule (R ⧸ I) (Fin n → R ⧸ I))
    (K' : Submodule R' (Fin n → R'))
    (hlocalized : Kbar.localized' R' Sbar locMap = K') :
    (Kbar.localized Sbar).map
        (((IsLocalizedModule.iso Sbar locMap).extendScalarsOfIsLocalization Sbar R').toLinearMap) =
      K' := by
  -- Route correction: transport once from the canonical localized submodule to `localized'`,
  -- and then reuse the denominator-clearing comparison without further coercion rewriting.
  rw [canonical_localized_submodule_image_eq_concrete_localized
    (I := I) (S := S) (locMap := locMap) (Kbar := Kbar)]
  exact hlocalized

/-- Helper for Lemma 10.126.3: once the reduction and localization comparisons are in place for a
finite free presentation, the quotient-after-mod-`I` localizes to the target quotient over `R'`. -/
lemma free_pi_localized_quotient_chain
    {n : ℕ}
    (K : Submodule R (Fin n → R))
    (Kbar : Submodule (R ⧸ I) (Fin n → R ⧸ I))
    (K' : Submodule R' (Fin n → R'))
    (hreduce : K.map (((Ideal.Quotient.mkₐ R I).toLinearMap).compLeft (Fin n)) =
      Kbar.restrictScalars R)
    (hKmap : ((Kbar.localized Sbar).map
      ((LinearEquiv.extendScalarsOfIsLocalization Sbar R'
        (IsLocalizedModule.iso Sbar (free_pi_localizedMap (I := I) (S := S) n))).toLinearMap)) = K') :
    Nonempty (LocalizedModule Sbar ((((Fin n → R) ⧸ K) ⧸
      (I • (⊤ : Submodule R ((Fin n → R) ⧸ K))))) ≃ₗ[R'] ((Fin n → R') ⧸ K')) := by
  rcases quotient_by_lifted_relations_reduce_mod_ideal_equiv
      (I := I) (K := K) (Kbar := Kbar) hreduce with ⟨ereduce⟩
  rcases localized_free_pi_quotient_equiv
      (I := I) (S := S) (locMap := free_pi_localizedMap (I := I) (S := S) n)
      Kbar K' hKmap with ⟨elocalized⟩
  let ereduceLoc :
      LocalizedModule Sbar ((((Fin n → R) ⧸ K) ⧸
        (I • (⊤ : Submodule R ((Fin n → R) ⧸ K))))) ≃ₗ[R']
        LocalizedModule Sbar ((Fin n → R ⧸ I) ⧸ Kbar) :=
    IsLocalizedModule.mapEquiv Sbar
      (LocalizedModule.mkLinearMap Sbar ((((Fin n → R) ⧸ K) ⧸
        (I • (⊤ : Submodule R ((Fin n → R) ⧸ K))))))
      (LocalizedModule.mkLinearMap Sbar ((Fin n → R ⧸ I) ⧸ Kbar))
      R' ereduce
  -- The source proof localizes the quotient comparison and then composes with the localized
  -- quotient over the finite free `R'`-module.
  exact ⟨ereduceLoc.trans elocalized⟩

/- Domain triage:
* primary domain: localization of quotient modules over a commutative ring;
* sampled owner declarations in this domain:
  `localizedQuotientEquiv`,
  `Module.FinitePresentation.exists_lift_of_isLocalizedModule`,
  `exists_finitePresentation_module_with_localizedLinearEquiv`;
* owner abstraction for the comparison data: existence of a `LinearEquiv`;
* primitive data: an `R`-module `M`;
* derived API: the localized quotient `LocalizedModule Sbar (M ⧸ (I • ⊤))`.

This item remains `source-facing`: it asserts existence of an `R`-module whose quotient modulo `I`
localizes to the given `R'`-module. The refinement here is only to expose the two source clauses as
direct binder-style theorem statements with `Nonempty` linear-equivalence witnesses, with the
lifted module kept in the same universe as the target `R'`-module.
-/
-- Proof sketch: for clause (1), first realize the finite `R'`-module as the localization of a
-- finite `(R ⧸ I)`-module and then regard that quotient module as coming from an `R`-module modulo
-- `I`. For clause (2), choose a finite presentation matrix over `R'`, clear denominators to lift
-- it to a matrix over `R`, and compare the resulting quotient after modding out by `I` and
-- localizing.
/-- Lemma 10.126.3 (1): every finite `R'`-module, where
`R' = Localization (Submonoid.map (Ideal.Quotient.mk I) S) = S⁻¹(R ⧸ I)`, is obtained from a
finite `R`-module by reducing modulo `I` and localizing at `S`. -/
theorem exists_finite_module_with_localizedQuotientLinearEquiv
    (M' : Type v) [AddCommGroup M'] [Module R' M'] [Module.Finite R' M'] :
    ∃ (M : Type v) (_ : AddCommGroup M) (_ : Module R M) (_ : Module.Finite R M),
      Nonempty (LocalizedModule Sbar (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R'] M') := by
  letI : Module (R ⧸ I) M' := Module.compHom M' (algebraMap (R ⧸ I) R')
  letI : Module R M' := Module.compHom M' (algebraMap R R')
  letI : IsScalarTower (R ⧸ I) R' M' := RestrictScalars.isScalarTower (R ⧸ I) R' M'
  letI : IsScalarTower R (R ⧸ I) M' := RestrictScalars.isScalarTower R (R ⧸ I) M'
  letI : IsLocalizedModule Sbar (LinearMap.id : M' →ₗ[(R ⧸ I)] M') :=
    isLocalizedModule_id (R := R ⧸ I) (S := Sbar) (M := M') R'
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := R') (M := M')
  let N : Submodule (R ⧸ I) M' := Submodule.span (R ⧸ I) (Set.range x)
  have hNfinite' : Module.Finite (R ⧸ I) N := by
    -- The source generators define a small finite `(R ⧸ I)`-submodule inside `M'`.
    simpa [N] using Module.Finite.span_of_finite (R ⧸ I) (Set.finite_range x)
  letI : Module.Finite (R ⧸ I) N := hNfinite'
  have hNfinite : Module.Finite R N := by
    -- Restrict scalars along the surjection `R → R ⧸ I`.
    letI : Module.Finite R (⊤ : Submodule R N) := Module.Finite.of_fg <| by
      simpa using Submodule.FG.restrictScalars_of_surjective
        (R := R) (A := R ⧸ I) (M := N) (S := (⊤ : Submodule (R ⧸ I) N))
        (Module.Finite.fg_top (R := R ⧸ I) (M := N)) Ideal.Quotient.mk_surjective
    exact Module.Finite.equiv (Submodule.topEquiv : (⊤ : Submodule R N) ≃ₗ[R] N)
  have hNlocTop : N.localized' R' Sbar (LinearMap.id : M' →ₗ[(R ⧸ I)] M') = ⊤ := by
    -- Route correction: follow the source proof inside `M'` itself, so localization of the span
    -- of the chosen generators is the whole target module.
    dsimp [N]
    rw [Submodule.localized'_span]
    simpa using hx
  let eQuot :
      (N ⧸ (I • ⊤ : Submodule R N)) ≃ₗ[R ⧸ I] N :=
    (quotient_module_quotient_equiv (I := I) (Q := N)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let eQuotLoc :
      LocalizedModule Sbar (N ⧸ (I • ⊤ : Submodule R N)) ≃ₗ[R'] LocalizedModule Sbar N :=
    IsLocalizedModule.mapEquiv Sbar
      (LocalizedModule.mkLinearMap Sbar (N ⧸ (I • ⊤ : Submodule R N)))
      (LocalizedModule.mkLinearMap Sbar N) R' eQuot
  let eLocalized :
      LocalizedModule Sbar N ≃ₗ[R'] N.localized' R' Sbar
        (LinearMap.id : M' →ₗ[(R ⧸ I)] M') :=
    (IsLocalizedModule.iso Sbar
      (Submodule.toLocalized' (S := R') (p := Sbar)
        (f := (LinearMap.id : M' →ₗ[(R ⧸ I)] M')) N)).extendScalarsOfIsLocalization Sbar R'
  let eTop :
      N.localized' R' Sbar (LinearMap.id : M' →ₗ[(R ⧸ I)] M') ≃ₗ[R'] M' :=
    (LinearEquiv.ofEq _ _ hNlocTop).trans Submodule.topEquiv
  -- Compose: quotient by `I` is harmless on `N`, then localize `N`, then identify the localized
  -- span with the whole target module `M'`.
  exact ⟨N, inferInstance, inferInstance, hNfinite,
    ⟨eQuotLoc.trans (eLocalized.trans eTop)⟩⟩

/-- Lemma 10.126.3 (2): every finitely presented `R'`-module is obtained from a finitely
presented `R`-module by reducing modulo `I` and localizing at `S`. -/
theorem exists_finitePresentation_module_with_localizedQuotientLinearEquiv
    (M' : Type v) [AddCommGroup M'] [Module R' M'] [Module.FinitePresentation R' M'] :
    ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module R M)
      (_ : Module.FinitePresentation R M),
      Nonempty (LocalizedModule Sbar (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R'] M') := by
  -- Route correction: the denominator-clearing bridge, the quotient/localization transport, and
  -- the final `ULift` comparison are now isolated in named helpers above. The remaining source
  -- step is to construct the lifted relation submodule over `R`, verify the `hKmap` hypothesis for
  -- `localized_free_pi_quotient_equiv`, and then compose the resulting equivalences.
  classical
  obtain ⟨n, K', e', hK'fg⟩ := Module.FinitePresentation.exists_fin R' M'
  obtain ⟨T, hT⟩ := hK'fg
  let locMap : (Fin n → R ⧸ I) →ₗ[(R ⧸ I)] (Fin n → R') :=
    free_pi_localizedMap (I := I) (S := S) n
  let Tbar : Finset (Fin n → R ⧸ I) := IsLocalizedModule.finsetIntegerMultiple Sbar locMap T
  let Kbar : Submodule (R ⧸ I) (Fin n → R ⧸ I) := Submodule.span (R ⧸ I) (Tbar : Set _)
  have hlocalized :
      Kbar.localized' R' Sbar locMap = K' := by
    -- Clearing denominators on finitely many relations over `R'` produces a relation submodule
    -- over `R ⧸ I` whose localization is exactly the original one.
    calc
      Kbar.localized' R' Sbar locMap = Submodule.span R' (T : Set (Fin n → R')) := by
        simpa [Kbar, Tbar, locMap] using
          localized_span_of_cleared_relation_generators
            (I := I) (S := S) (locMap := free_pi_localizedMap (I := I) (S := S) n) T
      _ = K' := hT
  let reduce : (Fin n → R) →ₗ[R] (Fin n → R ⧸ I) :=
    ((Ideal.Quotient.mkₐ R I).toLinearMap).compLeft (Fin n)
  have hreduce_surj : Function.Surjective reduce := by
    -- The coordinatewise reduction map is surjective because every quotient coordinate lifts.
    intro y
    choose x hx using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨fun i => x i, ?_⟩
    ext i
    exact hx i
  choose lift hlift using fun t : Tbar => hreduce_surj t
  let K : Submodule R (Fin n → R) := Submodule.span R (Set.range lift)
  have hreduce :
      K.map (((Ideal.Quotient.mkₐ R I).toLinearMap).compLeft (Fin n)) =
        Kbar.restrictScalars R := by
    -- The lifted relations reduce back to the cleared relations by construction.
    simpa [K, Kbar, reduce] using
      lifted_relation_span_maps_to_cleared_relation_span
        (I := I) (Tbar := Tbar) lift hlift
  have hKfg : K.FG := by
    -- The lifted relation submodule is spanned by finitely many chosen lifts.
    simpa [K] using (Submodule.fg_span (R := R) (Set.finite_range lift))
  let Q : Type u := (Fin n → R) ⧸ K
  letI : Module.FinitePresentation R Q := by
    -- Quotients of finite free modules by finitely generated relation submodules are finitely
    -- presented.
    exact Module.finitePresentation_of_surjective K.mkQ K.mkQ_surjective <| by
      simpa [Q, Submodule.ker_mkQ] using hKfg
  have hKmap :
      ((Kbar.localized Sbar).map
        ((LinearEquiv.extendScalarsOfIsLocalization Sbar R'
          (IsLocalizedModule.iso Sbar (free_pi_localizedMap (I := I) (S := S) n))).toLinearMap)) =
        K' := by
    -- The concrete localized relation equality upgrades to the canonical `hKmap` comparison used
    -- by the quotient-localization bridge.
    simpa [locMap] using
      lifted_relation_span_hKmap
        (I := I) (S := S) (locMap := free_pi_localizedMap (I := I) (S := S) n)
        Kbar K' hlocalized
  rcases free_pi_localized_quotient_chain
      (I := I) (S := S) (K := K) (Kbar := Kbar) (K' := K') hreduce hKmap with ⟨eQ⟩
  let M : Type (max u v) := ULift.{v} Q
  let eM : M ≃ₗ[R] Q := ULift.moduleEquiv
  letI : Module.FinitePresentation R M := Module.FinitePresentation.of_equiv eM.symm
  rcases localized_quotient_ulift_equiv (I := I) (S := S) (M := Q) with ⟨eUlift⟩
  -- Compose the `ULift` comparison, the quotient/localization bridge, and the presentation
  -- equivalence of `M'`.
  exact ⟨M, inferInstance, inferInstance, inferInstance, ⟨eUlift.trans (eQ.trans e'.symm)⟩⟩

end

/-! ### Lemma_10_126_4 (from Chap10) -/
universe u v w

section

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: choose finitely many elements of `M` whose images generate `LocalizedModule S M`
-- over `Localization S`, and let `M'` be the submodule they generate. Then the localized
-- submodule `M'.localized S` is all of `LocalizedModule S M`.
/-- Lemma 10.126.4 (1): if the localization `S⁻¹M` is finite over `S⁻¹R`, then some finitely
generated submodule of `M` has the same localization as `M`. -/
theorem exists_finite_submodule_with_top_localized
    [Module.Finite (Localization S) (LocalizedModule S M)] :
    ∃ M' : Submodule R M,
      Module.Finite R M' ∧
        M'.localized S = ⊤ := by
  classical
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := Localization S) (M := LocalizedModule S M)
  choose yt ht using
    fun i : Fin n ↦ IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M) (x i)
  let y : Fin n → M := fun i ↦ (yt i).1
  let t : Fin n → S := fun i ↦ (yt i).2
  let M' : Submodule R M := Submodule.span R (Set.range y)
  refine ⟨M', ?_, ?_⟩
  · -- The chosen numerators generate `M'`, so `M'` is finite over `R`.
    rw [Module.Finite.iff_fg]
    exact Submodule.fg_span (Set.finite_range y)
  · -- The localized numerators span the localized generators, hence all of `S⁻¹M`.
    apply top_le_iff.mp
    rw [← hx]
    rw [show M'.localized S =
      Submodule.span (Localization S)
        ((LocalizedModule.mkLinearMap S M) '' Set.range y) by
          simpa [M'] using
            (Submodule.localized'_span (Localization S) S (LocalizedModule.mkLinearMap S M)
              (Set.range y))]
    refine Submodule.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨i, rfl⟩
    rw [SetLike.mem_coe, ← IsLocalization.smul_mem_iff (s := t i)]
    rw [← (IsLocalizedModule.mk'_eq_iff (f := LocalizedModule.mkLinearMap S M)).mp (ht i)]
    exact Submodule.subset_span ⟨y i, ⟨i, rfl⟩, rfl⟩

/-- Helper for Lemma 10.126.4: after localizing a surjective presentation, its kernel is finite
because it sits in a short exact sequence with finite middle term and finitely presented cokernel. -/
lemma localized_kernel_finite_of_surjective_presentation
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M)
    (hπ : Function.Surjective (LocalizedModule.map S π))
    [Module.Finite (Localization S) (LocalizedModule S F)]
    [Module.FinitePresentation (Localization S) (LocalizedModule S M)] :
    Module.Finite (Localization S) (LinearMap.ker (LocalizedModule.map S π)) := by
  -- The localized kernel-subtype map is exact with the localized presentation map.
  have hExact :
      Function.Exact (LinearMap.ker (LocalizedModule.map S π)).subtype
        (LocalizedModule.map S π) := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
  exact Module.Finite.of_exact_of_finitePresentation
    (LinearMap.ker (LocalizedModule.map S π)).subtype
    (LocalizedModule.map S π)
    (Submodule.injective_subtype _)
    hπ
    hExact

/-- Helper for Lemma 10.126.4: if a submodule localizes to the whole localized module, then the
localized inclusion map is surjective. -/
lemma localized_subtype_range_eq_top_of_top_localized
    {K : Type*} [AddCommGroup K] [Module R K]
    (N : Submodule R K)
    (hN : N.localized S = ⊤) :
    LinearMap.range (LocalizedModule.map S N.subtype) = ⊤ := by
  -- Rewrite the target as surjectivity and pull a localized numerator back through `hN`.
  exact LinearMap.range_eq_top.2 <| by
    intro z
    have hz : z ∈ N.localized S := by
      simpa [hN] using
        (show z ∈ (⊤ : Submodule (Localization S) (LocalizedModule S K)) from trivial)
    rcases (Submodule.mem_localized'
        (S := Localization S) (p := S) (f := LocalizedModule.mkLinearMap S K) (M' := N) z).mp hz
      with ⟨x, hx, s, rfl⟩
    refine ⟨LocalizedModule.mk ⟨x, hx⟩ s, ?_⟩
    simpa [IsLocalizedModule.mk_eq_mk'] using
      (LocalizedModule.map_mk (S := S) N.subtype ⟨x, hx⟩ s)

/-- Helper for Lemma 10.126.4: if `N` already localizes to the whole source, then localizing the
image of `N` under a linear map recovers the full localized image. -/
lemma localized_image_of_top_localized_submodule
    {K : Type*} [AddCommGroup K] [Module R K]
    {F : Type*} [AddCommGroup F] [Module R F]
    (ι : K →ₗ[R] F)
    (N : Submodule R K)
    (hN : N.localized S = ⊤) :
    (N.map ι).localized S = LinearMap.range (LocalizedModule.map S ι) := by
  apply le_antisymm
  · -- Every localized image element comes from a localized source element in `N`.
    intro z hz
    rcases (Submodule.mem_localized'
        (S := Localization S) (p := S) (f := LocalizedModule.mkLinearMap S F) (M' := N.map ι) z).mp
        hz with ⟨x, hx, s, rfl⟩
    rcases hx with ⟨y, hy, rfl⟩
    refine ⟨LocalizedModule.mk y s, ?_⟩
    simpa [IsLocalizedModule.mk_eq_mk'] using
      (LocalizedModule.map_mk (S := S) ι y s)
  · -- Conversely, use `hN` to rewrite any localized source element with numerator in `N`.
    rintro z ⟨y, rfl⟩
    have hy : y ∈ N.localized S := by
      simpa [hN] using (show y ∈ (⊤ : Submodule (Localization S) (LocalizedModule S K)) from trivial)
    rcases (Submodule.mem_localized'
        (S := Localization S) (p := S) (f := LocalizedModule.mkLinearMap S K) (M' := N) y).mp hy
      with ⟨x, hx, s, hs⟩
    rw [← hs]
    exact (Submodule.mem_localized'
      (S := Localization S) (p := S) (f := LocalizedModule.mkLinearMap S F) (M' := N.map ι)
      (((LocalizedModule.map S) ι) (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S K) x s))).2
      ⟨ι x, ⟨x, hx, rfl⟩, s, by
        exact
          (IsLocalizedModule.map_mk'
            (S := S)
            (f := LocalizedModule.mkLinearMap S K)
            (g := LocalizedModule.mkLinearMap S F)
            ι x s).symm⟩

/-- Helper for Lemma 10.126.4: if a finite submodule of the kernel localizes to all of the
localized kernel module, then its image in the ambient module localizes to the localized kernel
submodule of the presentation. -/
lemma kernel_image_localized_eq_localized_kernel
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M)
    (Ksub : Submodule R (LinearMap.ker π))
    (hKsub : Ksub.localized S = ⊤) :
    (Ksub.map (LinearMap.ker π).subtype).localized S = (LinearMap.ker π).localized' (Localization S)
      S (LocalizedModule.mkLinearMap S F) := by
  -- First localize the finite kernel submodule inside the ambient free module.
  calc
    (Ksub.map (LinearMap.ker π).subtype).localized S =
        LinearMap.range (LocalizedModule.map S (LinearMap.ker π).subtype) := by
      simpa using
        localized_image_of_top_localized_submodule
          (S := S) (LinearMap.ker π).subtype Ksub hKsub
    _ = (LinearMap.ker π).localized' (Localization S) S (LocalizedModule.mkLinearMap S F) := by
      -- Then identify that localized range with the localized kernel by taking `N = ⊤`.
      symm
      simpa [Submodule.localized, Submodule.map_top, Submodule.range_subtype] using
        localized_image_of_top_localized_submodule
          (S := S) (LinearMap.ker π).subtype (⊤ : Submodule R (LinearMap.ker π))
          (by simp [Submodule.localized])

/-- Helper for Lemma 10.126.4: the inverse of `localizedQuotientEquiv` sends a localized quotient
generator to the quotient class of the localized numerator. -/
lemma localized_quotient_equiv_symm_apply_mk
    {F : Type*} [AddCommGroup F] [Module R F]
    (K0 : Submodule R F) (x : F) :
    (localizedQuotientEquiv S K0).symm
      (LocalizedModule.mkLinearMap S (F ⧸ K0) (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk (LocalizedModule.mkLinearMap S F x) := by
  -- The canonical localization equivalence is characterized by its action on quotient generators.
  simpa [localizedQuotientEquiv, Submodule.toLocalizedQuotient] using
    (IsLocalizedModule.linearEquiv_symm_apply
      (S := S)
      (f := K0.toLocalizedQuotient S)
      (g := LocalizedModule.mkLinearMap S (F ⧸ K0))
      (x := Submodule.Quotient.mk x))

/-- Helper for Lemma 10.126.4: the full quotient-comparison composite sends each localized quotient
generator to the corresponding localized image under the presentation map. -/
lemma localized_quotient_comparison_apply_mk
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M)
    (K0 : Submodule R F)
    (hkerloc : K0.localized S = LinearMap.ker (LocalizedModule.map S π))
    (hπ : Function.Surjective (LocalizedModule.map S π))
    (x : F) :
    (((localizedQuotientEquiv S K0).symm ≪≫ₗ
        Submodule.quotEquivOfEq _ _ hkerloc ≪≫ₗ
        (LocalizedModule.map S π).quotKerEquivOfSurjective hπ)
      (LocalizedModule.mkLinearMap S (F ⧸ K0) (Submodule.Quotient.mk x))) =
        LocalizedModule.mkLinearMap S M (π x) := by
  -- Route correction: compute the whole quotient comparison on generators before comparing maps.
  simp only [LinearEquiv.trans_apply]
  rw [localized_quotient_equiv_symm_apply_mk]
  rw [Submodule.quotEquivOfEq_mk]
  simpa using
    (LinearMap.quotKerEquivOfSurjective_apply_mk
      (f := LocalizedModule.map S π)
      (hf := hπ)
      (x := LocalizedModule.mkLinearMap S F x))

/-- Helper for Lemma 10.126.4: if the localized relation submodule agrees with the localized
kernel of a presentation, then the induced map on the quotient becomes an isomorphism after
localization. -/
lemma localized_quotient_equiv_of_surjective_and_kernel_match
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M)
    (K0 : Submodule R F)
    (fbar : F ⧸ K0 →ₗ[R] M)
    (hπ : Function.Surjective (LocalizedModule.map S π))
    (hfbar : fbar.comp (Submodule.mkQ K0) = π)
    (hK0 : K0.localized S = (LinearMap.ker π).localized' (Localization S) S
      (LocalizedModule.mkLinearMap S F)) :
    ∃ e : LocalizedModule S (F ⧸ K0) ≃ₗ[Localization S] LocalizedModule S M,
      e.toLinearMap = LocalizedModule.map S fbar := by
  have hkerloc : K0.localized S = LinearMap.ker (LocalizedModule.map S π) := by
    -- Rewrite the localized relation module into the actual kernel of the localized presentation.
    calc
      K0.localized S = (LinearMap.ker π).localized' (Localization S) S
          (LocalizedModule.mkLinearMap S F) := hK0
      _ = LinearMap.ker (LocalizedModule.map S π) := by
        simpa using
          (LinearMap.localized'_ker_eq_ker_localizedMap
            (S := Localization S)
            (p := S)
            (f := LocalizedModule.mkLinearMap S F)
            (f' := LocalizedModule.mkLinearMap S M)
            (g := π))
  let e : LocalizedModule S (F ⧸ K0) ≃ₗ[Localization S] LocalizedModule S M :=
    (localizedQuotientEquiv S K0).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hkerloc ≪≫ₗ
      (LocalizedModule.map S π).quotKerEquivOfSurjective hπ
  refine ⟨e, ?_⟩
  have hcomp :
      e.toLinearMap.restrictScalars R ∘ₗ LocalizedModule.mkLinearMap S (F ⧸ K0) =
        (LocalizedModule.map S fbar).restrictScalars R ∘ₗ LocalizedModule.mkLinearMap S (F ⧸ K0) := by
    ext x
    -- Compare both maps on the quotient generators coming from `F`.
    change e (LocalizedModule.mkLinearMap S (F ⧸ K0) (Submodule.Quotient.mk x)) =
      (LocalizedModule.map S fbar) (LocalizedModule.mkLinearMap S (F ⧸ K0) (Submodule.Quotient.mk x))
    rw [localized_quotient_comparison_apply_mk
      (S := S) (π := π) (K0 := K0) (hkerloc := hkerloc) (hπ := hπ) (x := x)]
    have hfbar_apply : fbar (Submodule.Quotient.mk x) = π x := by
      exact LinearMap.congr_fun hfbar x
    simpa [hfbar_apply] using
      (IsLocalizedModule.map_apply
        (S := S)
        (f := LocalizedModule.mkLinearMap S (F ⧸ K0))
        (g := LocalizedModule.mkLinearMap S M)
        (h := fbar)
        (x := Submodule.Quotient.mk x))
  have hEqR :
      e.toLinearMap.restrictScalars R = (LocalizedModule.map S fbar).restrictScalars R := by
    exact IsLocalizedModule.linearMap_ext
      (S := S)
      (LocalizedModule.mkLinearMap S (F ⧸ K0))
      (LocalizedModule.mkLinearMap S M)
      hcomp
  -- Equality after restricting scalars already determines the localized linear map.
  ext x
  exact LinearMap.congr_fun hEqR x

/-- Helper for Lemma 10.126.4: if the localized presentation map is surjective and its localized
kernel is finite, then the localization of the source-side kernel is finite as well. -/
lemma source_kernel_localized_finite_of_surjective_presentation
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M)
    (hπ : Function.Surjective (LocalizedModule.map S π))
    [Module.Finite (Localization S) (LocalizedModule S F)]
    [Module.FinitePresentation (Localization S) (LocalizedModule S M)] :
    Module.Finite (Localization S) (LocalizedModule S (LinearMap.ker π)) := by
  let κ : LinearMap.ker π →ₗ[R] LinearMap.ker (LocalizedModule.map S π) :=
    LinearMap.toKerIsLocalized
      (p := S)
      (f := LocalizedModule.mkLinearMap S F)
      (f' := LocalizedModule.mkLinearMap S M)
      π
  let _ : IsLocalizedModule S κ :=
    LinearMap.toKerLocalized_isLocalizedModule
      (S := Localization S)
      (p := S)
      (f := LocalizedModule.mkLinearMap S F)
      (f' := LocalizedModule.mkLinearMap S M)
      π
  let _ : Module.Finite (Localization S) (LinearMap.ker (LocalizedModule.map S π)) :=
    localized_kernel_finite_of_surjective_presentation (S := S) π hπ
  -- Transfer finiteness back across the canonical localization equivalence on kernels.
  exact Module.Finite.equiv
    (LinearEquiv.extendScalarsOfIsLocalization
      (S := S)
      (A := Localization S)
      (IsLocalizedModule.iso S κ)).symm

/-- Helper for Lemma 10.126.4: the kernel of the source presentation contains a finite submodule
whose localization is the entire localized kernel module. -/
lemma exists_finite_kernel_submodule_with_top_localized
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M)
    (hπ : Function.Surjective (LocalizedModule.map S π))
    [Module.Finite (Localization S) (LocalizedModule S F)]
    [Module.FinitePresentation (Localization S) (LocalizedModule S M)] :
    ∃ Ksub : Submodule R (LinearMap.ker π),
      Module.Finite R Ksub ∧
        Ksub.localized S = ⊤ := by
  let _ : Module.Finite (Localization S) (LocalizedModule S (LinearMap.ker π)) :=
    source_kernel_localized_finite_of_surjective_presentation (S := S) π hπ
  -- Apply part (1) to the source kernel module itself.
  exact exists_finite_submodule_with_top_localized (S := S) (M := LinearMap.ker π)

/-- Helper for Lemma 10.126.4: the image of a submodule of `ker π` still lies in `ker π`, so the
presentation map descends to the quotient by that image. -/
lemma kernel_submodule_image_le_ker
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M)
    (Ksub : Submodule R (LinearMap.ker π)) :
    Ksub.map (LinearMap.ker π).subtype ≤ LinearMap.ker π := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact y.2

-- Proof sketch: choose generators `x₁, ..., xₙ` of `LocalizedModule S M`, let
-- `Rⁿ → M` send the standard basis to these elements, and localize its kernel. By the finite case,
-- replace that localized kernel by a finite submodule `K'` of the original kernel with the same
-- localization. Then take `M' := (Fin n → R) ⧸ K'`; this module is finitely presented and its map
-- to `M` becomes a linear equivalence after localizing at `S`.
/-- Lemma 10.126.4 (2): if the localization `S⁻¹M` is finitely presented over `S⁻¹R`, then it is
the localization of a finitely presented `R`-module mapping to `M`. -/
theorem exists_finitePresentation_module_with_localizedLinearEquiv
    [Module.FinitePresentation (Localization S) (LocalizedModule S M)] :
    ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module R M') (_ : Module.FinitePresentation R M')
      (f : M' →ₗ[R] M)
      (e : LocalizedModule S M' ≃ₗ[Localization S] LocalizedModule S M),
      e.toLinearMap = LocalizedModule.map S f := by
  classical
  let _ : Module.Finite (Localization S) (LocalizedModule S M) := inferInstance
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := Localization S) (M := LocalizedModule S M)
  choose yt ht using
    fun i : Fin n ↦ IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M) (x i)
  let y : Fin n → M := fun i ↦ (yt i).1
  let t : Fin n → S := fun i ↦ (yt i).2
  let M0 : Submodule R M := Submodule.span R (Set.range y)
  have hM0_finite : Module.Finite R M0 := by
    -- The chosen numerators generate `M0`.
    rw [Module.Finite.iff_fg]
    simpa [M0] using Submodule.fg_span (Set.finite_range y)
  have hM0_top : M0.localized S = ⊤ := by
    -- The localized numerators already span the given localized generators.
    apply top_le_iff.mp
    rw [← hx]
    rw [show M0.localized S =
      Submodule.span (Localization S)
        ((LocalizedModule.mkLinearMap S M) '' Set.range y) by
          simpa [M0] using
            (Submodule.localized'_span (Localization S) S (LocalizedModule.mkLinearMap S M)
              (Set.range y))]
    refine Submodule.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨i, rfl⟩
    rw [SetLike.mem_coe, ← IsLocalization.smul_mem_iff (s := t i)]
    rw [← (IsLocalizedModule.mk'_eq_iff (f := LocalizedModule.mkLinearMap S M)).mp (ht i)]
    exact Submodule.subset_span ⟨y i, ⟨i, rfl⟩, rfl⟩
  obtain ⟨m, π0, hπ0⟩ := Module.Finite.exists_fin' R M0
  let π : (Fin m → R) →ₗ[R] M := M0.subtype ∘ₗ π0
  have hM0_surj : Function.Surjective (LocalizedModule.map S M0.subtype) := by
    -- Localizing the inclusion of `M0` is surjective because `M0.localized S = ⊤`.
    exact LinearMap.range_eq_top.1
      (localized_subtype_range_eq_top_of_top_localized (S := S) M0 hM0_top)
  have hπ0_surj : Function.Surjective (LocalizedModule.map S π0) :=
    LocalizedModule.map_surjective S π0 hπ0
  have hπ_surj : Function.Surjective (LocalizedModule.map S π) := by
    -- Surjectivity survives composition after localizing the free cover of `M0`.
    intro z
    obtain ⟨z0, hz0⟩ := hM0_surj z
    obtain ⟨w, hw⟩ := hπ0_surj z0
    refine ⟨w, ?_⟩
    calc
      (LocalizedModule.map S π) w
          = (LocalizedModule.map S M0.subtype) ((LocalizedModule.map S π0) w) := by
              simpa [π] using
                LinearMap.congr_fun
                  (IsLocalizedModule.map_comp'
                    (S := S)
                    (f₀ := LocalizedModule.mkLinearMap S (Fin m → R))
                    (f₁ := LocalizedModule.mkLinearMap S M0)
                    (f₂ := LocalizedModule.mkLinearMap S M)
                    π0 M0.subtype)
                  w
      _ = (LocalizedModule.map S M0.subtype) z0 := by rw [hw]
      _ = z := hz0
  let _ : Module.Finite (Localization S) (LocalizedModule S (Fin m → R)) := inferInstance
  obtain ⟨Ksub, hKsub_finite, hKsub_top⟩ :=
    exists_finite_kernel_submodule_with_top_localized (S := S) (π := π) hπ_surj
  let K0 : Submodule R (Fin m → R) := Ksub.map (LinearMap.ker π).subtype
  let fbar : (Fin m → R) ⧸ K0 →ₗ[R] M :=
    K0.liftQ π (kernel_submodule_image_le_ker (π := π) Ksub)
  have hfbar : fbar.comp (Submodule.mkQ K0) = π := by
    -- The descended quotient map is defined to agree with `π` on generators.
    simpa [fbar] using K0.liftQ_mkQ π (kernel_submodule_image_le_ker (π := π) Ksub)
  have hK0_fg : K0.FG := by
    let _ : Module.Finite R Ksub := hKsub_finite
    have hKsub_fg : Ksub.FG :=
      Submodule.FG.of_finite (R := R) (M := LinearMap.ker π) (N := Ksub)
    -- Finite generation is preserved when we map the descended relation module into the free one.
    simpa [K0] using
      Submodule.FG.map (LinearMap.ker π).subtype hKsub_fg
  let _ : Module.FinitePresentation R ((Fin m → R) ⧸ K0) :=
    Module.finitePresentation_of_surjective (Submodule.mkQ K0) (Submodule.mkQ_surjective _) <| by
      -- The kernel of the quotient map is exactly the relation submodule `K0`.
      change (LinearMap.ker (Submodule.mkQ K0)).FG
      simpa using hK0_fg
  have hK0 :
      K0.localized S = (LinearMap.ker π).localized' (Localization S) S
        (LocalizedModule.mkLinearMap S (Fin m → R)) := by
    -- Localizing the descended relation submodule recovers the localized kernel of `π`.
    simpa [K0] using
      kernel_image_localized_eq_localized_kernel (S := S) (π := π) Ksub hKsub_top
  obtain ⟨e, he⟩ :=
    localized_quotient_equiv_of_surjective_and_kernel_match
      (S := S) (π := π) (K0 := K0) fbar hπ_surj hfbar hK0
  -- The quotient by the descended finite relation module is the desired finitely presented source.
  exact ⟨(Fin m → R) ⧸ K0, inferInstance, inferInstance, inferInstance, fbar, e, he⟩

end

/-! ### Lemma_10_126_5 (from Chap10) -/
universe u v w

section

variable {R : Type u} [CommRing R]
variable (p : Ideal R) [p.IsPrime]
variable {M : Type v} [AddCommGroup M] [Module R M]

local notation "Rₚ" => Localization.AtPrime p
local notation "Mₚ" => LocalizedModule.AtPrime p M

-- Proof sketch: this is the prime-ideal specialization of Lemma `10.126.4 (1)`, obtained by
-- taking the multiplicative set `p.primeCompl`. The resulting finitely generated submodule has
-- full localization at `p`.
/-- Lemma 10.126.5 (1): if `M_p` is finite over `R_p`, then there exists a finitely generated
submodule of `M` whose localization at `p` is isomorphic to `M_p`. -/
theorem exists_finite_submodule_with_top_localized_atPrime
    [Module.Finite Rₚ Mₚ] :
    ∃ M' : Submodule R M,
      Module.Finite R M' ∧
        M'.localized p.primeCompl = ⊤ := by
  simpa using
    (exists_finite_submodule_with_top_localized p.primeCompl :
      ∃ M' : Submodule R M,
        Module.Finite R M' ∧
          M'.localized p.primeCompl = ⊤)

-- Proof sketch: this is the prime-ideal specialization of Lemma `10.126.4 (2)`, again with the
-- multiplicative set `p.primeCompl`. A finitely presented model of `M_p` over `R` is produced
-- together with a map to `M` whose localization at `p` is identified with a linear equivalence.
/-- Lemma 10.126.5 (2): if `M_p` is finitely presented over `R_p`, then there exists a finitely
presented `R`-module mapping to `M` whose localization at `p` is isomorphic to `M_p`. -/
theorem exists_finitePresentation_module_with_localizedLinearEquiv_atPrime
    [Module.FinitePresentation Rₚ Mₚ] :
    ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module R M') (_ : Module.FinitePresentation R M')
      (f : M' →ₗ[R] M)
      (e : LocalizedModule.AtPrime p M' ≃ₗ[Rₚ] Mₚ),
      e.toLinearMap = LocalizedModule.map p.primeCompl f := by
  -- Specialize the finitely presented localization theorem to the prime-complement submonoid.
  simpa using
    (exists_finitePresentation_module_with_localizedLinearEquiv p.primeCompl :
      ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module R M')
        (_ : Module.FinitePresentation R M') (f : M' →ₗ[R] M)
        (e : LocalizedModule.AtPrime p M' ≃ₗ[Rₚ] Mₚ),
        e.toLinearMap = LocalizedModule.map p.primeCompl f)

end
