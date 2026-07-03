import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_106_4 (from Chap10) -/
universe u

open IsLocalRing
open Ideal

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Helper for Lemma 10.106.4: the residue field at the maximal ideal agrees with the ordinary
residue field of a local ring. -/
noncomputable def maximalIdealResidueFieldEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

/-- Helper for Lemma 10.106.4: the canonical equivalence from the maximal-ideal residue field
sends the image of `a` to the ordinary residue class of `a`. -/
theorem maximalIdealResidueFieldEquiv_apply_algebraMap
    (A : Type u) [CommRing A] [IsLocalRing A] (a : A) :
    maximalIdealResidueFieldEquiv A (algebraMap A (maximalIdeal A).ResidueField a) =
      residue A a := by
  -- The maximal-ideal residue-field model is inverse to the ordinary residue map.
  rw [show algebraMap A (maximalIdeal A).ResidueField a =
      algebraMap (ResidueField A) (maximalIdeal A).ResidueField (residue A a) by rfl]
  exact (maximalIdealResidueFieldEquiv A).apply_symm_apply (residue A a)

/-- Helper for Lemma 10.106.4: the maximal-ideal residue-field model is compatible with the
ordinary residue-field map induced by a local ring homomorphism. -/
theorem maximalIdealResidueFieldEquiv_comp_residueFieldMap
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] :
    (maximalIdealResidueFieldEquiv B).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (ResidueField.map f).comp (maximalIdealResidueFieldEquiv A).toRingHom := by
  -- Compare both residue-field maps on residue classes coming from the source ring.
  apply Ideal.ResidueField.ringHom_ext
  ext a
  change
    maximalIdealResidueFieldEquiv B
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm (algebraMap A (maximalIdeal A).ResidueField a)) =
      ResidueField.map f
        (maximalIdealResidueFieldEquiv A (algebraMap A (maximalIdeal A).ResidueField a))
  rw [Ideal.ResidueField.map_algebraMap, maximalIdealResidueFieldEquiv_apply_algebraMap,
    maximalIdealResidueFieldEquiv_apply_algebraMap, IsLocalRing.ResidueField.map_residue]

/-- Helper for Lemma 10.106.4: if the quotient `R ⧸ I` is a nontrivial local ring, then the ideal
`I` is contained in the maximal ideal of `R`. -/
lemma ideal_le_maximalIdeal_of_regular_quotient (I : Ideal R)
    (hquot : IsRegularLocalRing (R ⧸ I)) :
    I ≤ maximalIdeal R := by
  letI : IsRegularLocalRing (R ⧸ I) := hquot
  have hI_ne_top : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  -- A proper ideal of a local ring is contained in the maximal ideal.
  exact IsLocalRing.le_maximalIdeal hI_ne_top

/-- Helper for Lemma 10.106.4: the quotient map induces a surjective cotangent map at the
maximal ideals. This packages the source proof's surjection
`m / m² → m̄ / m̄²` before any residue-field scalar transport is applied. -/
lemma quotient_cotangent_map_surjective_of_regular_quotient (I : Ideal R)
    (hquot : IsRegularLocalRing (R ⧸ I)) :
    let Q := R ⧸ I
    ∃ h : maximalIdeal R ≤ Ideal.comap (algebraMap R Q) (maximalIdeal Q),
      Function.Surjective
        (Ideal.mapCotangent (maximalIdeal R) (maximalIdeal Q) (Algebra.ofId R Q) h) := by
  let Q := R ⧸ I
  letI : IsRegularLocalRing Q := hquot
  haveI : IsLocalHom (algebraMap R Q) :=
    IsLocalHom.of_surjective (algebraMap R Q) (by simpa [Q] using Ideal.Quotient.mk_surjective)
  have hI_le : I ≤ maximalIdeal R :=
    ideal_le_maximalIdeal_of_regular_quotient (R := R) I hquot
  let hle : maximalIdeal R ≤ Ideal.comap (algebraMap R Q) (maximalIdeal Q) :=
    (maximalIdeal_comap (algebraMap R Q)).symm.le
  have hcomap :
      Ideal.comap (algebraMap R Q) (maximalIdeal Q) =
        RingHom.ker (algebraMap R Q) ⊔ maximalIdeal R := by
    -- The quotient maximal ideal pulls back to `maximalIdeal R`, and the quotient kernel is `I`.
    rw [maximalIdeal_comap (algebraMap R Q), show RingHom.ker (algebraMap R Q) = I by
      simpa [Q] using Ideal.mk_ker (I := I)]
    exact (sup_eq_right.mpr hI_le).symm
  -- Route correction: keep the quotient-cotangent step at the canonical `Ideal.mapCotangent`
  -- level, rather than unfolding `(I + m^2) / m^2` by hand.
  refine ⟨hle, ?_⟩
  simpa [Q, hle] using
    (Ideal.mapCotangent_surjective_of_comap_eq
      (A := R) (B := Q)
      (surj := show Function.Surjective (algebraMap R Q) by simpa [Q] using Ideal.Quotient.mk_surjective)
      hcomap)

/-- Helper for Lemma 10.106.4: the kernel of the quotient cotangent map is exactly the cotangent
subspace represented by elements of `I`. This is the source proof's subspace
`(I + m²) / m²`, still expressed at the canonical `Ideal.mapCotangent` level. -/
lemma quotient_cotangent_map_ker_of_regular_quotient (I : Ideal R)
    (hquot : IsRegularLocalRing (R ⧸ I)) :
    let Q := R ⧸ I
    ∃ h : maximalIdeal R ≤ Ideal.comap (algebraMap R Q) (maximalIdeal Q),
      LinearMap.ker (Ideal.mapCotangent (maximalIdeal R) (maximalIdeal Q) (Algebra.ofId R Q) h) =
        Submodule.map (maximalIdeal R).toCotangent
          (Submodule.comap (Submodule.subtype (maximalIdeal R)) (I ⊓ maximalIdeal R)) := by
  let Q := R ⧸ I
  letI : IsRegularLocalRing Q := hquot
  haveI : IsLocalHom (algebraMap R Q) :=
    IsLocalHom.of_surjective (algebraMap R Q) (by simpa [Q] using Ideal.Quotient.mk_surjective)
  have hI_le : I ≤ maximalIdeal R :=
    ideal_le_maximalIdeal_of_regular_quotient (R := R) I hquot
  let hle : maximalIdeal R ≤ Ideal.comap (algebraMap R Q) (maximalIdeal Q) :=
    (maximalIdeal_comap (algebraMap R Q)).symm.le
  have hcomap :
      Ideal.comap (algebraMap R Q) (maximalIdeal Q) =
        RingHom.ker (algebraMap R Q) ⊔ maximalIdeal R := by
    -- The quotient maximal ideal pulls back to `maximalIdeal R`, and the quotient kernel is `I`.
    rw [maximalIdeal_comap (algebraMap R Q), show RingHom.ker (algebraMap R Q) = I by
      simpa [Q] using Ideal.mk_ker (I := I)]
    exact (sup_eq_right.mpr hI_le).symm
  -- The kernel formula is the specialization of the canonical quotient-cotangent kernel theorem.
  refine ⟨hle, ?_⟩
  simpa [Q, hle] using
    (Ideal.mapCotangent_ker_of_surjective
      (A := R) (B := Q)
      (surj := show Function.Surjective (algebraMap R Q) by simpa [Q] using Ideal.Quotient.mk_surjective)
      hcomap)

/-- Helper for Lemma 10.106.4: after transporting the quotient cotangent map to
`ResidueField R`, membership in its kernel is still exactly membership in the cotangent subspace
represented by elements of `I`. -/
lemma quotient_cotangent_mem_ker_iff_over_residueField (I : Ideal R)
    (hquot : IsRegularLocalRing (R ⧸ I)) :
    let Q := R ⧸ I
    letI : IsRegularLocalRing Q := hquot
    letI : IsLocalHom (algebraMap R Q) :=
      IsLocalHom.of_surjective (algebraMap R Q)
        (by simpa [Q] using Ideal.Quotient.mk_surjective)
    ∃ h : maximalIdeal R ≤ Ideal.comap (algebraMap R Q) (maximalIdeal Q),
      let hTorsQ : Module.IsTorsionBySet R (CotangentSpace Q) (maximalIdeal R) :=
        fun {x} {a} ↦ Ideal.Cotangent.smul_eq_zero_of_mem (I := maximalIdeal Q) (h a.2) x
      letI : Module (ResidueField R) (CotangentSpace Q) := Module.IsTorsionBySet.module hTorsQ
      letI : IsScalarTower R (ResidueField R) (CotangentSpace Q) :=
        Module.IsTorsionBySet.isScalarTower hTorsQ
      let φR : CotangentSpace R →ₗ[R] CotangentSpace Q :=
        Ideal.mapCotangent (maximalIdeal R) (maximalIdeal Q) (Algebra.ofId R Q) h
      let φ : CotangentSpace R →ₗ[ResidueField R] CotangentSpace Q :=
        φR.extendScalarsOfSurjective (residue_surjective (R := R))
      ∀ x : CotangentSpace R,
        x ∈ LinearMap.ker φ ↔
          x ∈ Submodule.map (maximalIdeal R).toCotangent
            (Submodule.comap (Submodule.subtype (maximalIdeal R)) (I ⊓ maximalIdeal R)) := by
  let Q := R ⧸ I
  letI : IsRegularLocalRing Q := hquot
  letI : IsLocalHom (algebraMap R Q) :=
    IsLocalHom.of_surjective (algebraMap R Q)
      (by simpa [Q] using Ideal.Quotient.mk_surjective)
  obtain ⟨h, hker⟩ :=
    quotient_cotangent_map_ker_of_regular_quotient (R := R) I hquot
  refine ⟨h, ?_⟩
  let hTorsQ : Module.IsTorsionBySet R (CotangentSpace Q) (maximalIdeal R) :=
    fun {x} {a} ↦ Ideal.Cotangent.smul_eq_zero_of_mem (I := maximalIdeal Q) (h a.2) x
  letI : Module (ResidueField R) (CotangentSpace Q) := Module.IsTorsionBySet.module hTorsQ
  letI : IsScalarTower R (ResidueField R) (CotangentSpace Q) :=
    Module.IsTorsionBySet.isScalarTower hTorsQ
  let φR : CotangentSpace R →ₗ[R] CotangentSpace Q :=
    Ideal.mapCotangent (maximalIdeal R) (maximalIdeal Q) (Algebra.ofId R Q) h
  let φ : CotangentSpace R →ₗ[ResidueField R] CotangentSpace Q :=
    φR.extendScalarsOfSurjective (residue_surjective (R := R))
  change ∀ x : CotangentSpace R,
      x ∈ LinearMap.ker φ ↔
        x ∈ Submodule.map (maximalIdeal R).toCotangent
          (Submodule.comap (Submodule.subtype (maximalIdeal R)) (I ⊓ maximalIdeal R))
  intro x
  constructor
  · intro hx
    have hxR : x ∈ LinearMap.ker φR := by
      -- The scalar extension changes only the linear structure, not the underlying function.
      simpa [φ, φR, LinearMap.mem_ker] using hx
    rwa [hker] at hxR
  · intro hx
    have hxR : x ∈ LinearMap.ker φR := by
      rwa [hker]
    simpa [φ, φR, LinearMap.mem_ker] using hxR

/-- Helper for Lemma 10.106.4: choose a finite basis of the cotangent kernel and lift each basis
vector to an element of `I ∩ maximalIdeal R`. -/
lemma exists_kernel_basis_lift_in_ideal (I : Ideal R)
    (hquot : IsRegularLocalRing (R ⧸ I))
    {h : maximalIdeal R ≤ Ideal.comap (algebraMap R (R ⧸ I)) (maximalIdeal (R ⧸ I))}
    (hker :
      let Q := R ⧸ I
      letI : IsRegularLocalRing Q := hquot
      letI : IsLocalHom (algebraMap R Q) :=
        IsLocalHom.of_surjective (algebraMap R Q)
          (by simpa [Q] using Ideal.Quotient.mk_surjective)
      let hTorsQ : Module.IsTorsionBySet R (CotangentSpace Q) (maximalIdeal R) :=
        fun {x} {a} ↦ Ideal.Cotangent.smul_eq_zero_of_mem (I := maximalIdeal Q) (h a.2) x
      letI : Module (ResidueField R) (CotangentSpace Q) := Module.IsTorsionBySet.module hTorsQ
      letI : IsScalarTower R (ResidueField R) (CotangentSpace Q) :=
        Module.IsTorsionBySet.isScalarTower hTorsQ
      let φR : CotangentSpace R →ₗ[R] CotangentSpace Q :=
        Ideal.mapCotangent (maximalIdeal R) (maximalIdeal Q) (Algebra.ofId R Q) h
      let φ : CotangentSpace R →ₗ[ResidueField R] CotangentSpace Q :=
        φR.extendScalarsOfSurjective (residue_surjective (R := R))
      ∀ x : CotangentSpace R,
        x ∈ LinearMap.ker φ ↔
          x ∈ Submodule.map (maximalIdeal R).toCotangent
            (Submodule.comap (Submodule.subtype (maximalIdeal R)) (I ⊓ maximalIdeal R))) :
    let Q := R ⧸ I
    letI : IsRegularLocalRing Q := hquot
    letI : IsLocalHom (algebraMap R Q) :=
      IsLocalHom.of_surjective (algebraMap R Q)
        (by simpa [Q] using Ideal.Quotient.mk_surjective)
    let hTorsQ : Module.IsTorsionBySet R (CotangentSpace Q) (maximalIdeal R) :=
      fun {x} {a} ↦ Ideal.Cotangent.smul_eq_zero_of_mem (I := maximalIdeal Q) (h a.2) x
    letI : Module (ResidueField R) (CotangentSpace Q) := Module.IsTorsionBySet.module hTorsQ
    letI : IsScalarTower R (ResidueField R) (CotangentSpace Q) :=
      Module.IsTorsionBySet.isScalarTower hTorsQ
    let φR : CotangentSpace R →ₗ[R] CotangentSpace Q :=
      Ideal.mapCotangent (maximalIdeal R) (maximalIdeal Q) (Algebra.ofId R Q) h
    let φ : CotangentSpace R →ₗ[ResidueField R] CotangentSpace Q :=
      φR.extendScalarsOfSurjective (residue_surjective (R := R))
    ∃ (c : ℕ) (bK : Module.Basis (Fin c) (ResidueField R) (LinearMap.ker φ))
      (xI : Fin c → maximalIdeal R),
      (∀ i, (((xI i : maximalIdeal R) : R) ∈ I)) ∧
        (∀ i, (maximalIdeal R).toCotangent (xI i) = (bK i : CotangentSpace R)) := by
  let Q := R ⧸ I
  letI : IsRegularLocalRing Q := hquot
  letI : IsLocalHom (algebraMap R Q) :=
    IsLocalHom.of_surjective (algebraMap R Q)
      (by simpa [Q] using Ideal.Quotient.mk_surjective)
  let hTorsQ : Module.IsTorsionBySet R (CotangentSpace Q) (maximalIdeal R) :=
    fun {x} {a} ↦ Ideal.Cotangent.smul_eq_zero_of_mem (I := maximalIdeal Q) (h a.2) x
  letI : Module (ResidueField R) (CotangentSpace Q) := Module.IsTorsionBySet.module hTorsQ
  letI : IsScalarTower R (ResidueField R) (CotangentSpace Q) :=
    Module.IsTorsionBySet.isScalarTower hTorsQ
  let φR : CotangentSpace R →ₗ[R] CotangentSpace Q :=
    Ideal.mapCotangent (maximalIdeal R) (maximalIdeal Q) (Algebra.ofId R Q) h
  let φ : CotangentSpace R →ₗ[ResidueField R] CotangentSpace Q :=
    φR.extendScalarsOfSurjective (residue_surjective (R := R))
  let c : ℕ := Module.finrank (ResidueField R) (LinearMap.ker φ)
  let bK : Module.Basis (Fin c) (ResidueField R) (LinearMap.ker φ) :=
    Module.finBasisOfFinrankEq (ResidueField R) (LinearMap.ker φ) rfl
  have hxI_exists :
      ∀ i : Fin c,
        ∃ xi : maximalIdeal R,
          (((xi : maximalIdeal R) : R) ∈ I) ∧
            (maximalIdeal R).toCotangent xi = (bK i : CotangentSpace R) := by
    intro i
    have hmemMap :
        (bK i : CotangentSpace R) ∈
          Submodule.map (maximalIdeal R).toCotangent
            (Submodule.comap (Submodule.subtype (maximalIdeal R)) (I ⊓ maximalIdeal R)) := by
      -- The chosen basis vectors lie in the cotangent kernel, and `hker` identifies that kernel.
      have hmemK : (bK i : CotangentSpace R) ∈ LinearMap.ker φ := (bK i).2
      exact (hker (bK i : CotangentSpace R)).1 hmemK
    rcases Submodule.mem_map.mp hmemMap with ⟨xi, hxi, hcotxi⟩
    refine ⟨xi, (Ideal.mem_inf.mp hxi).1, hcotxi⟩
  choose xI hxI_mem hxI_toCotangent using hxI_exists
  exact ⟨c, bK, xI, hxI_mem, hxI_toCotangent⟩

/-- Helper for Lemma 10.106.4: if a parameter family in `R ⧸ I` is lifted coordinatewise to
elements of `maximalIdeal R`, then those lifts generate `maximalIdeal R` modulo `I`. -/
lemma parameterIdeal_sup_eq_maximalIdeal_of_quotient_parameter_lifts
    (I : Ideal R) [IsLocalRing (R ⧸ I)] {d : ℕ}
    {ybar : Fin d → maximalIdeal (R ⧸ I)} (hybar : parameterIdeal ybar = maximalIdeal (R ⧸ I))
    {y : Fin d → maximalIdeal R}
    (hy :
      ∀ i, Ideal.Quotient.mk I (((y i : maximalIdeal R) : R)) =
        ((ybar i : maximalIdeal (R ⧸ I)) : R ⧸ I)) :
    parameterIdeal y ⊔ I = maximalIdeal R := by
  let Q := R ⧸ I
  have hI_le : I ≤ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp inferInstance)
  have hmaxmap :
      Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal Q := by
    -- The quotient map sends the maximal ideal of `R` onto the maximal ideal downstairs.
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hy_parameter_map :
      Ideal.map (Ideal.Quotient.mk I) (parameterIdeal y) = parameterIdeal ybar := by
    -- Mapping the lifted family recovers the quotient parameter family entrywise.
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, parameterIdeal_eq_span]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      refine Ideal.mem_comap.2 ?_
      change Ideal.Quotient.mk I (((y i : maximalIdeal R) : R)) ∈ parameterIdeal ybar
      rw [hy i]
      exact Ideal.subset_span ⟨i, rfl⟩
    · rw [parameterIdeal_eq_span]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      have hyi_mem : ((y i : maximalIdeal R) : R) ∈ parameterIdeal y := by
        rw [parameterIdeal_eq_span]
        exact Ideal.subset_span ⟨i, rfl⟩
      change ((ybar i : maximalIdeal Q) : Q) ∈ Ideal.map (Ideal.Quotient.mk I) (parameterIdeal y)
      simpa [Q, hy i] using Ideal.mem_map_of_mem (Ideal.Quotient.mk I) hyi_mem
  -- Pulling back the quotient maximal ideal adds back exactly the kernel `I`.
  calc
    parameterIdeal y ⊔ I =
        Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) (parameterIdeal y)) := by
          rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
            ← RingHom.ker_eq_comap_bot]
          simpa using (Ideal.mk_ker (I := I)).symm
    _ = Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal Q) := by
          rw [hy_parameter_map, hybar]
    _ = maximalIdeal R := by
          rw [← hmaxmap, Ideal.comap_map_of_surjective (Ideal.Quotient.mk I)
            Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
            sup_eq_left.mpr (show RingHom.ker (Ideal.Quotient.mk I) ≤ maximalIdeal R by
              simpa using hI_le)]

/-- Helper for Lemma 10.106.4: a kernel basis in the cotangent space can be completed, via the
quotient-by-kernel basis `Module.Basis.sumQuot`, to a regular system of parameters upstairs. -/
lemma kernel_prefix_extends_to_regularSystemOfParameters_via_sumQuot
    {K : Submodule (ResidueField R) (CotangentSpace R)}
    {c : ℕ} (bK : Module.Basis (Fin c) (ResidueField R) K)
    (xI : Fin c → maximalIdeal R)
    (hxI_toCotangent : ∀ i, (maximalIdeal R).toCotangent (xI i) = (bK i : CotangentSpace R)) :
    let e := Module.finrank (ResidueField R) (CotangentSpace R ⧸ K)
    ∃ xtail : Fin e → maximalIdeal R, IsRegularSystemOfParameters (Fin.append xI xtail) := by
  let e : ℕ := Module.finrank (ResidueField R) (CotangentSpace R ⧸ K)
  let bQ : Module.Basis (Fin e) (ResidueField R) (CotangentSpace R ⧸ K) :=
    Module.finBasisOfFinrankEq (ResidueField R) (CotangentSpace R ⧸ K) rfl
  let bSum : Module.Basis (Fin c ⊕ Fin e) (ResidueField R) (CotangentSpace R) :=
    Module.Basis.sumQuot bK bQ
  let b : Module.Basis (Fin (c + e)) (ResidueField R) (CotangentSpace R) :=
    bSum.reindex finSumFinEquiv
  choose xtail hxtail using
    fun j : Fin e ↦ (maximalIdeal R).toCotangent_surjective (b (Fin.natAdd c j))
  let w : Fin (c + e) → maximalIdeal R := Fin.append xI xtail
  have himage :
      (maximalIdeal R).toCotangent '' Set.range w = Set.range b := by
    ext y
    constructor
    · rintro ⟨m, ⟨i, rfl⟩, rfl⟩
      refine Fin.addCases ?_ ?_ i
      · intro i'
        refine ⟨Fin.castAdd e i', ?_⟩
        -- The left block keeps the prescribed kernel basis vectors.
        simp [w, b, bSum, hxI_toCotangent, Module.Basis.reindex_apply]
      · intro j
        refine ⟨Fin.natAdd c j, ?_⟩
        -- The right block is lifted from the quotient-by-kernel basis.
        simpa [w] using (hxtail j).symm
    · rintro ⟨i, rfl⟩
      refine Fin.addCases ?_ ?_ i
      · intro i'
        refine ⟨xI i', ⟨Fin.castAdd e i', by simp [w]⟩, ?_⟩
        -- The prescribed prefix lands on the left basis coordinates.
        simp [b, bSum, hxI_toCotangent, Module.Basis.reindex_apply]
      · intro j
        refine ⟨xtail j, ⟨Fin.natAdd c j, by simp [w]⟩, ?_⟩
        -- The chosen tail lifts land on the right basis coordinates.
        simpa [w] using hxtail j
  have hspan_image :
      Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' Set.range w) = ⊤ := by
    -- Proof comment: every basis vector is realized as the cotangent image of one chosen lift.
    rw [himage]
    simpa using b.span_eq
  have hspan_top :
      Submodule.span R (Set.range w) = ⊤ := by
    -- Proof comment: spanning the cotangent space is equivalent to generating the maximal ideal.
    exact (CotangentSpace.span_image_eq_top_iff (R := R) (s := Set.range w)).1 hspan_image
  have hspan_val :
      Submodule.span R (Set.range fun i : Fin (c + e) ↦ ((w i : maximalIdeal R) : R)) =
        maximalIdeal R := by
    -- Proof comment: translate the span statement in `maximalIdeal R` back to the ambient ideal.
    exact (Submodule.span_range_subtype_eq_top_iff
      (p := maximalIdeal R)
      (s := fun i : Fin (c + e) ↦ ((w i : maximalIdeal R) : R))
      (hs := fun i ↦ (w i).2)).1 (by simpa using hspan_top)
  have hparameter : parameterIdeal w = maximalIdeal R := by
    -- Proof comment: `parameterIdeal` is exactly the ambient ideal generated by the family.
    simpa [parameterIdeal_eq_span, w] using hspan_val
  have hcot_dim :
      Module.finrank (ResidueField R) (CotangentSpace R) = c + e := by
    have hK_dim : Module.finrank (ResidueField R) K = c := by
      simpa using Module.finrank_eq_card_basis bK
    have hrank :
        Module.finrank (ResidueField R) (CotangentSpace R ⧸ K) +
            Module.finrank (ResidueField R) K =
          Module.finrank (ResidueField R) (CotangentSpace R) := by
      simpa using
        (Submodule.finrank_quotient_add_finrank
          (R := ResidueField R) (M := CotangentSpace R) K)
    have hrank' :
        e + c = Module.finrank (ResidueField R) (CotangentSpace R) := by
      simpa [e, hK_dim] using hrank
    omega
  have hdim :
      ringKrullDim R = c + e := by
    -- Proof comment: regular-locality identifies the cotangent dimension with the Krull dimension.
    calc
      ringKrullDim R = (maximalIdeal R).spanFinrank := by
        simpa using
          ((isRegularLocalRing_iff (R := R)).1 (inferInstance : IsRegularLocalRing R)).symm
      _ = Module.finrank (ResidueField R) (CotangentSpace R) := by
        rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)]
      _ = (c + e : ℕ) := by
        exact_mod_cast hcot_dim
  refine ⟨xtail, ?_⟩
  -- Proof comment: once the completed family generates `maximalIdeal R`, the dimension equality
  -- upgrades it to a regular system of parameters.
  exact (isRegularSystemOfParameters_iff_of_ringKrullDim_eq (R := R) hdim w).2 hparameter

/-- Helper for Lemma 10.106.4: the parameter ideal of the prefixed family is recovered by
restricting `Fin.append` to its first `c` coordinates. -/
lemma parameterIdeal_append_prefix_eq {c e : ℕ}
    (x : Fin c → maximalIdeal R) (y : Fin e → maximalIdeal R) :
    parameterIdeal (Fin.append x y ∘ Fin.castLE (Nat.le_add_right c e)) = parameterIdeal x := by
  -- Proof comment: the prefix restriction of `Fin.append` is definitionally the original family.
  rw [parameterIdeal_eq_span, parameterIdeal_eq_span]
  congr 1
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp [Function.comp]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp [Function.comp]⟩

/-- Helper for Lemma 10.106.4: reindexing the tail of an appended regular system by a canonical
`Fin.cast` does not change the regular-system-of-parameters property. -/
lemma isRegularSystemOfParameters_append_cast_right {c e e' : ℕ}
    (x : Fin c → maximalIdeal R) (y : Fin e → maximalIdeal R) (h : e' = e)
    (hfull : IsRegularSystemOfParameters (Fin.append x y)) :
    IsRegularSystemOfParameters (Fin.append x (y ∘ Fin.cast h)) := by
  have hlen : c + e' = c + e := by simpa [h]
  rw [isRegularSystemOfParameters_iff] at hfull ⊢
  constructor
  · simpa [h] using hfull.1
  · calc
      parameterIdeal (Fin.append x (y ∘ Fin.cast h)) =
          parameterIdeal (Fin.append x y ∘ Fin.cast hlen) := by
            simpa [hlen] using (Fin.append_cast_right x y e' h)
      _ = parameterIdeal (Fin.append x y) := by
            rw [parameterIdeal_eq_span, parameterIdeal_eq_span]
            congr 1
            ext z
            constructor
            · rintro ⟨i, rfl⟩
              exact ⟨Fin.cast hlen i, rfl⟩
            · rintro ⟨i, rfl⟩
              exact ⟨Fin.cast hlen.symm i, by simp⟩
      _ = maximalIdeal R := hfull.2

/-- Helper for Lemma 10.106.4: the quotient map `R → R ⧸ I` induces a bijection on residue
fields at the maximal ideals. -/
lemma quotient_residueField_map_bijective (I : Ideal R)
    (hquot : IsRegularLocalRing (R ⧸ I)) :
    let Q := R ⧸ I
    letI : IsRegularLocalRing Q := hquot
    letI : IsLocalHom (algebraMap R Q) :=
      IsLocalHom.of_surjective (algebraMap R Q)
        (by simpa [Q] using Ideal.Quotient.mk_surjective)
    Function.Bijective (ResidueField.map (algebraMap R Q)) := by
  let Q := R ⧸ I
  letI : IsRegularLocalRing Q := hquot
  letI : IsLocalHom (algebraMap R Q) :=
    IsLocalHom.of_surjective (algebraMap R Q)
      (by simpa [Q] using Ideal.Quotient.mk_surjective)
  let κideal :
      (maximalIdeal R).ResidueField →+* (maximalIdeal Q).ResidueField :=
    Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Q) (algebraMap R Q)
      (maximalIdeal_comap (algebraMap R Q)).symm
  have hsurj : Function.Surjective (algebraMap R Q) := by
    simpa [Q] using Ideal.Quotient.mk_surjective
  have hκideal_bij : Function.Bijective κideal := by
    -- Proof comment: surjectivity on stalks upgrades the quotient map to a bijection on the
    -- residue fields at the corresponding maximal ideals.
    simpa [κideal] using
      ((RingHom.surjectiveOnStalks_of_surjective hsurj).residueFieldMap_bijective
        (maximalIdeal R) (maximalIdeal Q) (maximalIdeal_comap (algebraMap R Q)).symm)
  let eR : (maximalIdeal R).ResidueField ≃+* ResidueField R := maximalIdealResidueFieldEquiv R
  let eQ : (maximalIdeal Q).ResidueField ≃+* ResidueField Q := maximalIdealResidueFieldEquiv Q
  have hcomp :
      eQ.toRingHom.comp κideal =
        (ResidueField.map (algebraMap R Q)).comp eR.toRingHom := by
    simpa [κideal, eR, eQ] using
      maximalIdealResidueFieldEquiv_comp_residueFieldMap
        (A := R) (B := Q) (algebraMap R Q)
  have hκ :
      ResidueField.map (algebraMap R Q) =
        (eQ.toRingHom.comp κideal).comp eR.symm.toRingHom := by
    ext x
    have hx := congrArg
      (fun f : (maximalIdeal R).ResidueField →+* ResidueField Q ↦ f (eR.symm x)) hcomp
    simpa [RingHom.comp_apply, eR] using hx.symm
  -- Proof comment: surjectivity on stalks upgrades the quotient map to a residue-field
  -- bijection at the corresponding maximal ideals, and the ordinary residue-field model is
  -- canonically equivalent to the maximal-ideal one.
  constructor
  · intro x y hxy
    have hx :
        eQ (κideal (eR.symm x)) = eQ (κideal (eR.symm y)) := by
      calc
        eQ (κideal (eR.symm x)) = ResidueField.map (algebraMap R Q) x := by
          simpa [hκ, RingHom.comp_apply]
        _ = ResidueField.map (algebraMap R Q) y := hxy
        _ = eQ (κideal (eR.symm y)) := by
          simpa [hκ, RingHom.comp_apply]
    apply eR.symm.injective
    apply hκideal_bij.1
    exact eQ.injective hx
  · intro z
    obtain ⟨w, hw⟩ := hκideal_bij.2 (eQ.symm z)
    refine ⟨eR w, ?_⟩
    calc
      ResidueField.map (algebraMap R Q) (eR w) =
          eQ (κideal (eR.symm (eR w))) := by
            simpa [hκ, RingHom.comp_apply]
      _ = eQ (κideal w) := by simp [eR]
      _ = eQ (eQ.symm z) := by rw [hw]
      _ = z := by simp [eQ]

/-- Helper for Lemma 10.106.4: transporting scalars back along a ring equivalence recovers the
original module action. -/
theorem ringEquiv_symm_apply_smul_eq_original
    {A : Type u} {P : Type*} {V : Type*}
    [CommSemiring A] [CommSemiring P] [AddCommMonoid V] [Module P V]
    (e : A ≃+* P) :
    letI : Module A V := Module.compHom V (e : A →+* P)
    ∀ c : P, ∀ x : V, e.symm c • x = c • x := by
  intro c x
  -- Proof comment: after restricting scalars along `e`, the action of `e.symm c` is
  -- definitionally the original action of `c`.
  change e (e.symm c) • x = c • x
  simpa using congrArg (fun d : P ↦ d • x) (e.right_inv c)

/-- Helper for Lemma 10.106.4: after identifying the residue fields of `R` and `R ⧸ I`, the
cotangent space downstairs has the expected Krull-dimension finrank over `ResidueField R`. -/
lemma quotient_cotangent_finrank_over_base_eq_ringKrullDim (I : Ideal R)
    (hquot : IsRegularLocalRing (R ⧸ I))
    {h : maximalIdeal R ≤ Ideal.comap (algebraMap R (R ⧸ I)) (maximalIdeal (R ⧸ I))} :
    let Q := R ⧸ I
    letI : IsRegularLocalRing Q := hquot
    letI : IsLocalHom (algebraMap R Q) :=
      IsLocalHom.of_surjective (algebraMap R Q)
        (by simpa [Q] using Ideal.Quotient.mk_surjective)
    let hTorsQ : Module.IsTorsionBySet R (CotangentSpace Q) (maximalIdeal R) :=
      fun {x} {a} ↦ Ideal.Cotangent.smul_eq_zero_of_mem (I := maximalIdeal Q) (h a.2) x
    letI : Module (ResidueField R) (CotangentSpace Q) := Module.IsTorsionBySet.module hTorsQ
    letI : IsScalarTower R (ResidueField R) (CotangentSpace Q) :=
      Module.IsTorsionBySet.isScalarTower hTorsQ
    Module.finrank (ResidueField R) (CotangentSpace Q) = ringKrullDim Q := by
  let Q := R ⧸ I
  letI : IsRegularLocalRing Q := hquot
  letI : IsLocalHom (algebraMap R Q) :=
    IsLocalHom.of_surjective (algebraMap R Q)
      (by simpa [Q] using Ideal.Quotient.mk_surjective)
  let hTorsQ : Module.IsTorsionBySet R (CotangentSpace Q) (maximalIdeal R) :=
    fun {x} {a} ↦ Ideal.Cotangent.smul_eq_zero_of_mem (I := maximalIdeal Q) (h a.2) x
  let oldModule : Module (ResidueField R) (CotangentSpace Q) := Module.IsTorsionBySet.module hTorsQ
  letI : Module (ResidueField R) (CotangentSpace Q) := oldModule
  letI : IsScalarTower R (ResidueField R) (CotangentSpace Q) :=
    Module.IsTorsionBySet.isScalarTower hTorsQ
  let κmap : ResidueField R →+* ResidueField Q := ResidueField.map (algebraMap R Q)
  have hκbij : Function.Bijective κmap := by
    simpa [Q, κmap] using quotient_residueField_map_bijective (R := R) I hquot
  let eκ : ResidueField R ≃+* ResidueField Q := RingEquiv.ofBijective κmap hκbij
  let newModule : Module (ResidueField R) (CotangentSpace Q) :=
    Module.compHom (CotangentSpace Q) (eκ : ResidueField R →+* ResidueField Q)
  have hmodule_eq : oldModule = newModule := by
    apply Module.ext' oldModule newModule
    intro c x
    refine Quotient.inductionOn' c ?_
    intro a
    -- Proof comment: both scalar actions are induced by the same element `a ∈ R`, once the
    -- residue-field map is rewritten through `ResidueField.map_residue`.
    change a • x = ResidueField.map (algebraMap R Q) (residue R a) • x
    rw [IsLocalRing.ResidueField.map_residue]
    change (algebraMap R Q a) • x = residue Q (algebraMap R Q a) • x
    rfl
  have hnew_finrank :
      @Module.finrank (ResidueField R) (CotangentSpace Q) _ _ newModule = ringKrullDim Q := by
    letI : Module (ResidueField R) (CotangentSpace Q) := newModule
    let n : ℕ := Module.finrank (ResidueField Q) (CotangentSpace Q)
    have hfinQ_nat :
        Module.finrank (ResidueField Q) (CotangentSpace Q) = (maximalIdeal Q).spanFinrank := by
      symm
      rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := Q)]
    have hfinQ :
        n = ringKrullDim Q := by
      calc
        (n : WithBot ℕ∞) = Module.finrank (ResidueField Q) (CotangentSpace Q) := by
          simp [n]
        _ = (maximalIdeal Q).spanFinrank := by
          exact_mod_cast hfinQ_nat
        _ = ringKrullDim Q := by
          simpa using (isRegularLocalRing_iff (R := Q)).1 hquot
    let bQ : Module.Basis (Fin n) (ResidueField Q) (CotangentSpace Q) :=
      Module.finBasisOfFinrankEq (ResidueField Q) (CotangentSpace Q) (by simp [n])
    let bR : Module.Basis (Fin n) (ResidueField R) (CotangentSpace Q) :=
      bQ.mapCoeffs eκ.symm (ringEquiv_symm_apply_smul_eq_original (V := CotangentSpace Q) eκ)
    have hfinR : @Module.finrank (ResidueField R) (CotangentSpace Q) _ _ newModule = n := by
      simpa [n] using (Module.finrank_eq_card_basis bR)
    -- Proof comment: a basis over `ResidueField Q` is also a basis over `ResidueField R` after
    -- transporting coefficients along the residue-field isomorphism.
    rw [hfinR]
    exact hfinQ
  -- Proof comment: first rewrite the current module structure to the transported one, then read
  -- off the finrank from the transported basis.
  change @Module.finrank (ResidueField R) (CotangentSpace Q) _ _ oldModule = ringKrullDim Q
  rw [hmodule_eq]
  exact hnew_finrank

/-- Helper for Lemma 10.106.4: the quotient-by-kernel cotangent space has the same finrank as the
cotangent space downstairs, and hence the same Krull dimension as the regular quotient. -/
lemma quotient_cotangent_quotKer_finrank_eq_ringKrullDim (I : Ideal R)
    (hquot : IsRegularLocalRing (R ⧸ I))
    {h : maximalIdeal R ≤ Ideal.comap (algebraMap R (R ⧸ I)) (maximalIdeal (R ⧸ I))}
    (hφ_surj :
      let Q := R ⧸ I
      letI : IsRegularLocalRing Q := hquot
      letI : IsLocalHom (algebraMap R Q) :=
        IsLocalHom.of_surjective (algebraMap R Q)
          (by simpa [Q] using Ideal.Quotient.mk_surjective)
      let hTorsQ : Module.IsTorsionBySet R (CotangentSpace Q) (maximalIdeal R) :=
        fun {x} {a} ↦ Ideal.Cotangent.smul_eq_zero_of_mem (I := maximalIdeal Q) (h a.2) x
      letI : Module (ResidueField R) (CotangentSpace Q) := Module.IsTorsionBySet.module hTorsQ
      letI : IsScalarTower R (ResidueField R) (CotangentSpace Q) :=
        Module.IsTorsionBySet.isScalarTower hTorsQ
      let φR : CotangentSpace R →ₗ[R] CotangentSpace Q :=
        Ideal.mapCotangent (maximalIdeal R) (maximalIdeal Q) (Algebra.ofId R Q) h
      let φ : CotangentSpace R →ₗ[ResidueField R] CotangentSpace Q :=
        φR.extendScalarsOfSurjective (residue_surjective (R := R))
      Function.Surjective φ) :
    let Q := R ⧸ I
    letI : IsRegularLocalRing Q := hquot
    letI : IsLocalHom (algebraMap R Q) :=
      IsLocalHom.of_surjective (algebraMap R Q)
        (by simpa [Q] using Ideal.Quotient.mk_surjective)
    let hTorsQ : Module.IsTorsionBySet R (CotangentSpace Q) (maximalIdeal R) :=
      fun {x} {a} ↦ Ideal.Cotangent.smul_eq_zero_of_mem (I := maximalIdeal Q) (h a.2) x
    letI : Module (ResidueField R) (CotangentSpace Q) := Module.IsTorsionBySet.module hTorsQ
    letI : IsScalarTower R (ResidueField R) (CotangentSpace Q) :=
      Module.IsTorsionBySet.isScalarTower hTorsQ
      let φR : CotangentSpace R →ₗ[R] CotangentSpace Q :=
        Ideal.mapCotangent (maximalIdeal R) (maximalIdeal Q) (Algebra.ofId R Q) h
      let φ : CotangentSpace R →ₗ[ResidueField R] CotangentSpace Q :=
        φR.extendScalarsOfSurjective (residue_surjective (R := R))
    Module.finrank (ResidueField R) (CotangentSpace R ⧸ LinearMap.ker φ) = ringKrullDim Q := by
  let Q := R ⧸ I
  letI : IsRegularLocalRing Q := hquot
  letI : IsLocalHom (algebraMap R Q) :=
    IsLocalHom.of_surjective (algebraMap R Q)
      (by simpa [Q] using Ideal.Quotient.mk_surjective)
  let hTorsQ : Module.IsTorsionBySet R (CotangentSpace Q) (maximalIdeal R) :=
    fun {x} {a} ↦ Ideal.Cotangent.smul_eq_zero_of_mem (I := maximalIdeal Q) (h a.2) x
  letI : Module (ResidueField R) (CotangentSpace Q) := Module.IsTorsionBySet.module hTorsQ
  letI : IsScalarTower R (ResidueField R) (CotangentSpace Q) :=
    Module.IsTorsionBySet.isScalarTower hTorsQ
  let φR : CotangentSpace R →ₗ[R] CotangentSpace Q :=
    Ideal.mapCotangent (maximalIdeal R) (maximalIdeal Q) (Algebra.ofId R Q) h
  let φ : CotangentSpace R →ₗ[ResidueField R] CotangentSpace Q :=
    φR.extendScalarsOfSurjective (residue_surjective (R := R))
  let eQuot : (CotangentSpace R ⧸ LinearMap.ker φ) ≃ₗ[ResidueField R] CotangentSpace Q :=
    LinearMap.quotKerEquivOfSurjective φ hφ_surj
  have hfinQuot :
      Module.finrank (ResidueField R) (CotangentSpace R ⧸ LinearMap.ker φ) =
        Module.finrank (ResidueField R) (CotangentSpace Q) := by
    simpa using (LinearEquiv.finrank_eq eQuot)
  have hfinQuot_cast :
      (Module.finrank (ResidueField R) (CotangentSpace R ⧸ LinearMap.ker φ) : WithBot ℕ∞) =
        Module.finrank (ResidueField R) (CotangentSpace Q) := by
    exact_mod_cast hfinQuot
  -- Proof comment: identify the quotient by the cotangent kernel with the downstairs cotangent
  -- space, then apply the residue-field transport finrank computation.
  exact hfinQuot_cast.trans <| by
    simpa [Q, hTorsQ] using
      quotient_cotangent_finrank_over_base_eq_ringKrullDim (R := R) I hquot (h := h)

/-- Helper for Lemma 10.106.4: the quotient by the prefix parameter ideal of a completed regular
system has Krull dimension equal to the tail length. -/
lemma prefix_parameterIdeal_ringKrullDim_of_append_regular {c e : ℕ}
    (x : Fin c → maximalIdeal R) (y : Fin e → maximalIdeal R)
    (hfull : IsRegularSystemOfParameters (Fin.append x y)) :
    ringKrullDim (R ⧸ parameterIdeal x) = e := by
  have hprefix : c ≤ c + e := Nat.le_add_right c e
  have hpart : IsPartOfRegularSystemOfParameters (c + e) x := by
    rw [IsPartOfRegularSystemOfParameters]
    refine ⟨fun i ↦ y (Fin.cast (Nat.add_sub_cancel_left c e) i), ?_⟩
    exact isRegularSystemOfParameters_append_cast_right (R := R) x y
      (Nat.add_sub_cancel_left c e) hfull
  have hquot :
      IsRegularLocalRing (R ⧸ parameterIdeal x) := hpart.isRegularLocalRing_quotient_parameterIdeal
  have hdimQuot :
      ringKrullDim (R ⧸ parameterIdeal x) =
        (maximalIdeal (R ⧸ parameterIdeal x)).spanFinrank := by
    simpa using ((isRegularLocalRing_iff (R := R ⧸ parameterIdeal x)).1 hquot).symm
  have hdimQuot_cast :
      (((maximalIdeal (R ⧸ parameterIdeal x)).spanFinrank : ℕ∞) : WithBot ℕ∞) =
        ringKrullDim (R ⧸ parameterIdeal x) := by
    simpa using hdimQuot.symm
  have hadd :=
    IsRegularSystemOfParameters.ringKrullDim_quotient_parameterIdeal_add_eq
      (R := R) hfull hprefix
  have hdimR : ringKrullDim R = c + e := (isRegularSystemOfParameters_iff _).1 hfull |>.1
  -- Proof comment: rewrite the canonical prefix ideal of the appended family back to
  -- `parameterIdeal x`, then compare both sides inside the finite-dimensional regular quotient.
  rw [parameterIdeal_append_prefix_eq (R := R) x y] at hadd
  have hnat_cast :
      (((maximalIdeal (R ⧸ parameterIdeal x)).spanFinrank : ℕ∞) : WithBot ℕ∞) + c = c + e := by
    calc
      (((maximalIdeal (R ⧸ parameterIdeal x)).spanFinrank : ℕ∞) : WithBot ℕ∞) + c =
          ringKrullDim (R ⧸ parameterIdeal x) + c := by rw [hdimQuot_cast]
      _ = ringKrullDim R := hadd
      _ = c + e := hdimR
  have hnat :
      (maximalIdeal (R ⧸ parameterIdeal x)).spanFinrank + c = c + e := by
    exact_mod_cast hnat_cast
  have hspan :
      (maximalIdeal (R ⧸ parameterIdeal x)).spanFinrank = e := by
    omega
  calc
    ringKrullDim (R ⧸ parameterIdeal x) =
        (maximalIdeal (R ⧸ parameterIdeal x)).spanFinrank := hdimQuot
    _ = e := by simpa using hspan

/-- Helper for Lemma 10.106.4: once the quotient by `parameterIdeal x` and the quotient by `I`
have the same dimension, the canonical surjection forces the two ideals to agree. -/
lemma parameterIdeal_eq_of_equal_dimension_regular_quotient_surjection
    (I : Ideal R) (hquot : IsRegularLocalRing (R ⧸ I)) {c : ℕ} {x : Fin c → maximalIdeal R}
    (hx : IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x)
    (hmem : ∀ i, (((x i : maximalIdeal R) : R) ∈ I))
    (hdim : ringKrullDim (R ⧸ parameterIdeal x) = ringKrullDim (R ⧸ I)) :
    parameterIdeal x = I := by
  let J : Ideal R := parameterIdeal x
  have hJ_le_I : J ≤ I := by
    change parameterIdeal x ≤ I
    rw [parameterIdeal_eq_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact hmem i
  by_contra hJI_ne
  let S := R ⧸ J
  letI : IsRegularLocalRing S := by
    simpa [S, J] using hx.isRegularLocalRing_quotient_parameterIdeal
  let K : Ideal S := Ideal.map (Ideal.Quotient.mk J) I
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    have hker :
        Ideal.comap (Ideal.Quotient.mk J) (⊥ : Ideal S) = J := by
      simpa [S, J, RingHom.ker_eq_comap_bot] using Ideal.mk_ker (I := J)
    have hI_le_J : I ≤ J := by
      have hcomap :
          Ideal.comap (Ideal.Quotient.mk J) K = I ⊔ J := by
        calc
          Ideal.comap (Ideal.Quotient.mk J) K = I ⊔ Ideal.comap (Ideal.Quotient.mk J) ⊥ := by
            simpa [S, J, K] using
              Ideal.comap_map_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective I
          _ = I ⊔ J := by rw [hker]
      have hsup_eq : I ⊔ J = J := by
        simpa [K, hK_bot, hker] using hcomap
      exact sup_eq_right.mp hsup_eq
    exact hJI_ne (le_antisymm hJ_le_I hI_le_J)
  obtain ⟨xbar, hxbar_mem, hxbar_ne_zero⟩ := K.ne_bot_iff.mp hK_ne_bot
  have hI_le_max : I ≤ maximalIdeal R :=
    ideal_le_maximalIdeal_of_regular_quotient (R := R) I hquot
  have hK_le_max : K ≤ maximalIdeal S := by
    have hmap_max :
        Ideal.map (Ideal.Quotient.mk J) (maximalIdeal R) = maximalIdeal S := by
      exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
        Ideal.Quotient.mk_surjective
    calc
      K = Ideal.map (Ideal.Quotient.mk J) I := rfl
      _ ≤ Ideal.map (Ideal.Quotient.mk J) (maximalIdeal R) := Ideal.map_mono hI_le_max
      _ = maximalIdeal S := hmap_max
  have hxbar_mem_max : xbar ∈ maximalIdeal S := hK_le_max hxbar_mem
  have hxbar_mem_nonZeroDivisors : xbar ∈ nonZeroDivisors S :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hxbar_ne_zero
  have hdrop :
      ringKrullDim (S ⧸ Ideal.span ({xbar} : Set S)) + 1 = ringKrullDim S := by
    -- Proof comment: the nonzero element of the kernel ideal cuts the dimension down by one in
    -- the regular-local domain `S`.
    simpa [S] using
      (ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
        (R := S) hxbar_mem_nonZeroDivisors hxbar_mem_max)
  have hspan_le_K : Ideal.span ({xbar} : Set S) ≤ K := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hxbar_mem
  have hquot_le :
      ringKrullDim (S ⧸ K) ≤ ringKrullDim (S ⧸ Ideal.span ({xbar} : Set S)) := by
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hspan_le_K)
      (Ideal.Quotient.factor_surjective hspan_le_K)
  have hthird :
      ringKrullDim (S ⧸ K) = ringKrullDim (R ⧸ I) := by
    -- Proof comment: identify the iterated quotient by the mapped kernel ideal with `R ⧸ I`.
    simpa [S, J, K] using ringKrullDim_eq_of_ringEquiv
      (DoubleQuot.quotQuotEquivQuotOfLE hJ_le_I)
  have hSdim : ringKrullDim S = ringKrullDim (R ⧸ I) := by
    simpa [S, J] using hdim
  have hstrict :
      ringKrullDim (R ⧸ I) + 1 ≤ ringKrullDim S := by
    calc
      ringKrullDim (R ⧸ I) + 1 = ringKrullDim (S ⧸ K) + 1 := by rw [← hthird]
      _ ≤ ringKrullDim (S ⧸ Ideal.span ({xbar} : Set S)) + 1 := by
        simpa [add_comm] using add_le_add_right hquot_le 1
      _ = ringKrullDim S := hdrop
  have hstrict' : ringKrullDim (R ⧸ I) + 1 ≤ ringKrullDim (R ⧸ I) := by
    simpa [hSdim] using hstrict
  have hdimI :
      ringKrullDim (R ⧸ I) = (maximalIdeal (R ⧸ I)).spanFinrank := by
    simpa using ((isRegularLocalRing_iff (R := R ⧸ I)).1 hquot).symm
  have hbad_cast :
      (((maximalIdeal (R ⧸ I)).spanFinrank : ℕ∞) : WithBot ℕ∞) + 1 ≤
        ((maximalIdeal (R ⧸ I)).spanFinrank : ℕ∞) := by
    simpa [hdimI] using hstrict'
  have hbad :
      (maximalIdeal (R ⧸ I)).spanFinrank + 1 ≤ (maximalIdeal (R ⧸ I)).spanFinrank := by
    exact_mod_cast hbad_cast
  exact Nat.not_succ_le_self _ hbad

/- Domain-style sampling pass.

Primary domain: local commutative algebra of regular local rings, regular systems of parameters,
and quotient ideals cut out by initial parameter families.

Sampled owner declarations:
* `IsLocalRing.parameterIdeal`;
* `IsLocalRing.IsRegularSystemOfParameters`;
* `IsLocalRing.IsPartOfRegularSystemOfParameters`;
* `isRegularLocalRing_iff_exists_regularSystemOfParameters`.

Best owner abstraction: the primitive source-facing datum here is not a full regular system of
parameters together with explicit prefix-cast bookkeeping, but rather a finite family
`x : Fin c → maximalIdeal R` whose generated ideal is `parameterIdeal x` and which extends to a
regular system of parameters. That extension property is already owned by
`IsPartOfRegularSystemOfParameters`, so the theorem below should expose that owner directly.

Primitive vs. derived:
* primitive data: the ideal `I` and the regular-local hypotheses on `R` and `R ⧸ I`;
* derived API: the existence of a partial parameter family `x` with `parameterIdeal x = I`, and
  the extension of `x` to a full regular system of parameters of total length
  `(maximalIdeal R).spanFinrank = ringKrullDim R`.

Source/core/bridge triage:
* source-facing: the existence of generators of `I` forming the initial part of a regular system of
  parameters of `R`;
* core/canonical: `parameterIdeal` and `IsPartOfRegularSystemOfParameters`;
* bridge/view: any later recovery of an explicit full system with `Fin.castLE` prefixes.
-/

-- Proof sketch: choose generators of `I` whose classes in the cotangent space of `R` complement
-- the cotangent space of `R ⧸ I`, extend them to a basis of the cotangent space of `R`, and lift
-- that basis to a regular system of parameters. The initial family then generates `I`, so the
-- canonical owner statement is that this family is part of a regular system of parameters and has
-- parameter ideal `I`.
/-- Lemma 10.106.4: if `R` is a regular local ring and `R ⧸ I` is also a regular local ring, then
there is a finite family in `maximalIdeal R` whose generated parameter ideal is `I` and which is
part of a regular system of parameters of total length
`(maximalIdeal R).spanFinrank = ringKrullDim R`. Equivalently, `I` is generated by an initial
segment of some regular system of parameters of `R`. -/
theorem exists_regularSystemOfParameters_with_prefix_span_eq_of_quotient_isRegularLocalRing
    (I : Ideal R) (hquot : IsRegularLocalRing (R ⧸ I)) :
    ∃ (c : ℕ) (x : Fin c → maximalIdeal R),
      IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x ∧
        parameterIdeal x = I := by
  classical
  let Q := R ⧸ I
  letI : IsRegularLocalRing Q := hquot
  haveI : IsLocalHom (algebraMap R Q) :=
    IsLocalHom.of_surjective (algebraMap R Q) (by simpa [Q] using Ideal.Quotient.mk_surjective)
  obtain ⟨hcot_h, hφ_ker⟩ :
      ∃ h : maximalIdeal R ≤ Ideal.comap (algebraMap R Q) (maximalIdeal Q),
        let hTorsQ : Module.IsTorsionBySet R (CotangentSpace Q) (maximalIdeal R) :=
          fun {x} {a} ↦ Ideal.Cotangent.smul_eq_zero_of_mem (I := maximalIdeal Q) (h a.2) x
        letI : Module (ResidueField R) (CotangentSpace Q) := Module.IsTorsionBySet.module hTorsQ
        letI : IsScalarTower R (ResidueField R) (CotangentSpace Q) :=
          Module.IsTorsionBySet.isScalarTower hTorsQ
        let φR : CotangentSpace R →ₗ[R] CotangentSpace Q :=
          Ideal.mapCotangent (maximalIdeal R) (maximalIdeal Q) (Algebra.ofId R Q) h
        let φ : CotangentSpace R →ₗ[ResidueField R] CotangentSpace Q :=
          φR.extendScalarsOfSurjective (residue_surjective (R := R))
        ∀ x : CotangentSpace R,
          x ∈ LinearMap.ker φ ↔
            x ∈ Submodule.map (maximalIdeal R).toCotangent
              (Submodule.comap (Submodule.subtype (maximalIdeal R)) (I ⊓ maximalIdeal R)) := by
    simpa [Q] using quotient_cotangent_mem_ker_iff_over_residueField (R := R) I hquot
  let hTorsQ : Module.IsTorsionBySet R (CotangentSpace Q) (maximalIdeal R) :=
    fun {x} {a} ↦ Ideal.Cotangent.smul_eq_zero_of_mem (I := maximalIdeal Q) (hcot_h a.2) x
  letI : Module (ResidueField R) (CotangentSpace Q) := Module.IsTorsionBySet.module hTorsQ
  letI : IsScalarTower R (ResidueField R) (CotangentSpace Q) :=
    Module.IsTorsionBySet.isScalarTower hTorsQ
  let φR : CotangentSpace R →ₗ[R] CotangentSpace Q :=
    Ideal.mapCotangent (maximalIdeal R) (maximalIdeal Q) (Algebra.ofId R Q) hcot_h
  let φ : CotangentSpace R →ₗ[ResidueField R] CotangentSpace Q :=
    φR.extendScalarsOfSurjective (residue_surjective (R := R))
  obtain ⟨c, bK, xI, hxI_mem, hxI_toCotangent⟩ :
      ∃ (c : ℕ) (bK : Module.Basis (Fin c) (ResidueField R) (LinearMap.ker φ))
        (xI : Fin c → maximalIdeal R),
        (∀ i, (((xI i : maximalIdeal R) : R) ∈ I)) ∧
          (∀ i, (maximalIdeal R).toCotangent (xI i) = (bK i : CotangentSpace R)) := by
    -- This is the source step choosing `x₁, …, x_c ∈ I` whose cotangent classes form the kernel.
    simpa [Q, hTorsQ, φR, φ] using
      exists_kernel_basis_lift_in_ideal (R := R) I hquot (h := hcot_h) hφ_ker
  obtain ⟨xtail, hfull⟩ :
      let e := Module.finrank (ResidueField R) (CotangentSpace R ⧸ LinearMap.ker φ)
      ∃ xtail : Fin e → maximalIdeal R, IsRegularSystemOfParameters (Fin.append xI xtail) := by
    -- Proof comment: the source complement step is now discharged by `Module.Basis.sumQuot`.
    simpa [φ] using
      kernel_prefix_extends_to_regularSystemOfParameters_via_sumQuot
        (R := R) (K := LinearMap.ker φ) bK xI hxI_toCotangent
  -- Route correction: the mixed-scalar cotangent obstacle is now isolated in `φ`, so the
  -- remaining work is the source-faithful dimension comparison: identify the tail length from the
  -- quotient cotangent space, package `xI` as a part of a regular system of parameters of length
  -- `(maximalIdeal R).spanFinrank`, and then run the equal-dimension quotient contradiction for
  -- `parameterIdeal xI`.
  have hφ_surj :
      Function.Surjective φ := by
    obtain ⟨h', hsurj⟩ :=
      quotient_cotangent_map_surjective_of_regular_quotient (R := R) I hquot
    -- Proof comment: the scalar extension leaves the underlying cotangent map surjective.
    simpa [Q, hTorsQ, φR, φ] using hsurj
  have he :
      Module.finrank (ResidueField R) (CotangentSpace R ⧸ LinearMap.ker φ) = ringKrullDim Q := by
    -- Proof comment: the quotient-by-kernel cotangent dimension is exactly the quotient Krull
    -- dimension from the source proof.
    simpa [Q, hTorsQ, φR, φ] using
      quotient_cotangent_quotKer_finrank_eq_ringKrullDim (R := R) I hquot
        (h := hcot_h) hφ_surj
  have hpart_dim :
      (maximalIdeal R).spanFinrank =
        c + Module.finrank (ResidueField R) (CotangentSpace R ⧸ LinearMap.ker φ) := by
    have hfull_dim : ringKrullDim R = c + Module.finrank (ResidueField R)
        (CotangentSpace R ⧸ LinearMap.ker φ) :=
      (isRegularSystemOfParameters_iff (Fin.append xI xtail)).1 hfull |>.1
    have hdim_cast :
        (((maximalIdeal R).spanFinrank : ℕ∞) : WithBot ℕ∞) =
          c + Module.finrank (ResidueField R)
            (CotangentSpace R ⧸ LinearMap.ker φ) := by
      calc
        (((maximalIdeal R).spanFinrank : ℕ∞) : WithBot ℕ∞) = ringKrullDim R := by
          simpa using (isRegularLocalRing_iff (R := R)).1
            (inferInstance : IsRegularLocalRing R)
        _ = c + Module.finrank (ResidueField R)
            (CotangentSpace R ⧸ LinearMap.ker φ) := hfull_dim
    exact_mod_cast hdim_cast
  have hpart :
      IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank xI := by
    -- Proof comment: `hfull` already gives the required complementary tail once the total length
    -- is rewritten as the span finrank of the maximal ideal.
    rw [hpart_dim, IsPartOfRegularSystemOfParameters]
    refine ⟨fun i ↦ xtail (Fin.cast (Nat.add_sub_cancel_left c
      (Module.finrank (ResidueField R) (CotangentSpace R ⧸ LinearMap.ker φ))) i), ?_⟩
    exact isRegularSystemOfParameters_append_cast_right (R := R) xI xtail
      (Nat.add_sub_cancel_left c
        (Module.finrank (ResidueField R) (CotangentSpace R ⧸ LinearMap.ker φ))) hfull
  have hprefix_dim :
      ringKrullDim (R ⧸ parameterIdeal xI) =
        Module.finrank (ResidueField R) (CotangentSpace R ⧸ LinearMap.ker φ) := by
    simpa [Q] using
      prefix_parameterIdeal_ringKrullDim_of_append_regular (R := R) xI xtail hfull
  have hdim_eq :
      ringKrullDim (R ⧸ parameterIdeal xI) = ringKrullDim (R ⧸ I) := by
    rw [hprefix_dim, he]
  refine ⟨c, xI, hpart, ?_⟩
  -- Proof comment: the source's final equal-dimension contradiction now identifies the prefix
  -- parameter ideal with the original ideal `I`.
  exact
    parameterIdeal_eq_of_equal_dimension_regular_quotient_surjection
      (R := R) I hquot hpart hxI_mem hdim_eq

end

/-! ### Lemma_10_106_5 (from Chap10) -/
universe u v

open IsLocalRing
open scoped Pointwise TensorProduct

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Helper for Lemma 10.106.5: if one chooses lifts in `M` of a basis of `M / x M`, then the
induced map on the quotients of the free module is a bijection. -/
private theorem quotSMulTop_map_bijective_of_basis_lifts
    {ι : Type*} [Finite ι] {x : R}
    (b : Module.Basis ι (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M))
    (v : ι → M)
    (hv : ∀ i, (Submodule.Quotient.mk (v i) : QuotSMulTop x M) = b i) :
    Function.Bijective (QuotSMulTop.map x (Finsupp.linearCombination R v)) := by
  -- TODO: express `QuotSMulTop x (ι →₀ R)` as `ι →₀ (R ⧸ (x))` through the tensor-model
  -- equivalence and show the induced map is `b.repr.symm`.
  sorry

/-- Helper for Lemma 10.106.5: lifts of a basis of `M / x M` generate `M`. -/
private theorem span_eq_top_of_basis_lifts
    {ι : Type*} [Finite ι] {x : R} (hx : x ∈ maximalIdeal R)
    (b : Module.Basis ι (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M))
    (v : ι → M)
    (hv : ∀ i, (Submodule.Quotient.mk (v i) : QuotSMulTop x M) = b i) :
    Submodule.span R (Set.range v) = ⊤ := by
  -- TODO: lift the quotient-basis coefficients from `R ⧸ (x)` back to `R` and apply
  -- Nakayama clause (8) to the finite set of chosen lifts.
  sorry

/- 
Layering for this item:
- `source-facing`: the Stacks hypothesis that `R` is Noetherian local, `M` is finite, `x` is
  `M`-regular, and the quotient `QuotSMulTop x M` is free over `R ⧸ (x)`;
- `core/canonical`: the owner objects `QuotSMulTop x M`, `IsSMulRegular M x`,
  `Module.FinitePresentation R M`, and the local-ring freeness machinery in
  `Mathlib.RingTheory.LocalRing.Module`;
- `bridge/view`: Noetherianity plus `Module.Finite R M` only serve to supply the canonical finite
  presentation instance `Module.finitePresentation_of_finite R M`.
-/

-- Proof sketch: choose lifts in `M` of a basis of `QuotSMulTop x M` over `R ⧸ (x)`,
-- obtaining a surjection
-- `R^n → M` by Nakayama. Any relation among the lifts has coefficients in `xR`; divide by `x` and
-- use that `x` is a nonzerodivisor on `M` to show the kernel `K` satisfies `xK = K`, hence
-- `K = 0` by Nakayama's lemma.
private theorem free_of_isSMulRegular_of_free_quotSMulTop_of_finitePresentation
    [Module.FinitePresentation R M] {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    [Module.Free (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M)] :
    Module.Free R M := by
  classical
  let I : Ideal R := Ideal.span ({x} : Set R)
  let b : Module.Basis (Module.Free.ChooseBasisIndex (R ⧸ I) (QuotSMulTop x M)) (R ⧸ I)
      (QuotSMulTop x M) := Module.Free.chooseBasis (R ⧸ I) (QuotSMulTop x M)
  let ι := Module.Free.ChooseBasisIndex (R ⧸ I) (QuotSMulTop x M)
  -- TODO: identify the canonical `(R ⧸ I)`-module structure on `QuotSMulTop x M` with the one
  -- used by `Module.Free`, then derive finiteness of the chosen basis index from
  -- `Module.Finite R (QuotSMulTop x M)`.
  haveI : Finite ι := by
    sorry
  choose v hv using fun i : ι ↦
    Submodule.mkQ_surjective (x • (⊤ : Submodule R M)) (b i)
  let π : (ι →₀ R) →ₗ[R] M := Finsupp.linearCombination R v
  have hquot_bij :
      Function.Bijective (QuotSMulTop.map x π) :=
    quotSMulTop_map_bijective_of_basis_lifts (b := b) (v := v) hv
  have hspan : Submodule.span R (Set.range v) = ⊤ :=
    span_eq_top_of_basis_lifts hx (b := b) (v := v) hv
  have hπ : Function.Surjective π := by
    -- The lifts generate `M`, so the free cover `π` is surjective.
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    simpa [π] using hspan
  let K : Submodule R (ι →₀ R) := LinearMap.ker π
  have hK_le_x_top : K ≤ x • (⊤ : Submodule R (ι →₀ R)) := by
    intro l hl
    have hzero : QuotSMulTop.map x π (Submodule.Quotient.mk l) = 0 := by
      have hπl : π l = 0 := by
        simpa [K, LinearMap.mem_ker] using hl
      simpa [QuotSMulTop.map_apply_mk, hπl]
    have hmk :
        (Submodule.Quotient.mk l : QuotSMulTop x (ι →₀ R)) = 0 :=
      hquot_bij.1 hzero
    exact (Submodule.Quotient.mk_eq_zero _).1 hmk
  have hquot_reg : IsSMulRegular ((ι →₀ R) ⧸ K) x := by
    -- Transport regularity across the quotient isomorphism coming from `π`.
    exact ((LinearMap.quotKerEquivOfSurjective π hπ).isSMulRegular_congr x).2 hreg
  have hK_inf : x • (⊤ : Submodule R (ι →₀ R)) ⊓ K ≤ x • K := by
    -- This is the formal “divide the relation by `x`” step.
    exact smul_top_inf_eq_smul_of_isSMulRegular_on_quot hquot_reg
  have hK_le_xK : K ≤ x • K := by
    intro l hl
    exact hK_inf ⟨hK_le_x_top hl, hl⟩
  have hK_finite : Module.Finite R K :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker π hπ)
  let _ : Module.Finite R K := hK_finite
  have hK_smul_top : I • (⊤ : Submodule R K) = ⊤ := by
    -- Reinterpret `K ≤ xK` as `IK = K` inside the submodule `K`.
    refine top_unique ?_
    intro k hk
    rw [Submodule.mem_smul_top_iff I K]
    simpa [I, Submodule.ideal_span_singleton_smul] using hK_le_xK k.2
  have hIjac : I ≤ Ring.jacobson R := by
    -- In a local ring, `(x)` is contained in the Jacobson radical.
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal R]
    exact (Ideal.span_singleton_le_iff_mem (maximalIdeal R)).2 hx
  have hK_subsingleton : Subsingleton K :=
    subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson (I := I) hK_smul_top hIjac
  have hK_bot : K = ⊥ := (Submodule.subsingleton_iff_eq_bot).1 hK_subsingleton
  have hπ_injective : Function.Injective π := (LinearMap.ker_eq_bot).1 hK_bot
  let e : (ι →₀ R) ≃ₗ[R] M := LinearEquiv.ofBijective π ⟨hπ_injective, hπ⟩
  -- The resulting linear equivalence transports the standard basis of the free module to `M`.
  exact Module.Free.of_basis (Finsupp.basisSingleOne.map e)

/-- Lemma 10.106.5: if `R` is a Noetherian local ring, `x ∈ maximalIdeal R` is a nonzerodivisor on
a finite `R`-module `M`, and `M / xM`, written as `QuotSMulTop x M`, is free over
`R ⧸ Ideal.span {x}`, then `M` is free over `R`. -/
theorem free_of_isSMulRegular_of_free_quotSMulTop
    {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    [Module.Free (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M)] :
    Module.Free R M := by
  let _ : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact free_of_isSMulRegular_of_free_quotSMulTop_of_finitePresentation hx hreg

end
