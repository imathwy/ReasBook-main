import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

open MeasureTheory
open Set Filter

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]

/- Source/core/bridge triage:
- `source-facing`: `existsUnique_measure_integral_mul_right_eq`;
- `core/canonical`: `Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)`;
- `bridge/view`: `normalizedHaarMeasure` together with the normalization, uniqueness, and
  translation-invariance API below.
-/

/-- The canonical normalized Haar measure on a compact group `G`. -/
noncomputable abbrev normalizedHaarMeasure : Measure G :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)

/-- The textbook symbol `μ_G`, written in Lean as `μG`, for the normalized Haar measure on a
compact group `G`. -/
noncomputable abbrev μG : Measure G :=
  normalizedHaarMeasure

/-- The textbook right-translation integral invariance on continuous complex-valued functions. -/
def HasIntegralMulRightEq (μ : Measure G) : Prop :=
  ∀ f : ContinuousMap G ℂ, ∀ s : G, (∫ t, f t ∂μ) = ∫ t, f (t * s) ∂μ

/-- Helper for Theorem 4-5: the separation quotient carries its Borel measurable structure. -/
instance separationQuotientMeasurableSpace : MeasurableSpace (SeparationQuotient G) :=
  borel (SeparationQuotient G)

/-- Helper for Theorem 4-5: the separation quotient is equipped with the Borel σ-algebra. -/
instance separationQuotientBorelSpace : BorelSpace (SeparationQuotient G) :=
  ⟨rfl⟩

/-- Helper for Theorem 4-5: the separation quotient of a compact group is compact. -/
instance separationQuotientCompactSpace : CompactSpace (SeparationQuotient G) :=
  ⟨by
    simpa [Set.range_eq_univ.2 SeparationQuotient.surjective_mk] using
      (isCompact_univ.image SeparationQuotient.continuous_mk)⟩

omit [Group G] [CompactSpace G] [IsTopologicalGroup G] in
/-- Helper for Theorem 4-5: every measurable set in `G` is the preimage of its image in
`SeparationQuotient G`. -/
lemma measurableSet_image_separationQuotient_mk {s : Set G} (hs : MeasurableSet s) :
    MeasurableSet (SeparationQuotient.mk '' s) ∧
      SeparationQuotient.mk ⁻¹' (SeparationQuotient.mk '' s) = s := by
  -- Push the Borel-set construction through open sets, complements, and countable disjoint unions.
  refine MeasurableSet.induction_on_open ?open_case ?compl_case ?union_case s hs
  · intro t ht
    exact ⟨(SeparationQuotient.isOpenMap_mk t ht).measurableSet,
      SeparationQuotient.preimage_image_mk_open ht⟩
  · intro t ht h_ind
    rcases h_ind with ⟨ht_meas, ht_preimage⟩
    have hmem (x : G) : SeparationQuotient.mk x ∈ SeparationQuotient.mk '' t ↔ x ∈ t := by
      constructor
      · rintro ⟨y, hy, hxy⟩
        exact (SeparationQuotient.mk_eq_mk.1 hxy).mem_measurableSet_iff ht |>.1 hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hmemc (x : G) : SeparationQuotient.mk x ∈ SeparationQuotient.mk '' tᶜ ↔ x ∉ t := by
      constructor
      · rintro ⟨y, hy, hxy⟩ hx
        exact hy ((SeparationQuotient.mk_eq_mk.1 hxy).mem_measurableSet_iff ht |>.2 hx)
      · intro hx
        exact ⟨x, hx, rfl⟩
    have himage : SeparationQuotient.mk '' tᶜ = (SeparationQuotient.mk '' t)ᶜ := by
      ext q
      obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk q
      simpa [hmem x] using hmemc x
    exact ⟨by
      rw [himage]
      exact ht_meas.compl, by
      rw [himage, Set.preimage_compl, ht_preimage]⟩
  · intro f _hf hf h_ind
    have hImageUnion :
        SeparationQuotient.mk '' ⋃ i, f i = ⋃ i, SeparationQuotient.mk '' f i := by
      ext q
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
        exact Set.mem_iUnion.mpr ⟨i, ⟨x, hxi, rfl⟩⟩
      · rintro (hq : q ∈ ⋃ i, SeparationQuotient.mk '' f i)
        rcases Set.mem_iUnion.mp hq with ⟨i, x, hx, rfl⟩
        exact ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [hImageUnion] using MeasurableSet.iUnion (fun i ↦ (h_ind i).1)
    · calc
        SeparationQuotient.mk ⁻¹' (SeparationQuotient.mk '' ⋃ i, f i)
            = SeparationQuotient.mk ⁻¹' (⋃ i, SeparationQuotient.mk '' f i) := by
              rw [hImageUnion]
        _ = ⋃ i, SeparationQuotient.mk ⁻¹' (SeparationQuotient.mk '' f i) := by
              rw [Set.preimage_iUnion]
        _ = ⋃ i, f i := by
              simp [fun i ↦ (h_ind i).2]

omit [Group G] [CompactSpace G] [IsTopologicalGroup G] in
/-- Helper for Theorem 4-5: equality after pushing forward to `SeparationQuotient G` already
forces equality of measures on `G`. -/
lemma measure_eq_of_map_separationQuotient_eq (μ ν : Measure G)
    (hmap : Measure.map SeparationQuotient.mk μ = Measure.map SeparationQuotient.mk ν) :
    μ = ν := by
  -- Compare measures on the quotient image of each measurable set in `G`.
  ext s hs
  rcases measurableSet_image_separationQuotient_mk hs with ⟨hs_image, hs_preimage⟩
  have hmap_apply :=
    congrArg (fun m : Measure (SeparationQuotient G) ↦ m (SeparationQuotient.mk '' s)) hmap
  simpa [Measure.map_apply, SeparationQuotient.continuous_mk.measurable, hs_image, hs_preimage]
    using hmap_apply

omit [CompactSpace G] in
/-- Helper for Theorem 4-5: the textbook right-translation integral identity descends to
`SeparationQuotient G`. -/
lemma hasIntegralMulRightEq_mapSeparationQuotient (μ : Measure G)
    (hμ_right : HasIntegralMulRightEq μ) :
    HasIntegralMulRightEq (Measure.map SeparationQuotient.mk μ) := by
  -- Rewrite quotient integrals as integrals on `G`, then use `SeparationQuotient.mk_mul`.
  let mkContinuous : ContinuousMap G (SeparationQuotient G) :=
    ⟨SeparationQuotient.mk, SeparationQuotient.continuous_mk⟩
  have hmk_ae :
      AEMeasurable (mkContinuous : G → SeparationQuotient G) μ :=
    mkContinuous.continuous.aemeasurable
  intro f q
  obtain ⟨s, rfl⟩ := SeparationQuotient.surjective_mk q
  let fLift : ContinuousMap G ℂ :=
    f.comp mkContinuous
  let fTranslated : ContinuousMap (SeparationQuotient G) ℂ :=
    ⟨fun t ↦ f (t * SeparationQuotient.mk s), f.continuous.comp (continuous_mul_const _)⟩
  have hLift := hμ_right fLift s
  have hRightMap :
      ∫ t, fTranslated t ∂Measure.map SeparationQuotient.mk μ
        = ∫ t, fTranslated (SeparationQuotient.mk t) ∂μ := by
    simpa [mkContinuous] using
      (integral_map hmk_ae fTranslated.continuous.aestronglyMeasurable)
  calc
    ∫ t, f t ∂Measure.map SeparationQuotient.mk μ = ∫ t, fLift t ∂μ := by
      simpa [mkContinuous, fLift] using
        (integral_map hmk_ae f.continuous.aestronglyMeasurable)
    _ = ∫ t, fLift (t * s) ∂μ := hLift
    _ = ∫ t, fTranslated (SeparationQuotient.mk t) ∂μ := by
      simp [mkContinuous, fLift, fTranslated]
    _ = ∫ t, fTranslated t ∂Measure.map SeparationQuotient.mk μ := hRightMap.symm
    _ = ∫ t, f (t * SeparationQuotient.mk s) ∂Measure.map SeparationQuotient.mk μ := by
      rfl

omit [CompactSpace G] in
/-- Helper for Theorem 4-5: the source-facing right-translation integral identity gives equality
between `μ` and its right-translate pushforward on bounded continuous real test functions. -/
theorem integral_map_mulRight_eq_of_hasIntegralMulRightEq
    (μ : Measure G) [IsProbabilityMeasure μ] (hμ_right : HasIntegralMulRightEq μ)
    (f : BoundedContinuousFunction G ℝ) (s : G) :
    ∫ t, f t ∂Measure.map (Homeomorph.mulRight s) μ = ∫ t, f t ∂μ := by
  let fComplex : ContinuousMap G ℂ :=
    ⟨fun t ↦ (f t : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hComplex : (∫ t, fComplex t ∂μ) = ∫ t, fComplex (t * s) ∂μ :=
    hμ_right fComplex s
  have hReal :
      ((∫ t, f t ∂μ : ℝ) : ℂ) = ((∫ t, f (t * s) ∂μ : ℝ) : ℂ) := by
    simpa [fComplex, integral_complex_ofReal] using hComplex
  have hTranslated : ∫ t, f (t * s) ∂μ = ∫ t, f t ∂μ :=
    Complex.ofReal_injective hReal.symm
  -- Rewrite the pushed-forward integral as a translated integral, then apply the hypothesis.
  calc
    ∫ t, f t ∂Measure.map (Homeomorph.mulRight s) μ = ∫ t, f (t * s) ∂μ := by
      simpa using
        (Homeomorph.mulRight s).measurableEmbedding.integral_map (fun t : G ↦ f t)
    _ = ∫ t, f t ∂μ := hTranslated

omit [MeasurableSpace G] [BorelSpace G] in
/-- Helper for Theorem 4-5: on the separated compact quotient, the integral identity should force
right invariance of the measure. -/
lemma isMulRightInvariant_of_integral_mul_right_eq_separated
    (ν : Measure (SeparationQuotient G)) [IsProbabilityMeasure ν] [ν.Regular]
    (hν_right : HasIntegralMulRightEq ν) :
    ν.IsMulRightInvariant := by
  letI : CompactSpace (SeparationQuotient G) :=
    ⟨by
      simpa [Set.range_eq_univ.2 SeparationQuotient.surjective_mk] using
        (isCompact_univ.image SeparationQuotient.continuous_mk)⟩
  constructor
  intro q
  -- Compare `ν` with its right-translate on compactly supported real-valued test functions.
  letI : (Measure.map (Homeomorph.mulRight q) ν).Regular :=
    Measure.Regular.map (Homeomorph.mulRight q)
  refine Measure.ext_of_integral_eq_on_compactlySupported ?_
  intro f
  -- The source-facing integral identity already gives the required equality on bounded
  -- continuous functions, and compactly supported functions are a special case on the quotient.
  simpa using
    integral_map_mulRight_eq_of_hasIntegralMulRightEq
      (G := SeparationQuotient G) ν hν_right f.toBoundedContinuousFunction q

/-- The normalized Haar measure on a compact group has total mass `1`. -/
theorem normalizedHaarMeasure_univ :
    normalizedHaarMeasure (Set.univ : Set G) = 1 := by
  simpa [normalizedHaarMeasure] using
    (Measure.haarMeasure_self :
      Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
        (⊤ : TopologicalSpace.PositiveCompacts G) = 1)

/-- The normalized Haar measure on a compact group is a probability measure. -/
instance instIsProbabilityMeasureNormalizedHaarMeasure :
    IsProbabilityMeasure (normalizedHaarMeasure : Measure G) where
  measure_univ := normalizedHaarMeasure_univ

/-- The normalized Haar measure on a compact group is left-invariant. -/
instance instIsMulLeftInvariantNormalizedHaarMeasure :
    Measure.IsMulLeftInvariant (normalizedHaarMeasure : Measure G) :=
  inferInstance

/-- The normalized Haar measure on a compact group is right-invariant. -/
instance instIsMulRightInvariantNormalizedHaarMeasure :
    Measure.IsMulRightInvariant (normalizedHaarMeasure : Measure G) := by
  constructor
  intro g
  let ν : Measure G :=
    Measure.map (fun t : G ↦ t * g) normalizedHaarMeasure
  letI : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ]
    simp
  letI : ν.IsHaarMeasure := by
    dsimp [ν]
    infer_instance
  simpa [ν, normalizedHaarMeasure] using
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure ν normalizedHaarMeasure

/-- Helper for Theorem 4-5: the inverse of a right-invariant probability measure on a compact
group is a Haar measure. -/
lemma isHaarMeasure_inv_of_isProbabilityMeasure_of_isMulRightInvariant
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant] :
    μ.inv.IsHaarMeasure := by
  have hμinv_univ : μ.inv (Set.univ : Set G) = 1 := by
    rw [Measure.inv_apply]
    simp
  have hμinv_nonempty : (interior (Set.univ : Set G)).Nonempty := by
    simp [interior_univ]
  have hμinv_ne_zero : μ.inv (Set.univ : Set G) ≠ 0 := by
    simp [hμinv_univ]
  have hμinv_ne_top : μ.inv (Set.univ : Set G) ≠ ⊤ := by
    simp [hμinv_univ]
  -- Right invariance of `μ` turns inversion into the left invariance needed by the Haar criterion.
  exact Measure.isHaarMeasure_of_isCompact_nonempty_interior μ.inv Set.univ isCompact_univ
    hμinv_nonempty hμinv_ne_zero hμinv_ne_top

/-- Any right-invariant probability measure on a compact group is the normalized Haar measure. -/
theorem eq_normalizedHaarMeasure_of_isProbabilityMeasure_of_isMulRightInvariant
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant] :
    μ = normalizedHaarMeasure := by
  have hμinv_univ : μ.inv (Set.univ : Set G) = 1 := by
    rw [Measure.inv_apply]
    simp
  letI : IsProbabilityMeasure μ.inv := ⟨hμinv_univ⟩
  letI : μ.inv.IsHaarMeasure :=
    isHaarMeasure_inv_of_isProbabilityMeasure_of_isMulRightInvariant μ
  have hμGinv_univ : (normalizedHaarMeasure : Measure G).inv (Set.univ : Set G) = 1 := by
    rw [Measure.inv_apply]
    simp
  letI : IsProbabilityMeasure ((normalizedHaarMeasure : Measure G).inv) := ⟨hμGinv_univ⟩
  letI : ((normalizedHaarMeasure : Measure G).inv).IsHaarMeasure :=
    isHaarMeasure_inv_of_isProbabilityMeasure_of_isMulRightInvariant
      (normalizedHaarMeasure : Measure G)
  -- Compare the inverse measures, where both sides live on the canonical left-invariant API.
  have hInv : μ.inv = (normalizedHaarMeasure : Measure G).inv :=
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure μ.inv
      (normalizedHaarMeasure.inv : Measure G)
  simpa using congrArg Measure.inv hInv

/-- The textbook right-translation integral invariance on continuous functions implies the
canonical right-invariance class on measures. -/
theorem isMulRightInvariant_of_integral_mul_right_eq
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.Regular] (hμ_right : HasIntegralMulRightEq μ) :
    μ.IsMulRightInvariant := by
  let ν : Measure (SeparationQuotient G) := Measure.map SeparationQuotient.mk μ
  letI : CompactSpace (SeparationQuotient G) :=
    ⟨by
      simpa [Set.range_eq_univ.2 SeparationQuotient.surjective_mk] using
        (isCompact_univ.image SeparationQuotient.continuous_mk)⟩
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map SeparationQuotient.continuous_mk.aemeasurable
  letI : Measure.InnerRegularCompactLTTop ν :=
    Measure.InnerRegularCompactLTTop.map_of_continuous SeparationQuotient.continuous_mk
  letI : ν.Regular := inferInstance
  have hν_right : HasIntegralMulRightEq ν :=
    hasIntegralMulRightEq_mapSeparationQuotient μ hμ_right
  letI : ν.IsMulRightInvariant :=
    isMulRightInvariant_of_integral_mul_right_eq_separated ν hν_right
  constructor
  intro g
  -- Push the desired equality to the separated quotient, where the quotient measure is already
  -- known to be right invariant.
  apply measure_eq_of_map_separationQuotient_eq
  have hMapMul :
      Measure.map SeparationQuotient.mk (Measure.map (fun t : G ↦ t * g) μ)
        = Measure.map (fun t : G ↦ SeparationQuotient.mk (t * g)) μ := by
    simpa using
      (Measure.map_map (μ := μ) (f := fun t : G ↦ t * g) (g := SeparationQuotient.mk)
        SeparationQuotient.continuous_mk.measurable (continuous_mul_const g).measurable)
  have hMapQuot :
      Measure.map (fun t : G ↦ SeparationQuotient.mk t * SeparationQuotient.mk g) μ
        = Measure.map (fun q : SeparationQuotient G ↦ q * SeparationQuotient.mk g) ν := by
    simpa [ν, Function.comp] using
      (Measure.map_map (μ := μ) (f := SeparationQuotient.mk)
        (g := fun q : SeparationQuotient G ↦ q * SeparationQuotient.mk g)
        (continuous_mul_const _).measurable SeparationQuotient.continuous_mk.measurable).symm
  calc
    Measure.map SeparationQuotient.mk (Measure.map (fun t : G ↦ t * g) μ)
        = Measure.map (fun t : G ↦ SeparationQuotient.mk (t * g)) μ := hMapMul
    _ = Measure.map (fun t : G ↦ SeparationQuotient.mk t * SeparationQuotient.mk g) μ := by
          exact
            congrArg (fun f : G → SeparationQuotient G ↦ Measure.map f μ)
              (funext fun t ↦ SeparationQuotient.mk_mul t g)
    _ = Measure.map (fun q : SeparationQuotient G ↦ q * SeparationQuotient.mk g) ν := hMapQuot
    _ = ν := by
          simpa [ν] using
            (map_mul_right_eq_self ν (SeparationQuotient.mk g))
    _ = Measure.map SeparationQuotient.mk μ := by
          rfl

/-- A regular probability measure on a compact group with the textbook right-translation integral
invariance is the normalized Haar measure. -/
theorem eq_normalizedHaarMeasure_of_isProbabilityMeasure_of_hasIntegralMulRightEq
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.Regular] (hμ_right : HasIntegralMulRightEq μ) :
    μ = normalizedHaarMeasure := by
  letI : μ.IsMulRightInvariant :=
    isMulRightInvariant_of_integral_mul_right_eq μ hμ_right
  exact eq_normalizedHaarMeasure_of_isProbabilityMeasure_of_isMulRightInvariant μ

/-- A regular measure on a compact group with the textbook right-translation integral invariance
and total mass `1` is the normalized Haar measure. -/
theorem eq_normalizedHaarMeasure_of_integral_mul_right_eq
    (μ : Measure G) [μ.Regular] (hμ_right : HasIntegralMulRightEq μ)
    (hμ_univ : μ Set.univ = 1) :
    μ = normalizedHaarMeasure := by
  letI : IsProbabilityMeasure μ := ⟨hμ_univ⟩
  exact eq_normalizedHaarMeasure_of_isProbabilityMeasure_of_hasIntegralMulRightEq μ hμ_right

/-- Right translation does not change the integral of a function against the normalized Haar
measure. -/
theorem integral_normalizedHaarMeasure_mul_right_eq
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : G → E) (s : G) :
    (∫ t, f t ∂normalizedHaarMeasure) = ∫ t, f (t * s) ∂normalizedHaarMeasure := by
  have h : (∫ t, f (t * s) ∂normalizedHaarMeasure) = ∫ t, f t ∂normalizedHaarMeasure :=
    integral_mul_right_eq_self f s
  exact h.symm

/-- Left translation does not change the integral of a function against the normalized Haar
measure. -/
theorem integral_normalizedHaarMeasure_mul_left_eq
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : G → E) (s : G) :
    (∫ t, f t ∂normalizedHaarMeasure) = ∫ t, f (s * t) ∂normalizedHaarMeasure := by
  have h : (∫ t, f (s * t) ∂normalizedHaarMeasure) = ∫ t, f t ∂normalizedHaarMeasure :=
    integral_mul_left_eq_self f s
  exact h.symm

/-- A measure on a compact group satisfying Serre's right-translation integral identity and
normalized by `μ Set.univ = 1`. -/
class IsNormalizedRightInvariantMeasure (μ : Measure G) : Prop where
  hasIntegralMulRightEq : HasIntegralMulRightEq μ
  measure_univ : μ Set.univ = 1

/-- Helper for Theorem 4-5: the normalized Haar measure satisfies the source-facing
right-translation integral identity. -/
theorem hasIntegralMulRightEq_normalizedHaarMeasure :
    HasIntegralMulRightEq (normalizedHaarMeasure : Measure G) := by
  -- The canonical Haar API already gives right-translation invariance for all integrable targets.
  intro f s
  simpa using
    integral_normalizedHaarMeasure_mul_right_eq (G := G) (E := ℂ) (f := fun t ↦ f t) s

/-- Helper for Theorem 4-5: the normalized Haar measure is Serre's normalized right-invariant
source-facing measure. -/
instance instIsNormalizedRightInvariantMeasureNormalizedHaarMeasure :
    IsNormalizedRightInvariantMeasure (normalizedHaarMeasure : Measure G) where
  hasIntegralMulRightEq := hasIntegralMulRightEq_normalizedHaarMeasure
  measure_univ := normalizedHaarMeasure_univ

/-- Helper for Theorem 4-5: after passing to the separated quotient, a normalized source-facing
candidate has a regular probability companion agreeing on bounded continuous real test functions. -/
lemma exists_regularProbabilityCompanion_mapSeparationQuotient_of_isNormalizedRightInvariantMeasure
    (μ : Measure G) [IsNormalizedRightInvariantMeasure μ] :
    let ν : Measure (SeparationQuotient G) := Measure.map SeparationQuotient.mk μ
    ∃ νr : Measure (SeparationQuotient G), νr.Regular ∧ IsProbabilityMeasure νr ∧
      ∀ g : BoundedContinuousFunction (SeparationQuotient G) ℝ,
        ∫ x, g x ∂ν = ∫ x, g x ∂νr := by
  let ν : Measure (SeparationQuotient G) := Measure.map SeparationQuotient.mk μ
  letI : CompactSpace (SeparationQuotient G) :=
    ⟨by
      simpa [Set.range_eq_univ.2 SeparationQuotient.surjective_mk] using
        (isCompact_univ.image SeparationQuotient.continuous_mk)⟩
  letI : IsProbabilityMeasure μ := ⟨IsNormalizedRightInvariantMeasure.measure_univ (μ := μ)⟩
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map SeparationQuotient.continuous_mk.aemeasurable
  obtain ⟨νr, hνr_regular, _hνr_finite, hνr_eq⟩ := Measure.exists_regular_eq_of_compactSpace ν
  have hνr_real_univ : νr.real Set.univ = 1 := by
    -- Test the quotient regular companion on the constant-one function to transport normalization.
    simpa [integral_const] using
      (hνr_eq (1 : BoundedContinuousFunction (SeparationQuotient G) ℝ)).symm
  letI : IsProbabilityMeasure νr := (isProbabilityMeasure_iff_real).2 hνr_real_univ
  exact ⟨νr, hνr_regular, inferInstance, hνr_eq⟩

/-- Helper for Theorem 4-5: a regular companion of a finite measure on a compact Hausdorff
Borel space dominates the original measure on compact sets. -/
lemma measure_le_regularCompanion_of_isCompact
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [ν.Regular]
    (hμν : ∀ g : BoundedContinuousFunction X ℝ, ∫ x, g x ∂μ = ∫ x, g x ∂ν)
    {K : Set X} (hK : IsCompact K) :
    μ K ≤ ν K := by
  -- Compare compact sets through compactly supported continuous functions, which are bounded on a
  -- compact space.
  refine RealRMK.measure_le_of_isCompact_of_integral (μ := μ) (ν := ν) ?_ hK
  intro f
  simpa using (hμν f.toBoundedContinuousFunction).le

/-- Helper for Theorem 4-5: the same regular companion is dominated by the original measure on
open sets. -/
lemma regularCompanion_le_measure_of_isOpen
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [ν.Regular]
    (hμν : ∀ g : BoundedContinuousFunction X ℝ, ∫ x, g x ∂μ = ∫ x, g x ∂ν)
    {U : Set X} (hU : IsOpen U) :
    ν U ≤ μ U := by
  -- First identify the total masses by testing against the constant-one function.
  have hUnivReal : μ.real Set.univ = ν.real Set.univ := by
    simpa [integral_const] using hμν (1 : BoundedContinuousFunction X ℝ)
  have hUniv : μ Set.univ = ν Set.univ := by
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp <| by
      simpa [Measure.real_def] using hUnivReal
  -- Then compare the complements, which are compact in a compact Hausdorff space.
  have hCompl :
      μ Uᶜ ≤ ν Uᶜ :=
    measure_le_regularCompanion_of_isCompact μ ν hμν hU.isClosed_compl.isCompact
  have hMeasureComplν : ν U = ν Set.univ - ν Uᶜ := by
    simpa using
      (measure_compl (μ := ν) hU.isClosed_compl.measurableSet (measure_ne_top _ _))
  have hMeasureComplμ : μ U = μ Set.univ - μ Uᶜ := by
    simpa using
      (measure_compl (μ := μ) hU.isClosed_compl.measurableSet (measure_ne_top _ _))
  calc
    ν U = ν Set.univ - ν Uᶜ := hMeasureComplν
    _ = μ Set.univ - ν Uᶜ := by
      rw [hUniv]
    _ ≤ μ Set.univ - μ Uᶜ := by
      exact tsub_le_tsub_left hCompl _
    _ = μ U := hMeasureComplμ.symm

/-- Helper for Theorem 4-5: compact domination together with open domination forces equality of
total masses on a compact Borel space. -/
lemma measure_univ_eq_of_isCompact_le_of_isOpen_ge
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X)
    (hCompact : ∀ ⦃K : Set X⦄, IsCompact K → μ K ≤ ν K)
    (hOpen : ∀ ⦃U : Set X⦄, IsOpen U → ν U ≤ μ U) :
    μ Set.univ = ν Set.univ := by
  -- Compare both total masses on `univ`, which is simultaneously compact and open.
  apply le_antisymm
  · exact hCompact isCompact_univ
  · exact hOpen isOpen_univ

/-- Helper for Theorem 4-5: on a finite compact Borel space, domination on open sets transfers
back to the same domination direction on closed sets after complementing. -/
lemma closedMeasure_le_of_measure_univ_eq_of_isOpen_ge
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hUniv : μ Set.univ = ν Set.univ)
    (hOpen : ∀ ⦃U : Set X⦄, IsOpen U → ν U ≤ μ U)
    {F : Set X} (hF : IsClosed F) :
    μ F ≤ ν F := by
  -- Complement the open-set inequality and rewrite both measures using their common total mass.
  have hCompl : ν Fᶜ ≤ μ Fᶜ := hOpen hF.isOpen_compl
  have hMeasureComplν : ν F = ν Set.univ - ν Fᶜ := by
    simpa using
      (measure_compl (μ := ν) hF.isOpen_compl.measurableSet (measure_ne_top _ _))
  have hMeasureComplμ : μ F = μ Set.univ - μ Fᶜ := by
    simpa using
      (measure_compl (μ := μ) hF.isOpen_compl.measurableSet (measure_ne_top _ _))
  calc
    μ F = μ Set.univ - μ Fᶜ := hMeasureComplμ
    _ = ν Set.univ - μ Fᶜ := by rw [hUniv]
    _ ≤ ν Set.univ - ν Fᶜ := by exact tsub_le_tsub_left hCompl _
    _ = ν F := hMeasureComplν.symm

/-- Helper for Theorem 4-5: two measures that agree on bounded continuous real test functions also
agree on the level set `f ⁻¹' {1}` of a compactly supported continuous real function. -/
lemma measure_preimage_one_eq_of_forall_boundedContinuous_integral_eq
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hμν : ∀ g : BoundedContinuousFunction X ℝ, ∫ x, g x ∂μ = ∫ x, g x ∂ν)
    {f : X → ℝ} (hf : Continuous f) (h'f : HasCompactSupport f) :
    μ (f ⁻¹' {1}) = ν (f ⁻¹' {1}) := by
  obtain ⟨u, _, u_mem, u_lim⟩ :
      ∃ u, StrictAnti u ∧ (∀ n : ℕ, u n ∈ Set.Ioo 0 1) ∧
        Filter.Tendsto u Filter.atTop (nhds 0) :=
    exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ) < 1)
  let v : ℕ → ℝ → ℝ := fun n x ↦ thickenedIndicator (u_mem n).1 ({1} : Set ℝ) x
  have hv_cont (n : ℕ) : Continuous (v n) := by
    exact Continuous.comp' NNReal.continuous_coe
      (BoundedContinuousFunction.continuous (thickenedIndicator (u_mem n).1 ({1} : Set ℝ)))
  have hIntegralEq (n : ℕ) : ∫ x, v n (f x) ∂μ = ∫ x, v n (f x) ∂ν := by
    let g : BoundedContinuousFunction X ℝ :=
      BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ v n (f x)) ((hv_cont n).comp hf) 1
        (fun x ↦ by
          simpa only [Real.norm_eq_abs, v, NNReal.abs_eq] using
            (show ((thickenedIndicator (u_mem n).1 ({1} : Set ℝ)) (f x) : ℝ) ≤ 1 by
              norm_cast
              exact thickenedIndicator_le_one (u_mem n).1 ({1} : Set ℝ) (f x)))
    simpa [g] using hμν g
  have hTendsto :
      ∀ ρ : Measure X, IsFiniteMeasureOnCompacts ρ →
        Filter.Tendsto (fun n ↦ ∫ x, v n (f x) ∂ρ) Filter.atTop
          (nhds (∫ x, Set.indicator ({1} : Set ℝ) (fun _ ↦ (1 : ℝ)) (f x) ∂ρ)) := by
    intro ρ _hρ
    apply tendsto_integral_of_dominated_convergence
      (bound := (tsupport f).indicator (fun _ : X ↦ (1 : ℝ)))
    · intro n
      exact ((hv_cont n).comp hf).aestronglyMeasurable
    · exact IntegrableOn.integrable_indicator
        (integrableOn_const (μ := ρ) (s := tsupport f)
          (by simpa using (IsCompact.measure_lt_top (μ := ρ) h'f).ne))
        (isClosed_tsupport f).measurableSet
    · intro n
      refine Eventually.of_forall fun x ↦ ?_
      by_cases hx : x ∈ tsupport f
      · simp only [Real.norm_eq_abs, v, hx, indicator_of_mem]
        have hle : v n (f x) ≤ 1 := by
          simpa [v] using
            (show ((thickenedIndicator (u_mem n).1 ({1} : Set ℝ)) (f x) : ℝ) ≤ 1 by
              norm_cast
              exact thickenedIndicator_le_one (u_mem n).1 ({1} : Set ℝ) (f x))
        have hnonneg : 0 ≤ v n (f x) := by
          simp [v]
        rwa [abs_of_nonneg hnonneg]
      · simp only [Real.norm_eq_abs, v, hx, not_false_eq_true, indicator_of_notMem]
        rw [thickenedIndicator_zero]
        · simp
        · simpa [image_eq_zero_of_notMem_tsupport hx] using (u_mem n).2.le
    · filter_upwards with x
      have hx :=
        tendsto_pi_nhds.1
          (thickenedIndicator_tendsto_indicator_closure (fun n ↦ (u_mem n).1) u_lim
            ({1} : Set ℝ)) (f x)
      simp only [closure_singleton] at hx
      convert NNReal.tendsto_coe.2 hx using 1
      simp
  have hμ_tendsto := hTendsto μ inferInstance
  simp_rw [hIntegralEq] at hμ_tendsto
  have hν_tendsto := hTendsto ν inferInstance
  have hIndicatorIntegral :
      ∫ x, Set.indicator ({1} : Set ℝ) (fun _ ↦ (1 : ℝ)) (f x) ∂μ
        = ∫ x, Set.indicator ({1} : Set ℝ) (fun _ ↦ (1 : ℝ)) (f x) ∂ν :=
    tendsto_nhds_unique hμ_tendsto hν_tendsto
  have hReal :
      μ.real (f ⁻¹' {1}) = ν.real (f ⁻¹' {1}) := by
    have hIndicator :
        (fun x ↦ Set.indicator ({1} : Set ℝ) (fun _ ↦ (1 : ℝ)) (f x))
          = fun x ↦ Set.indicator (f ⁻¹' ({1} : Set ℝ)) (fun _ ↦ (1 : ℝ)) x := by
      ext x
      exact (indicator_comp_right f (s := ({1} : Set ℝ)) (g := fun _ ↦ (1 : ℝ)) (x := x)).symm
    have hf_meas : MeasurableSet (f ⁻¹' ({1} : Set ℝ)) :=
      (isClosed_singleton.preimage hf).measurableSet
    have hRealMul : μ.real (f ⁻¹' ({1} : Set ℝ)) * 1 = ν.real (f ⁻¹' ({1} : Set ℝ)) * 1 := by
      simpa only [hIndicator, hf_meas, integral_indicator_const, smul_eq_mul] using
        hIndicatorIntegral
    simpa using hRealMul
  have hCompactPreimage : IsCompact (f ⁻¹' ({1} : Set ℝ)) :=
    h'f.isCompact_preimage hf isClosed_singleton (by simp)
  rw [measureReal_eq_measureReal_iff hCompactPreimage.measure_lt_top.ne
    hCompactPreimage.measure_lt_top.ne] at hReal
  simpa using hReal

/-- Helper for Theorem 4-5: the regular probability companion of the separation-quotient
pushforward is already the canonical normalized Haar measure on the quotient. -/
lemma regularCompanion_eq_normalizedHaarMeasure_of_isNormalizedRightInvariantMeasure
    (μ : Measure G) [IsNormalizedRightInvariantMeasure μ] :
    let ν : Measure (SeparationQuotient G) := Measure.map SeparationQuotient.mk μ
    ∃ νr : Measure (SeparationQuotient G), νr.Regular ∧ IsProbabilityMeasure νr ∧
      νr = (normalizedHaarMeasure : Measure (SeparationQuotient G)) ∧
      ∀ g : BoundedContinuousFunction (SeparationQuotient G) ℝ,
        ∫ x, g x ∂ν = ∫ x, g x ∂νr := by
  let ν : Measure (SeparationQuotient G) := Measure.map SeparationQuotient.mk μ
  have hν_right : HasIntegralMulRightEq ν :=
    hasIntegralMulRightEq_mapSeparationQuotient μ
      (IsNormalizedRightInvariantMeasure.hasIntegralMulRightEq (μ := μ))
  letI : IsProbabilityMeasure μ := ⟨IsNormalizedRightInvariantMeasure.measure_univ (μ := μ)⟩
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map SeparationQuotient.continuous_mk.aemeasurable
  rcases
      exists_regularProbabilityCompanion_mapSeparationQuotient_of_isNormalizedRightInvariantMeasure
        (G := G) (μ := μ) with
    ⟨νr, hνr_regular, hνr_prob, hνr_eq⟩
  letI : νr.Regular := hνr_regular
  letI : IsProbabilityMeasure νr := hνr_prob
  have hνr_map_eq :
      ∀ g : BoundedContinuousFunction (SeparationQuotient G) ℝ, ∀ q : SeparationQuotient G,
        ∫ x, g x ∂Measure.map (Homeomorph.mulRight q) νr = ∫ x, g x ∂νr := by
    intro g q
    let gTranslated : BoundedContinuousFunction (SeparationQuotient G) ℝ :=
      g.compContinuous ⟨Homeomorph.mulRight q, (Homeomorph.mulRight q).continuous⟩
    have hMapνr :
        ∫ x, g x ∂Measure.map (Homeomorph.mulRight q) νr = ∫ x, gTranslated x ∂νr := by
      simpa [gTranslated] using
        (Homeomorph.mulRight q).measurableEmbedding.integral_map
          (fun x : SeparationQuotient G ↦ g x)
    have hTranslateEq : ∫ x, gTranslated x ∂νr = ∫ x, gTranslated x ∂ν := by
      simpa [gTranslated] using (hνr_eq gTranslated).symm
    have hMapνTranslated :
        ∫ x, g x ∂Measure.map (Homeomorph.mulRight q) ν = ∫ x, gTranslated x ∂ν := by
      simpa [gTranslated] using
        (Homeomorph.mulRight q).measurableEmbedding.integral_map
          (fun x : SeparationQuotient G ↦ g x) (μ := ν)
    have hMapν :
        ∫ x, gTranslated x ∂ν = ∫ x, g x ∂ν := by
      exact hMapνTranslated.symm.trans
        (integral_map_mulRight_eq_of_hasIntegralMulRightEq
          (G := SeparationQuotient G) ν hν_right g q)
    have hBaseEq : ∫ x, g x ∂ν = ∫ x, g x ∂νr := hνr_eq g
    calc
      ∫ x, g x ∂Measure.map (Homeomorph.mulRight q) νr = ∫ x, gTranslated x ∂νr := hMapνr
      _ = ∫ x, gTranslated x ∂ν := hTranslateEq
      _ = ∫ x, g x ∂ν := hMapν
      _ = ∫ x, g x ∂νr := hBaseEq
  have hνr_rightInvariant : νr.IsMulRightInvariant := by
    constructor
    intro q
    letI : (Measure.map (Homeomorph.mulRight q) νr).Regular :=
      Measure.Regular.map (Homeomorph.mulRight q)
    -- Compare translated and untranslated regular measures on compactly supported real functions.
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    simpa using hνr_map_eq f.toBoundedContinuousFunction q
  letI : νr.IsMulRightInvariant := hνr_rightInvariant
  -- Once the regular companion is right invariant and normalized, the canonical uniqueness theorem
  -- identifies it with normalized Haar measure on the quotient.
  exact ⟨νr, hνr_regular, hνr_prob,
    eq_normalizedHaarMeasure_of_isProbabilityMeasure_of_isMulRightInvariant νr, hνr_eq⟩

/-- Helper for Theorem 4-5: the separation-quotient pushforward of any normalized right-invariant
measure is the canonical normalized Haar measure on the quotient. -/
lemma mapSeparationQuotient_eq_normalizedHaarMeasure_of_isNormalizedRightInvariantMeasure
    (μ : Measure G) [IsNormalizedRightInvariantMeasure μ] :
    Measure.map SeparationQuotient.mk μ
      = (normalizedHaarMeasure : Measure (SeparationQuotient G)) := by
  let ν : Measure (SeparationQuotient G) := Measure.map SeparationQuotient.mk μ
  letI : IsProbabilityMeasure μ := ⟨IsNormalizedRightInvariantMeasure.measure_univ (μ := μ)⟩
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map SeparationQuotient.continuous_mk.aemeasurable
  rcases regularCompanion_eq_normalizedHaarMeasure_of_isNormalizedRightInvariantMeasure
      (G := G) (μ := μ) with ⟨νr, hνr_regular, hνr_prob, hνr_haar, hνr_eq⟩
  letI : νr.Regular := hνr_regular
  letI : IsProbabilityMeasure νr := hνr_prob
  letI : νr.IsMulLeftInvariant := by
    rw [hνr_haar]
    infer_instance
  have hνr_le : ∀ ⦃s : Set (SeparationQuotient G)⦄, MeasurableSet s → νr s ≤ ν s := by
    intro s hs
    refine le_of_forall_lt fun r hr ↦ ?_
    rcases
        (Measure.innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_group
          (μ := νr) (U := s) ⟨hs, measure_ne_top _ _⟩ r hr) with
      ⟨K, hKs, ⟨f, hf, hf_comp, hK⟩, hrK⟩
    have hK_eq : νr (f ⁻¹' ({1} : Set ℝ)) = ν (f ⁻¹' ({1} : Set ℝ)) := by
      simpa using
        (measure_preimage_one_eq_of_forall_boundedContinuous_integral_eq νr ν
          (fun g ↦ (hνr_eq g).symm) hf hf_comp)
    calc
      r < νr K := hrK
      _ = ν (f ⁻¹' ({1} : Set ℝ)) := by simpa [hK] using hK_eq
      _ ≤ ν s := by simpa [hK] using (measure_mono hKs : ν K ≤ ν s)
  have hν_eq : ν = νr := by
    ext s hs
    apply le_antisymm
    · have hCompl := hνr_le hs.compl
      calc
        ν s = ν Set.univ - ν sᶜ := by
          simpa using (measure_compl (μ := ν) hs.compl (measure_ne_top _ _))
        _ = 1 - ν sᶜ := by simp
        _ ≤ 1 - νr sᶜ := by exact tsub_le_tsub_left hCompl _
        _ = νr Set.univ - νr sᶜ := by simp
        _ = νr s := by
          simpa using (measure_compl (μ := νr) hs.compl (measure_ne_top _ _)).symm
    · exact hνr_le hs
  simpa [ν] using hν_eq.trans hνr_haar

/-- Theorem 4-5 — Existence and Uniqueness of Normalized Haar Measure: on a compact group `G`,
there exists a unique measure `μ` such that every continuous `f : G → ℂ` has the same integral as
its right translate `fun t ↦ f (t * s)` for every `s : G`, and `μ Set.univ = 1`. -/
theorem existsUnique_measure_integral_mul_right_eq :
    ∃! μ : Measure G, IsNormalizedRightInvariantMeasure μ := by
  refine ⟨normalizedHaarMeasure, ?_, ?_⟩
  · infer_instance
  · intro μ hμ
    letI : IsNormalizedRightInvariantMeasure μ := hμ
    -- Route correction: first identify both source-facing measures after pushing to the separated
    -- quotient, where regularity is recovered from the regular companion and uniqueness is known.
    have hμ_map :
        Measure.map SeparationQuotient.mk μ
          = (normalizedHaarMeasure : Measure (SeparationQuotient G)) :=
      mapSeparationQuotient_eq_normalizedHaarMeasure_of_isNormalizedRightInvariantMeasure
        (μ := μ)
    have hμG_map :
        Measure.map SeparationQuotient.mk (normalizedHaarMeasure : Measure G)
          = (normalizedHaarMeasure : Measure (SeparationQuotient G)) :=
      mapSeparationQuotient_eq_normalizedHaarMeasure_of_isNormalizedRightInvariantMeasure
        (μ := (normalizedHaarMeasure : Measure G))
    exact
      measure_eq_of_map_separationQuotient_eq μ normalizedHaarMeasure
        (hμ_map.trans hμG_map.symm)

/-- Moreover, a measure satisfying Serre's right-translation identity and normalization is also
invariant under left translations. -/
theorem integral_mul_left_eq_of_isNormalizedRightInvariantMeasure
    (μ : Measure G) [IsNormalizedRightInvariantMeasure μ] (f : ContinuousMap G ℂ) (s : G) :
    (∫ t, f t ∂μ) = ∫ t, f (s * t) ∂μ := by
  -- Route correction: derive left invariance from uniqueness of the normalized right-invariant
  -- measure instead of rebuilding a second invariance argument from scratch.
  rcases existsUnique_measure_integral_mul_right_eq (G := G) with ⟨μ0, hμ0, huniq⟩
  have hμ : μ = μ0 :=
    huniq μ (by infer_instance)
  have hμ0 : μ0 = (normalizedHaarMeasure : Measure G) :=
    huniq (normalizedHaarMeasure : Measure G) inferInstance |>.symm
  calc
    ∫ t, f t ∂μ = ∫ t, f t ∂(normalizedHaarMeasure : Measure G) := by
      simp [hμ, hμ0]
    _ = ∫ t, f (s * t) ∂(normalizedHaarMeasure : Measure G) := by
      simpa using
        integral_normalizedHaarMeasure_mul_left_eq (G := G) (E := ℂ) (f := fun t ↦ f t) s
    _ = ∫ t, f (s * t) ∂μ := by
      simp [hμ, hμ0]
