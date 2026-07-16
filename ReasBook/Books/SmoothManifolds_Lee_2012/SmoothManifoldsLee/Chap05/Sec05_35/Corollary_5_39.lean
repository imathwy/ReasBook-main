import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_30.Definition_5_30_extra_3
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_35.Notation_5_35_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_35.Proposition_5_38

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section SubmanifoldLevelSetTangent

universe uE uE' uH uH' uM

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ∞ S]

omit [TopologicalSpace M] in
/-- Helper for Corollary 5.39: on a global level set `S = Φ ⁻¹' {c}`, membership in `S` is
equivalent to having the same `Φ`-value as any chosen base point of `S`. -/
theorem mem_level_set_iff_eq_basepoint {k : ℕ} {Φ : M → Fin k → ℝ} {c : Fin k → ℝ} {p q : M}
    (hlevel : S = Φ ⁻¹' {c}) (hpS : p ∈ S) :
    q ∈ S ↔ Φ q = Φ p := by
  -- First identify the value of `Φ` at the chosen base point from the global level-set equation.
  have hpΦ : Φ p = c := by
    have hpΦmem : Φ p ∈ ({c} : Set (Fin k → ℝ)) := by
      change p ∈ Φ ⁻¹' ({c} : Set (Fin k → ℝ))
      simpa [hlevel] using hpS
    exact Set.mem_singleton_iff.mp hpΦmem
  -- Then both sides are the same singleton-membership condition for the value `c`.
  simp [hlevel, hpΦ]

/-- Helper for Corollary 5.39: surjectivity of the manifold derivative is equivalent to
surjectivity of the corresponding fixed-base tangent-coordinate operator, as long as both chart
side conditions needed to write that operator hold. -/
theorem surjective_mfderiv_iff_surjective_in_tangent_coordinates {k : ℕ} {Φ : M → Fin k → ℝ}
    {x y : M} (hy : y ∈ (extChartAt I x).source)
    (hΦy : Φ y ∈ (extChartAt 𝓘(ℝ, Fin k → ℝ) (Φ x)).source) :
    Function.Surjective (mfderiv I 𝓘(ℝ, Fin k → ℝ) Φ y) ↔
      Function.Surjective
        (inTangentCoordinates I 𝓘(ℝ, Fin k → ℝ) id Φ
          (fun z ↦ mfderiv I 𝓘(ℝ, Fin k → ℝ) Φ z) x y) := by
  have hy_chart : y ∈ (chartAt H x).source := by
    simpa [extChartAt_source] using hy
  have hΦy_chart : Φ y ∈ (chartAt (Fin k → ℝ) (Φ x)).source := by
    simpa [extChartAt_source] using hΦy
  -- Rewrite the coordinate operator as a chart derivative sandwich around `mfderiv Φ`.
  rw [inTangentCoordinates_eq_mfderiv_comp hy_chart hΦy_chart]
  constructor
  · intro hsurj
    -- Post- and pre-composition by the chart derivatives preserve surjectivity.
    exact
      (isInvertible_mfderiv_extChartAt hΦy).surjective.comp <|
        hsurj.comp
          (isInvertible_mfderivWithin_extChartAt_symm ((extChartAt I x).map_source hy)).surjective
  · intro hsurj
    -- Apply surjectivity to a charted target vector, then cancel the chart derivative.
    intro z
    obtain ⟨w, hw⟩ :=
      hsurj
        ((mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, Fin k → ℝ)
            (extChartAt 𝓘(ℝ, Fin k → ℝ) (Φ x)) (Φ y)) z)
    refine
      ⟨(mfderiv[Set.range I] (extChartAt I x).symm (extChartAt I x y)) w, ?_⟩
    exact (isInvertible_mfderiv_extChartAt hΦy).injective hw

/-- Helper for Corollary 5.39: once the fixed-base tangent-coordinate derivative is surjective at
the base point, it stays surjective on some open neighborhood that remains inside the chosen
source charts. -/
theorem exists_nhds_surjective_in_tangent_coordinates {k : ℕ} {Φ : M → Fin k → ℝ} {x : M}
    (hΦsmooth : ContMDiff I 𝓘(ℝ, Fin k → ℝ) ∞ Φ)
    (hAxsurj : Function.Surjective
      (inTangentCoordinates I 𝓘(ℝ, Fin k → ℝ) id Φ
        (fun z ↦ mfderiv I 𝓘(ℝ, Fin k → ℝ) Φ z) x x)) :
    ∃ U : TopologicalSpace.Opens M, x ∈ U ∧
      ((U : Set M) ⊆ (extChartAt I x).source) ∧
      ((U : Set M) ⊆ Φ ⁻¹' (extChartAt 𝓘(ℝ, Fin k → ℝ) (Φ x)).source) ∧
      ∀ y ∈ (U : Set M),
        Function.Surjective
          (inTangentCoordinates I 𝓘(ℝ, Fin k → ℝ) id Φ
            (fun z ↦ mfderiv I 𝓘(ℝ, Fin k → ℝ) Φ z) x y) := by
  let A : M → E →L[ℝ] (Fin k → ℝ) :=
    inTangentCoordinates I 𝓘(ℝ, Fin k → ℝ) id Φ
      (fun z ↦ mfderiv I 𝓘(ℝ, Fin k → ℝ) Φ z) x
  have hArange : (A x).range = ⊤ := LinearMap.range_eq_top.2 hAxsurj
  obtain ⟨B, hB⟩ := ContinuousLinearMap.exists_rightInverse_of_surjective (A x) hArange
  have hAmdiff :
      ContMDiffAt I 𝓘(ℝ, E →L[ℝ] (Fin k → ℝ)) 0 A x := by
    -- `ContMDiffAt.mfderiv_const` gives continuity of the fixed-base tangent-coordinate derivative.
    simpa [A] using hΦsmooth.contMDiffAt.mfderiv_const (m := 0) (by simp)
  have hAcont : ContinuousAt A x := hAmdiff.continuousAt
  have hABcont : ContinuousAt (fun y ↦ (A y).comp B) x := by
    -- Compose with the fixed right inverse to move surjectivity into endomorphisms of `ℝ^k`.
    exact (continuous_id.clm_comp_const B).continuousAt.comp hAcont
  have hBallPre :
      (fun y ↦ (A y).comp B) ⁻¹' Metric.ball (ContinuousLinearMap.id ℝ (Fin k → ℝ)) 1 ∈ nhds x := by
    apply hABcont.preimage_mem_nhds
    -- We center the perturbation argument at the exact identity `A x ∘ B = id`.
    simpa [hB] using
      (Metric.ball_mem_nhds (ContinuousLinearMap.id ℝ (Fin k → ℝ)) zero_lt_one)
  rcases mem_nhds_iff.mp hBallPre with ⟨V, hVsubset, hVopen, hVx⟩
  let U : TopologicalSpace.Opens M :=
    ⟨((extChartAt I x).source ∩
        (Φ ⁻¹' (extChartAt 𝓘(ℝ, Fin k → ℝ) (Φ x)).source)) ∩ V,
      ((isOpen_extChartAt_source x).inter
        ((isOpen_extChartAt_source (Φ x)).preimage hΦsmooth.continuous)).inter hVopen⟩
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · -- The neighborhood keeps the point inside both chart sources and the perturbation set.
    exact ⟨⟨mem_extChartAt_source x, mem_extChartAt_source (Φ x)⟩, hVx⟩
  · intro y hy
    exact hy.1.1
  · intro y hy
    exact hy.1.2
  · intro y hyU
    have hyV : (y : M) ∈ V := hyU.2
    have hNear :
        ‖ContinuousLinearMap.id ℝ (Fin k → ℝ) - (A y).comp B‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hVsubset hyV
    have hUnit : IsUnit ((A y).comp B) := by
      -- Endomorphisms within distance `< 1` of the identity are invertible.
      have hCancel :
          ContinuousLinearMap.id ℝ (Fin k → ℝ) -
              (ContinuousLinearMap.id ℝ (Fin k → ℝ) - (A y).comp B) =
            (A y).comp B := by
        ext z
        simp
      have hUnit' :
          IsUnit
            (ContinuousLinearMap.id ℝ (Fin k → ℝ) -
              (ContinuousLinearMap.id ℝ (Fin k → ℝ) - (A y).comp B)) :=
        isUnit_one_sub_of_norm_lt_one hNear
      exact hCancel ▸ hUnit'
    have hCompSurj : Function.Surjective ((A y).comp B) :=
      (ContinuousLinearMap.isUnit_iff_bijective.mp hUnit).2
    -- Surjectivity of `A y ∘ B` immediately implies surjectivity of `A y`.
    intro z
    obtain ⟨w, hw⟩ := hCompSurj z
    exact ⟨B w, hw⟩

theorem exists_open_neighborhood_surjective_mfderiv {k : ℕ} {Φ : M → Fin k → ℝ} {x : M}
    (hΦsmooth : ContMDiff I 𝓘(ℝ, Fin k → ℝ) ∞ Φ)
    (hsurj : Function.Surjective (mfderiv I 𝓘(ℝ, Fin k → ℝ) Φ x)) :
    ∃ U : TopologicalSpace.Opens M, x ∈ U ∧
      ∀ y : U, Function.Surjective (mfderiv I 𝓘(ℝ, Fin k → ℝ) Φ y) := by
  let A : M → E →L[ℝ] (Fin k → ℝ) :=
    inTangentCoordinates I 𝓘(ℝ, Fin k → ℝ) id Φ
      (fun z ↦ mfderiv I 𝓘(ℝ, Fin k → ℝ) Φ z) x
  have hAxsurj : Function.Surjective (A x) := by
    -- First move the base-point surjectivity statement into fixed tangent coordinates.
    simpa [A] using
      (surjective_mfderiv_iff_surjective_in_tangent_coordinates
        (I := I) (Φ := Φ) (x := x) (y := x)
        (mem_extChartAt_source x) (mem_extChartAt_source (Φ x))).mp hsurj
  rcases exists_nhds_surjective_in_tangent_coordinates (I := I) (Φ := Φ) (x := x)
      hΦsmooth hAxsurj with
    ⟨U, hxU, hUsource, hUtarget, hUsurj⟩
  refine ⟨U, hxU, ?_⟩
  intro y
  -- Then transport pointwise surjectivity back from the fixed chart model to `mfderiv Φ`.
  exact
    (surjective_mfderiv_iff_surjective_in_tangent_coordinates
      (I := I) (Φ := Φ) (x := x) (y := y)
      (hUsource y.2) (hUtarget y.2)).mpr <|
      hUsurj y y.2

/-- Helper for Corollary 5.39: a global defining function yields a local defining map on some open
neighborhood of each point of `S`. -/
theorem exists_local_defining_mapOn_nhds_of_isDefiningFunction {k : ℕ} {Φ : M → Fin k → ℝ}
    (hΦ : Set.IsDefiningFunction I S Φ) (p : S) :
    ∃ U : TopologicalSpace.Opens M, (p : M) ∈ U ∧
      IsLocalDefiningMapOn I 𝓘(ℝ, Fin k → ℝ) S (U : Set M) Φ := by
  rcases hΦ with ⟨c, hΦsmooth, hlevel, hsurj⟩
  -- Shrink to an open neighborhood where the submersion condition persists away from `S`.
  rcases exists_open_neighborhood_surjective_mfderiv hΦsmooth (hsurj (p : M) p.2) with
    ⟨U, hpU, hUderiv⟩
  refine ⟨U, hpU, ?_⟩
  refine
    { isOpen_source := U.2
      smoothOn := hΦsmooth.contMDiffOn
      mem_iff_eq := ?_
      surjective_mfderiv := ?_ }
  · intro p' q hp'S hp'U hqU
    -- On the chosen neighborhood, the defining set is still the fiber through the base point.
    exact mem_level_set_iff_eq_basepoint hlevel hp'S
  · intro p' hp'U
    -- The neighborhood was chosen precisely so that the derivative stays surjective everywhere.
    exact hUderiv ⟨p', hp'U⟩

/-- Corollary 5.39: if `S` is cut out globally by a defining function `Φ : M → ℝ^k`, then a
vector `v ∈ T_(p : M) M` is tangent to `S` exactly when the derivative of `Φ` at `p` applied to
`v` vanishes. -/
theorem tangent_iff_mfderiv_eq_zero_of_isDefiningFunction {k : ℕ} {Φ : M → Fin k → ℝ}
    (hS : IsSmoothEmbedding J I ∞ ((↑) : S → M))
    (hΦ : Set.IsDefiningFunction I S Φ) {p : S} (v : TangentSpace I (p : M)) :
    v ∈ T[J; p] ↔
      mfderiv I 𝓘(ℝ, Fin k → ℝ) Φ (p : M) v = 0 := by
  rcases exists_local_defining_mapOn_nhds_of_isDefiningFunction hΦ p with ⟨U, hpU, hU⟩
  -- Proposition 5.38 converts the local defining-map data into the tangent-space/kernel identity.
  rw [tangentSpace_eq_ker_mfderiv_of_isLocalDefiningMapOn hS hU p hpU]
  -- Kernel membership is exactly the vanishing of the derivative applied to `v`.
  exact LinearMap.mem_ker

end SubmanifoldLevelSetTangent
