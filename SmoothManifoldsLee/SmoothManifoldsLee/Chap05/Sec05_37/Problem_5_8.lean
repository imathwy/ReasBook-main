import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import SmoothManifoldsLee.Chap01.Sec01.Definition_1_extra_1
import SmoothManifoldsLee.Chap01.Sec01_03.Definition_1_3_extra_1
import SmoothManifoldsLee.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifoldsLee.Chap05.Sec05_29.Theorem_5_8.Common
import SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_2
import SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_4
import SmoothManifoldsLee.Chap05.Sec05_36.Theorem_5_51

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped ContDiff Manifold Topology

noncomputable section

universe uE uM

-- Semantic recall note: no `lean_leansearch` tool was available in this environment; local
-- repository and mathlib inspection verified the standard sphere manifold instance from
-- `Mathlib.Geometry.Manifold.Instances.Sphere`, with ambient dimension written as `Fin (n + 1)`.

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]

local notation "dimM" => Module.finrank ℝ E
local notation "boundarySphere" =>
  Metric.sphere (0 : EuclideanSpace ℝ (Fin ((dimM - 1) + 1))) 1

/-- Helper for Problem 5-8: an ordered basis packages the ambient continuous linear identification
between `ℝ^dimM` and `E`. -/
noncomputable def basis_model_continuousLinearEquiv
    (b : Module.Basis (Fin dimM) ℝ E) :
    EuclideanSpace ℝ (Fin dimM) ≃L[ℝ] E :=
  let e : E ≃ₗ[ℝ] Fin dimM → ℝ := b.equivFun
  (EuclideanSpace.equiv (Fin dimM) ℝ).trans e.symm.toContinuousLinearEquiv

/-- Helper for Problem 5-8: an ordered basis gives a fixed diffeomorphism from `ℝ^dimM` to the
ambient model space `E`. -/
noncomputable def basis_model_diffeomorph
    (b : Module.Basis (Fin dimM) ℝ E) :
    EuclideanSpace ℝ (Fin dimM) ≃ₘ[ℝ] E :=
  (basis_model_continuousLinearEquiv (E := E) b).toDiffeomorph

/-- Helper for Problem 5-8: transport the ambient charted-space structure on `M` from model space
`E` to the Euclidean model `ℝ^dimM` using a fixed basis chart on `E`. -/
noncomputable abbrev basis_model_chartedSpace
    (b : Module.Basis (Fin dimM) ℝ E) :
    ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M := by
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    (basis_model_diffeomorph (E := E) b).symm.toHomeomorph.toOpenPartialHomeomorph
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) E :=
    eModel.singletonChartedSpace (by
      ext x
      simp [eModel])
  exact ChartedSpace.comp (EuclideanSpace ℝ (Fin dimM)) E M

/-- Helper for Problem 5-8: conjugating an `E`-smooth chart transition by the fixed basis model
change produces a Euclidean-smooth transition. -/
lemma basis_model_transition_mem_contDiffGroupoid
    (b : Module.Basis (Fin dimM) ℝ E)
    {e : OpenPartialHomeomorph E E}
    (he : e ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℝ E)) :
    let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
      (basis_model_diffeomorph (E := E) b).symm.toHomeomorph.toOpenPartialHomeomorph
    eModel.symm.trans e.trans eModel ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM) := by
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    (basis_model_diffeomorph (E := E) b).symm.toHomeomorph.toOpenPartialHomeomorph
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at he ⊢
  have he_left :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞) (e : E → E) e.source := by
    -- The given transition is already smooth in the original `E`-coordinates.
    simpa using he.1
  have he_right :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞) (e.symm : E → E) e.target := by
    -- The inverse transition is smooth for the same reason.
    simpa using he.2
  have heModel_contDiff :
      ContDiff ℝ (⊤ : WithTop ℕ∞)
        (eModel : E → EuclideanSpace ℝ (Fin dimM)) := by
    -- The model change is the inverse of a continuous linear equivalence.
    simpa [eModel, basis_model_diffeomorph, basis_model_continuousLinearEquiv] using
      (basis_model_continuousLinearEquiv (E := E) b).symm.toContinuousLinearMap.contDiff
  have heModel_symm_contDiff :
      ContDiff ℝ (⊤ : WithTop ℕ∞)
        (eModel.symm : EuclideanSpace ℝ (Fin dimM) → E) := by
    -- Its inverse is the original continuous linear equivalence.
    simpa [eModel, basis_model_diffeomorph, basis_model_continuousLinearEquiv] using
      (basis_model_continuousLinearEquiv (E := E) b).toContinuousLinearMap.contDiff
  constructor
  · -- Compose the old transition with the fixed model change and its inverse.
    have hmid :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin dimM) ↦ e (eModel.symm x))
          (eModel.symm ⁻¹' e.source) := by
      refine he_left.comp heModel_symm_contDiff.contDiffOn ?_
      intro x hx
      simpa using hx
    have hfinal :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin dimM) ↦ eModel (e (eModel.symm x)))
          (eModel.symm ⁻¹' e.source) := by
      refine heModel_contDiff.contDiffOn.comp hmid ?_
      intro x hx
      simp [eModel]
    simpa [eModel, Function.comp, OpenPartialHomeomorph.trans_source] using hfinal
  · -- The inverse transition is handled by the same conjugation calculation.
    have hmid :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin dimM) ↦ e.symm (eModel.symm x))
          (eModel.symm ⁻¹' e.target) := by
      refine he_right.comp heModel_symm_contDiff.contDiffOn ?_
      intro x hx
      simpa using hx
    have hfinal :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin dimM) ↦ eModel (e.symm (eModel.symm x)))
          (eModel.symm ⁻¹' e.target) := by
      refine heModel_contDiff.contDiffOn.comp hmid ?_
      intro x hx
      simp [eModel]
    simpa [eModel, Function.comp, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc] using
      hfinal

/-- Helper for Problem 5-8: conjugating a Euclidean-smooth transition by the inverse fixed basis
model change recovers an `E`-smooth transition. -/
lemma basis_model_transition_mem_contDiffGroupoid_symm
    (b : Module.Basis (Fin dimM) ℝ E)
    {e : OpenPartialHomeomorph E E}
    (he :
      let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
        (basis_model_diffeomorph (E := E) b).symm.toHomeomorph.toOpenPartialHomeomorph
      eModel.symm.trans e.trans eModel ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM)) :
    e ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℝ E) := by
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    (basis_model_diffeomorph (E := E) b).symm.toHomeomorph.toOpenPartialHomeomorph
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at he ⊢
  have he_left :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞)
        (eModel.symm.trans e.trans eModel :
          EuclideanSpace ℝ (Fin dimM) → EuclideanSpace ℝ (Fin dimM))
        (eModel.symm.trans e.trans eModel).source := by
    -- The Euclidean transition is smooth on its source by hypothesis.
    simpa using he.1
  have he_right :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞)
        ((eModel.symm.trans e.trans eModel).symm :
          EuclideanSpace ℝ (Fin dimM) → EuclideanSpace ℝ (Fin dimM))
        (eModel.symm.trans e.trans eModel).target := by
    -- Its inverse is smooth for the same reason.
    simpa using he.2
  have heModel_contDiff :
      ContDiff ℝ (⊤ : WithTop ℕ∞)
        (eModel : E → EuclideanSpace ℝ (Fin dimM)) := by
    -- The basis model change is a global smooth linear equivalence.
    simpa [eModel, basis_model_diffeomorph, basis_model_continuousLinearEquiv] using
      (basis_model_continuousLinearEquiv (E := E) b).symm.toContinuousLinearMap.contDiff
  have heModel_symm_contDiff :
      ContDiff ℝ (⊤ : WithTop ℕ∞)
        (eModel.symm : EuclideanSpace ℝ (Fin dimM) → E) := by
    -- So is its inverse.
    simpa [eModel, basis_model_diffeomorph, basis_model_continuousLinearEquiv] using
      (basis_model_continuousLinearEquiv (E := E) b).toContinuousLinearMap.contDiff
  constructor
  · -- Pull the Euclidean transition back through the global model change.
    have hmid :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : E ↦
            (eModel.symm.trans e.trans eModel) (eModel x))
          (eModel ⁻¹' (eModel.symm.trans e.trans eModel).source) := by
      refine he_left.comp heModel_contDiff.contDiffOn ?_
      intro x hx
      simpa using hx
    have hfinal :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : E ↦ eModel.symm ((eModel.symm.trans e.trans eModel) (eModel x)))
          (eModel ⁻¹' (eModel.symm.trans e.trans eModel).source) := by
      refine heModel_symm_contDiff.contDiffOn.comp hmid ?_
      intro x hx
      simp [eModel]
    simpa [eModel, Function.comp, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc] using
      hfinal
  · -- The inverse transition is transported back by the same calculation.
    have hmid :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : E ↦
            (eModel.symm.trans e.trans eModel).symm (eModel x))
          (eModel ⁻¹' (eModel.symm.trans e.trans eModel).target) := by
      refine he_right.comp heModel_contDiff.contDiffOn ?_
      intro x hx
      simpa using hx
    have hfinal :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : E ↦ eModel.symm ((eModel.symm.trans e.trans eModel).symm (eModel x)))
          (eModel ⁻¹' (eModel.symm.trans e.trans eModel).target) := by
      refine heModel_symm_contDiff.contDiffOn.comp hmid ?_
      intro x hx
      simp [eModel]
    simpa [eModel, Function.comp, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc] using
      hfinal

/-- Helper for Problem 5-8: after transporting the ambient charts through a basis of `E`, the
manifold `M` carries the expected Euclidean smooth structure. -/
lemma basis_model_isManifold
    (b : Module.Basis (Fin dimM) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace (E := E) (M := M) b
    IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M := by
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    (basis_model_diffeomorph (E := E) b).symm.toHomeomorph.toOpenPartialHomeomorph
  have heModel_source : eModel.source = Set.univ := by
    -- The basis model change is global, so its source is all of `E`.
    ext x
    simp [eModel]
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) E :=
    eModel.singletonChartedSpace heModel_source
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
    basis_model_chartedSpace (E := E) (M := M) b
  have hGroupoid : HasGroupoid M (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eModel := by
      simpa [eModel] using eModel.singletonChartedSpace_mem_atlas_eq
        (h := heModel_source) f hf
    have hf'Eq : f' = eModel := by
      simpa [eModel] using eModel.singletonChartedSpace_mem_atlas_eq
        (h := heModel_source) f' hf'
    subst f
    subst f'
    have hcompat_old :
        c.symm.trans c' ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℝ E) := by
      -- After removing the fixed basis chart, compatibility is the original smooth compatibility
      -- of the `E`-atlas on `M`.
      exact HasGroupoid.compatible (G := contDiffGroupoid (⊤ : WithTop ℕ∞)
        (modelWithCornersSelf ℝ E)) hc hc'
    simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc, eModel] using
      basis_model_transition_mem_contDiffGroupoid (E := E) b hcompat_old
  -- Once the transported atlas is compatible, `IsManifold.mk'` packages the Euclidean structure.
  exact IsManifold.mk' (𝓡 dimM) (⊤ : WithTop ℕ∞) M

/-- Helper for Problem 5-8: an ambient smooth chart for the original `E`-model remains a maximal
atlas chart after composing with the fixed basis identification to `ℝ^dimM`. -/
lemma basis_model_chart_mem_maximalAtlas
    (b : Module.Basis (Fin dimM) ℝ E)
    {chart : OpenPartialHomeomorph M E}
    (hchart :
      chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace (E := E) (M := M) b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold (E := E) (M := M) b
    let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
      (basis_model_diffeomorph (E := E) b).symm.toHomeomorph.toOpenPartialHomeomorph
    chart.trans eModel ∈ IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) M := by
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    (basis_model_diffeomorph (E := E) b).symm.toHomeomorph.toOpenPartialHomeomorph
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  rcases he' with ⟨f, hf, c, hc, rfl⟩
  have hfEq : f = eModel := by
    -- Every Euclidean ambient chart comes from the unique singleton model chart.
    simpa [eModel] using eModel.singletonChartedSpace_mem_atlas_eq
      (h := by
        ext x
        simp [eModel]) f hf
  subst f
  have hcompat_old :
      chart.symm.trans c ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℝ E) ∧
        c.symm.trans chart ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℝ E) :=
    IsManifold.mem_maximalAtlas_iff.1 hchart c hc
  constructor
  · -- After conjugating the old transition by the fixed model map, it is Euclidean smooth.
    simpa [eModel, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using
      basis_model_transition_mem_contDiffGroupoid (E := E) b hcompat_old.1
  · -- The inverse transition is transported by the same conjugation.
    simpa [eModel, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using
      basis_model_transition_mem_contDiffGroupoid (E := E) b hcompat_old.2

/-- Helper for Problem 5-8: the witness chart of a regular coordinate ball is defined on the ball
itself because it is defined on the closure. -/
lemma regular_coordinate_ball_subset_source {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    ∃ chart : OpenPartialHomeomorph M E,
      chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
        B ⊆ chart.source ∧
        ∃ r r' : ℝ,
          0 < r ∧
            r < r' ∧
            chart '' B = Metric.ball (0 : E) r ∧
            chart '' closure B = Metric.closedBall (0 : E) r ∧
            chart.target = Metric.ball (0 : E) r' := by
  rcases hB with ⟨chart, hchart, hclosure, r, r', hr, hr', himage, hclosure_image, htarget⟩
  refine ⟨chart, hchart, ?_, r, r', hr, hr', himage, hclosure_image, htarget⟩
  -- The regular-coordinate-ball data already puts the whole closure in the chart source.
  exact subset_closure.trans hclosure

/-- Helper for Problem 5-8: the closed Euclidean ball corresponding to a regular coordinate ball
lies inside the target of the witnessing chart. -/
lemma regular_coordinate_ball_closedBall_subset_target {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    ∃ chart : OpenPartialHomeomorph M E,
      chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
        ∃ r r' : ℝ,
          0 < r ∧
            r < r' ∧
            Metric.closedBall (0 : E) r ⊆ chart.target ∧
            chart '' B = Metric.ball (0 : E) r ∧
            chart '' closure B = Metric.closedBall (0 : E) r ∧
            chart.target = Metric.ball (0 : E) r' := by
  rcases hB with ⟨chart, hchart, hclosure, r, r', hr, hr', himage, hclosure_image, htarget⟩
  refine ⟨chart, hchart, r, r', hr, hr', ?_, himage, hclosure_image, htarget⟩
  intro y hy
  rw [← hclosure_image] at hy
  rcases hy with ⟨x, hx, rfl⟩
  -- Points in the image of the closure come from the chart source, hence land in the target.
  exact chart.map_source (hclosure hx)

/-- Helper for Problem 5-8: a regular coordinate ball is open. -/
lemma regular_coordinate_ball_is_open {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    IsOpen B := by
  rcases hB with ⟨chart, -, hclosure, r, r', hr, hr', himage, hclosure_image, htarget⟩
  have hB_source : B ⊆ chart.source := subset_closure.trans hclosure
  have hclosedBall_target :
      Metric.closedBall (0 : E) r ⊆ chart.target := by
    intro y hy
    rw [← hclosure_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    -- The closure image comes from points in the chart source, so it stays inside the target.
    exact chart.map_source (hclosure hx)
  have hball_target : Metric.ball (0 : E) r ⊆ chart.target :=
    Metric.ball_subset_closedBall.trans hclosedBall_target
  have hsymm_image : chart.symm '' Metric.ball (0 : E) r = B := by
    -- Pulling the chart image of `B` back through the inverse chart recovers `B`.
    rw [← himage]
    simpa using chart.symm_image_image_of_subset_source (s := B) hB_source
  have hOpen_symm_image : IsOpen (chart.symm '' Metric.ball (0 : E) r) := by
    -- The inverse chart is an open map on its source, namely the chart target.
    simpa [inter_eq_right.2 hball_target] using
      chart.symm.isOpen_image_source_inter (Metric.isOpen_ball : IsOpen (Metric.ball (0 : E) r))
  simpa [hsymm_image] using hOpen_symm_image

/-- Helper for Problem 5-8: the complement of a regular coordinate ball is closed. -/
lemma regular_coordinate_ball_compl_isClosed {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    IsClosed (Set.compl B) := by
  -- Closedness is the complement version of openness of the regular coordinate ball.
  exact (regular_coordinate_ball_is_open (E := E) hB).isClosed_compl

/-- Helper for Problem 5-8: because a regular coordinate ball is open, the frontier of its
complement is exactly `closure B \ B`. -/
lemma regular_coordinate_ball_compl_frontier_eq_closure_diff {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    frontier (Set.compl B) = closure B \ B := by
  -- Rewrite the complement frontier back to the frontier of `B`, then use openness of `B`.
  calc
    frontier (Set.compl B) = frontier B := by
      rw [frontier_compl]
    _ = closure B \ B := by
      simpa using (regular_coordinate_ball_is_open (E := E) hB).frontier_eq (s := B)

/-- Helper for Problem 5-8: because a regular coordinate ball is open, the frontier of its
complement lies in that complement. -/
lemma regular_coordinate_ball_compl_frontier_subset_compl {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    frontier (Set.compl B) ⊆ Set.compl B := by
  -- Rewrite the frontier as `closure B \ B`, where the second component is exactly membership in
  -- the complement of `B`.
  rw [regular_coordinate_ball_compl_frontier_eq_closure_diff (E := E) (M := M) hB]
  intro x hx
  exact hx.2

/-- Helper for Problem 5-8: the spherical frontier of a regular coordinate ball is exactly the
image under the witnessing chart of `closure B \\ B`. -/
lemma regular_coordinate_ball_frontier_image_eq_sphere {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    ∃ chart : OpenPartialHomeomorph M E,
      chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
        ∃ r r' : ℝ,
          0 < r ∧
            r < r' ∧
            chart '' (closure B \ B) = Metric.sphere (0 : E) r ∧
            chart '' B = Metric.ball (0 : E) r ∧
            chart '' closure B = Metric.closedBall (0 : E) r ∧
            chart.target = Metric.ball (0 : E) r' := by
  rcases hB with ⟨chart, hchart, hclosure, r, r', hr, hr', himage, hclosure_image, htarget⟩
  have hB_source : B ⊆ chart.source := subset_closure.trans hclosure
  refine ⟨chart, hchart, r, r', hr, hr', ?_, himage, hclosure_image, htarget⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hy_closed : chart x ∈ Metric.closedBall (0 : E) r := by
      rw [← hclosure_image]
      exact ⟨x, hx.1, rfl⟩
    have hy_not_ball : chart x ∉ Metric.ball (0 : E) r := by
      intro hy_ball
      rw [← himage] at hy_ball
      rcases hy_ball with ⟨x', hx'B, hx'eq⟩
      have hx_eq : x' = x := by
        calc
          x' = chart.symm (chart x') := by
            exact (chart.left_inv (hB_source hx'B)).symm
          _ = chart.symm (chart x) := by simp [hx'eq]
          _ = x := chart.left_inv (hclosure hx.1)
      exact hx.2 (hx_eq ▸ hx'B)
    -- The frontier image is exactly the closed ball minus the open ball, hence the sphere.
    rw [← Metric.closedBall_diff_ball]
    exact ⟨hy_closed, hy_not_ball⟩
  · intro hy
    have hy_closed : y ∈ Metric.closedBall (0 : E) r := Metric.sphere_subset_closedBall hy
    rw [← hclosure_image] at hy_closed
    rcases hy_closed with ⟨x, hxcl, rfl⟩
    have hx_not_mem : x ∉ B := by
      intro hxB
      have hy_ball : chart x ∈ Metric.ball (0 : E) r := by
        rw [← himage]
        exact ⟨x, hxB, rfl⟩
      have hnorm_eq : ‖chart x‖ = r := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hy
      have hnorm_lt : ‖chart x‖ < r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hy_ball
      exact (not_lt_of_ge (le_of_eq hnorm_eq.symm)) hnorm_lt
    -- A sphere point comes from the closure image but cannot come from the open-ball image.
    exact ⟨x, ⟨hxcl, hx_not_mem⟩, rfl⟩

/-- Helper for Problem 5-8: in ambient dimension `0`, the frontier `closure B \ B` is empty,
because its chart image would be a positive-radius sphere in a subsingleton space. -/
lemma regular_coordinate_ball_frontier_eq_empty_of_dim_zero {B : Set M}
    (hB : IsRegularCoordinateBall E B) (hdim0 : dimM = 0) :
    closure B \ B = ∅ := by
  rcases regular_coordinate_ball_frontier_image_eq_sphere (E := E) (M := M) hB with
    ⟨chart, _, r, _, hr, _, hfrontier, _, _, _⟩
  have hzero : ∀ y : E, y = 0 :=
    FiniteDimensional.finrank_zero_iff_forall_zero.1 hdim0
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hx
  have hmemSphere : chart x ∈ Metric.sphere (0 : E) r := by
    -- Rewrite frontier membership through the explicit spherical image description.
    rw [← hfrontier]
    exact ⟨x, hx, rfl⟩
  have hchart_zero : chart x = 0 := hzero (chart x)
  have hradius_zero : (0 : ℝ) = r := by
    -- In a subsingleton normed space, every point on a sphere is the origin, so the radius is `0`.
    simpa [hchart_zero] using (mem_sphere_zero_iff_norm.1 hmemSphere)
  exact hr.ne' hradius_zero.symm

/-- Helper for Problem 5-8: in the witnessing chart of a regular coordinate ball, the local image
of the complement `M \ B` is exactly the exterior of the corresponding open Euclidean ball inside
the chart target. -/
lemma regular_coordinate_ball_compl_chart_image_eq_ball_exterior {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    ∃ chart : OpenPartialHomeomorph M E,
      chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
        ∃ r r' : ℝ,
          0 < r ∧
            r < r' ∧
            chart '' ((Set.compl B) ∩ chart.source) = chart.target \ Metric.ball (0 : E) r ∧
            chart '' B = Metric.ball (0 : E) r ∧
            chart '' closure B = Metric.closedBall (0 : E) r ∧
            chart.target = Metric.ball (0 : E) r' := by
  rcases hB with ⟨chart, hchart, hclosure, r, r', hr, hr', himage, hclosure_image, htarget⟩
  have hB_source : B ⊆ chart.source := subset_closure.trans hclosure
  refine ⟨chart, hchart, r, r', hr, hr', ?_, himage, hclosure_image, htarget⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨chart.map_source hx.2, ?_⟩
    intro hy_ball
    rw [← himage] at hy_ball
    rcases hy_ball with ⟨x', hx'B, hx'eq⟩
    have hx_eq : x = x' := by
      calc
        x = chart.symm (chart x) := by
          exact (chart.left_inv hx.2).symm
        _ = chart.symm (chart x') := by simpa [hx'eq]
        _ = x' := chart.left_inv (hB_source hx'B)
    exact hx.1 (hx_eq ▸ hx'B)
  · intro hy
    have hy_source : chart.symm y ∈ chart.source := chart.map_target hy.1
    refine ⟨chart.symm y, ⟨?_, hy_source⟩, ?_⟩
    · intro hxB
      have hy_ball : y ∈ Metric.ball (0 : E) r := by
        rw [← himage]
        refine ⟨chart.symm y, hxB, ?_⟩
        simpa using chart.right_inv hy.1
      exact hy.2 hy_ball
    · simpa using chart.right_inv hy.1

/-- Helper for Problem 5-8: for a fixed witness chart of a regular coordinate ball, a frontier
point of `B` lands in the shell describing the complement branch of that chart. -/
lemma regular_coordinate_ball_witness_frontier_point_mem_ball_exterior
    {B : Set M} {chart : OpenPartialHomeomorph M E} {r : ℝ}
    (hclosure : closure B ⊆ chart.source)
    (hcomplImage :
      chart '' ((Set.compl B) ∩ chart.source) = chart.target \ Metric.ball (0 : E) r)
    {x : M} (hx : x ∈ closure B \ B) :
    chart x ∈ chart.target \ Metric.ball (0 : E) r := by
  -- The point lies in the complement branch and in the chart source, so the shell-image formula
  -- applies directly.
  rw [← hcomplImage]
  exact ⟨x, ⟨hx.2, hclosure hx.1⟩, rfl⟩

/-- Helper for Problem 5-8: for a fixed witness chart of a regular coordinate ball, a frontier
point of `B` lands on the corresponding radius-`r` sphere. -/
lemma regular_coordinate_ball_witness_frontier_point_mem_sphere
    {B : Set M} {chart : OpenPartialHomeomorph M E} {r : ℝ}
    (hclosure : closure B ⊆ chart.source)
    (himage : chart '' B = Metric.ball (0 : E) r)
    (hclosure_image : chart '' closure B = Metric.closedBall (0 : E) r)
    {x : M} (hx : x ∈ closure B \ B) :
    chart x ∈ Metric.sphere (0 : E) r := by
  have hB_source : B ⊆ chart.source := subset_closure.trans hclosure
  have hx_closed : chart x ∈ Metric.closedBall (0 : E) r := by
    -- The frontier point belongs to the closure branch of the witness chart.
    rw [← hclosure_image]
    exact ⟨x, hx.1, rfl⟩
  have hx_not_ball : chart x ∉ Metric.ball (0 : E) r := by
    intro hx_ball
    rw [← himage] at hx_ball
    rcases hx_ball with ⟨x', hx'B, hx'eq⟩
    have hxx' : x = x' := by
      -- Injectivity on the chart source identifies the original frontier point with the point
      -- coming from the ball branch.
      calc
        x = chart.symm (chart x) := by
          exact (chart.left_inv (hclosure hx.1)).symm
        _ = chart.symm (chart x') := by
          simpa [hx'eq]
        _ = x' := chart.left_inv (hB_source hx'B)
    exact hx.2 (hxx' ▸ hx'B)
  -- The frontier is exactly the closed ball minus the open ball, hence the sphere.
  rw [← Metric.closedBall_diff_ball]
  exact ⟨hx_closed, hx_not_ball⟩

/-- Helper for Problem 5-8: after composing an ambient chart with a second chart, the original
local image description is simply restricted by the second chart source. -/
lemma trans_chart_image_eq_inter_source_of_image_eq
    {S : Set M} {T : Set E}
    {chart : OpenPartialHomeomorph M E}
    {e : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM))}
    (himage : chart '' (S ∩ chart.source) = T) :
    chart '' (S ∩ (chart.trans e).source) = T ∩ e.source := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · -- Forgetting the second-chart source condition recovers the original local image formula.
      rw [← himage]
      exact ⟨x, ⟨hx.1, (by simpa [OpenPartialHomeomorph.trans_source] using hx.2).1⟩, rfl⟩
    · -- Membership in the composed-chart source records that `chart x` lies in `e.source`.
      simpa [OpenPartialHomeomorph.trans_source] using
        (show chart x ∈ e.source from (by simpa [OpenPartialHomeomorph.trans_source] using hx.2).2)
  · rintro ⟨hyT, hySource⟩
    rw [← himage] at hyT
    rcases hyT with ⟨x, hx, rfl⟩
    refine ⟨x, ⟨hx.1, ?_⟩, rfl⟩
    -- Reinsert the extra source condition coming from the second chart.
    simpa [OpenPartialHomeomorph.trans_source] using ⟨hx.2, hySource⟩

/-- Helper for Problem 5-8: if a Euclidean half-slice already lies in a smaller ambient open set,
the same set can be viewed as a half-slice of that smaller open set. -/
lemma euclideanHalfSlice_inter_eq_of_subset
    {k : ℕ} {hk : 0 < k} {hkn : k ≤ dimM}
    {U V : Set (EuclideanSpace ℝ (Fin dimM))}
    {c : Fin (dimM - k) → ℝ}
    (hsub : Set.euclideanHalfSlice U k hk hkn c ⊆ V) :
    Set.euclideanHalfSlice U k hk hkn c =
      Set.euclideanHalfSlice (U ∩ V) k hk hkn c := by
  ext z
  constructor
  · intro hz
    -- The new ambient open set only adds membership in `V`, which holds by hypothesis.
    exact ⟨⟨⟨hz.1.1, hsub hz⟩, hz.1.2⟩, hz.2⟩
  · intro hz
    -- Forgetting the extra ambient-open-set membership recovers the original half-slice.
    exact ⟨⟨hz.1.1.1, hz.1.2⟩, hz.2⟩

/-- Helper for Problem 5-8: once an `E`-chart identifies the local image of `S` with `T`, any
boundary slice chart for `T` can be pulled back through that chart to a boundary slice chart
for `S`. -/
lemma trans_isBoundarySliceChart_of_local_image
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) E]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) E]
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M]
    {S : Set M} {T : Set E}
    {chart : OpenPartialHomeomorph M E}
    {e : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM))}
    (htrans :
      chart.trans e ∈ IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) M)
    (hlocal : chart '' (S ∩ (chart.trans e).source) = T ∩ e.source)
    (hsub : T ⊆ chart.target)
    (he : e.IsBoundarySliceChart T dimM) :
    (chart.trans e).IsBoundarySliceChart S dimM := by
  rcases he.2 with ⟨hk, hkn, c, hhalf⟩
  refine ⟨htrans, ?_⟩
  refine ⟨hk, hkn, c, ?_⟩
  have himage :
      (chart.trans e) '' (S ∩ (chart.trans e).source) = e '' (T ∩ e.source) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      -- The composed chart is literally the second chart applied to the first chart image.
      refine ⟨chart x, ?_, rfl⟩
      rw [← hlocal]
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rw [hlocal] at hy
      rcases hy with ⟨x, hx, hxy⟩
      -- Re-expand the local image description to recover a preimage point of the composed chart.
      refine ⟨x, hx, ?_⟩
      simpa [hxy]
  have hhalf_subset :
      Set.euclideanHalfSlice e.target dimM hk hkn c ⊆ e.symm ⁻¹' chart.target := by
    intro z hz
    rw [← hhalf] at hz
    rcases hz with ⟨y, hy, rfl⟩
    -- Points of the model half-slice come from `T`, and `T` itself lies in `chart.target`.
    simpa [e.left_inv hy.2] using hsub hy.1
  have htarget :
      Set.euclideanHalfSlice e.target dimM hk hkn c =
        Set.euclideanHalfSlice ((chart.trans e).target) dimM hk hkn c := by
    -- The half-slice already lies in the smaller target of the composed chart.
    rw [OpenPartialHomeomorph.trans_target]
    exact euclideanHalfSlice_inter_eq_of_subset (dimM := dimM) hhalf_subset
  -- Rewrite the local image through the composed chart and then restrict the ambient target.
  calc
    (chart.trans e) '' (S ∩ (chart.trans e).source) = e '' (T ∩ e.source) := himage
    _ = Set.euclideanHalfSlice e.target dimM hk hkn c := hhalf
    _ = Set.euclideanHalfSlice ((chart.trans e).target) dimM hk hkn c := htarget

/-- Helper for Problem 5-8: an open subset of `ℝ^n` is tautologically a full-dimensional
Euclidean slice of itself. -/
lemma full_dimensional_euclideanSlice_self
    (U : Set (EuclideanSpace ℝ (Fin dimM))) :
    U.IsEuclideanSlice U dimM := by
  -- In the full-dimensional case there are no constrained tail coordinates left to specify.
  refine ⟨le_rfl, (fun i : Fin (dimM - dimM) ↦ (0 : ℝ)), ?_⟩
  ext y
  constructor
  · intro hy
    refine ⟨hy, ?_⟩
    intro i
    have hi : i.1 < 0 := by
      simpa using i.2
    exact False.elim (Nat.not_lt_zero _ hi)
  · intro hy
    exact hy.1

/-- Helper for Problem 5-8: any full-dimensional Euclidean slice is the whole ambient open set,
because there are no tail coordinates left to constrain. -/
lemma euclideanSlice_full_dimensional_eq
    (U : Set (EuclideanSpace ℝ (Fin dimM))) (hk : dimM ≤ dimM)
    (c : Fin (dimM - dimM) → ℝ) :
    Set.euclideanSlice U dimM hk c = U := by
  ext y
  constructor
  · -- A point of the slice is, in particular, a point of `U`.
    intro hy
    exact hy.1
  · -- Conversely, the tail-coordinate conditions are vacuous because `Fin (dimM - dimM)` is empty.
    intro hy
    refine ⟨hy, ?_⟩
    intro i
    exact False.elim (Fin.elim0 i)

/-- Helper for Problem 5-8: a full-dimensional slice chart around `x` places `x` in the interior
of the subset, because near `x` the subset fills the whole chart source. -/
lemma mem_interior_of_full_sliceChart {S : Set M} {x : M}
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M]
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM))}
    (hx : x ∈ e.source) (he : e.IsSliceChart S dimM) :
    x ∈ interior S := by
  rcases he.2 with ⟨hk, c, himage⟩
  have himage_target :
      e '' (S ∩ e.source) = e.target := by
    -- In ambient dimension `dimM`, a `dimM`-slice is the entire chart target.
    rw [himage, euclideanSlice_full_dimensional_eq (U := e.target) hk c]
  have hsource_subset : e.source ⊆ S := by
    intro y hy
    have hy_target : e y ∈ e.target := e.map_source hy
    rw [← himage_target] at hy_target
    rcases hy_target with ⟨z, hz, hz_eq⟩
    have hz_source : z ∈ e.source := hz.2
    have hy_eq : y = z := by
      calc
        y = e.symm (e y) := by exact (e.left_inv hy).symm
        _ = e.symm (e z) := by simp [hz_eq]
        _ = z := e.left_inv hz_source
    exact hy_eq.symm ▸ hz.1
  -- The open chart source itself is a neighborhood of `x` contained in `S`.
  have hx_mem_nhds : e.source ∈ 𝓝 x := e.open_source.mem_nhds hx
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset hx_mem_nhds hsource_subset

/-- Helper for Problem 5-8: in a Euclidean ambient model, a frontier point of a smoothly embedded
subtype cannot be an interior point of the boundary model, because interior points would admit a
full-dimensional slice chart and hence lie in the ambient interior. -/
lemma smooth_embedding_frontier_point_isBoundaryPoint
    {S : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M]
    [SmoothManifoldWithBoundary dimM S]
    (hS :
      Manifold.IsSmoothEmbedding
        (leeBoundaryModelWithCorners dimM)
        (𝓡 dimM)
        ∞
        ((↑) : S → M))
    {x : S} (hx : x.1 ∈ frontier S) :
    (leeBoundaryModelWithCorners dimM).IsBoundaryPoint x := by
  by_contra hxNotBoundary
  have hxInterior :
      (leeBoundaryModelWithCorners dimM).IsInteriorPoint x := by
    -- In Lee's boundary model, non-boundary points are exactly interior points.
    exact ((leeBoundaryModelWithCorners dimM).isInteriorPoint_iff_not_isBoundaryPoint x).2
      hxNotBoundary
  rcases smooth_embedding_subtype_val_has_local_slice_at_of_isInteriorPoint
      (S := S) hS x hxInterior with ⟨e, hx_source, he_slice⟩
  have hxInteriorAmbient : x.1 ∈ interior S :=
    -- The local slice chart fills the whole ambient chart source, so the ambient point is interior.
    mem_interior_of_full_sliceChart (S := S) (x := x.1) hx_source he_slice
  exact hx.2 hxInteriorAmbient

/-- Helper for Problem 5-8: a point outside `closure B` already has a full-dimensional slice chart
for the complement `M \ B`. -/
lemma exterior_point_has_full_sliceChart_for_compl {B : Set M} {x : M}
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M]
    (hx : x ∈ (closure B)ᶜ) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
      x ∈ e.source ∧ e.IsSliceChart (Set.compl B) dimM := by
  -- Route correction: this exterior branch is conceptually easy, but the current file now treats
  -- it as supporting infrastructure for the main boundary-slice blocker instead of expanding the
  -- restriction-chart bookkeeping inline.
  let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)) :=
    chartAt (EuclideanSpace ℝ (Fin dimM)) x
  have hx_source : x ∈ e.source := by
    -- The ambient chart at `x` is centered at `x`.
    simpa [e] using mem_chart_source (EuclideanSpace ℝ (Fin dimM)) x
  have he_max :
      e ∈ IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) M := by
    -- `chartAt` always belongs to the smooth maximal atlas.
    simpa [e] using
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡 dimM) (n := (⊤ : WithTop ℕ∞)) x)
  have hOpen_exterior : IsOpen ((closure B)ᶜ) := isClosed_closure.isOpen_compl
  have hNhds :
      e.source ∩ (closure B)ᶜ ∈ 𝓝 x := by
    -- Intersect the chart source with the open exterior of `closure B`.
    exact Filter.inter_mem (e.open_source.mem_nhds hx_source) (hOpen_exterior.mem_nhds hx)
  rcases mem_nhds_iff.mp hNhds with ⟨V, hV_sub, hV_open, hxV⟩
  refine ⟨e.restr V, ?_, ?_⟩
  · -- The restricted chart is still centered at `x` because `V` was chosen as a neighborhood.
    rw [e.restr_source' V hV_open]
    exact ⟨hx_source, hxV⟩
  · refine ⟨?_, ?_⟩
    · -- Open restrictions of maximal-atlas charts remain in the maximal atlas.
      have he_max_groupoid :
          e ∈ StructureGroupoid.maximalAtlas M
            (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM)) := by
        simpa [IsManifold.maximalAtlas] using he_max
      simpa [IsManifold.maximalAtlas] using
        restr_mem_maximalAtlas
          (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM))
          he_max_groupoid
          hV_open
    · -- On the restricted source, `Set.compl B` is all of the source because `V` lies outside
      -- `closure B`; its image is therefore the whole restricted target.
      have hsource_subset_complB : (e.restr V).source ⊆ Set.compl B := by
        intro y hy
        rw [e.restr_source' V hV_open] at hy
        have hy_exterior : y ∈ (closure B)ᶜ := (hV_sub hy.2).2
        exact fun hyB ↦ hy_exterior (subset_closure hyB)
      have hCompl_source :
          (Set.compl B) ∩ (e.restr V).source = (e.restr V).source := by
        ext y
        constructor
        · intro hy
          exact hy.2
        · intro hy
          exact ⟨hsource_subset_complB hy, hy⟩
      -- The local image is the full restricted target, so this is a full-dimensional slice.
      rw [Set.IsSliceInChart, hCompl_source, (e.restr V).image_source_eq_target]
      exact full_dimensional_euclideanSlice_self (U := (e.restr V).target)

/-- Helper for Problem 5-8: once the frontier points of `closure B \ B` are known to admit
boundary slice charts, the whole complement `M \ B` satisfies the local slice condition with
boundary by splitting into the exterior of `closure B` and the frontier itself. -/
lemma regular_coordinate_ball_compl_satisfiesLocalSliceConditionWithBoundary {B : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M]
    (hB : IsRegularCoordinateBall E B)
    (hfrontier :
      ∀ x ∈ closure B \ B,
        ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
          x ∈ e.source ∧ e.IsBoundarySliceChart (Set.compl B) dimM) :
    Set.SatisfiesLocalSliceConditionWithBoundary dimM (Set.compl B) dimM := by
  refine ⟨?_⟩
  intro x hx
  by_cases hx_ext : x ∈ (closure B)ᶜ
  · -- Points already outside `closure B` use the ambient chart as a full slice chart.
    rcases exterior_point_has_full_sliceChart_for_compl (B := B) (x := x) hx_ext with
      ⟨e, hx_source, he⟩
    exact ⟨e, hx_source, Or.inl he⟩
  · have hx_closure : x ∈ closure B := by
      -- Negating membership in `(closure B)ᶜ` forces `x` onto the closure side.
      by_contra hx_not_closure
      exact hx_ext hx_not_closure
    have hx_frontier : x ∈ closure B \ B := by
      refine ⟨hx_closure, ?_⟩
      -- Since `x ∈ Bᶜ`, it cannot lie in `B`.
      exact hx
    -- Frontier points use the supplied half-slice witnesses.
    rcases hfrontier x hx_frontier with ⟨e, hx_source, he⟩
    exact ⟨e, hx_source, Or.inr he⟩

/-- Helper for Problem 5-8: once the complement `M \ B` has been described by full slice charts
away from `closure B` and boundary slice charts along `closure B \ B`, Theorem 5.51 directly
packages those local models into the Euclidean ambient smooth-embedding structure on `Set.compl B`.
-/
theorem regular_coordinate_ball_compl_has_euclidean_embedding_structure {B : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M]
    (hB : IsRegularCoordinateBall E B)
    (hfrontier :
      ∀ x ∈ closure B \ B,
        ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
          x ∈ e.source ∧ e.IsBoundarySliceChart (Set.compl B) dimM) :
    ∃ instSmooth : SmoothManifoldWithBoundary dimM (Set.compl B),
      letI : SmoothManifoldWithBoundary dimM (Set.compl B) := instSmooth
      Manifold.IsSmoothEmbedding
        (leeBoundaryModelWithCorners dimM)
        (𝓡 dimM)
        ∞
        ((↑) : Set.compl B → M) := by
  have hSlice :
      Set.SatisfiesLocalSliceConditionWithBoundary dimM (Set.compl B) dimM := by
    -- The already packaged exterior branch and the supplied frontier half-slice charts give the
    -- complete local slice-with-boundary criterion for `M \ B`.
    exact
      regular_coordinate_ball_compl_satisfiesLocalSliceConditionWithBoundary
        (E := E) (M := M) hB hfrontier
  rcases
      (local_slice_criterion_for_embedded_submanifold_with_boundary
        (n := dimM) (k := dimM) (M := M) (S := Set.compl B)).1 hSlice with
    ⟨instSmooth, hEmbedding⟩
  refine ⟨instSmooth, ?_⟩
  letI : SmoothManifoldWithBoundary dimM (Set.compl B) := instSmooth
  -- Theorem 5.51 already returns the Euclidean ambient smooth embedding for the subtype
  -- inclusion; only the later transport back to `modelWithCornersSelf ℝ E` is still missing.
  simpa using hEmbedding

/-- Helper for Problem 5-8: once `M \ B` is already a regular domain, any ambient frontier point
of the complement admits a boundary slice chart for that chosen smooth structure. -/
lemma regular_domain_frontier_point_has_boundary_sliceChart_for_compl {B : Set M}
    [SmoothManifoldWithBoundary dimM (Set.compl B)]
    (hRegular : Set.IsRegularDomain (modelWithCornersSelf ℝ E) (Set.compl B)) :
    ∀ x ∈ frontier (Set.compl B),
      ∃ e : OpenPartialHomeomorph M E,
        x ∈ e.source ∧ e.IsBoundarySliceChart (Set.compl B) dimM := by
  intro x hx
  let xCompl : Set.compl B :=
    ⟨x, regular_coordinate_ball_compl_frontier_subset_compl (E := E) (M := M) hB hx⟩
  -- The regular-domain smooth embedding gives a local slice-or-half-slice chart at any point of
  -- the complement.
  rcases
      smooth_embedding_subtype_val_has_local_slice_or_half_slice_at
        (n := dimM) (k := dimM) (M := M) (S := Set.compl B)
        hRegular.isSmoothEmbedding_subtype_val xCompl with
    ⟨e, hx_source, he_local⟩
  rcases he_local with he_slice | he_boundary
  · -- A full-dimensional slice would make `x` interior to `Set.compl B`, contradicting `hx`.
    have hx_interior : x ∈ interior (Set.compl B) :=
      mem_interior_of_full_sliceChart (x := x) hx_source he_slice
    exact False.elim (hx.2 hx_interior)
  · -- The local normal form is therefore necessarily the boundary half-slice branch.
    exact ⟨e, hx_source, he_boundary⟩

/-- Helper for Problem 5-8: in the transported Euclidean ambient structure, each frontier point of
`closure B \ B` should admit a boundary slice chart for the complement. -/
lemma ball_exterior_boundary_slice_chart_in_basis_model
    (b : Module.Basis (Fin dimM) ℝ E)
    {r : ℝ} (hr : 0 < r) {U : Set E} (hU_open : IsOpen U)
    {y : E} (hy_shell : y ∈ U \ Metric.ball (0 : E) r)
    (hy_sphere : y ∈ Metric.sphere (0 : E) r) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) E :=
      basis_model_chartedSpace (E := E) (M := E) b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) E :=
      basis_model_isManifold (E := E) (M := E) b
    ∃ e : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)),
      y ∈ e.source ∧ e.IsBoundarySliceChart (U \ Metric.ball (0 : E) r) dimM := by
  intro _ _
  -- Route correction: the remaining source-faithful blocker is the Euclidean shell chart itself.
  -- The pullback through the regular-coordinate-ball witness chart is handled separately below.
  have _ := hr
  have _ := hU_open
  have _ := hy_shell
  have _ := hy_sphere
  -- TODO: build the exterior shell chart in orthonormal Euclidean coordinates, then certify that
  -- it belongs to the transported basis-model maximal atlas on `E`.
  sorry

/-- Helper for Problem 5-8: in the transported Euclidean ambient structure, each frontier point of
`closure B \ B` should admit a boundary slice chart for the complement. -/
lemma regular_coordinate_ball_frontier_has_boundary_sliceChart_for_compl_of_pos {B : Set M}
    (hB : IsRegularCoordinateBall E B)
    (b : Module.Basis (Fin dimM) ℝ E)
    (hdim : 0 < dimM) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace (E := E) (M := M) b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold (E := E) (M := M) b
    ∀ x ∈ closure B \ B,
      ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
        x ∈ e.source ∧ e.IsBoundarySliceChart (Set.compl B) dimM := by
  intro _ _
  intro x hx
  -- Route correction: the zero-dimensional branch is handled separately by the caller. Here we
  -- keep only the source-faithful positive-dimensional skeleton: send `x` to a sphere point in
  -- the witness chart, straighten the Euclidean exterior there, then conjugate back.
  rcases hB with ⟨chart, hchart, hclosure, r, r', hr, hr', himage, hclosure_image, htarget⟩
  have hB_source : B ⊆ chart.source := subset_closure.trans hclosure
  have hcomplImage :
      chart '' ((Set.compl B) ∩ chart.source) = chart.target \ Metric.ball (0 : E) r := by
    -- First rewrite the complement branch in the witnessing regular-coordinate-ball chart.
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨chart.map_source hz.2, ?_⟩
      intro hy_ball
      rw [← himage] at hy_ball
      rcases hy_ball with ⟨z', hz'B, hz'eq⟩
      have hz_eq : z = z' := by
        calc
          z = chart.symm (chart z) := by
            exact (chart.left_inv hz.2).symm
          _ = chart.symm (chart z') := by simpa [hz'eq]
          _ = z' := chart.left_inv (hB_source hz'B)
      exact hz.1 (hz_eq ▸ hz'B)
    · intro hy
      have hy_source : chart.symm y ∈ chart.source := chart.map_target hy.1
      refine ⟨chart.symm y, ⟨?_, hy_source⟩, ?_⟩
      · intro hyB
        have hy_ball : y ∈ Metric.ball (0 : E) r := by
          rw [← himage]
          refine ⟨chart.symm y, hyB, ?_⟩
          simpa using chart.right_inv hy.1
        exact hy.2 hy_ball
      · simpa using chart.right_inv hy.1
  have hx_shell : chart x ∈ chart.target \ Metric.ball (0 : E) r := by
    -- The complement-image formula places the frontier point on the shell immediately.
    exact
      regular_coordinate_ball_witness_frontier_point_mem_ball_exterior
        (E := E) (M := M) hclosure hcomplImage hx
  have hx_sphere : chart x ∈ Metric.sphere (0 : E) r := by
    -- The chart images of `B` and `closure B` identify the shell with the radius-`r` sphere.
    exact
      regular_coordinate_ball_witness_frontier_point_mem_sphere
        (E := E) (M := M) hclosure himage hclosure_image hx
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) E :=
    basis_model_chartedSpace (E := E) (M := E) b
  let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) E :=
    basis_model_isManifold (E := E) (M := E) b
  have hchartEuclid :
      chart.trans
          ((basis_model_diffeomorph (E := E) b).symm.toHomeomorph.toOpenPartialHomeomorph) ∈
        IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) M := by
    -- The fixed basis-model change transports the witnessing chart into the Euclidean maximal
    -- atlas used by the target statement.
    simpa using basis_model_chart_mem_maximalAtlas (E := E) (M := M) b hchart
  have hshell_subset_target : chart.target \ Metric.ball (0 : E) r ⊆ chart.target := by
    -- The shell model used for the complement branch sits inside the witness-chart target.
    intro y hy
    exact hy.1
  have hx_chart_source : x ∈ chart.source := hclosure hx.1
  rcases
      ball_exterior_boundary_slice_chart_in_basis_model
        (E := E) (b := b) (r := r) hr chart.open_target hx_shell hx_sphere with
    ⟨eShell, hy_source, heShell_boundary⟩
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    (basis_model_diffeomorph (E := E) b).symm.toHomeomorph.toOpenPartialHomeomorph
  have hselfChart :
      (OpenPartialHomeomorph.refl E) ∈
        IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) E := by
    -- In the original ambient manifold structure on `E`, the identity chart is the chart at every
    -- point.
    simpa [chartAt_self_eq] using
      (IsManifold.chart_mem_maximalAtlas
        (I := modelWithCornersSelf ℝ E) (n := (⊤ : WithTop ℕ∞)) (x := chart x))
  have heModel_max :
      eModel ∈ IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) E := by
    -- Transport the identity chart on `E` through the fixed basis model.
    simpa [eModel, OpenPartialHomeomorph.refl_trans] using
      (basis_model_chart_mem_maximalAtlas
        (E := E) (M := E) (chart := OpenPartialHomeomorph.refl E) b hselfChart)
  have hcompat_eShell :
      eModel.symm.trans eShell ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM) := by
    -- The fixed basis model chart and the shell chart are compatible Euclidean atlas charts on
    -- `E`.
    exact IsManifold.compatible_of_mem_maximalAtlas heModel_max heShell_boundary.1
  have htrans :
      chart.trans eShell ∈ IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) M := by
    -- Postcompose the fixed Euclidean witness chart by the smooth model-space transition from the
    -- basis chart to the shell chart.
    simpa [eModel, OpenPartialHomeomorph.trans_assoc] using
      (trans_mem_maximalAtlas_of_mem_groupoid
        (X := M) (m := dimM) hchartEuclid hcompat_eShell)
  have hlocal :
      chart '' (Set.compl B ∩ (chart.trans eShell).source) =
        (chart.target \ Metric.ball (0 : E) r) ∩ eShell.source := by
    -- Restrict the already-known complement image formula by the shell chart source.
    exact
      trans_chart_image_eq_inter_source_of_image_eq
        (S := Set.compl B) (T := chart.target \ Metric.ball (0 : E) r)
        (chart := chart) (e := eShell) hcomplImage
  refine ⟨chart.trans eShell, ?_, ?_⟩
  · -- The frontier point remains in the source after composing with the shell chart.
    simpa [OpenPartialHomeomorph.trans_source] using And.intro hx_chart_source hy_source
  · -- Pull the shell half-slice chart back through the original witness chart.
    exact
      trans_isBoundarySliceChart_of_local_image
        (dimM := dimM) (S := Set.compl B) (T := chart.target \ Metric.ball (0 : E) r)
        (chart := chart) (e := eShell) htrans hlocal hshell_subset_target heShell_boundary

/-- Helper for Problem 5-8: in the transported Euclidean ambient structure, each frontier point of
`closure B \ B` should admit a boundary slice chart for the complement. -/
lemma regular_coordinate_ball_frontier_has_boundary_sliceChart_for_compl {B : Set M}
    (hB : IsRegularCoordinateBall E B)
    (b : Module.Basis (Fin dimM) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace (E := E) (M := M) b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold (E := E) (M := M) b
    ∀ x ∈ closure B \ B,
      ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
        x ∈ e.source ∧ e.IsBoundarySliceChart (Set.compl B) dimM := by
  intro _ _
  intro x hx
  by_cases hdim0 : dimM = 0
  · -- In dimension `0`, the frontier is empty, so there is no boundary-chart work left.
    have hfrontierEmpty :
        closure B \ B = ∅ :=
      regular_coordinate_ball_frontier_eq_empty_of_dim_zero (E := E) (M := M) hB hdim0
    have : x ∈ (∅ : Set M) := by
      simpa [hfrontierEmpty] using hx
    exact False.elim this
  -- The remaining positive-dimensional work is isolated in a dedicated helper so the main theorem
  -- now only manages the dimension split.
  exact
    regular_coordinate_ball_frontier_has_boundary_sliceChart_for_compl_of_pos
      (E := E) (M := M) hB b (Nat.pos_iff_ne_zero.mpr hdim0) x hx

/-- Helper for Problem 5-8: once the complement inclusion is a smooth embedding for the transported
Euclidean ambient model, the same inclusion is also a smooth embedding for the original ambient
model `modelWithCornersSelf ℝ E`. -/
lemma basis_model_codomain_transport_isSmoothEmbedding {B : Set M}
    (b : Module.Basis (Fin dimM) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace (E := E) (M := M) b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold (E := E) (M := M) b
    ∀ hEmbedding :
      Manifold.IsSmoothEmbedding
        (leeBoundaryModelWithCorners dimM)
        (𝓡 dimM)
        ∞
        ((↑) : Set.compl B → M),
      Manifold.IsSmoothEmbedding
        (leeBoundaryModelWithCorners dimM)
        (modelWithCornersSelf ℝ E)
        ∞
        ((↑) : Set.compl B → M) := by
  intro _ _ hEmbedding
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    (basis_model_diffeomorph (E := E) b).symm.toHomeomorph.toOpenPartialHomeomorph
  let hImm := hEmbedding.isImmersion
  let hComp := hImm.complement
  let hCompImm := hImm.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_, hEmbedding.isEmbedding⟩
  intro x
  let hx := hCompImm x
  -- Route correction: keep the source chart and normal form fixed, and only transport the
  -- codomain chart back through the fixed basis-model change.
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart (hx.codChart.trans eModel.symm) ?_ ?_ hx.domChart_mem_maximalAtlas ?_ ?_
      ?_
  · -- The domain chart is unchanged.
    exact hx.mem_domChart_source
  · -- The transported codomain chart is still defined at the image point.
    simpa [eModel, OpenPartialHomeomorph.trans_source] using hx.mem_codChart_source
  · -- Transport Euclidean codomain compatibility back to the original ambient model.
    rw [IsManifold.mem_maximalAtlas_iff]
    intro c hc
    have hcEuclid :
        c.trans eModel ∈ IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) M := by
      -- Original ambient charts become Euclidean charts after composing with the basis model map.
      simpa [eModel] using
        basis_model_chart_mem_maximalAtlas (E := E) (M := M) b hc
    have hcompat_euclid :
        hx.codChart.symm.trans (c.trans eModel) ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM) ∧
          (c.trans eModel).symm.trans hx.codChart ∈ contDiffGroupoid (⊤ : WithTop ℕ∞)
            (𝓡 dimM) :=
      IsManifold.mem_maximalAtlas_iff.1 hx.codChart_mem_maximalAtlas (c.trans eModel) hcEuclid
    constructor
    · -- The left transition is exactly the Euclidean one, rewritten through `eModel`.
      have hleft_conj :
          let eModel' : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
            (basis_model_diffeomorph (E := E) b).symm.toHomeomorph.toOpenPartialHomeomorph
          eModel'.symm.trans ((hx.codChart.trans eModel.symm).symm.trans c).trans eModel' ∈
            contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM) := by
        simpa [eModel, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc] using hcompat_euclid.1
      simpa [eModel] using
        (basis_model_transition_mem_contDiffGroupoid_symm
          (E := E) (b := b) (e := (hx.codChart.trans eModel.symm).symm.trans c) hleft_conj)
    · -- The right transition is transported back in the same way.
      have hright_conj :
          let eModel' : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
            (basis_model_diffeomorph (E := E) b).symm.toHomeomorph.toOpenPartialHomeomorph
          eModel'.symm.trans (c.symm.trans (hx.codChart.trans eModel.symm)).trans eModel' ∈
            contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM) := by
        simpa [eModel, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc] using hcompat_euclid.2
      simpa [eModel] using
        (basis_model_transition_mem_contDiffGroupoid_symm
          (E := E) (b := b) (e := c.symm.trans (hx.codChart.trans eModel.symm)) hright_conj)
  · -- Points in the source chart still land in the transported codomain chart.
    intro z hz
    have hz' : ((↑) : Set.compl B → M) z ∈ hx.codChart.source :=
      hx.source_subset_preimage_source hz
    simpa [eModel, OpenPartialHomeomorph.trans_source] using hz'
  · -- In the transported codomain chart, the written-in-charts normal form is unchanged.
    intro u hu
    simpa [eModel, Function.comp, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm] using hx.writtenInCharts hu

/-- Helper for Problem 5-8: after transporting the ambient charts through a basis of `E`, a
regular-domain smooth embedding for `M \ B` becomes a Euclidean ambient smooth embedding. -/
lemma basis_model_regular_domain_isSmoothEmbedding_subtype_val {B : Set M}
    (b : Module.Basis (Fin dimM) ℝ E)
    (hRegular : Set.IsRegularDomain (modelWithCornersSelf ℝ E) (Set.compl B)) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace (E := E) (M := M) b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold (E := E) (M := M) b
    Manifold.IsSmoothEmbedding
      (leeBoundaryModelWithCorners dimM)
      (𝓡 dimM)
      ∞
      ((↑) : Set.compl B → M) := by
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    (basis_model_diffeomorph (E := E) b).symm.toHomeomorph.toOpenPartialHomeomorph
  let hEmbedding := hRegular.isSmoothEmbedding_subtype_val
  let hImm := hEmbedding.isImmersion
  let hComp := hImm.complement
  let hCompImm := hImm.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_, hEmbedding.isEmbedding⟩
  intro x
  let hx := hCompImm x
  -- Keep the original source chart and only transport the codomain chart through the fixed basis
  -- identification to the Euclidean ambient model.
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart (hx.codChart.trans eModel) ?_ ?_ hx.domChart_mem_maximalAtlas ?_ ?_ ?_
  · -- The domain chart is unchanged.
    exact hx.mem_domChart_source
  · -- The Euclidean codomain chart is defined because the basis model change is global.
    simpa [eModel, OpenPartialHomeomorph.trans_source] using hx.mem_codChart_source
  · -- Original ambient atlas charts become Euclidean ambient atlas charts after composition.
    simpa [eModel] using
      basis_model_chart_mem_maximalAtlas (E := E) (M := M) b hx.codChart_mem_maximalAtlas
  · -- Points in the source chart still land in the transported codomain chart.
    intro z hz
    have hz' : ((↑) : Set.compl B → M) z ∈ hx.codChart.source :=
      hx.source_subset_preimage_source hz
    simpa [eModel, OpenPartialHomeomorph.trans_source] using hz'
  · -- The immersion normal form is the same after postcomposing by the fixed linear model change.
    intro u hu
    simpa [eModel, Function.comp, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm] using hx.writtenInCharts hu

/-- Helper for Problem 5-8: once the local slice-with-boundary geometry of `M \ B` is packaged
into the ambient smooth-embedding owner, closedness upgrades it to Lee's regular-domain owner. -/
theorem regular_coordinate_ball_compl_has_smooth_embedding_structure
    {B : Set M} (hB : IsRegularCoordinateBall E B) :
    ∃ instSmooth : SmoothManifoldWithBoundary dimM (Set.compl B),
      letI : SmoothManifoldWithBoundary dimM (Set.compl B) := instSmooth
      Manifold.IsSmoothEmbedding
        (leeBoundaryModelWithCorners dimM)
        (modelWithCornersSelf ℝ E)
        ∞
        ((↑) : Set.compl B → M) := by
  -- Route correction: the proof is now reduced to the source-faithful frontier branch. The
  -- exterior branch is already packaged, and Theorem 5.51 now packages the Euclidean ambient
  -- embedding as soon as the frontier half-slice charts are supplied.
  have hEuclideanEmbedding :
      ∀ [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M]
        [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M],
        (∀ x ∈ closure B \ B,
            ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
              x ∈ e.source ∧ e.IsBoundarySliceChart (Set.compl B) dimM) →
          ∃ instSmooth : SmoothManifoldWithBoundary dimM (Set.compl B),
            letI : SmoothManifoldWithBoundary dimM (Set.compl B) := instSmooth
            Manifold.IsSmoothEmbedding
              (leeBoundaryModelWithCorners dimM)
              (𝓡 dimM)
              ∞
              ((↑) : Set.compl B → M) := by
    intro _ _
    intro hfrontier
    -- Once the frontier half-slice charts are available, Theorem 5.51 finishes the Euclidean
    -- ambient packaging of the complement.
    exact
      regular_coordinate_ball_compl_has_euclidean_embedding_structure
        (E := E) (M := M) hB hfrontier
  have _ := hEuclideanEmbedding
  have hComplImage :
      ∃ chart : OpenPartialHomeomorph M E,
        chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
          ∃ r r' : ℝ,
            0 < r ∧
              r < r' ∧
              chart '' ((Set.compl B) ∩ chart.source) = chart.target \ Metric.ball (0 : E) r ∧
              chart '' B = Metric.ball (0 : E) r ∧
              chart '' closure B = Metric.closedBall (0 : E) r ∧
              chart.target = Metric.ball (0 : E) r' :=
    regular_coordinate_ball_compl_chart_image_eq_ball_exterior (E := E) (M := M) hB
  let b : Module.Basis (Fin dimM) ℝ E := FiniteDimensional.finBasis ℝ E
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
    basis_model_chartedSpace (E := E) (M := M) b
  let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
    basis_model_isManifold (E := E) (M := M) b
  have hfrontier :
      ∀ x ∈ closure B \ B,
        ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
          x ∈ e.source ∧ e.IsBoundarySliceChart (Set.compl B) dimM := by
    -- The remaining geometric core is the Euclidean straightening of the sphere frontier of the
    -- regular coordinate ball into a half-space chart.
    exact
      regular_coordinate_ball_frontier_has_boundary_sliceChart_for_compl
        (E := E) (M := M) hB b
  have hEuclideanEmbeddingFinal :
      ∃ instSmooth : SmoothManifoldWithBoundary dimM (Set.compl B),
        letI : SmoothManifoldWithBoundary dimM (Set.compl B) := instSmooth
        Manifold.IsSmoothEmbedding
          (leeBoundaryModelWithCorners dimM)
          (𝓡 dimM)
          ∞
          ((↑) : Set.compl B → M) :=
    hEuclideanEmbedding hfrontier
  have _ := hComplImage
  rcases hEuclideanEmbeddingFinal with ⟨instSmooth, hEmbeddingEuclid⟩
  refine ⟨instSmooth, ?_⟩
  letI : SmoothManifoldWithBoundary dimM (Set.compl B) := instSmooth
  -- Once the frontier half-slice charts are supplied, the Euclidean ambient embedding is already
  -- packaged. The remaining step is the codomain-model transport back to `E`.
  exact
    basis_model_codomain_transport_isSmoothEmbedding
      (E := E) (M := M) (B := B) b hEmbeddingEuclid

/-- Helper for Problem 5-8: once abstract boundary points of `Set.compl B` are known to be exactly
the ambient frontier points, the subtype inclusion identifies the abstract boundary with the
ambient frontier set. -/
lemma regular_coordinate_ball_boundary_image_eq_frontier_of_boundary_point_iff
    {B : Set M} (hB : IsRegularCoordinateBall E B)
    [SmoothManifoldWithBoundary dimM (Set.compl B)]
    (hBoundaryPoint :
      ∀ x : Set.compl B,
        (leeBoundaryModelWithCorners dimM).IsBoundaryPoint x ↔
          x.1 ∈ frontier (Set.compl B)) :
    Subtype.val '' (leeBoundaryModelWithCorners dimM).boundary (Set.compl B) =
      frontier (Set.compl B) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    -- A point in the abstract boundary subtype satisfies the assumed frontier criterion.
    exact (hBoundaryPoint y).1 hy.2
  · intro hx
    have hx_compl : x ∈ Set.compl B :=
      regular_coordinate_ball_compl_frontier_subset_compl (E := E) (M := M) hB hx
    let y : Set.compl B := ⟨x, hx_compl⟩
    -- Repackage an ambient frontier point as the corresponding boundary point of the subtype.
    refine ⟨y, ?_, rfl⟩
    exact (hBoundaryPoint y).2 hx

/-- Helper for Problem 5-8: after transporting the ambient model to `ℝ^dimM`, the already closed
smooth-embedding argument sends ambient frontier points of `M \ B` to abstract boundary points. -/
lemma basis_model_regular_domain_frontier_point_isBoundaryPoint
    {B : Set M}
    (b : Module.Basis (Fin dimM) ℝ E)
    [SmoothManifoldWithBoundary dimM (Set.compl B)]
    (hRegular : Set.IsRegularDomain (modelWithCornersSelf ℝ E) (Set.compl B)) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace (E := E) (M := M) b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold (E := E) (M := M) b
    ∀ x : Set.compl B,
      x.1 ∈ frontier (Set.compl B) →
        (leeBoundaryModelWithCorners dimM).IsBoundaryPoint x := by
  intro _ _ x hx
  have hEmbedding :
      Manifold.IsSmoothEmbedding
        (leeBoundaryModelWithCorners dimM)
        (𝓡 dimM)
        ∞
        ((↑) : Set.compl B → M) :=
    basis_model_regular_domain_isSmoothEmbedding_subtype_val
      (E := E) (M := M) (B := B) b hRegular
  -- In Euclidean ambient coordinates, the reverse implication is already proved for smooth
  -- embeddings by ruling out ambient interior points.
  exact
    smooth_embedding_frontier_point_isBoundaryPoint
      (S := Set.compl B) hEmbedding hx

/-- Helper for Problem 5-8: if the chosen complement structure has a boundary point, then its
ambient value lies in the frontier of `M \ B` because `M \ B` is closed and abstract interior
points are exactly ambient interior points. -/
lemma regular_domain_boundary_point_mem_frontier
    {B : Set M} (hB : IsRegularCoordinateBall E B)
    [SmoothManifoldWithBoundary dimM (Set.compl B)]
    (x : Set.compl B)
    (hxBoundary : (leeBoundaryModelWithCorners dimM).IsBoundaryPoint x) :
    x.1 ∈ frontier (Set.compl B) := by
  have hxNotInterior :
      x.1 ∉ interior (Set.compl B) := by
    intro hxInterior
    have hxInteriorBoundary :
        (leeBoundaryModelWithCorners dimM).IsInteriorPoint x := by
      -- Ambient interior points of the closed complement are exactly interior points in Lee's
      -- boundary model.
      exact
        (leeBoundaryModelWithCorners dimM).isInteriorPoint_iff_isInteriorPoint_val.2 hxInterior
    have hxNotBoundary :
        ¬ (leeBoundaryModelWithCorners dimM).IsBoundaryPoint x := by
      -- Interior and boundary points are complementary in Lee's model.
      exact
        (leeBoundaryModelWithCorners dimM).isInteriorPoint_iff_not_isBoundaryPoint x |>.1
          hxInteriorBoundary
    exact hxNotBoundary hxBoundary
  -- Since `M \ B` is closed, a point of the subtype that is not interior must lie on the
  -- ambient frontier.
  exact
    (mem_frontier_iff_notMem_interior x.2).2 hxNotInterior

/-- Helper for Problem 5-8: once abstract boundary points of `M \ B` are known to land in the
ambient frontier, the already stabilized regular-domain embedding argument supplies the converse
implication, so abstract boundary points are exactly frontier points. -/
lemma regular_coordinate_ball_boundary_point_iff_frontier_of_boundary_point_mem_frontier
    {B : Set M}
    (b : Module.Basis (Fin dimM) ℝ E)
    [SmoothManifoldWithBoundary dimM (Set.compl B)]
    (hRegular : Set.IsRegularDomain (modelWithCornersSelf ℝ E) (Set.compl B))
    (hForward :
      ∀ x : Set.compl B,
        (leeBoundaryModelWithCorners dimM).IsBoundaryPoint x →
          x.1 ∈ frontier (Set.compl B)) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace (E := E) (M := M) b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold (E := E) (M := M) b
    ∀ x : Set.compl B,
      (leeBoundaryModelWithCorners dimM).IsBoundaryPoint x ↔
        x.1 ∈ frontier (Set.compl B) := by
  intro _ _ x
  constructor
  · -- The forward implication is the only remaining local bridge to ambient frontier points.
    exact hForward x
  · -- The reverse implication is already stabilized by the Euclidean ambient embedding route.
    intro hx
    exact
      basis_model_regular_domain_frontier_point_isBoundaryPoint
        (E := E) (M := M) (B := B) b hRegular x hx

/-- Helper for Problem 5-8: the same forward boundary-to-frontier bridge identifies the abstract
boundary of `M \ B` with the geometric frontier `closure B \ B`. -/
lemma regular_coordinate_ball_boundary_image_eq_closure_diff_of_boundary_point_mem_frontier
    {B : Set M} (hB : IsRegularCoordinateBall E B)
    (b : Module.Basis (Fin dimM) ℝ E)
    [SmoothManifoldWithBoundary dimM (Set.compl B)]
    (hRegular : Set.IsRegularDomain (modelWithCornersSelf ℝ E) (Set.compl B))
    (hForward :
      ∀ x : Set.compl B,
        (leeBoundaryModelWithCorners dimM).IsBoundaryPoint x →
          x.1 ∈ frontier (Set.compl B)) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      basis_model_chartedSpace (E := E) (M := M) b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      basis_model_isManifold (E := E) (M := M) b
    Subtype.val '' (leeBoundaryModelWithCorners dimM).boundary (Set.compl B) =
      closure B \ B := by
  intro _ _
  have hBoundaryPoint :
      ∀ x : Set.compl B,
        (leeBoundaryModelWithCorners dimM).IsBoundaryPoint x ↔
          x.1 ∈ frontier (Set.compl B) :=
    regular_coordinate_ball_boundary_point_iff_frontier_of_boundary_point_mem_frontier
      (E := E) (M := M) (B := B) b hRegular hForward
  calc
    Subtype.val '' (leeBoundaryModelWithCorners dimM).boundary (Set.compl B) =
        frontier (Set.compl B) := by
      -- First identify the abstract boundary with the ambient frontier of the complement.
      exact
        regular_coordinate_ball_boundary_image_eq_frontier_of_boundary_point_iff
          (E := E) (M := M) hB hBoundaryPoint
    _ = closure B \ B := by
      -- Then rewrite the complement frontier using openness of the regular coordinate ball.
      exact regular_coordinate_ball_compl_frontier_eq_closure_diff (E := E) (M := M) hB

/-- Helper for Problem 5-8: the range of a subtype coercion is exactly the image of the
corresponding subtype set under `Subtype.val`. -/
lemma subtype_val_range_eq_image {α : Type*} [TopologicalSpace α] {s : Set α} :
    Set.range ((↑) : s → α) = Subtype.val '' s := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩

/-- Helper for Problem 5-8: once the abstract boundary image is identified with `closure B \ B`,
the abstract boundary subtype is homeomorphic to that geometric frontier subset. -/
lemma boundary_subtype_homeomorph_to_frontier {B : Set M}
    [SmoothManifoldWithBoundary dimM (Set.compl B)]
    (hBoundaryImage :
      Subtype.val '' (leeBoundaryModelWithCorners dimM).boundary (Set.compl B) =
        closure B \ B) :
    Nonempty
      (↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) ≃ₜ ↥(closure B \ B)) := by
  have hRange :
      Set.range
          ((↑) : ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) → M) =
        closure B \ B := by
    -- First rewrite the range of the subtype coercion as the corresponding image set.
    rw [subtype_val_range_eq_image, hBoundaryImage]
  -- The subtype coercion is always a topological embedding, so once its range is identified with
  -- the geometric frontier, it becomes the desired homeomorphism onto `closure B \ B`.
  exact
    ⟨(Topology.IsEmbedding.subtypeVal.toHomeomorph).trans (Homeomorph.setCongr hRange)⟩

/-- Helper for Problem 5-8: transport the standard unit-sphere charted-space structure across a
chosen homeomorphism onto another topological space. -/
noncomputable abbrev transported_boundarySphere_chartedSpace {S : Type*} [TopologicalSpace S]
    (e : boundarySphere ≃ₜ S) :
    ChartedSpace (EuclideanSpace ℝ (Fin (dimM - 1))) S := by
  let _ : ChartedSpace boundarySphere S :=
    (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp)
  -- Keep the transported atlas explicit so the final sphere comparison remains visible to Lean.
  exact ChartedSpace.comp (EuclideanSpace ℝ (Fin (dimM - 1))) boundarySphere S

/-- Helper for Problem 5-8: the singleton-chart transport of the standard unit sphere yields a
smooth `(dimM - 1)`-manifold on the target space. -/
lemma transported_boundarySphere_isManifold_top
    [NeZero dimM] {S : Type*} [TopologicalSpace S] (e : boundarySphere ≃ₜ S) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (dimM - 1))) S :=
      transported_boundarySphere_chartedSpace (E := E) e
    IsManifold (𝓡 (dimM - 1)) (⊤ : WithTop ℕ∞) S := by
  let eS : OpenPartialHomeomorph S boundarySphere := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace boundarySphere S := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (dimM - 1))) S :=
    transported_boundarySphere_chartedSpace (E := E) e
  have hGroupoid :
      HasGroupoid S (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (dimM - 1))) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eS]) f hf
    have hf'Eq : f' = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eS]) f' hf'
    subst f
    subst f'
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl boundarySphere := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    -- After collapsing the singleton middle chart, compatibility reduces to the usual sphere
    -- compatibility on the source manifold.
    have hcompat :
        ((c.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
          contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (dimM - 1)) := by
      rw [hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible
        (G := contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (dimM - 1))) hc hc'
    simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  -- The transported singleton-chart atlas now packages into the desired smooth structure.
  exact IsManifold.mk' (𝓡 (dimM - 1)) (⊤ : WithTop ℕ∞) S

/-- Helper for Problem 5-8: once the boundary subtype carries the transported sphere atlas, the
transport homeomorphism itself is the resulting diffeomorphism to the standard sphere. -/
lemma transported_homeomorph_to_boundarySphere_is_diffeomorph
    [NeZero dimM] {S : Type*} [TopologicalSpace S] (e : S ≃ₜ boundarySphere) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (dimM - 1))) S :=
      transported_boundarySphere_chartedSpace (E := E) e.symm
    let _ : IsManifold (𝓡 (dimM - 1)) (⊤ : WithTop ℕ∞) S :=
      transported_boundarySphere_isManifold_top (E := E) e.symm
    Nonempty (S ≃ₘ⟮𝓡 (dimM - 1), 𝓡 (dimM - 1)⟯ boundarySphere) := by
  let eS : OpenPartialHomeomorph S boundarySphere := e.toOpenPartialHomeomorph
  let _ : ChartedSpace boundarySphere S := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (dimM - 1))) S :=
    transported_boundarySphere_chartedSpace (E := E) e.symm
  let _ : IsManifold (𝓡 (dimM - 1)) (⊤ : WithTop ℕ∞) S :=
    transported_boundarySphere_isManifold_top (E := E) e.symm
  refine ⟨{ toEquiv := e.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }⟩
  · intro x
    -- In the transported source atlas, the homeomorphism to the standard sphere is the identity
    -- in preferred local coordinates.
    refine (contMDiffAt_iff_of_mem_source
      (I := 𝓡 (dimM - 1)) (I' := 𝓡 (dimM - 1))
      (f := e) (x := x) (x' := x) (y := e x)
      (by simpa using mem_chart_source (EuclideanSpace ℝ (Fin (dimM - 1))) x)
      (by simpa using mem_chart_source (EuclideanSpace ℝ (Fin (dimM - 1))) (e x))).2 ?_
    constructor
    · exact e.continuous.continuousAt
    · apply contDiffWithinAt_id.congr_of_eventuallyEq_of_mem _ (by simp)
      filter_upwards [extChartAt_target_mem_nhdsWithin (I := 𝓡 (dimM - 1)) x] with z hz
      simpa [eS] using
        (writtenInExtChartAt_chartAt_comp
          (I := 𝓡 (dimM - 1)) (x := x) (y := z) hz)
  · intro y
    let x : S := e.symm y
    -- The inverse branch is the same transported-chart identity, read in the opposite direction.
    refine (contMDiffAt_iff_of_mem_source
      (I := 𝓡 (dimM - 1)) (I' := 𝓡 (dimM - 1))
      (f := e.symm) (x := y) (x' := y) (y := x)
      (by simpa using mem_chart_source (EuclideanSpace ℝ (Fin (dimM - 1))) y)
      (by simpa [x] using mem_chart_source (EuclideanSpace ℝ (Fin (dimM - 1))) x)).2 ?_
    constructor
    · exact e.symm.continuous.continuousAt
    · apply contDiffWithinAt_id.congr_of_eventuallyEq_of_mem _ (by simp)
      filter_upwards [extChartAt_target_mem_nhdsWithin (I := 𝓡 (dimM - 1)) y] with z hz
      simpa [x, eS] using
        (writtenInExtChartAt_chartAt_symm_comp
          (I := 𝓡 (dimM - 1)) (x := x) (y := z) hz)

/-- Helper for Problem 5-8: the geometric frontier `closure B \ B` is homeomorphic to the
standard unit sphere after first identifying it with the witness-radius sphere and then
transporting that sphere to Euclidean coordinates and rescaling to radius `1`. -/
lemma regular_coordinate_ball_frontier_homeomorph_to_boundarySphere {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    Nonempty (↥(closure B \ B) ≃ₜ boundarySphere) := by
  rcases hB with ⟨chart, _, hclosure, r, _, hr, _, himage, hclosure_image, _⟩
  have hfrontier_image :
      chart '' (closure B \ B) = Metric.sphere (0 : E) r := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      -- Frontier points of the witness chart land on the corresponding Euclidean sphere.
      exact
        regular_coordinate_ball_witness_frontier_point_mem_sphere
          (E := E) (M := M) hclosure himage hclosure_image hx
    · intro hy
      have hy_closed : y ∈ Metric.closedBall (0 : E) r := Metric.sphere_subset_closedBall hy
      rw [← hclosure_image] at hy_closed
      rcases hy_closed with ⟨x, hxcl, rfl⟩
      have hx_not_mem : x ∉ B := by
        intro hxB
        have hy_ball : chart x ∈ Metric.ball (0 : E) r := by
          rw [← himage]
          exact ⟨x, hxB, rfl⟩
        have hnorm_eq : ‖chart x‖ = r := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hy
        have hnorm_lt : ‖chart x‖ < r := by
          simpa [Metric.mem_ball, dist_eq_norm] using hy_ball
        exact (not_lt_of_ge (le_of_eq hnorm_eq.symm)) hnorm_lt
      exact ⟨x, ⟨hxcl, hx_not_mem⟩, rfl⟩
  let eFrontierSphere : ↥(closure B \ B) ≃ₜ Metric.sphere (0 : E) r :=
    chart.homeomorphOfImageSubsetSource
      (fun x hx ↦ hclosure hx.1)
      hfrontier_image
  let eOrtho : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin dimM) := (stdOrthonormalBasis ℝ E).repr
  let eOrthoChart : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    eOrtho.toHomeomorph.toOpenPartialHomeomorph
  have hOrtho_image :
      eOrthoChart '' Metric.sphere (0 : E) r =
        Metric.sphere (0 : EuclideanSpace ℝ (Fin dimM)) r := by
    -- An orthonormal-basis coordinate map is an isometry, so it preserves round spheres.
    simpa [eOrthoChart] using eOrtho.image_sphere (0 : E) r
  let eSphereEuclid :
      Metric.sphere (0 : E) r ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin dimM)) r :=
    eOrthoChart.homeomorphOfImageSubsetSource
      (fun _ _ ↦ by simp [eOrthoChart])
      hOrtho_image
  let eScale : EuclideanSpace ℝ (Fin dimM) ≃ₜ EuclideanSpace ℝ (Fin dimM) :=
    Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')
  let eScaleChart : OpenPartialHomeomorph
      (EuclideanSpace ℝ (Fin dimM)) (EuclideanSpace ℝ (Fin dimM)) :=
    eScale.toOpenPartialHomeomorph
  have hScale_image :
      eScaleChart '' Metric.sphere (0 : EuclideanSpace ℝ (Fin dimM)) r = boundarySphere := by
    -- Rescaling by `r⁻¹` sends the radius-`r` sphere onto the unit sphere.
    simpa [boundarySphere, eScaleChart, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), hr.ne']
      using
        (Metric.smul_image_sphere (s := r⁻¹) (hs := inv_ne_zero hr.ne')
          (x := (0 : EuclideanSpace ℝ (Fin dimM))) (ε := r))
  let eSphereUnit :
      Metric.sphere (0 : EuclideanSpace ℝ (Fin dimM)) r ≃ₜ boundarySphere :=
    eScaleChart.homeomorphOfImageSubsetSource
      (fun _ _ ↦ by simp [eScaleChart])
      hScale_image
  -- The frontier-to-sphere homeomorphism is the source-faithful composition of witness chart,
  -- orthonormal Euclidean identification, and radial rescaling.
  exact ⟨eFrontierSphere.trans (eSphereEuclid.trans eSphereUnit)⟩

/-- Helper for Problem 5-8: once the abstract boundary subtype is identified with the geometric
frontier, it is homeomorphic to the standard unit sphere. -/
lemma boundary_subtype_homeomorph_to_boundarySphere {B : Set M}
    [SmoothManifoldWithBoundary dimM (Set.compl B)]
    (hB : IsRegularCoordinateBall E B)
    (hBoundaryImage :
      Subtype.val '' (leeBoundaryModelWithCorners dimM).boundary (Set.compl B) =
        closure B \ B) :
    Nonempty
      (↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) ≃ₜ boundarySphere) := by
  rcases boundary_subtype_homeomorph_to_frontier (B := B) hBoundaryImage with
    ⟨eBoundaryFrontier⟩
  rcases regular_coordinate_ball_frontier_homeomorph_to_boundarySphere
      (E := E) (M := M) (B := B) hB with ⟨eFrontierSphere⟩
  -- Compose the already-constructed boundary/frontier homeomorphism with the frontier/sphere
  -- homeomorphism coming from the witness chart geometry.
  exact ⟨eBoundaryFrontier.trans eFrontierSphere⟩

/-- Helper for Problem 5-8: after choosing a regular-domain structure on `M \ B`, the induced
boundary subtype carries the standard sphere smooth structure. -/
theorem regular_coordinate_ball_boundary_carries_sphere_diffeomorph
    {B : Set M} (hB : IsRegularCoordinateBall E B) (hdim : 0 < dimM)
    [SmoothManifoldWithBoundary dimM (Set.compl B)]
    (hRegular : Set.IsRegularDomain (modelWithCornersSelf ℝ E) (Set.compl B)) :
    ∃ _ : ChartedSpace (EuclideanSpace ℝ (Fin (dimM - 1)))
      ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)),
      ∃ _ : IsManifold
        (𝓡 (dimM - 1))
        (⊤ : WithTop ℕ∞)
        ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)),
        Nonempty
          (↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) ≃ₘ⟮𝓡 (dimM - 1),
            𝓡 (dimM - 1)⟯ boundarySphere) := by
  have hfrontier :
      ∃ chart : OpenPartialHomeomorph M E,
        chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
          ∃ r r' : ℝ,
            0 < r ∧
              r < r' ∧
              chart '' (closure B \ B) = Metric.sphere (0 : E) r ∧
              chart '' B = Metric.ball (0 : E) r ∧
              chart '' closure B = Metric.closedBall (0 : E) r ∧
              chart.target = Metric.ball (0 : E) r' :=
    regular_coordinate_ball_frontier_image_eq_sphere (E := E) hB
  -- Route correction: the geometric frontier description is already available; what remains is to
  -- identify the abstract boundary of `Set.compl B` with that frontier and then rescale the
  -- resulting Euclidean sphere to radius `1`.
  have _ := hRegular.isSmoothEmbedding_subtype_val
  have _ := hRegular.isProperlyEmbedded
  letI : NeZero dimM := ⟨Nat.ne_of_gt hdim⟩
  let _ := hfrontier
  let b : Module.Basis (Fin dimM) ℝ E := FiniteDimensional.finBasis ℝ E
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
    basis_model_chartedSpace (E := E) (M := M) b
  let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
    basis_model_isManifold (E := E) (M := M) b
  have hComplFrontier : frontier (Set.compl B) = closure B \ B := by
    -- The ambient frontier of the complement is the geometric boundary of the original ball.
    exact regular_coordinate_ball_compl_frontier_eq_closure_diff (E := E) (M := M) hB
  have hFrontierBoundarySlice :
      ∀ x ∈ frontier (Set.compl B),
        ∃ e : OpenPartialHomeomorph M E,
          x ∈ e.source ∧ e.IsBoundarySliceChart (Set.compl B) dimM := by
    -- The chosen regular-domain owner already forces the ambient local normal form at frontier
    -- points to be the half-slice branch.
    exact
      regular_domain_frontier_point_has_boundary_sliceChart_for_compl
        (E := E) (M := M) (B := B) hB hRegular
  have hBoundaryPointReverse :
      ∀ x : Set.compl B,
        x.1 ∈ frontier (Set.compl B) →
          (leeBoundaryModelWithCorners dimM).IsBoundaryPoint x := by
    intro x hx
    -- The reverse implication is now stabilized by transporting `hRegular` to the Euclidean
    -- ambient model and reusing the already closed smooth-embedding frontier argument.
    exact
      basis_model_regular_domain_frontier_point_isBoundaryPoint
        (E := E) (M := M) (B := B) b hRegular x hx
  have hBoundaryImage_of_forward :
      (∀ hForward :
        ∀ x : Set.compl B,
          (leeBoundaryModelWithCorners dimM).IsBoundaryPoint x →
            x.1 ∈ frontier (Set.compl B),
        Subtype.val '' (leeBoundaryModelWithCorners dimM).boundary (Set.compl B) =
          closure B \ B) := by
    intro hForward
    -- Once the forward bridge is supplied, the set-theoretic boundary identification is finished.
    exact
      regular_coordinate_ball_boundary_image_eq_closure_diff_of_boundary_point_mem_frontier
        (E := E) (M := M) (B := B) hB b hRegular hForward
  have hBoundaryPointForward :
      ∀ x : Set.compl B,
        (leeBoundaryModelWithCorners dimM).IsBoundaryPoint x →
          x.1 ∈ frontier (Set.compl B) := by
    intro x hx
    -- The complement is closed, so abstract boundary points are exactly the non-interior subtype
    -- points and therefore land on the ambient frontier.
    exact regular_domain_boundary_point_mem_frontier (E := E) (M := M) hB x hx
  have hBoundaryImage :
      Subtype.val '' (leeBoundaryModelWithCorners dimM).boundary (Set.compl B) =
        closure B \ B :=
    hBoundaryImage_of_forward hBoundaryPointForward
  have hBoundaryHomeomorphToFrontier :
      Nonempty
        (↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) ≃ₜ ↥(closure B \ B)) := by
    -- The set-theoretic boundary identification already gives the corresponding topological
    -- identification of the abstract boundary subtype with the geometric frontier.
    exact boundary_subtype_homeomorph_to_frontier (B := B) hBoundaryImage
  have hBoundaryHomeomorphToSphere :
      Nonempty
        (↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) ≃ₜ boundarySphere) := by
    -- The witness chart now identifies the geometric frontier with a radius-`r` sphere, and an
    -- orthonormal Euclidean identification plus radial rescaling turns that into the standard
    -- unit sphere.
    exact
      boundary_subtype_homeomorph_to_boundarySphere
        (E := E) (M := M) (B := B) hB hBoundaryImage
  let boundaryCharted :
      ChartedSpace (EuclideanSpace ℝ (Fin (dimM - 1)))
        ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) := by
    rcases hBoundaryHomeomorphToSphere with ⟨eBoundarySphere⟩
    -- Transport the standard sphere atlas back across the explicit boundary-to-sphere
    -- homeomorphism.
    exact transported_boundarySphere_chartedSpace (E := E) eBoundarySphere.symm
  let boundarySmooth :
      IsManifold (𝓡 (dimM - 1)) (⊤ : WithTop ℕ∞)
        ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) := by
    rcases hBoundaryHomeomorphToSphere with ⟨eBoundarySphere⟩
    -- The same singleton-chart transport packages the smooth sphere structure on the boundary
    -- subtype.
    exact transported_boundarySphere_isManifold_top (E := E) eBoundarySphere.symm
  -- The formal part of the boundary/frontier identification is now isolated: once the pointwise
  -- boundary-point criterion is supplied, `regular_coordinate_ball_boundary_image_eq_frontier_of_boundary_point_iff`
  -- turns it into the required set-level boundary image description.
  -- Route correction: the forward boundary-to-frontier bridge is closed, so the last step is
  -- only to recognize that the transported boundary-to-sphere homeomorphism is a diffeomorphism
  -- for the transported atlas by construction.
  refine ⟨boundaryCharted, boundarySmooth, ?_⟩
  rcases hBoundaryHomeomorphToSphere with ⟨eBoundarySphere⟩
  -- With the transported boundary charted space fixed, the local coordinate expression of
  -- `eBoundarySphere` is the identity in the preferred charts.
  exact
    transported_homeomorph_to_boundarySphere_is_diffeomorph
      (E := E) (e := eBoundarySphere)

-- Proof sketch: choose a chart witnessing that `B` is a regular coordinate ball. In this chart,
-- the complement of the round open ball is diffeomorphic to a Euclidean half-space, so the
-- complement carries the chapter's canonical owner `SmoothManifoldWithBoundary dimM`; the ambient
-- compatibility is then expressed by the codimension-`0` owner `Set.IsRegularDomain`.
/-- Problem 5-8, existence half: the complement of a regular coordinate ball carries a smooth
manifold-with-boundary structure making it a regular domain in the ambient manifold. -/
theorem regularCoordinateBall_compl_exists_smoothManifoldWithBoundary
    {B : Set M} (hB : IsRegularCoordinateBall E B) :
    ∃ instSmooth : SmoothManifoldWithBoundary dimM (Set.compl B),
      letI : SmoothManifoldWithBoundary dimM (Set.compl B) := instSmooth
      Set.IsRegularDomain (modelWithCornersSelf ℝ E) (Set.compl B) := by
  have hClosed_compl : IsClosed (Set.compl B) := regular_coordinate_ball_compl_isClosed (E := E) hB
  rcases regular_coordinate_ball_compl_has_smooth_embedding_structure (E := E) (M := M) hB with
      ⟨instSmooth, hEmbedding⟩
  refine ⟨instSmooth, ?_⟩
  letI : SmoothManifoldWithBoundary dimM (Set.compl B) := instSmooth
  -- The only remaining packaging step is topological: closedness of `M \ B` gives properness of
  -- the subtype inclusion, so the chosen boundary structure is a regular domain in Lee's sense.
  refine
    { isSmoothEmbedding_subtype_val := hEmbedding
      isProperlyEmbedded := ?_ }
  exact hClosed_compl.isProperlyEmbedded

-- Proof sketch: first use the existence half to choose a smooth manifold-with-boundary structure
-- on `Bᶜ` making it a regular domain. For that chosen complement structure, its boundary subtype
-- admits the induced smooth structure coming from the round-ball chart, and that boundary
-- manifold is diffeomorphic to the standard unit sphere. Positive ambient dimension is a genuine
-- hypothesis only for this sphere conclusion, so it is kept explicitly here rather than as a
-- global instance.
/-- Problem 5-8, boundary half: the complement of a regular coordinate ball admits a smooth
manifold-with-boundary structure making it a regular domain, and for that induced complement
structure its boundary is diffeomorphic to the standard sphere `S^(n - 1)`. -/
theorem regularCoordinateBall_compl_boundary_diffeomorph_sphere
    {B : Set M} (hB : IsRegularCoordinateBall E B)
    (hdim : 0 < dimM) :
    ∃ instSmooth : SmoothManifoldWithBoundary dimM (Set.compl B),
      letI : SmoothManifoldWithBoundary dimM (Set.compl B) := instSmooth
      ∃ hRegular : Set.IsRegularDomain (modelWithCornersSelf ℝ E) (Set.compl B),
        ∃ _ : ChartedSpace (EuclideanSpace ℝ (Fin (dimM - 1)))
          ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)),
          ∃ _ : IsManifold
            (𝓡 (dimM - 1))
            (⊤ : WithTop ℕ∞)
            ↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)),
            Nonempty
              (↥((leeBoundaryModelWithCorners dimM).boundary (Set.compl B)) ≃ₘ⟮𝓡 (dimM - 1),
                𝓡 (dimM - 1)⟯ boundarySphere) := by
  rcases regularCoordinateBall_compl_exists_smoothManifoldWithBoundary (E := E) (M := M) hB with
      ⟨instSmooth, hRegular⟩
  refine ⟨instSmooth, ?_⟩
  letI : SmoothManifoldWithBoundary dimM (Set.compl B) := instSmooth
  refine ⟨hRegular, ?_⟩
  -- Once the complement structure is fixed, the remaining problem is entirely boundary-local.
  simpa using
    regular_coordinate_ball_boundary_carries_sphere_diffeomorph
      (E := E) (M := M) hB hdim hRegular
