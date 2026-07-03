import SmoothManifolds_Lee_2012.Chap03.Sec03_17.Definition_3_17_extra_1
import SmoothManifolds_Lee_2012.Chap03.Sec03_17.Proposition_3_24
import SmoothManifolds_Lee_2012.Chap04.Sec04_24.Example_4_19
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_32.Corollary_5_30
import SmoothManifolds_Lee_2012.Chap05.Sec05_35.Notation_5_35_extra_1
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

noncomputable section

universe uE uE' uH uH' uM

section EmbeddedSubmanifoldCurves

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ⊤ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ⊤ S]

/-- Helper for Problem 5-19: the subtype inclusion of an embedded submanifold is
manifold-differentiable at every point. -/
lemma subtype_val_mdifferentiableAt_of_isEmbeddedSubmanifold
    [IsEmbeddedSubmanifold I J S]
    (p : S) :
    MDifferentiableAt J I (Subtype.val : S → M) p := by
  let hι : Manifold.IsImmersionAt J I ⊤ (Subtype.val : S → M) p :=
    IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val.isImmersion.isImmersionAt p
  have hdom :
      hι.domChart ∈ IsManifold.maximalAtlas J 1 S :=
    IsManifold.maximalAtlas_subset_of_le
      (I := J) (M := S) (show (1 : ℕ∞ω) ≤ (⊤ : ℕ∞ω) by simp)
      hι.domChart_mem_maximalAtlas
  have hcod :
      hι.codChart ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le
      (I := I) (M := M) (show (1 : ℕ∞ω) ≤ (⊤ : ℕ∞ω) by simp)
      hι.codChart_mem_maximalAtlas
  have hp_source : p ∈ (hι.domChart.extend J).source := by
    simpa [hι.domChart.extend_source (I := J)] using hι.mem_domChart_source
  have hp_target : (hι.domChart.extend J) p ∈ (hι.domChart.extend J).target := by
    exact (hι.domChart.extend J).map_source hp_source
  have hlinear :
      DifferentiableWithinAt ℝ
        (((hι.equiv).toContinuousLinearMap).comp (ContinuousLinearMap.inl ℝ E' hι.complement))
        (hι.domChart.extend J).target ((hι.domChart.extend J) p) := by
    exact (((hι.equiv).toContinuousLinearMap).comp
      (ContinuousLinearMap.inl ℝ E' hι.complement)).differentiableAt.differentiableWithinAt
  have hchart :
      DifferentiableWithinAt ℝ
        ((hι.codChart.extend I) ∘ (Subtype.val : S → M) ∘ (hι.domChart.extend J).symm)
        (hι.domChart.extend J).target ((hι.domChart.extend J) p) := by
    refine hlinear.congr ?_ ?_
    · intro x hx
      simpa [ContinuousLinearMap.comp_apply, Function.comp_apply] using hι.writtenInCharts hx
    · simpa [ContinuousLinearMap.comp_apply, Function.comp_apply] using hι.writtenInCharts hp_target
  have hwithin :
      MDifferentiableWithinAt J I (Subtype.val : S → M) hι.domChart.source p := by
    have hset := hι.domChart.extend_symm_preimage_inter_range_eventuallyEq
      (I := J) (s := hι.domChart.source) (fun x hx ↦ hx) hι.mem_domChart_source
    have hchart_image :
        DifferentiableWithinAt ℝ
          ((hι.codChart.extend I) ∘ (Subtype.val : S → M) ∘ (hι.domChart.extend J).symm)
          ((hι.domChart.extend J) '' hι.domChart.source) ((hι.domChart.extend J) p) := by
      convert hchart using 2
      exact (hι.domChart.extend_target_eq_image_source (I := J)).symm
    have hchart_source :
        DifferentiableWithinAt ℝ
          ((hι.codChart.extend I) ∘ (Subtype.val : S → M) ∘ (hι.domChart.extend J).symm)
          (Set.preimage (↑hι.domChart.symm ∘ ↑J.symm) hι.domChart.source ∩ Set.range ↑J)
          ((hι.domChart.extend J) p) :=
      (differentiableWithinAt_congr_set (f := (hι.codChart.extend I) ∘
          (Subtype.val : S → M) ∘ (hι.domChart.extend J).symm) hset).2 hchart_image
    refine (mdifferentiableWithinAt_iff_of_mem_maximalAtlas
      (I := J) (I' := I) (f := (Subtype.val : S → M))
      (s := hι.domChart.source) (e := hι.domChart) (e' := hι.codChart)
      hdom hcod hι.mem_domChart_source hι.mem_codChart_source).2 ?_
    refine ⟨continuous_subtype_val.continuousWithinAt, ?_⟩
    simpa [hι.domChart.extend_source (I := J)] using hchart_source
  exact hwithin.mdifferentiableAt (hι.domChart.open_source.mem_nhds hι.mem_domChart_source)

/-- Helper for Problem 5-19: after lifting a curve with image in an embedded submanifold to the
subtype, the ambient velocity is the derivative of the inclusion applied to the intrinsic
velocity. -/
lemma curve_velocity_eq_subtype_inclusion_mfderiv
    [IsEmbeddedSubmanifold I J S]
    (γ : ℝ → M) (hγ_smooth : ContMDiff 𝓘(ℝ) I ⊤ γ)
    (hγ : ∀ t : ℝ, γ t ∈ S) (t : ℝ) :
    curve_velocity I γ t =
      mfderiv J I (Subtype.val : S → M) ⟨γ t, hγ t⟩
        (curve_velocity J (Set.codRestrict γ S hγ) t) := by
  let γS : ℝ → S := Set.codRestrict γ S hγ
  have hγS_smooth : ContMDiff 𝓘(ℝ) J ⊤ γS :=
    contMDiff_toSubtype_of_isEmbeddedSubmanifold hγ_smooth hγ
  have hγS_mdifferentiable : MDifferentiableAt 𝓘(ℝ) J γS t := by
    simpa using hγS_smooth.mdifferentiableAt (show (⊤ : ℕ∞ω) ≠ 0 by simp)
  have hcomp :
      curve_velocityWithin I ((Subtype.val : S → M) ∘ γS) Set.univ t =
        mfderiv J I (Subtype.val : S → M) (γS t)
          (curve_velocityWithin J γS Set.univ t) := by
    exact composite_curve_velocity
      (I := J) (I' := I) (J := Set.univ) (t₀ := t)
      (F := (Subtype.val : S → M)) (γ := γS)
      (uniqueMDiffWithinAt_univ 𝓘(ℝ))
      (subtype_val_mdifferentiableAt_of_isEmbeddedSubmanifold (I := I) (J := J) (S := S) (γS t))
      hγS_mdifferentiable.mdifferentiableWithinAt
  have hγ_univ :
      curve_velocityWithin I γ Set.univ t = curve_velocity I γ t :=
    curve_velocityWithin_eq_curve_velocity
      (I := I) (γ := γ) (s := Set.univ) (t := t)
      (uniqueMDiffWithinAt_univ 𝓘(ℝ))
      (by simpa using hγ_smooth.mdifferentiableAt (show (⊤ : ℕ∞ω) ≠ 0 by simp))
  have hγS_univ :
      curve_velocityWithin J γS Set.univ t = curve_velocity J γS t :=
    curve_velocityWithin_eq_curve_velocity
      (I := J) (γ := γS) (s := Set.univ) (t := t)
      (uniqueMDiffWithinAt_univ 𝓘(ℝ)) hγS_mdifferentiable
  -- The ambient curve is definitionally the inclusion composed with the lifted curve.
  have hcod : ((Subtype.val : S → M) ∘ γS) = γ := by
    funext x
    rfl
  rw [hγS_univ] at hcomp
  rw [hcod, hγ_univ] at hcomp
  simpa [γS] using hcomp

/-- Problem 5-19 (1): if a smooth curve in `M` has image in an embedded submanifold `S`, then its
ambient velocity vector lies in the tangent subspace of `S`, viewed as the range of the
differential of the subtype inclusion. -/
theorem curve_velocity_mem_embedded_submanifold_tangent
    [IsEmbeddedSubmanifold I J S]
    (γ : ℝ → M) (hγ_smooth : ContMDiff 𝓘(ℝ) I ⊤ γ)
    (hγ : ∀ t : ℝ, γ t ∈ S) (t : ℝ) :
    curve_velocity I γ t ∈ T[J; ⟨γ t, hγ t⟩] := by
  let γS : ℝ → S := Set.codRestrict γ S hγ
  -- Lift the curve to the subtype, then read the ambient velocity as an image under the inclusion.
  have hvelocity :
      curve_velocity I γ t =
        mfderiv J I (Subtype.val : S → M) ⟨γ t, hγ t⟩
          (curve_velocity J γS t) :=
    curve_velocity_eq_subtype_inclusion_mfderiv γ hγ_smooth hγ t
  exact LinearMap.mem_range.mpr ⟨curve_velocity J γS t, hvelocity.symm⟩

end EmbeddedSubmanifoldCurves

/-- Helper for Problem 5-19: every tangent vector to the real line is the corresponding scalar
multiple of the unit tangent vector. -/
lemma tangentSpace_real_smul_one_eq (t : ℝ) (v : TangentSpace 𝓘(ℝ) t) :
    (NormedSpace.fromTangentSpace t v) • (1 : TangentSpace 𝓘(ℝ) t) = v := by
  have hone : (NormedSpace.fromTangentSpace t) (1 : TangentSpace 𝓘(ℝ) t) = (1 : ℝ) := rfl
  apply (NormedSpace.fromTangentSpace t).injective
  simp [hone, smul_eq_mul]

/-- The derivative of the figure-eight immersion at parameter `t`, expressed in `ℝ²` using
`NormedSpace.fromTangentSpace`. -/
def figureEightTangentMap (t : ℝ) : TangentSpace 𝓘(ℝ) t →L[ℝ] ℝ × ℝ :=
  (NormedSpace.fromTangentSpace (figureEightCurveMap t)).toContinuousLinearMap ∘L
    mfderiv 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) figureEightCurveMap t

/-- The velocity of the figure-eight branch at parameter `t`, written in `ℝ²` via
`NormedSpace.fromTangentSpace`. -/
abbrev figureEightBranchVelocity (t : ℝ) : ℝ × ℝ :=
  NormedSpace.fromTangentSpace (figureEightCurveMap t)
    (curve_velocity 𝓘(ℝ, ℝ × ℝ) figureEightCurveMap t)

/-- The tangent line in `ℝ²` determined by the figure-eight branch at parameter `t`. -/
def figureEightTangentLine (t : ℝ) : Submodule ℝ (ℝ × ℝ) :=
  (figureEightTangentMap t).range

/-- Helper for Problem 5-19: the branch velocity of the figure-eight is the explicit vector
`(2 cos (2t), cos t)` in `ℝ²`. -/
lemma figureEightBranchVelocity_eq (t : ℝ) :
    figureEightBranchVelocity t = (2 * Real.cos (2 * t), Real.cos t) := by
  have hfst : HasDerivAt (Real.sin ∘ HMul.hMul 2) (2 * Real.cos (2 * t)) t := by
    simpa [two_mul, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_sin (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)
  have hsnd : HasDerivAt (fun x : ℝ ↦ Real.sin x) (Real.cos t) t := by
    simpa using Real.hasDerivAt_sin t
  have hcurve : HasDerivAt figureEightCurveMap (2 * Real.cos (2 * t), Real.cos t) t := by
    -- Differentiate the two coordinates separately and reassemble them into the product map.
    simpa [figureEightCurveMap, Function.comp] using hfst.prodMk hsnd
  have hcurve_fderiv :
      fderiv ℝ figureEightCurveMap t =
        ContinuousLinearMap.toSpanSingleton ℝ (2 * Real.cos (2 * t), Real.cos t) := by
    simpa using hcurve.hasFDerivAt.fderiv
  have hfderiv :
      fderiv ℝ figureEightCurveMap t 1 = (2 * Real.cos (2 * t), Real.cos t) := by
    -- Applying the Fréchet derivative to `1` recovers the ordinary one-variable derivative.
    simpa using DFunLike.congr_fun hcurve_fderiv 1
  simpa [figureEightBranchVelocity, curve_velocity, mfderiv_eq_fderiv] using hfderiv

/-- Helper for Problem 5-19: every value of the figure-eight tangent map is a scalar multiple of
the branch velocity at the same parameter. -/
lemma figureEightTangentMap_apply_eq_smul_branch_velocity
    (t : ℝ) (v : TangentSpace 𝓘(ℝ) t) :
    figureEightTangentMap t v =
      (NormedSpace.fromTangentSpace t v) • figureEightBranchVelocity t := by
  -- The parameter-line tangent space is one-dimensional, so the tangent map is determined by its
  -- value on the unit tangent vector.
  calc
    figureEightTangentMap t v
        = figureEightTangentMap t
            ((NormedSpace.fromTangentSpace t v) • (1 : TangentSpace 𝓘(ℝ) t)) := by
          rw [tangentSpace_real_smul_one_eq t v]
    _ = (NormedSpace.fromTangentSpace t v) •
          figureEightTangentMap t (1 : TangentSpace 𝓘(ℝ) t) := by
          rw [map_smul]
    _ = (NormedSpace.fromTangentSpace t v) • figureEightBranchVelocity t := by
          rfl

/-- Helper for Problem 5-19: the tangent line determined by a branch of the figure-eight is the
span of its branch velocity. -/
lemma figureEightTangentLine_eq_span_branch_velocity (t : ℝ) :
    figureEightTangentLine t = ℝ ∙ figureEightBranchVelocity t := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    -- Any tangent-map value is a scalar multiple of the branch velocity.
    refine Submodule.mem_span_singleton.mpr ?_
    refine ⟨NormedSpace.fromTangentSpace t w, ?_⟩
    simpa using (figureEightTangentMap_apply_eq_smul_branch_velocity t w).symm
  · intro hv
    rcases Submodule.mem_span_singleton.mp hv with ⟨a : ℝ, ha⟩
    -- Conversely, every scalar multiple is realized by feeding that scalar into the tangent map.
    refine LinearMap.mem_range.mpr ?_
    refine ⟨((NormedSpace.fromTangentSpace t).symm a : TangentSpace 𝓘(ℝ) t), ?_⟩
    have hscalar :
        figureEightTangentMap t ((NormedSpace.fromTangentSpace t).symm a : TangentSpace 𝓘(ℝ) t) =
          a • figureEightBranchVelocity t := by
      simpa using
        figureEightTangentMap_apply_eq_smul_branch_velocity t
          ((NormedSpace.fromTangentSpace t).symm a : TangentSpace 𝓘(ℝ) t)
    exact hscalar.trans ha

-- Proof sketch: evaluate `figureEightCurveMap` at `0` and `π` to see they give the same ambient
-- point, then compare the two branch velocities after identifying tangent spaces of `ℝ²` with
-- `ℝ²` via `NormedSpace.fromTangentSpace`, and check that the velocity at `0` is not contained in
-- the tangent line coming from the branch through `π`.
/-- Problem 5-19 (2): the figure-eight immersion of `ℝ` into `ℝ²` gives a counterexample in the
non-embedded case: the same ambient point is reached at parameters `0` and `π`, but the velocity
at `0` is not in the tangent line determined by the branch at `π`, after identifying tangent
spaces of `ℝ²` with `ℝ²` by `NormedSpace.fromTangentSpace`. -/
theorem figureEightCurveMap_counterexample :
    figureEightCurveMap 0 = figureEightCurveMap Real.pi ∧
      figureEightBranchVelocity 0 ∉ figureEightTangentLine Real.pi := by
  constructor
  · -- The two parameters `0` and `π` map to the same self-intersection point of the figure-eight.
    simp [figureEightCurveMap]
  · intro hmem
    rw [figureEightTangentLine_eq_span_branch_velocity] at hmem
    rcases Submodule.mem_span_singleton.mp hmem with ⟨a, ha⟩
    have hfst : a * (2 * Real.cos (2 * Real.pi)) = 2 * Real.cos (2 * 0) := by
      simpa [figureEightBranchVelocity_eq, smul_eq_mul] using congrArg Prod.fst ha
    have hsnd : a * Real.cos Real.pi = Real.cos 0 := by
      simpa [figureEightBranchVelocity_eq, smul_eq_mul] using congrArg Prod.snd ha
    -- The first coordinate forces `a = 1`, while the second then gives `-1 = 1`.
    have hfst' : a * 2 = 2 := by
      simpa [Real.cos_zero, Real.cos_two_pi] using hfst
    have hsnd' : -a = 1 := by
      simpa [Real.cos_zero, Real.cos_pi] using hsnd
    linarith
