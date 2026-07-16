import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Immersion
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap03.Sec03_17.Definition_3_17_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap03.Sec03_17.Proposition_3_24
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap03.Sec03_18.Definition_3_18_extra_3
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_35.Notation_5_35_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section TangentSpaceToSubmanifoldByCurves

universe uE uE' uH uH' uM

open Manifold Set

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ∞ S] [BoundarylessManifold J S]

local notation "BasedSmoothCurveAt" => @SmoothCurveAt E' _ _ H' _ J { x // x ∈ S } _ _

/-- Helper for Proposition 5.35: the ambient owner `IsImmersedSubmanifold` is the assertion that
the subtype inclusion `S ↪ M` is an immersion for the chosen smooth structure on `S`. -/
abbrev IsImmersedSubmanifold
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type uH} [TopologicalSpace H]
    {H' : Type uH'} [TopologicalSpace H']
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (J : ModelWithCorners ℝ E' H') (S : Set M)
    [ChartedSpace H' S] [IsManifold J ∞ S] : Prop :=
  Manifold.IsImmersion J I ∞ (Subtype.val : S → M)

-- Proof sketch: for `→`, write `v` as `d(Subtype.val)_p w` and realize `w ∈ TₚS` by a based
-- smooth curve in the boundaryless immersed submanifold `S` through `p`; composing with the
-- inclusion gives the required ambient velocity. For `←`, differentiate the inclusion-composed
-- curve at `0` and use the immersion hypothesis on `Subtype.val : S → M` to see that its ambient
-- velocity lies in the range of `d(Subtype.val)_p`.
/-- Helper for Proposition 5.35: every intrinsic tangent vector to the submanifold `S` at `p` is
represented by a based smooth curve in `S` through `p`. -/
lemma exists_based_smoothCurveAt_tangentVector_eq (p : S) (w : TangentSpace J p) :
    ∃ γ : BasedSmoothCurveAt p, γ.tangentVector = w :=
  exists_smoothCurveAt_tangentVector_eq (I := J) p w

omit [BoundarylessManifold J S] in
/-- Helper for Proposition 5.35: the subtype inclusion of an immersed submanifold is
manifold-differentiable at each point. -/
lemma subtype_val_mdifferentiableAt_of_isImmersedSubmanifold
    (hS : IsImmersedSubmanifold I J S) (p : S) :
    MDifferentiableAt J I (Subtype.val : S → M) p := by
  let hι : Manifold.IsImmersionAt J I ∞ (Subtype.val : S → M) p := hS.isImmersionAt p
  have hdomChart :
      hι.domChart ∈ IsManifold.maximalAtlas J 1 S :=
    IsManifold.maximalAtlas_subset_of_le (I := J) (M := S) (m := 1) (n := ∞)
      (by simp) hι.domChart_mem_maximalAtlas
  have hcodChart :
      hι.codChart ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (I := I) (M := M) (m := 1) (n := ∞)
      (by simp) hι.codChart_mem_maximalAtlas
  -- Express differentiability in the source and target charts supplied by the immersion datum.
  rw [← mdifferentiableWithinAt_univ]
  rw [mdifferentiableWithinAt_iff_of_mem_maximalAtlas
      (s := Set.univ)
      (e := hι.domChart) (e' := hι.codChart)
      hdomChart hcodChart
      hι.mem_domChart_source hι.mem_codChart_source]
  simp only [continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  -- Replace the chart expression by the linear normal form valid on the immersion chart target.
  have hEq :
      ((hι.codChart.extend I) ∘ (Subtype.val : S → M) ∘ (hι.domChart.extend J).symm)
        =ᶠ[nhdsWithin (hι.domChart.extend J p) (range J)]
      hι.equiv ∘ fun x : E' ↦ (x, (0 : hι.complement)) := by
    exact hι.writtenInCharts.eventuallyEq_of_mem
      ((hι.domChart).extend_target_mem_nhdsWithin (I := J) hι.mem_domChart_source)
  have hxrange : hι.domChart.extend J p ∈ range J := by
    rw [OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  have hxtarget : hι.domChart.extend J p ∈ (hι.domChart.extend J).target :=
    mem_of_mem_nhdsWithin hxrange
      ((hι.domChart).extend_target_mem_nhdsWithin (I := J) hι.mem_domChart_source)
  have hEq0 :
      ((hι.codChart.extend I) ∘ (Subtype.val : S → M) ∘ (hι.domChart.extend J).symm)
          (hι.domChart.extend J p) =
        (hι.equiv ∘ fun x : E' ↦ (x, (0 : hι.complement))) (hι.domChart.extend J p) :=
    hι.writtenInCharts hxtarget
  have hlin :
      DifferentiableWithinAt ℝ
        (hι.equiv ∘ fun x : E' ↦ (x, (0 : hι.complement)))
        (range J)
        (hι.domChart.extend J p) := by
    fun_prop
  exact hlin.congr_of_eventuallyEq hEq hEq0

omit [BoundarylessManifold J S] in
/-- Helper for Proposition 5.35: the ambient velocity of a curve in `S`, viewed in `M`, is the
differential of the subtype inclusion applied to the curve's intrinsic tangent vector. -/
lemma ambient_velocity_eq_subtype_mfderiv_tangentVector
    (hS : IsImmersedSubmanifold I J S) {p : S} (γ : BasedSmoothCurveAt p) :
    γ.source ▸ curve_velocityWithin I (((↑) : S → M) ∘ γ) γ.sourceSet 0 =
      mfderiv J I (Subtype.val : S → M) p γ.tangentVector := by
  rcases γ with ⟨r, f, hs, hsm⟩
  let γ0 : BasedSmoothCurveAt p := ⟨r, f, hs, hsm⟩
  have hsub : MDifferentiableAt J I (Subtype.val : S → M) (f 0) := by
    simpa [hs] using
      subtype_val_mdifferentiableAt_of_isImmersedSubmanifold (hS := hS) (p := p)
  have hγ :
      MDifferentiableWithinAt 𝓘(ℝ) J f γ0.sourceSet 0 := by
    exact (γ0.smooth.mdifferentiableOn (by simp)) 0 γ0.zero_mem_sourceSet
  -- Route correction: differentiate the inclusion-composed curve via the chain rule instead of
  -- unfolding tangent vectors directly.
  have hcomp :
      curve_velocityWithin I (((↑) : S → M) ∘ f) γ0.sourceSet 0 =
        mfderiv J I (Subtype.val : S → M) (f 0) (curve_velocityWithin J f γ0.sourceSet 0) :=
    composite_curve_velocity
      (I := J) (I' := I) (J := γ0.sourceSet) (t₀ := 0)
      (F := (Subtype.val : S → M)) (γ := f) γ0.uniqueMDiffWithinAt_sourceSet hsub hγ
  cases hs
  simpa [γ0, SmoothCurveAt.tangentVector, Function.comp] using hcomp

/-- Proposition 5.35: for a boundaryless immersed submanifold `S ⊆ M`, an ambient tangent vector
at `p` belongs to `TₚS` exactly when it is the velocity at `0` of the inclusion of a based smooth
curve in `S`. -/
theorem tangentVector_mem_submanifold_iff_exists_curve
    (hS : IsImmersedSubmanifold I J S) (p : S) (v : TangentSpace I (p : M)) :
    v ∈ T[J; p] ↔
      ∃ γ : BasedSmoothCurveAt p,
        γ.source ▸ curve_velocityWithin I (((↑) : S → M) ∘ γ) γ.sourceSet 0 = v :=
    by
  constructor
  · intro hv
    -- Unpack tangent-space membership as a range witness for the inclusion differential.
    rw [show T[J; p] = (mfderiv J I (Subtype.val : S → M) p).range by rfl,
      LinearMap.mem_range] at hv
    rcases hv with ⟨w, rfl⟩
    rcases exists_based_smoothCurveAt_tangentVector_eq (p := p) w with ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    -- The ambient velocity is the image of the curve's intrinsic tangent vector.
    calc
      γ.source ▸ curve_velocityWithin I (((↑) : S → M) ∘ γ) γ.sourceSet 0
          = mfderiv J I (Subtype.val : S → M) p γ.tangentVector :=
        ambient_velocity_eq_subtype_mfderiv_tangentVector (hS := hS) (γ := γ)
      _ = mfderiv J I (Subtype.val : S → M) p w := by rw [hγ]
  · rintro ⟨γ, hγ⟩
    -- The differential image of the curve's intrinsic tangent vector is its ambient velocity.
    rw [show T[J; p] = (mfderiv J I (Subtype.val : S → M) p).range by rfl,
      LinearMap.mem_range]
    refine ⟨γ.tangentVector, ?_⟩
    exact (ambient_velocity_eq_subtype_mfderiv_tangentVector
      (hS := hS) (γ := γ)).symm.trans hγ

end TangentSpaceToSubmanifoldByCurves
