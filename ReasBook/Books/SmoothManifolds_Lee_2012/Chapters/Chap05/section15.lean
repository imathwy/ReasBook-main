import Mathlib
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_5_15 (from Chap05/Sec05_30) -/
open scoped Manifold

section

variable (n : ℕ)

/- Example 5.15 is a bridge/view item, not a new owner: the source-facing owner for the unit
sphere as an embedded submanifold was already established in Example 5.9, and the smooth-embedding
formulation is the canonical projection `IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val`. -/
recall unitSphere_isEmbeddedSubmanifold (n : ℕ) :
    IsEmbeddedSubmanifold
      (𝓡 (n + 1))
      (𝓡 n)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/- Example 5.15, in smooth-embedding language, is exactly the subtype-inclusion projection
furnished by the embedded-submanifold owner above. -/
#check (unitSphere_isEmbeddedSubmanifold n).isSmoothEmbedding_subtype_val

end

/-! ### Problem_5_15 (from Chap05/Sec05_37) -/
open scoped ContDiff
open Manifold

noncomputable section

local notation "Plane" => ℝ × ℝ
local notation "StandardFigureEightInterval" => Set.Ioo (-Real.pi) Real.pi
local notation "ShiftedFigureEightInterval" => Set.Ioo (0 : ℝ) (2 * Real.pi)
local notation "FigureEightImage" => Set.range figureEightCurve

/-- Helper for Problem 5-15: transport the source charted-space structure across a homeomorphism
onto a chosen subset of the plane. -/
noncomputable abbrev transported_subset_chartedSpace {N : Type*} [TopologicalSpace N]
    [ChartedSpace ℝ N] {S : Set Plane} [TopologicalSpace S] (e : N ≃ₜ S) :
    ChartedSpace ℝ S := by
  let _ : ChartedSpace N S :=
    (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp)
  -- Use the explicit singleton-chart route so the transported charts remain visible to Lean.
  exact ChartedSpace.comp ℝ N S

/-- Helper for Problem 5-15: the transported range charted space is again a smooth `1`-manifold at
the outer regularity `⊤`. -/
lemma transported_subset_isManifold_top {N : Type*} [TopologicalSpace N] [ChartedSpace ℝ N]
    [IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) N] {S : Set Plane} [TopologicalSpace S] (e : N ≃ₜ S) :
    let _ : ChartedSpace ℝ S := transported_subset_chartedSpace e
    IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := by
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace ℝ S := transported_subset_chartedSpace e
  have hGroupoid : HasGroupoid S (contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ)) := by
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
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    -- The transported charts differ only by the source charts on `N`, so compatibility reduces
    -- to the already-known compatibility on the source manifold.
    have hcompat :
        ((c.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ) := by
      rw [hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible (G := contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ)) hc hc'
    simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  -- The explicit transported atlas therefore defines a smooth manifold structure on the range.
  exact IsManifold.mk' 𝓘(ℝ) (⊤ : WithTop ℕ∞) S

/-- Helper for Problem 5-15: once the transported topology and atlas on the range are fixed
definitionally, the subtype inclusion uses the same immersion charts as the original map. -/
lemma transported_subset_val_eq_comp_homeomorph_symm {N : Type*} [TopologicalSpace N]
    [ChartedSpace ℝ N] {g : N → Plane} {S : Set Plane} [TopologicalSpace S] (e : N ≃ₜ S)
    (he : ∀ x, ((e x : S) : Plane) = g x) :
    (Subtype.val : S → Plane) = g ∘ e.symm := by
  -- Evaluate the factorization at a point of the transported subset and rewrite using
  -- `e (e.symm x) = x`.
  funext x
  simpa using he (e.symm x)

/-- Helper for Problem 5-15: once the transported topology and atlas on the range are fixed
definitionally, the subtype inclusion uses the same immersion charts as the original map. -/
lemma transported_subset_val_isImmersionAt_explicit {N : Type*} [TopologicalSpace N]
    [ChartedSpace ℝ N] [IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) N] {g : N → Plane}
    {S : Set Plane} [TopologicalSpace S]
    (hg : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) g) (e : N ≃ₜ S)
    (he : ∀ x, ((e x : S) : Plane) = g x) (x : S) :
    let _ : ChartedSpace ℝ S := transported_subset_chartedSpace e
    let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := transported_subset_isManifold_top e
    IsImmersionAtOfComplement hg.complement 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
      (Subtype.val : S → Plane) x := by
  let instCharted : ChartedSpace ℝ S := transported_subset_chartedSpace e
  let _ : ChartedSpace ℝ S := instCharted
  let instManifold : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := transported_subset_isManifold_top e
  let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := instManifold
  let hCompImm := hg.isImmersionOfComplement_complement
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext z
    simp [eS])
  let hx := hCompImm (e.symm x)
  -- Transport the source chart of `g` across the homeomorphism onto `S`.
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv (e.symm.toOpenPartialHomeomorph.trans hx.domChart) hx.codChart ?_ ?_ ?_ ?_ ?_ ?_
  · -- The transported source chart still contains the point `x`.
    simpa [OpenPartialHomeomorph.trans_source] using hx.mem_domChart_source
  · -- The codomain chart condition is the same pointwise statement as for `g`.
    have hxe : g (e.symm x) = (x : Plane) := by
      simpa using (he (e.symm x)).symm
    simpa [hxe] using hx.mem_codChart_source
  · -- The transported source chart stays in the maximal atlas after chart transport.
    intro d hd
    rcases hd with ⟨f, hf, c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext z
        simp [eS]) f hf
    subst f
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    constructor
    · have hleft :
          ((hx.domChart.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
            contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ) := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').1
      simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hleft
    · have hright :
          ((c'.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ hx.domChart) ∈
            contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ) := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').2
      simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hright
  · exact hx.codChart_mem_maximalAtlas
  · -- Source points in the transported chart map into the codomain chart source because
    -- `Subtype.val ∘ e = g`.
    intro z hz
    have hz' : e.symm z ∈ hx.domChart.source := by
      simpa [OpenPartialHomeomorph.trans_source] using hz
    have hze : g (e.symm z) = (z : Plane) := by
      simpa using (he (e.symm z)).symm
    simpa [hze] using hx.source_subset_preimage_source hz'
  · -- In the transported source chart, the inclusion `S ↪ ℝ²` has the same normal form as `g`.
    intro u hu
    have hu' : u ∈ (hx.domChart.extend 𝓘(ℝ)).target := by
      simpa [OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target] using hu
    have hpoint : ((e (hx.domChart.symm u) : S) : Plane) = g (hx.domChart.symm u) := by
      exact he (hx.domChart.symm u)
    simpa [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe, hpoint] using
      hx.writtenInCharts hu'

/-- Helper for Problem 5-15: once the transported topology and atlas on the range are fixed
definitionally, the subtype inclusion uses the same immersion charts as the original map. -/
lemma transported_subset_val_isImmersion_explicit {N : Type*} [TopologicalSpace N]
    [ChartedSpace ℝ N] [IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) N] {g : N → Plane}
    {S : Set Plane} [TopologicalSpace S]
    (hg : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) g) (e : N ≃ₜ S)
    (he : ∀ x, ((e x : S) : Plane) = g x) :
    let _ : ChartedSpace ℝ S := transported_subset_chartedSpace e
    let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := transported_subset_isManifold_top e
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) (Subtype.val : S → Plane) := by
  let instCharted : ChartedSpace ℝ S := transported_subset_chartedSpace e
  let _ : ChartedSpace ℝ S := instCharted
  let instManifold : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := transported_subset_isManifold_top e
  let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := instManifold
  -- Route correction: prove the global immersion by reusing the pointwise transported witness,
  -- rather than asking Lean to elaborate the full singleton-chart transport in one step.
  refine ⟨hg.complement, inferInstance, inferInstance, ?_⟩
  intro x
  exact transported_subset_val_isImmersionAt_explicit hg e he x

/-- Helper for Problem 5-15: transporting the interval structure along a range equivalence gives
an immersed-curve structure on the common image. -/
lemma transported_subset_isImmersedCurveWithTopology {N : Type*} [TopologicalSpace N]
    [ChartedSpace ℝ N] [IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) N] {g : N → Plane}
    {S : Set Plane} [TopologicalSpace S]
    (hg : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) g) (e : N ≃ₜ S)
    (he : ∀ x, ((e x : S) : Plane) = g x) :
    Set.IsImmersedCurveWithTopology S (inferInstance : TopologicalSpace S) := by
  let instCharted : ChartedSpace ℝ S := transported_subset_chartedSpace e
  let _ : ChartedSpace ℝ S := instCharted
  let instManifold : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := transported_subset_isManifold_top e
  let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := instManifold
  -- Package the transported atlas and manifold structure, then discharge immersion explicitly.
  refine ⟨instCharted, instManifold, ?_⟩
  simpa using transported_subset_val_isImmersion_explicit hg e he

/-- Helper for Problem 5-15: the shifted figure-eight cut uses the parameter interval `(0, 2π)`. -/
def figureEightShiftedCurve : Set.Ioo (0 : ℝ) (2 * Real.pi) → Plane :=
  fun t ↦ figureEightCurveMap t

/-- Helper for Problem 5-15: the standard parameter interval `(-π, π)` carries its usual
one-chart smooth structure. -/
instance : Nonempty (Set.Ioo (-Real.pi) Real.pi) :=
  ⟨⟨0, by
    constructor
    · simpa using neg_lt_zero.mpr Real.pi_pos
    · simpa using Real.pi_pos⟩⟩

/-- Helper for Problem 5-15: the standard parameter interval `(-π, π)` carries its usual
one-chart smooth structure. -/
noncomputable instance : ChartedSpace ℝ (Set.Ioo (-Real.pi) Real.pi) :=
  by
    let U : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-Real.pi) Real.pi, isOpen_Ioo⟩
    -- Use the canonical open-subtype owner so later `IsImmersion.of_opens` lemmas elaborate
    -- without transport mismatches.
    change ChartedSpace ℝ U
    infer_instance

/-- Helper for Problem 5-15: the standard parameter interval `(-π, π)` is a smooth `1`-manifold. -/
instance : IsManifold (𝓘(ℝ)) (⊤ : WithTop ℕ∞) (Set.Ioo (-Real.pi) Real.pi) :=
  by
    let U : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-Real.pi) Real.pi, isOpen_Ioo⟩
    -- Keep the manifold instance aligned with the canonical charted-space owner above.
    change IsManifold (𝓘(ℝ)) (⊤ : WithTop ℕ∞) U
    infer_instance

/-- Helper for Problem 5-15: the shifted parameter interval `(0, 2π)` carries its usual
one-chart smooth structure. -/
instance : Nonempty (Set.Ioo (0 : ℝ) (2 * Real.pi)) :=
  ⟨⟨Real.pi, by
    constructor
    · exact Real.pi_pos
    · linarith [Real.pi_pos]⟩⟩

/-- Helper for Problem 5-15: the shifted parameter interval `(0, 2π)` carries its usual
one-chart smooth structure. -/
noncomputable instance : ChartedSpace ℝ (Set.Ioo (0 : ℝ) (2 * Real.pi)) :=
  by
    let U : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (0 : ℝ) (2 * Real.pi), isOpen_Ioo⟩
    -- Use the canonical open-subtype owner so the shifted restriction matches `of_opens`.
    change ChartedSpace ℝ U
    infer_instance

/-- Helper for Problem 5-15: the shifted parameter interval `(0, 2π)` is a smooth `1`-manifold. -/
instance : IsManifold (𝓘(ℝ)) (⊤ : WithTop ℕ∞) (Set.Ioo (0 : ℝ) (2 * Real.pi)) :=
  by
    let U : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (0 : ℝ) (2 * Real.pi), isOpen_Ioo⟩
    -- Keep the shifted manifold instance synchronized with the canonical open-subtype charts.
    change IsManifold (𝓘(ℝ)) (⊤ : WithTop ℕ∞) U
    infer_instance

/-- Helper for Problem 5-15: the standard parameter interval includes into `ℝ` as a smooth
immersion. -/
lemma figure_eight_standard_parameter_interval_subtype_val_isImmersion :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
      (Subtype.val : Set.Ioo (-Real.pi) Real.pi → ℝ) := by
  let U : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (-Real.pi) Real.pi, isOpen_Ioo⟩
  -- The standard cut now uses the same canonical open-subtype owner as the shifted cut.
  change IsImmersion 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞) (Subtype.val : U → ℝ)
  simpa [U] using Manifold.IsImmersion.of_opens (I := 𝓘(ℝ)) (n := (⊤ : WithTop ℕ∞)) U

/-- Helper for Problem 5-15: the shifted parameter interval includes into `ℝ` as a smooth
immersion. -/
lemma figure_eight_shifted_parameter_interval_subtype_val_isImmersion :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
      (Subtype.val : Set.Ioo (0 : ℝ) (2 * Real.pi) → ℝ) := by
  let U : TopologicalSpace.Opens ℝ := ⟨Set.Ioo (0 : ℝ) (2 * Real.pi), isOpen_Ioo⟩
  -- After switching to the canonical open-subtype charted-space owner, `of_opens` applies
  -- directly to the shifted interval inclusion.
  change IsImmersion 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞) (Subtype.val : U → ℝ)
  simpa [U] using Manifold.IsImmersion.of_opens (I := 𝓘(ℝ)) (n := (⊤ : WithTop ℕ∞)) U

/-- Helper for Problem 5-15: differentiating the ambient figure-eight curve gives the explicit
velocity vector `(2 cos (2t), cos t)`. -/
lemma figure_eight_curveMap_fderiv_apply_one (t : ℝ) :
    fderiv ℝ figureEightCurveMap t 1 = (2 * Real.cos (2 * t), Real.cos t) := by
  -- Differentiate the two coordinates separately and then reassemble the product map.
  have hfst' : HasDerivAt (fun x : ℝ ↦ Real.sin (x * 2)) (2 * Real.cos (2 * t)) t := by
    simpa [two_mul, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_sin (t * 2)).comp t (hasDerivAt_mul_const (2 : ℝ))
  have hfst : HasDerivAt (fun x : ℝ ↦ Real.sin (2 * x)) (2 * Real.cos (2 * t)) t := by
    simpa [mul_comm] using hfst'
  have hsnd : HasDerivAt (fun x : ℝ ↦ Real.sin x) (Real.cos t) t := by
    simpa using Real.hasDerivAt_sin t
  have hcurve : HasDerivAt figureEightCurveMap (2 * Real.cos (2 * t), Real.cos t) t := by
    -- The product derivative is the pair of the coordinate derivatives.
    simpa [figureEightCurveMap] using hfst.prodMk hsnd
  -- Applying the Fréchet derivative to `1` recovers the one-variable derivative.
  simpa using DFunLike.congr_fun hcurve.hasFDerivAt.fderiv 1

/-- Helper for Problem 5-15: the ambient figure-eight derivative never vanishes. -/
lemma figure_eight_curveMap_fderiv_ne_zero (t : ℝ) :
    fderiv ℝ figureEightCurveMap t ≠ 0 := by
  -- Evaluate the derivative on `1` and show the resulting velocity vector cannot be zero.
  intro hzero
  have hvec :
      (2 * Real.cos (2 * t), Real.cos t) = 0 := by
    rw [← figure_eight_curveMap_fderiv_apply_one t]
    simpa using DFunLike.congr_fun hzero 1
  have hcos : Real.cos t = 0 := by
    simpa using congrArg Prod.snd hvec
  have hcos2 : Real.cos (2 * t) = -1 := by
    rw [Real.cos_two_mul, hcos]
    ring
  have hfst : 2 * Real.cos (2 * t) = 0 := by
    simpa using congrArg Prod.fst hvec
  linarith

/-- Helper for Problem 5-15: a nonzero continuous linear map out of `ℝ` is injective. -/
lemma continuous_linearMap_injective_from_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ →L[ℝ] E} (hL : L ≠ 0) :
    Function.Injective L := by
  -- The source is one-dimensional, so a nonzero linear map out of `ℝ` has trivial kernel.
  exact LinearMap.injective_of_ne_zero (f := L.toLinearMap) <| by
    intro hzero
    exact hL <| ContinuousLinearMap.ext fun x ↦ DFunLike.congr_fun hzero x

/-- Helper for Problem 5-15: the manifold derivative of the ambient figure-eight map is injective
at every real parameter because its Fréchet derivative never vanishes. -/
lemma figure_eight_curveMap_mfderiv_injective_real (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) figureEightCurveMap t) := by
  -- Reinterpret the manifold derivative on Euclidean space as the usual derivative.
  have hNonzero : mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) figureEightCurveMap t ≠ 0 := by
    rw [mfderiv_eq_fderiv]
    exact figure_eight_curveMap_fderiv_ne_zero t
  -- In one real dimension, every nonzero continuous linear map is injective.
  exact continuous_linearMap_injective_from_real (E := Plane) hNonzero

/-- Helper for Problem 5-15: the ambient figure-eight map should be turned into an immersion using
the derivative criterion and `figure_eight_curveMap_fderiv_ne_zero`. -/
lemma figure_eight_curveMap_isImmersion :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) figureEightCurveMap := by
  exact figureEightCurveMap_isImmersion_top

/-- Helper for Problem 5-15: the original figure-eight cut `(-π, π)` inherits immersion from the
ambient figure-eight map. -/
lemma figure_eight_standard_isImmersion :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) figureEightCurve := by
  exact figureEightCurve_isImmersion_top

/-- Helper for Problem 5-15: shifting the parameter by `2π` leaves the ambient figure-eight point
unchanged. -/
lemma figure_eight_curveMap_add_two_pi (t : ℝ) :
    figureEightCurveMap (t + 2 * Real.pi) = figureEightCurveMap t := by
  -- Each coordinate is `2π`-periodic.
  ext
  · have harg : 2 * (t + 2 * Real.pi) = 2 * t + 2 * (2 * Real.pi) := by
      ring
    rw [figureEightCurveMap, figureEightCurveMap, harg]
    simpa using Real.sin_add_nat_mul_two_pi (2 * t) 2
  · rw [figureEightCurveMap, figureEightCurveMap]
    rw [Real.sin_add_two_pi]

/-- Helper for Problem 5-15: subtracting `2π` from the parameter also preserves the ambient
figure-eight point. -/
lemma figure_eight_curveMap_sub_two_pi (t : ℝ) :
    figureEightCurveMap (t - 2 * Real.pi) = figureEightCurveMap t := by
  -- Rewrite subtraction as addition by `-2π` and use the previous periodicity lemma.
  have h := figure_eight_curveMap_add_two_pi (t - 2 * Real.pi)
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h.symm

/-- Helper for Problem 5-15: the standard parameter value `0` lies in `(-π, π)`. -/
lemma zero_mem_standard_parameter_interval :
    (0 : ℝ) ∈ Set.Ioo (-Real.pi) Real.pi := by
  -- This is the distinguished branch-point parameter on the standard cut.
  constructor
  · simpa using neg_lt_zero.mpr Real.pi_pos
  · simpa using Real.pi_pos

/-- Helper for Problem 5-15: the shifted parameter cut `(0, 2π)` has the same image as the
original cut `(-π, π)`. -/
lemma figure_eight_shifted_range_eq :
    Set.range figureEightShiftedCurve = Set.range figureEightCurve := by
  -- Compare the two parameter intervals by moving negative parameters by `+2π` and the branch
  -- point `0` to `π`.
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    by_cases ht_lt : (t : ℝ) < Real.pi
    · -- Parameters below `π` already lie in the standard interval.
      refine ⟨⟨t, ?_⟩, ?_⟩
      · constructor
        · linarith [t.2.1, Real.pi_pos]
        · exact ht_lt
      · rfl
    · have ht_ge : Real.pi ≤ (t : ℝ) := le_of_not_gt ht_lt
      by_cases ht_eq : (t : ℝ) = Real.pi
      · -- The branch point at `π` matches the standard parameter `0`.
        refine ⟨⟨0, zero_mem_standard_parameter_interval⟩, ?_⟩
        rw [show figureEightShiftedCurve t = figureEightCurveMap Real.pi by
          simp [figureEightShiftedCurve, ht_eq]]
        simp [figureEightCurve, figureEightCurveMap, Real.sin_pi, Real.sin_two_pi]
      · -- Parameters above `π` move back by `2π` into `(-π, 0)`.
        refine ⟨⟨(t : ℝ) - 2 * Real.pi, ?_⟩, ?_⟩
        · constructor
          · have ht_gt : Real.pi < (t : ℝ) := lt_of_le_of_ne ht_ge (Ne.symm ht_eq)
            linarith
          · linarith [t.2.2]
        · simpa [figureEightShiftedCurve, figureEightCurve] using
            figure_eight_curveMap_sub_two_pi (t : ℝ)
  · rintro ⟨t, rfl⟩
    by_cases ht_pos : (0 : ℝ) < t
    · -- Positive standard parameters are already shifted parameters.
      refine ⟨⟨t, ?_⟩, ?_⟩
      · constructor
        · exact ht_pos
        · linarith [t.2.2]
      · exact figureEightCurve_eq_figureEightCurveMap t
    · have ht_le : (t : ℝ) ≤ 0 := le_of_not_gt ht_pos
      by_cases ht_zero : (t : ℝ) = 0
      · -- The standard parameter `0` becomes the shifted parameter `π`.
        refine ⟨⟨Real.pi, by
          constructor
          · exact Real.pi_pos
          · linarith [Real.pi_pos]⟩, ?_⟩
        simp [figureEightShiftedCurve, figureEightCurve, figureEightCurveMap, ht_zero,
          Real.sin_pi, Real.sin_two_pi]
      · -- Negative standard parameters move forward by `2π` into `(π, 2π)`.
        refine ⟨⟨(t : ℝ) + 2 * Real.pi, ?_⟩, ?_⟩
        · constructor
          · linarith [t.2.1]
          · have ht_neg : (t : ℝ) < 0 := lt_of_le_of_ne ht_le ht_zero
            linarith
        · simpa [figureEightShiftedCurve, figureEightCurve] using
            figure_eight_curveMap_add_two_pi (t : ℝ)

/-- Helper for Problem 5-15: the shifted figure-eight cut is still a smooth immersion. -/
lemma figure_eight_shifted_isImmersion :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) figureEightShiftedCurve := by
  -- This is the restriction of the ambient immersion to the shifted open parameter interval.
  simpa [figureEightShiftedCurve, Function.comp] using
    Manifold.IsImmersion.comp figure_eight_curveMap_isImmersion
      figure_eight_shifted_parameter_interval_subtype_val_isImmersion

/-- Helper for Problem 5-15: parameters below `π` already lie in the standard cut `(-π, π)`. -/
lemma shifted_to_standard_parameter_mem_of_lt_pi
    (t : ShiftedFigureEightInterval) (ht_lt : (t : ℝ) < Real.pi) :
    (t : ℝ) ∈ StandardFigureEightInterval := by
  -- The shifted interval starts positive, so only the upper bound needs the branch assumption.
  constructor
  · linarith [t.2.1, Real.pi_pos]
  · exact ht_lt

/-- Helper for Problem 5-15: parameters above `π` move back by `2π` into the standard cut. -/
lemma shifted_to_standard_parameter_mem_of_pi_lt
    (t : ShiftedFigureEightInterval) (ht_gt : Real.pi < (t : ℝ)) :
    (t : ℝ) - 2 * Real.pi ∈ StandardFigureEightInterval := by
  -- Subtracting the period lands in `(-π, 0)`.
  constructor
  · linarith
  · linarith [t.2.2]

/-- Helper for Problem 5-15: each shifted parameter has a canonical representative in the standard
cut `(-π, π)`. -/
noncomputable def shifted_to_standard_parameter (t : ShiftedFigureEightInterval) :
    StandardFigureEightInterval :=
  if ht_lt : (t : ℝ) < Real.pi then
    ⟨t, shifted_to_standard_parameter_mem_of_lt_pi t ht_lt⟩
  else if ht_eq : (t : ℝ) = Real.pi then
    ⟨0, zero_mem_standard_parameter_interval⟩
  else
    ⟨(t : ℝ) - 2 * Real.pi,
      shifted_to_standard_parameter_mem_of_pi_lt t
        (lt_of_le_of_ne (le_of_not_gt ht_lt) (Ne.symm ht_eq))⟩

/-- Helper for Problem 5-15: on the lower branch, the canonical representative is the parameter
itself. -/
lemma shifted_to_standard_parameter_of_lt_pi
    (t : ShiftedFigureEightInterval) (ht_lt : (t : ℝ) < Real.pi) :
    shifted_to_standard_parameter t =
      ⟨t, shifted_to_standard_parameter_mem_of_lt_pi t ht_lt⟩ := by
  -- The `t < π` branch of the definition applies directly.
  simp [shifted_to_standard_parameter, ht_lt]

/-- Helper for Problem 5-15: the branch point `π` corresponds to the standard parameter `0`. -/
lemma shifted_to_standard_parameter_of_eq_pi
    (t : ShiftedFigureEightInterval) (ht_eq : (t : ℝ) = Real.pi) :
    shifted_to_standard_parameter t = ⟨0, zero_mem_standard_parameter_interval⟩ := by
  -- The middle branch handles the double point.
  simp [shifted_to_standard_parameter, ht_eq]

/-- Helper for Problem 5-15: on the upper branch, the canonical representative is `t - 2π`. -/
lemma shifted_to_standard_parameter_of_pi_lt
    (t : ShiftedFigureEightInterval) (ht_gt : Real.pi < (t : ℝ)) :
    shifted_to_standard_parameter t =
      ⟨(t : ℝ) - 2 * Real.pi, shifted_to_standard_parameter_mem_of_pi_lt t ht_gt⟩ := by
  have hnot_lt : ¬ (t : ℝ) < Real.pi := not_lt.mpr (le_of_lt ht_gt)
  have hnot_eq : ¬ (t : ℝ) = Real.pi := ne_of_gt ht_gt
  -- Only the translated upper branch survives once the side conditions are fixed.
  apply Subtype.ext
  simp [shifted_to_standard_parameter, hnot_lt, hnot_eq]

/-- Helper for Problem 5-15: the shifted and standard representatives determine the same point of
the figure-eight image. -/
lemma figure_eight_shifted_eq_standard_parameterized (t : ShiftedFigureEightInterval) :
    figureEightCurve (shifted_to_standard_parameter t) = figureEightShiftedCurve t := by
  by_cases ht_lt : (t : ℝ) < Real.pi
  · -- On the lower branch, the canonical representative is the same real parameter.
    rw [shifted_to_standard_parameter_of_lt_pi t ht_lt]
    rfl
  · have ht_ge : Real.pi ≤ (t : ℝ) := le_of_not_gt ht_lt
    by_cases ht_eq : (t : ℝ) = Real.pi
    · -- At the double point, both parameter cuts hit the same ambient point.
      rw [shifted_to_standard_parameter_of_eq_pi t ht_eq]
      simp [figureEightCurve, figureEightShiftedCurve, figureEightCurveMap, ht_eq, Real.sin_pi,
        Real.sin_two_pi]
    · have ht_gt : Real.pi < (t : ℝ) := lt_of_le_of_ne ht_ge (Ne.symm ht_eq)
      -- On the upper branch, subtract `2π` and use periodicity of the ambient curve.
      rw [shifted_to_standard_parameter_of_pi_lt t ht_gt]
      simpa [figureEightCurve, figureEightShiftedCurve] using
        figure_eight_curveMap_sub_two_pi (t : ℝ)

/-- Helper for Problem 5-15: the canonical standard representative distinguishes shifted
parameters. -/
lemma shifted_to_standard_parameter_injective :
    Function.Injective shifted_to_standard_parameter := by
  intro t₁ t₂ h
  have hval :
      ((shifted_to_standard_parameter t₁ : StandardFigureEightInterval) : ℝ) =
        ((shifted_to_standard_parameter t₂ : StandardFigureEightInterval) : ℝ) :=
    congrArg Subtype.val h
  by_cases ht₁_lt : (t₁ : ℝ) < Real.pi
  · by_cases ht₂_lt : (t₂ : ℝ) < Real.pi
    · -- Both parameters lie on the lower branch, so the representatives are the parameters.
      apply Subtype.ext
      have hreal : (t₁ : ℝ) = (t₂ : ℝ) := by
        simpa [shifted_to_standard_parameter_of_lt_pi, ht₁_lt, ht₂_lt] using hval
      exact hreal
    · have ht₂_ge : Real.pi ≤ (t₂ : ℝ) := le_of_not_gt ht₂_lt
      by_cases ht₂_eq : (t₂ : ℝ) = Real.pi
      · -- The lower branch lands in `(0, π)`, so it cannot equal the branch-point value `0`.
        have hzero :
            ((shifted_to_standard_parameter t₁ : StandardFigureEightInterval) : ℝ) = 0 := by
          simpa [shifted_to_standard_parameter_of_eq_pi, ht₂_eq] using hval
        have ht₁_pos : 0 < (t₁ : ℝ) := t₁.2.1
        have : ¬ (t₁ : ℝ) = 0 := ne_of_gt ht₁_pos
        exact (this <| by simpa [shifted_to_standard_parameter_of_lt_pi, ht₁_lt] using hzero).elim
      · have ht₂_gt : Real.pi < (t₂ : ℝ) := lt_of_le_of_ne ht₂_ge (Ne.symm ht₂_eq)
        -- Lower-branch representatives are positive, upper-branch representatives are negative.
        have hneg : ((shifted_to_standard_parameter t₂ : StandardFigureEightInterval) : ℝ) < 0 := by
          have hfrac : (t₂ : ℝ) - 2 * Real.pi < 0 := by linarith [t₂.2.2]
          simpa [shifted_to_standard_parameter_of_pi_lt, ht₂_gt] using hfrac
        have hpos : 0 < ((shifted_to_standard_parameter t₁ : StandardFigureEightInterval) : ℝ) := by
          simpa [shifted_to_standard_parameter_of_lt_pi, ht₁_lt] using t₁.2.1
        linarith
  · have ht₁_ge : Real.pi ≤ (t₁ : ℝ) := le_of_not_gt ht₁_lt
    by_cases ht₁_eq : (t₁ : ℝ) = Real.pi
    · by_cases ht₂_lt : (t₂ : ℝ) < Real.pi
      · -- Symmetric contradiction with the previous lower-vs-branch-point case.
        have hzero :
            ((shifted_to_standard_parameter t₂ : StandardFigureEightInterval) : ℝ) = 0 := by
          simpa [shifted_to_standard_parameter_of_eq_pi, ht₁_eq] using hval.symm
        have ht₂_pos : 0 < (t₂ : ℝ) := t₂.2.1
        have : ¬ (t₂ : ℝ) = 0 := ne_of_gt ht₂_pos
        exact (this <| by simpa [shifted_to_standard_parameter_of_lt_pi, ht₂_lt] using hzero).elim
      · have ht₂_ge : Real.pi ≤ (t₂ : ℝ) := le_of_not_gt ht₂_lt
        by_cases ht₂_eq : (t₂ : ℝ) = Real.pi
        · apply Subtype.ext
          simp [ht₁_eq, ht₂_eq]
        · have ht₂_gt : Real.pi < (t₂ : ℝ) := lt_of_le_of_ne ht₂_ge (Ne.symm ht₂_eq)
          -- The branch-point representative is `0`, but the upper branch gives a negative value.
          have hneg :
              ((shifted_to_standard_parameter t₂ : StandardFigureEightInterval) : ℝ) < 0 := by
            have hfrac : (t₂ : ℝ) - 2 * Real.pi < 0 := by linarith [t₂.2.2]
            simpa [shifted_to_standard_parameter_of_pi_lt, ht₂_gt] using hfrac
          have hzero :
              ((shifted_to_standard_parameter t₂ : StandardFigureEightInterval) : ℝ) = 0 := by
            simpa [shifted_to_standard_parameter_of_eq_pi, ht₁_eq] using hval.symm
          linarith
    · have ht₁_gt : Real.pi < (t₁ : ℝ) := lt_of_le_of_ne ht₁_ge (Ne.symm ht₁_eq)
      by_cases ht₂_lt : (t₂ : ℝ) < Real.pi
      · -- Upper-branch representatives are negative, lower-branch representatives are positive.
        have hneg : ((shifted_to_standard_parameter t₁ : StandardFigureEightInterval) : ℝ) < 0 := by
          have hfrac : (t₁ : ℝ) - 2 * Real.pi < 0 := by linarith [t₁.2.2]
          simpa [shifted_to_standard_parameter_of_pi_lt, ht₁_gt] using hfrac
        have hpos : 0 < ((shifted_to_standard_parameter t₂ : StandardFigureEightInterval) : ℝ) := by
          simpa [shifted_to_standard_parameter_of_lt_pi, ht₂_lt] using t₂.2.1
        linarith
      · have ht₂_ge : Real.pi ≤ (t₂ : ℝ) := le_of_not_gt ht₂_lt
        by_cases ht₂_eq : (t₂ : ℝ) = Real.pi
        · -- Symmetric contradiction with the previous upper-vs-branch-point case.
          have hneg :
              ((shifted_to_standard_parameter t₁ : StandardFigureEightInterval) : ℝ) < 0 := by
            have hfrac : (t₁ : ℝ) - 2 * Real.pi < 0 := by linarith [t₁.2.2]
            simpa [shifted_to_standard_parameter_of_pi_lt, ht₁_gt] using hfrac
          have hzero :
              ((shifted_to_standard_parameter t₁ : StandardFigureEightInterval) : ℝ) = 0 := by
            simpa [shifted_to_standard_parameter_of_eq_pi, ht₂_eq] using hval
          linarith
        · have ht₂_gt : Real.pi < (t₂ : ℝ) := lt_of_le_of_ne ht₂_ge (Ne.symm ht₂_eq)
          -- Both parameters lie on the translated upper branch, so add back `2π`.
          apply Subtype.ext
          have hreal : (t₁ : ℝ) - 2 * Real.pi = (t₂ : ℝ) - 2 * Real.pi := by
            simpa [shifted_to_standard_parameter_of_pi_lt, ht₁_gt, ht₂_gt] using hval
          linarith

/-- Helper for Problem 5-15: the shifted cut is injective because its canonical standard
representatives are injective and preserve the image point. -/
lemma figure_eight_shifted_injective : Function.Injective figureEightShiftedCurve := by
  intro t₁ t₂ h
  have hstd :
      figureEightCurve (shifted_to_standard_parameter t₁) =
        figureEightCurve (shifted_to_standard_parameter t₂) := by
    calc
      figureEightCurve (shifted_to_standard_parameter t₁) = figureEightShiftedCurve t₁ :=
        figure_eight_shifted_eq_standard_parameterized t₁
      _ = figureEightShiftedCurve t₂ := h
      _ = figureEightCurve (shifted_to_standard_parameter t₂) :=
        (figure_eight_shifted_eq_standard_parameterized t₂).symm
  -- Reduce injectivity to the standard cut and then recover the original shifted parameters.
  exact shifted_to_standard_parameter_injective (figureEightCurve_injective hstd)

/-- Helper for Problem 5-15: the standard cut identifies the interval with the common figure-eight
image. -/
noncomputable abbrev figure_eight_standard_equiv :
    StandardFigureEightInterval ≃ FigureEightImage :=
  Equiv.ofBijective
    (fun t ↦ ⟨figureEightCurve t, ⟨t, rfl⟩⟩)
    ⟨by
        intro t₁ t₂ h
        exact figureEightCurve_injective (congrArg Subtype.val h)
      , by
        intro x
        rcases x with ⟨p, hp⟩
        rcases hp with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        exact Subtype.ext ht⟩

/-- Helper for Problem 5-15: the shifted cut also identifies its interval with the same figure-eight
image. -/
noncomputable abbrev figure_eight_shifted_equiv :
    ShiftedFigureEightInterval ≃ FigureEightImage :=
  Equiv.ofBijective
    (fun t ↦ ⟨figureEightShiftedCurve t, by
      have ht : figureEightShiftedCurve t ∈ Set.range figureEightShiftedCurve := ⟨t, rfl⟩
      simpa [figure_eight_shifted_range_eq] using ht⟩)
    ⟨by
        intro t₁ t₂ h
        exact figure_eight_shifted_injective (congrArg Subtype.val h)
      , by
        intro x
        have hx : x.1 ∈ Set.range figureEightShiftedCurve := by
          have hx' : x.1 ∈ Set.range figureEightCurve := x.2
          exact figure_eight_shifted_range_eq.symm ▸ hx'
        rcases hx with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        exact Subtype.ext ht⟩

/-- Helper for Problem 5-15: the standard transported topology on the common image is the one that
makes the inverse standard coordinate map continuous by definition. -/
noncomputable abbrev figure_eight_standard_topology : TopologicalSpace FigureEightImage :=
  figure_eight_standard_equiv.symm.topologicalSpace

/-- Helper for Problem 5-15: the shifted transported topology on the common image is the one that
makes the inverse shifted coordinate map continuous by definition. -/
noncomputable abbrev figure_eight_shifted_topology : TopologicalSpace FigureEightImage :=
  figure_eight_shifted_equiv.symm.topologicalSpace

/-- Helper for Problem 5-15: composing the shifted coordinate map with the standard inverse
coordinate map is exactly the branch-switch parameter map. -/
lemma figure_eight_standard_inverse_comp_shifted_eq :
    (figure_eight_standard_equiv.symm ∘ figure_eight_shifted_equiv) =
      shifted_to_standard_parameter := by
  funext t
  apply figureEightCurve_injective
  -- Both standard parameters map to the same point of the common figure-eight image.
  have hEq :
      figure_eight_standard_equiv
          (figure_eight_standard_equiv.symm (figure_eight_shifted_equiv t)) =
        figure_eight_shifted_equiv t :=
    Equiv.apply_symm_apply figure_eight_standard_equiv (figure_eight_shifted_equiv t)
  calc
    figureEightCurve (figure_eight_standard_equiv.symm (figure_eight_shifted_equiv t))
        = figureEightShiftedCurve t := congrArg Subtype.val hEq
    _ = figureEightCurve (shifted_to_standard_parameter t) :=
      (figure_eight_shifted_eq_standard_parameterized t).symm

/-- Helper for Problem 5-15: the standard transported topology carries an immersed-curve
structure on the common figure-eight image. -/
lemma figure_eight_standard_isImmersedCurveWithTopology :
    Set.IsImmersedCurveWithTopology FigureEightImage figure_eight_standard_topology := by
  let _ : TopologicalSpace FigureEightImage := figure_eight_standard_topology
  -- Transport the standard interval structure to the common image through its coordinate map.
  simpa [figure_eight_standard_topology] using
    transported_subset_isImmersedCurveWithTopology figure_eight_standard_isImmersion
      ((figure_eight_standard_equiv.symm.homeomorph).symm) (fun t ↦ rfl)

/-- Helper for Problem 5-15: the shifted transported topology carries an immersed-curve structure
on the same figure-eight image. -/
lemma figure_eight_shifted_isImmersedCurveWithTopology :
    Set.IsImmersedCurveWithTopology FigureEightImage figure_eight_shifted_topology := by
  let _ : TopologicalSpace FigureEightImage := figure_eight_shifted_topology
  -- Transport the shifted interval structure to the same image through its shifted coordinate map.
  simpa [figure_eight_shifted_topology] using
    transported_subset_isImmersedCurveWithTopology figure_eight_shifted_isImmersion
      ((figure_eight_shifted_equiv.symm.homeomorph).symm) (fun t ↦ rfl)

/-- Helper for Problem 5-15: the sequence `π - 1 / (n + 1)` stays inside the shifted cut
`(0, 2π)`. -/
lemma figure_eight_shifted_approach_pi_mem_interval (n : ℕ) :
    Real.pi - 1 / (n + 1 : ℝ) ∈ ShiftedFigureEightInterval := by
  have hfrac_pos : 0 < 1 / (n + 1 : ℝ) := by
    have hden_pos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    exact one_div_pos.mpr hden_pos
  have hfrac_le_one : 1 / (n + 1 : ℝ) ≤ 1 := by
    simpa [one_div] using (Nat.cast_inv_le_one (α := ℝ) (n + 1))
  have hone_lt_pi : (1 : ℝ) < Real.pi := by
    linarith [Real.pi_gt_three]
  have hpi_lt_two_pi : Real.pi < 2 * Real.pi := by
    linarith [Real.pi_pos]
  -- The lower bound uses `1 / (n + 1) ≤ 1 < π`, and the upper bound is automatic since
  -- `π - 1 / (n + 1) < π < 2π`.
  constructor
  · linarith
  · linarith

/-- Helper for Problem 5-15: along the sequence approaching `π` from below, the branch-switch map
keeps the same real parameter because only the lower branch of the definition is active. -/
lemma shifted_to_standard_parameter_approach_pi_val (n : ℕ) :
    (((shifted_to_standard_parameter
        ⟨Real.pi - 1 / (n + 1 : ℝ), figure_eight_shifted_approach_pi_mem_interval n⟩ :
          StandardFigureEightInterval) : ℝ)) =
      Real.pi - 1 / (n + 1 : ℝ) := by
  have hu_lt : Real.pi - 1 / (n + 1 : ℝ) < Real.pi := by
    have hpos : 0 < (1 : ℝ) / (n + 1 : ℝ) := by
      have hden_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact one_div_pos.mpr hden_pos
    -- Subtracting a positive amount from `π` moves the sequence strictly below `π`.
    linarith
  let u : ShiftedFigureEightInterval :=
    ⟨Real.pi - 1 / (n + 1 : ℝ), figure_eight_shifted_approach_pi_mem_interval n⟩
  -- The lower-branch formula identifies the canonical representative with the original value.
  simpa [u] using congrArg Subtype.val (shifted_to_standard_parameter_of_lt_pi u hu_lt)

/-- Helper for Problem 5-15: the shifted branch-switch map to the standard parameter interval is
not continuous at the double-point parameter `π`. -/
lemma shifted_to_standard_parameter_val_not_continuousAt_pi :
    let tπ : ShiftedFigureEightInterval :=
      ⟨Real.pi, by
        constructor
        · exact Real.pi_pos
        · linarith [Real.pi_pos]⟩
    ¬ ContinuousAt
      (fun t : ShiftedFigureEightInterval ↦
        ((shifted_to_standard_parameter t : StandardFigureEightInterval) : ℝ))
      tπ := by
  dsimp
  let tπ : ShiftedFigureEightInterval :=
    ⟨Real.pi, by
      constructor
      · exact Real.pi_pos
      · linarith [Real.pi_pos]⟩
  change ¬ ContinuousAt
      (fun t : ShiftedFigureEightInterval ↦
        ((shifted_to_standard_parameter t : StandardFigureEightInterval) : ℝ))
      tπ
  intro hcont
  let u : ℕ → ShiftedFigureEightInterval := fun n ↦
    ⟨Real.pi - 1 / (n + 1 : ℝ), figure_eight_shifted_approach_pi_mem_interval n⟩
  have hu_tendsto_real :
      Filter.Tendsto (fun n ↦ ((u n : ShiftedFigureEightInterval) : ℝ))
        Filter.atTop (nhds Real.pi) := by
    have hdiv :
        Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1 : ℝ))
          Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    -- The shifted sequence approaches the branch point `π` from below.
    simpa [u] using (Filter.Tendsto.sub tendsto_const_nhds hdiv)
  have hu_tendsto :
      Filter.Tendsto u Filter.atTop (nhds tπ) := by
    exact (tendsto_subtype_rng (x := tπ)).2 (by simpa [u, tπ] using hu_tendsto_real)
  have hvalue_tendsto :
      Filter.Tendsto
        (fun n ↦
          (((shifted_to_standard_parameter (u n) : StandardFigureEightInterval) : ℝ)))
        Filter.atTop
        (nhds ((((shifted_to_standard_parameter tπ : StandardFigureEightInterval) : ℝ)))) :=
    hcont.tendsto.comp hu_tendsto
  have hat_pi_val :
      ((((shifted_to_standard_parameter tπ : StandardFigureEightInterval) : ℝ))) = 0 := by
    -- At the shifted double point `π`, the standard representative is the branch-point `0`.
    simpa [tπ] using
      congrArg Subtype.val (shifted_to_standard_parameter_of_eq_pi tπ rfl)
  have hvalue_zero_tendsto :
      Filter.Tendsto
        (fun n ↦
          (((shifted_to_standard_parameter (u n) : StandardFigureEightInterval) : ℝ)))
        Filter.atTop
        (nhds 0) := by
    rw [hat_pi_val] at hvalue_tendsto
    exact hvalue_tendsto
  have hu_eq :
      (fun n : ℕ ↦
        (((shifted_to_standard_parameter (u n) : StandardFigureEightInterval) : ℝ))) =
          fun n : ℕ ↦ Real.pi - 1 / (n + 1 : ℝ) := by
    funext n
    -- Along the approaching sequence, the lower branch of the definition is active.
    simpa [u] using shifted_to_standard_parameter_approach_pi_val n
  have hu_zero_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ Real.pi - 1 / (n + 1 : ℝ))
        Filter.atTop (nhds 0) := by
    rw [← hu_eq]
    exact hvalue_zero_tendsto
  have hpi_eq_zero : Real.pi = 0 := tendsto_nhds_unique hu_tendsto_real hu_zero_tendsto
  -- The sequence also converges to `π`, so uniqueness of limits forces the contradiction.
  linarith [Real.pi_pos, hpi_eq_zero]

/-- Helper for Problem 5-15: the two explicit transported topologies on the common image differ. -/
lemma shifted_to_standard_parameter_continuous_of_topology_eq
    (h : figure_eight_standard_topology = figure_eight_shifted_topology) :
    Continuous shifted_to_standard_parameter := by
  let _ : TopologicalSpace FigureEightImage := figure_eight_shifted_topology
  have hshift :
      Continuous (figure_eight_shifted_equiv : ShiftedFigureEightInterval → FigureEightImage) := by
    -- The shifted coordinate map is a homeomorphism by construction of the transported topology.
    simpa using ((figure_eight_shifted_equiv.symm.homeomorph).symm.continuous_toFun)
  have hstd' :
      @Continuous FigureEightImage StandardFigureEightInterval figure_eight_standard_topology
        instTopologicalSpaceSubtype (figure_eight_standard_equiv.symm) := by
    -- The standard inverse coordinate map is continuous by definition of the transported
    -- standard topology.
    let _ : TopologicalSpace FigureEightImage := figure_eight_standard_topology
    exact figure_eight_standard_equiv.symm.homeomorph.continuous_toFun
  have hstd :
      @Continuous FigureEightImage StandardFigureEightInterval figure_eight_shifted_topology
        instTopologicalSpaceSubtype (figure_eight_standard_equiv.symm) := by
    rwa [← h]
  -- The branch-switch map is the composition of the shifted coordinate map with the standard
  -- inverse coordinate map once the two transported topologies are identified.
  have hcomp :
      Continuous (figure_eight_standard_equiv.symm ∘ figure_eight_shifted_equiv) :=
    hstd.comp hshift
  exact figure_eight_standard_inverse_comp_shifted_eq ▸ hcomp

/-- Helper for Problem 5-15: the two explicit transported topologies on the common image differ. -/
lemma figure_eight_standard_vs_shifted_topology_ne :
    figure_eight_standard_topology ≠ figure_eight_shifted_topology := by
  intro htop
  have hcont :
      Continuous
        (fun t : ShiftedFigureEightInterval ↦
          ((shifted_to_standard_parameter t : StandardFigureEightInterval) : ℝ)) := by
    -- Under the assumed topology equality, the branch-switch map would become continuous, and so
    -- would its real-valued coordinate.
    exact continuous_subtype_val.comp
      (shifted_to_standard_parameter_continuous_of_topology_eq htop)
  have hAt :
      let tπ : ShiftedFigureEightInterval :=
        ⟨Real.pi, by
          constructor
          · exact Real.pi_pos
          · linarith [Real.pi_pos]⟩
      ContinuousAt
        (fun t : ShiftedFigureEightInterval ↦
          ((shifted_to_standard_parameter t : StandardFigureEightInterval) : ℝ))
        tπ := by
    -- Continuity of a map implies continuity at the shifted branch-point parameter `π`.
    dsimp
    exact hcont.continuousAt
  exact shifted_to_standard_parameter_val_not_continuousAt_pi hAt

/-- Helper for Problem 5-15: the original cut on the figure-eight image yields an immersed-curve
topology. -/
lemma figure_eight_standard_exists_topology :
    ∃ t : TopologicalSpace FigureEightImage,
      Set.IsImmersedCurveWithTopology FigureEightImage t := by
  -- Use the explicitly transported topology from the standard cut.
  exact ⟨figure_eight_standard_topology, figure_eight_standard_isImmersedCurveWithTopology⟩

/-- Helper for Problem 5-15: the shifted cut on the same figure-eight image yields an immersed-curve
topology. -/
lemma figure_eight_shifted_exists_topology :
    ∃ t : TopologicalSpace FigureEightImage,
      Set.IsImmersedCurveWithTopology FigureEightImage t := by
  -- Use the explicitly transported topology from the shifted cut.
  exact ⟨figure_eight_shifted_topology, figure_eight_shifted_isImmersedCurveWithTopology⟩

-- Proof sketch: use a self-intersecting immersed plane curve, such as a figure-eight, and endow
-- its underlying subset with two different manifold topologies obtained by pairing the local
-- branches through the double point in two different ways.
/-- Problem 5-15: There exists a subset of `ℝ²` that carries two distinct topologies, each with a
smooth `1`-manifold structure making the inclusion into `ℝ²` a smooth immersion. -/
theorem exists_subset_with_two_immersed_curve_topologies :
    ∃ S : Set Plane, ∃ t₁ t₂ : TopologicalSpace S,
      t₁ ≠ t₂ ∧
        S.IsImmersedCurveWithTopology t₁ ∧
        S.IsImmersedCurveWithTopology t₂ := by
  -- Use the figure-eight image with the two explicit transported interval topologies.
  refine ⟨FigureEightImage, figure_eight_standard_topology, figure_eight_shifted_topology,
    figure_eight_standard_vs_shifted_topology_ne,
    figure_eight_standard_isImmersedCurveWithTopology,
    figure_eight_shifted_isImmersedCurveWithTopology⟩
