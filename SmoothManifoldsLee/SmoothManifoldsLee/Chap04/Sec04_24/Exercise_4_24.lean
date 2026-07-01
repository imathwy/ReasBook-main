import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Geometry.Manifold.SmoothEmbedding
import SmoothManifoldsLee.Chap01.Sec01.Example_1_3

open Topology
open scoped Manifold ContDiff

-- Declarations for this item will be appended below by the statement pipeline.

/-- The oscillating curve `t ↦ (exp t, sin (exp (-t)))` in `ℝ × ℝ`. -/
noncomputable def oscillatingCurveMap : ℝ → ℝ × ℝ :=
  fun t ↦ (Real.exp t, Real.sin (Real.exp (-t)))

/-- Helper for Exercise 4.24: in Euclidean coordinates the oscillating curve is `C^∞`. -/
lemma oscillatingCurveMap_contDiff : ContDiff ℝ ∞ oscillatingCurveMap := by
  -- The first coordinate is `exp`, while the second is `sin ∘ exp ∘ (-)`.
  simpa [oscillatingCurveMap] using
    (Real.contDiff_exp).prodMk (Real.contDiff_sin.comp (Real.contDiff_exp.comp contDiff_id.neg))

/-- Helper for Exercise 4.24: the Euclidean smoothness statement is the manifold smoothness
statement for the standard models on `ℝ` and `ℝ × ℝ`. -/
lemma oscillatingCurveMap_contMDiff :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ oscillatingCurveMap := by
  -- For the standard models, `ContMDiff` is equivalent to ordinary `ContDiff`.
  rw [contMDiff_iff_contDiff]
  exact oscillatingCurveMap_contDiff

/-- Helper for Exercise 4.24: the oscillating curve is a topological embedding because it is the
graph of `x ↦ sin (1 / x)` over the positive ray, reparametrized by `exp`. -/
lemma oscillatingCurveMap_isEmbedding : IsEmbedding oscillatingCurveMap := by
  have hgraph :
      IsEmbedding (graphMap (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ Real.sin (x⁻¹))) := by
    -- The graph route reduces embedding to continuity of `x ↦ sin (1 / x)` on `(0, ∞)`.
    apply graphMap_isEmbedding
    have hinv : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Set.Ioi (0 : ℝ)) :=
      continuousOn_id.inv₀ fun x hx ↦ ne_of_gt hx
    exact Real.continuous_sin.continuousOn.comp hinv fun _ _ ↦ Set.mem_univ _
  have hexp :
      IsEmbedding (fun t : ℝ ↦ (Real.expOrderIso.toHomeomorph t : Set.Ioi (0 : ℝ))) :=
    Real.expOrderIso.toHomeomorph.isEmbedding
  -- Composing the graph embedding with the exponential homeomorphism gives the curve.
  have hcomp : IsEmbedding (fun t : ℝ ↦ (Real.exp t, Real.sin (1 / Real.exp t))) := by
    simpa [graphMap, Function.comp, one_div] using hgraph.comp hexp
  have hEq : (fun t : ℝ ↦ (Real.exp t, Real.sin (1 / Real.exp t))) = oscillatingCurveMap := by
    funext t
    simp [oscillatingCurveMap, Real.exp_neg, one_div]
  exact hEq ▸ hcomp

/-- Helper for Exercise 4.24: the straightening chart is defined on the open half-plane `x > 0`. -/
def oscillatingHalfPlane : Set (ℝ × ℝ) :=
  { p | 0 < p.1 }

/-- Helper for Exercise 4.24: the half-plane `x > 0` is open. -/
lemma oscillatingHalfPlane_isOpen : IsOpen oscillatingHalfPlane := by
  -- The straightening chart starts on an ordinary open half-plane in `ℝ²`.
  simpa [oscillatingHalfPlane] using isOpen_lt continuous_const continuous_fst

/-- Helper for Exercise 4.24: package the half-plane `x > 0` as an open subset. -/
def oscillatingHalfPlaneOpens : TopologicalSpace.Opens (ℝ × ℝ) :=
  ⟨oscillatingHalfPlane, oscillatingHalfPlane_isOpen⟩

/-- Helper for Exercise 4.24: the half-plane `x > 0` is nonempty. -/
lemma oscillatingHalfPlane_nonempty : Nonempty oscillatingHalfPlaneOpens := by
  -- The point `(1, 0)` lies in the source of the chart.
  refine ⟨⟨(1, 0), ?_⟩⟩
  change (1, 0) ∈ oscillatingHalfPlane
  norm_num [oscillatingHalfPlane]

/-- Helper for Exercise 4.24: the straightening map on the half-plane. -/
noncomputable def oscillatingStraighteningForward : ℝ × ℝ → ℝ × ℝ :=
  fun p ↦ (Real.log p.1, p.2 - Real.sin (1 / p.1))

/-- Helper for Exercise 4.24: the inverse straightening map on the plane. -/
noncomputable def oscillatingStraighteningInverse : ℝ × ℝ → ℝ × ℝ :=
  fun p ↦ (Real.exp p.1, p.2 + Real.sin (Real.exp (-p.1)))

/-- Helper for Exercise 4.24: the inverse straightening map lands in the half-plane. -/
lemma oscillatingStraighteningInverse_mem_halfPlane (p : ℝ × ℝ) :
    oscillatingStraighteningInverse p ∈ oscillatingHalfPlane := by
  -- The inverse has first coordinate `exp`, hence stays in `x > 0`.
  simp [oscillatingStraighteningInverse, oscillatingHalfPlane, Real.exp_pos]

/-- Helper for Exercise 4.24: the explicit inverse cancels the straightening map on the half-plane. -/
lemma oscillatingStraightening_left_inv (p : oscillatingHalfPlaneOpens) :
    oscillatingStraighteningInverse (oscillatingStraighteningForward p.1) = p.1 := by
  -- The first coordinate uses `exp (log x) = x`, and the second coordinate cancels the sine term.
  rcases p with ⟨⟨x, y⟩, hx⟩
  ext <;> dsimp [oscillatingStraighteningForward, oscillatingStraighteningInverse]
  · exact Real.exp_log hx
  · rw [Real.exp_neg, Real.exp_log hx]
    ring_nf

/-- Helper for Exercise 4.24: the straightening map cancels the explicit inverse on the plane. -/
lemma oscillatingStraightening_right_inv (p : ℝ × ℝ) :
    oscillatingStraighteningForward (oscillatingStraighteningInverse p) = p := by
  -- The first coordinate uses `log (exp u) = u`, and the second coordinate cancels the sine term.
  rcases p with ⟨x, y⟩
  ext <;> dsimp [oscillatingStraighteningForward, oscillatingStraighteningInverse]
  · exact Real.log_exp x
  · rw [show 1 / Real.exp x = Real.exp (-x) by simpa [one_div] using (Real.exp_neg x).symm]
    ring_nf

/-- Helper for Exercise 4.24: the straightening map is continuous on the half-plane subtype. -/
lemma oscillatingStraighteningForward_continuous :
    Continuous fun p : oscillatingHalfPlaneOpens ↦ oscillatingStraighteningForward p.1 := by
  -- On the subtype `x > 0`, both `log x` and `1 / x` are ordinary continuous functions.
  have hfst : Continuous fun p : oscillatingHalfPlaneOpens ↦ (p : ℝ × ℝ).1 :=
    continuous_fst.comp continuous_subtype_val
  have hsnd : Continuous fun p : oscillatingHalfPlaneOpens ↦ (p : ℝ × ℝ).2 :=
    continuous_snd.comp continuous_subtype_val
  have hlog : Continuous fun p : oscillatingHalfPlaneOpens ↦ Real.log ((p : ℝ × ℝ).1) :=
    hfst.log fun p ↦ ne_of_gt p.2
  have hinv : Continuous fun p : oscillatingHalfPlaneOpens ↦ ((p : ℝ × ℝ).1)⁻¹ :=
    hfst.inv₀ fun p ↦ ne_of_gt p.2
  have hsin : Continuous fun p : oscillatingHalfPlaneOpens ↦ Real.sin (((p : ℝ × ℝ).1)⁻¹) :=
    Real.continuous_sin.comp hinv
  -- Pair the two continuous coordinate expressions to obtain continuity of the chart map.
  simpa [oscillatingStraighteningForward, one_div] using hlog.prodMk (hsnd.sub hsin)

/-- Helper for Exercise 4.24: the explicit inverse straightening map is continuous. -/
lemma oscillatingStraighteningInverse_continuous :
    Continuous oscillatingStraighteningInverse := by
  -- Every coordinate is built from globally smooth elementary functions.
  have hexp : Continuous fun p : ℝ × ℝ ↦ Real.exp p.1 :=
    Real.continuous_exp.comp continuous_fst
  have hsine : Continuous fun p : ℝ × ℝ ↦ Real.sin (Real.exp (-p.1)) :=
    Real.continuous_sin.comp (Real.continuous_exp.comp (continuous_neg.comp continuous_fst))
  have hsnd : Continuous fun p : ℝ × ℝ ↦ p.2 :=
    continuous_snd
  -- Pair the two coordinate functions to get continuity of the inverse.
  change Continuous (fun p : ℝ × ℝ ↦ (Real.exp p.1, p.2 + Real.sin (Real.exp (-p.1))))
  exact Continuous.prodMk hexp (hsnd.add hsine)

/-- Helper for Exercise 4.24: the straightening homeomorphism between the half-plane and `ℝ²`. -/
noncomputable def oscillatingStraighteningHomeomorph : oscillatingHalfPlaneOpens ≃ₜ (ℝ × ℝ) where
  toEquiv :=
    { toFun := fun p ↦ oscillatingStraighteningForward p.1
      invFun := fun p ↦ ⟨oscillatingStraighteningInverse p,
        oscillatingStraighteningInverse_mem_halfPlane p⟩
      left_inv := fun p ↦ Subtype.ext (oscillatingStraightening_left_inv p)
      right_inv := oscillatingStraightening_right_inv }
  continuous_toFun := oscillatingStraighteningForward_continuous
  continuous_invFun := oscillatingStraighteningInverse_continuous.subtype_mk _

/-- Helper for Exercise 4.24: the explicit straightening chart on the half-plane. -/
noncomputable def oscillatingStraightening : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
  ((oscillatingHalfPlaneOpens.openPartialHomeomorphSubtypeCoe oscillatingHalfPlane_nonempty).symm).trans
    oscillatingStraighteningHomeomorph.toOpenPartialHomeomorph

/-- Helper for Exercise 4.24: the straightening chart has source exactly the half-plane `x > 0`. -/
lemma oscillatingStraightening_source :
    oscillatingStraightening.source = oscillatingHalfPlane := by
  -- The source is inherited from the subtype inclusion, and the homeomorphism part is defined on all
  -- of the subtype.
  simp [oscillatingStraightening, oscillatingHalfPlaneOpens]

/-- Helper for Exercise 4.24: the straightening chart has target all of `ℝ²`. -/
lemma oscillatingStraightening_target :
    oscillatingStraightening.target = Set.univ := by
  -- The homeomorphism part is defined everywhere on the target space.
  simp [oscillatingStraightening]

/-- Helper for Exercise 4.24: on the half-plane, the chart agrees with the explicit formula. -/
lemma oscillatingStraightening_apply_of_mem_halfPlane {p : ℝ × ℝ} (hp : p ∈ oscillatingHalfPlane) :
    oscillatingStraightening p = oscillatingStraighteningForward p := by
  -- Inside the source, the subtype inclusion inverse recovers the original point.
  let e := oscillatingHalfPlaneOpens.openPartialHomeomorphSubtypeCoe oscillatingHalfPlane_nonempty
  have hp' : p ∈ e.target := by
    simpa [e, oscillatingHalfPlaneOpens] using hp
  have hval : ((e.symm p : oscillatingHalfPlaneOpens) : ℝ × ℝ) = p := by
    simpa [e] using e.right_inv hp'
  -- After rewriting the recovered subtype point, the composite is the explicit forward formula.
  rw [oscillatingStraightening, OpenPartialHomeomorph.trans_apply]
  change oscillatingStraighteningHomeomorph ((
      oscillatingHalfPlaneOpens.openPartialHomeomorphSubtypeCoe oscillatingHalfPlane_nonempty).symm p) =
    oscillatingStraighteningForward p
  simpa [oscillatingStraighteningHomeomorph] using congrArg oscillatingStraighteningForward hval

/-- Helper for Exercise 4.24: the inverse chart agrees everywhere with the explicit inverse formula. -/
lemma oscillatingStraightening_symm_apply (p : ℝ × ℝ) :
    oscillatingStraightening.symm p = oscillatingStraighteningInverse p := by
  -- The inverse first applies the homeomorphism inverse, then forgets the subtype condition.
  simp [oscillatingStraightening, oscillatingStraighteningHomeomorph, oscillatingStraighteningInverse]

/-- Helper for Exercise 4.24: the forward straightening map is smooth on its source. -/
lemma oscillatingStraighteningForward_contDiffOn :
    ContDiffOn ℝ ∞ oscillatingStraighteningForward oscillatingHalfPlane := by
  -- Each coordinate is a standard smooth function on the open half-plane `x > 0`.
  have hfst : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ p.1) oscillatingHalfPlane :=
    contDiff_fst.contDiffOn
  have hsnd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ p.2) oscillatingHalfPlane :=
    contDiff_snd.contDiffOn
  have hlog : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ Real.log p.1) oscillatingHalfPlane := by
    have hlogBase : ContDiffOn ℝ ∞ Real.log ({0} : Set ℝ)ᶜ := Real.contDiffOn_log
    refine hlogBase.comp hfst ?_
    intro p hp
    have hp' : 0 < p.1 := by simpa [oscillatingHalfPlane] using hp
    exact hp'.ne'
  have hinv : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ (p.1)⁻¹) oscillatingHalfPlane := by
    have hinvBase : ContDiffOn ℝ ∞ (fun x : ℝ ↦ x⁻¹) ({0} : Set ℝ)ᶜ := contDiffOn_inv (𝕜 := ℝ)
    refine hinvBase.comp hfst ?_
    intro p hp
    have hp' : 0 < p.1 := by simpa [oscillatingHalfPlane] using hp
    exact hp'.ne'
  have hsin : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ Real.sin ((p.1)⁻¹)) oscillatingHalfPlane :=
    (Real.contDiff_sin.contDiffOn).comp hinv fun _ _ ↦ Set.mem_univ _
  -- Combine the smooth coordinate functions into a smooth map to `ℝ²`.
  change ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ (Real.log p.1, p.2 - Real.sin (1 / p.1)))
    oscillatingHalfPlane
  simpa [one_div] using hlog.prodMk (hsnd.sub hsin)

/-- Helper for Exercise 4.24: the explicit inverse straightening map is smooth. -/
lemma oscillatingStraighteningInverse_contDiffOn :
    ContDiffOn ℝ ∞ oscillatingStraighteningInverse Set.univ := by
  -- The inverse uses only globally smooth operations on `ℝ²`.
  have hexp : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ Real.exp p.1) Set.univ :=
    Real.contDiff_exp.contDiffOn.comp contDiff_fst.contDiffOn fun _ _ ↦ Set.mem_univ _
  have hsnd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ p.2) Set.univ :=
    contDiff_snd.contDiffOn
  have hsine : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ Real.sin (Real.exp (-p.1))) Set.univ := by
    refine Real.contDiff_sin.contDiffOn.comp ?_ fun _ _ ↦ Set.mem_univ _
    refine Real.contDiff_exp.contDiffOn.comp ?_ fun _ _ ↦ Set.mem_univ _
    simpa using (contDiff_fst.contDiffOn.neg : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ -p.1) Set.univ)
  -- Pair the smooth coordinate expressions to obtain the smooth inverse.
  simpa [oscillatingStraighteningInverse] using hexp.prodMk (hsnd.add hsine)

/-- Helper for Exercise 4.24: the straightening chart lies in the smooth groupoid. -/
lemma oscillating_straightening_mem_contDiffGroupoid :
    oscillatingStraightening ∈ contDiffGroupoid ∞ 𝓘(ℝ, ℝ × ℝ) := by
  -- For the self model, groupoid membership reduces to ordinary `ContDiffOn` for the map
  -- and its inverse on their respective source and target.
  have hforward : ContDiffOn ℝ ∞ oscillatingStraightening oscillatingStraightening.source := by
    rw [oscillatingStraightening_source]
    refine oscillatingStraighteningForward_contDiffOn.congr ?_
    intro p hp
    exact oscillatingStraightening_apply_of_mem_halfPlane hp
  have hbackward : ContDiffOn ℝ ∞ oscillatingStraightening.symm oscillatingStraightening.target := by
    rw [oscillatingStraightening_target]
    refine oscillatingStraighteningInverse_contDiffOn.congr ?_
    intro p hp
    exact oscillatingStraightening_symm_apply p
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · simpa [modelWithCornersSelf_coe] using hforward
  · simpa [modelWithCornersSelf_coe] using hbackward

/-- Helper for Exercise 4.24: the straightening chart belongs to the smooth maximal atlas. -/
lemma oscillating_straightening_mem_maximalAtlas :
    oscillatingStraightening ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℝ × ℝ) ∞ (ℝ × ℝ) := by
  -- Maximal-atlas membership is the standard bridge from groupoid membership.
  exact (contDiffGroupoid ∞ 𝓘(ℝ, ℝ × ℝ)).mem_maximalAtlas_of_mem_groupoid
    oscillating_straightening_mem_contDiffGroupoid

/-- Helper for Exercise 4.24: the oscillating curve lies in the source of the straightening chart. -/
lemma oscillatingCurveMap_mem_halfPlane (t : ℝ) :
    oscillatingCurveMap t ∈ oscillatingHalfPlane := by
  -- The first coordinate of the curve is `exp t`, which is always positive.
  simp [oscillatingCurveMap, oscillatingHalfPlane, Real.exp_pos]

/-- Helper for Exercise 4.24: the straightening chart sends the oscillating curve to `(t, 0)`. -/
lemma oscillating_straightening_apply_curve (t : ℝ) :
    oscillatingStraightening (oscillatingCurveMap t) = (t, 0) := by
  -- Once we are in the half-plane source, the chart is given by its explicit formula.
  rw [oscillatingStraightening_apply_of_mem_halfPlane (oscillatingCurveMap_mem_halfPlane t)]
  simp [oscillatingStraighteningForward, oscillatingCurveMap, Real.exp_neg, one_div]

/-- Helper for Exercise 4.24: the oscillating curve is an immersion because the derivative of its
first coordinate is the nonvanishing map `t ↦ exp t`. -/
lemma oscillatingCurveMap_isImmersion :
    Manifold.IsImmersion 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ oscillatingCurveMap := by
  -- Route correction: instead of forcing a derivative-only argument, we straighten the curve by the
  -- source-faithful half-plane chart `(x, y) ↦ (log x, y - sin (1 / x))`.
  refine ⟨ℝ, inferInstance, inferInstance, ?_⟩
  intro t
  -- In these charts, the curve becomes the standard inclusion `u ↦ (u, 0)`.
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (oscillatingCurveMap_contDiff.continuous.continuousAt)
    (ContinuousLinearEquiv.refl ℝ (ℝ × ℝ))
    (OpenPartialHomeomorph.refl ℝ)
    oscillatingStraightening
  · simpa using Set.mem_univ t
  · simpa [oscillatingStraightening_source] using oscillatingCurveMap_mem_halfPlane t
  · simpa using (contDiffGroupoid ∞ 𝓘(ℝ)).id_mem_maximalAtlas
  · exact oscillating_straightening_mem_maximalAtlas
  · intro x hx
    -- The written-in-charts identity is exactly the normalization `t ↦ (t, 0)`.
    simpa [oscillating_straightening_apply_curve, oscillatingStraightening_target]

/-- Helper for Exercise 4.24: the origin is in the closure of the oscillating curve's range. -/
lemma origin_mem_closure_range_oscillatingCurveMap :
    ((0 : ℝ), (0 : ℝ)) ∈ closure (Set.range oscillatingCurveMap) := by
  rw [mem_closure_iff_nhds]
  intro s hs
  rcases Metric.mem_nhds_iff.mp hs with ⟨ε, hεpos, hball⟩
  have hεπ : 0 < ε * Real.pi := mul_pos hεpos Real.pi_pos
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 / (n + 1 : ℝ) < ε * Real.pi := exists_nat_one_div_lt hεπ
  let t : ℝ := -Real.log (Real.pi * (n + 1 : ℝ))
  have hmulpos : 0 < Real.pi * (n + 1 : ℝ) := by
    positivity
  have hpoint : oscillatingCurveMap t = ((1 / (Real.pi * (n + 1 : ℝ))), (0 : ℝ)) := by
    -- This special parameter lands at a zero of the sine factor.
    ext
    · dsimp [t, oscillatingCurveMap]
      rw [Real.exp_neg, Real.exp_log hmulpos]
      simp [one_div]
    · dsimp [t, oscillatingCurveMap]
      rw [neg_neg, Real.exp_log hmulpos, mul_comm]
      simpa using Real.sin_nat_mul_pi (n + 1)
  have hlt : 1 / (Real.pi * (n + 1 : ℝ)) < ε := by
    -- The chosen index puts the point inside the requested `ε`-ball.
    have hrewrite : 1 / (Real.pi * (n + 1 : ℝ)) = (1 / (n + 1 : ℝ)) / Real.pi := by
      field_simp [Real.pi_ne_zero]
    rw [hrewrite]
    exact (div_lt_iff₀ Real.pi_pos).2 hn
  have hnonneg : 0 ≤ 1 / (Real.pi * (n + 1 : ℝ)) := by
    positivity
  have hdist : dist (oscillatingCurveMap t) ((0 : ℝ), (0 : ℝ)) < ε := by
    rw [dist_eq_norm, hpoint]
    simp [Prod.norm_def]
    have hnat_nonneg : 0 ≤ (n : ℝ) + 1 := by
      positivity
    have hpinonneg : 0 ≤ Real.pi := Real.pi_pos.le
    simpa [abs_of_nonneg hnat_nonneg, abs_of_nonneg hpinonneg] using hlt
  refine ⟨oscillatingCurveMap t, ?_⟩
  exact ⟨hball hdist, ⟨t, rfl⟩⟩

/-- Exercise 4.24 (1): The oscillating curve defines a smooth embedding of `ℝ` into `ℝ × ℝ`. -/
-- Proof sketch: Reparametrize the standard curve `x ↦ (x, sin (1 / x))` on `(0, ∞)` by the
-- diffeomorphism `t ↦ exp t`, and prove that the resulting graph map is both a smooth immersion
-- and a topological embedding.
theorem oscillatingCurveMap_isSmoothEmbedding :
    Manifold.IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ oscillatingCurveMap := by
  -- The definition of smooth embedding is exactly immersion plus topological embedding.
  exact Manifold.IsSmoothEmbedding.mk
    oscillatingCurveMap_isImmersion
    oscillatingCurveMap_isEmbedding

/-- Exercise 4.24 (2): The oscillating curve is not an open map. -/
-- Proof sketch: The image of the open set `univ` is the whole oscillating curve, and that curve is
-- a one-dimensional subset of `ℝ × ℝ`, hence not open in the plane.
theorem oscillatingCurveMap_not_isOpenMap :
    ¬ IsOpenMap oscillatingCurveMap := by
  intro hopen
  have hrange : IsOpen (Set.range oscillatingCurveMap) := hopen.isOpen_range
  have hbase : (1, Real.sin 1) ∈ Set.range oscillatingCurveMap := by
    refine ⟨0, ?_⟩
    simp [oscillatingCurveMap]
  rcases Metric.isOpen_iff.mp hrange (1, Real.sin 1) hbase with ⟨ε, hεpos, hball⟩
  let q : ℝ × ℝ := (1, Real.sin 1 + ε / 2)
  have hqball : q ∈ Metric.ball (1, Real.sin 1) ε := by
    -- A vertical perturbation stays in the ball but leaves the graph.
    dsimp [q]
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    have hhalfpos : 0 < ε / 2 := by
      positivity
    have hhalfabs : |ε / 2| < ε := by
      have hhalflt : ε / 2 < ε := by
        linarith
      simpa [abs_of_pos hhalfpos] using hhalflt
    have hmax : max 0 |ε / 2| < ε := by
      exact max_lt_iff.mpr ⟨hεpos, hhalfabs⟩
    simpa [abs_of_pos hhalfpos] using hmax
  rcases hball hqball with ⟨t, ht⟩
  have ht0 : t = 0 := by
    have hfst : Real.exp t = 1 := by
      simpa [oscillatingCurveMap, q] using congrArg Prod.fst ht
    exact (Real.exp_eq_one_iff t).1 hfst
  have hsnd : Real.sin (Real.exp (-t)) = Real.sin 1 + ε / 2 := by
    simpa [oscillatingCurveMap, q] using congrArg Prod.snd ht
  have : Real.sin 1 = Real.sin 1 + ε / 2 := by
    simpa [ht0] using hsnd
  linarith

/-- Exercise 4.24 (3): The oscillating curve is not a closed map. -/
-- Proof sketch: The closed set `univ ⊆ ℝ` maps to a set whose closure contains accumulation points
-- on `{0} × [-1, 1]` that are not in the image, so the image is not closed.
theorem oscillatingCurveMap_not_isClosedMap :
    ¬ IsClosedMap oscillatingCurveMap := by
  intro hclosed
  have hrange : IsClosed (Set.range oscillatingCurveMap) := hclosed.isClosed_range
  have horigin_mem : ((0 : ℝ), (0 : ℝ)) ∈ Set.range oscillatingCurveMap := by
    simpa [hrange.closure_eq] using origin_mem_closure_range_oscillatingCurveMap
  rcases horigin_mem with ⟨t, ht⟩
  have hfst : Real.exp t = 0 := by
    simpa [oscillatingCurveMap] using congrArg Prod.fst ht
  exact (Real.exp_pos t).ne' hfst
