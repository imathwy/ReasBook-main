import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap09.Proposition_9_19
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap16.Definition_16_1

open Filter
open WithLp
open scoped Topology InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialCalculus

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- On the real-height graph of `f`, adding the indicator of `dom (∂ f)` simply cuts out the graph
-- points whose base point is subdifferentiable.
omit [CompleteSpace H] in
@[simp] theorem mem_graph_add_indicator_subdifferentiabilityDomain_iff
    {f : H → Set.Ioi (⊥ : EReal)} (p : graph f.asEReal) :
    ((p : H × ℝ) ∈ graph ((f + ι[SetValuedOperator.dom (∂ f)]).asEReal)) ↔
      SubdifferentiableAt f p.1.1 := by
  rcases p with ⟨⟨x, ξ⟩, hp⟩
  rw [subdifferentiableAt_iff_mem_dom]
  by_cases hx : x ∈ SetValuedOperator.dom (∂ f)
  · simpa [add_apply, indicator_apply, hx] using hp
  · have hfx_ne_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hsum : ((f x : EReal) + ⊤) = ⊤ := EReal.add_top_of_ne_bot hfx_ne_bot
    simp [add_apply, indicator_apply, hx, hsum]

-- Proof sketch: the constrained graph from the textbook is exactly the subgraph cut out by the
-- owner predicate `SubdifferentiableAt`, so density can be stated directly on `graph f.asEReal`.
-- Proposition 9.19 then approximates each finite graph point `(x, (f x).toReal)` by graph points
-- above subdifferentiability points.
omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 16 38: on the real-height graph, the second coordinate is the finite
value `(f x).toReal`. -/
private lemma graph_toReal_eq_snd
    {f : H → Set.Ioi (⊥ : EReal)} (q : graph f.asEReal) :
    (f q.1.1 : EReal).toReal = q.1.2 := by
  -- Applying `toReal` to the graph identity recovers the real ordinate.
  simpa using congrArg EReal.toReal q.2

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 16 38: a point of the real-height epigraph has finite base value. -/
private theorem mem_effectiveDomain_of_mem_real_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {ξ : ℝ}
    (hxξ : (x, ξ) ∈ epigraph (fun y : H ↦ (f y : EReal))) :
    x ∈ effectiveDomain f := by
  -- Epigraph membership bounds `f x` by the finite real height `ξ`, so `x` lies in the
  -- effective domain.
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt (mem_epigraph_iff _ _ _ |>.mp hxξ) (EReal.coe_lt_top _)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 16 38: lowering only the second coordinate by `δ` changes the
`ℓ²` product distance by exactly `δ`. -/
private lemma dist_same_fst_drop_snd_eq
    {x : H} {ξ δ : ℝ} (hδ : 0 ≤ δ) :
    dist (x, ξ - δ) (x, ξ) = δ := by
  have hsnd : dist (ξ - δ) ξ = δ := by
    -- On `ℝ`, the distance is the absolute vertical difference.
    rw [Real.dist_eq, show ξ - δ - ξ = -δ by ring, abs_neg, abs_of_nonneg hδ]
  have hdist_transport :
      dist (x, ξ - δ) (x, ξ) =
        dist (WithLp.toLp 2 ((x, ξ - δ) : H × ℝ))
          (WithLp.toLp 2 ((x, ξ) : H × ℝ)) := by
    rfl
  -- The horizontal distance vanishes, so the product distance reduces to the vertical gap.
  have hprod :
      dist (x, ξ - δ) (x, ξ) = √(dist x x ^ 2 + dist (ξ - δ) ξ ^ 2) := by
    rw [hdist_transport]
    simpa using
      WithLp.prod_dist_eq_of_L2
        (WithLp.toLp 2 ((x, ξ - δ) : H × ℝ))
        (WithLp.toLp 2 ((x, ξ) : H × ℝ))
  rw [hprod, dist_self, hsnd, zero_pow (by norm_num), zero_add]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hδ]

/-- Helper for Proposition 16 38: projecting a point placed strictly below the graph produces the
explicit subgradient encoded by the projection residual. -/
private theorem mem_subdifferential_of_projectionPoint_below_graph
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x p : H} {ξ π : ℝ}
    (hx : x ∈ effectiveDomain f) (hξ : ξ < (f x : EReal).toReal)
    (hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)) :
    ((π - ξ)⁻¹ • (x - p)) ∈ (∂ f) p := by
  -- Route correction: first extract the explicit affine minorant from Proposition 9.19, and only
  -- then package it as membership in the subdifferential.
  have hp_mem_epigraph :
      (p, π) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    -- The metric projection lands in the epigraph.
    rw [hproj]
    exact
      projectionPoint_mem (epigraph (fun y : H ↦ (f y : EReal)))
        (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  have hp : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_real_epigraph hp_mem_epigraph
  rcases
      strict_lt_value_and_value_eq_height_of_eq_projectionPoint_epigraph_of_mem_gammaZero
        hf hx hξ hproj with
    ⟨hξ_lt_fp, hfp_eq_pi_real⟩
  have hξ_lt_pi : ξ < π := by
    -- Proposition 9.19 identifies the projection height with the finite graph height at `p`.
    simpa [hfp_eq_pi_real] using hξ_lt_fp
  have hgap_pos : 0 < π - ξ := sub_pos.mpr hξ_lt_pi
  have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hfp_bot : (f p : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hfp_eq_pi : (f p : EReal) = (π : EReal) := by
    -- Finite epigraph contact upgrades the real-height equality to actual graph equality.
    calc
      (f p : EReal) = (((f p : EReal).toReal : ℝ) : EReal) := by
        symm
        exact EReal.coe_toReal hfp_top hfp_bot
      _ = (π : EReal) := by
        exact_mod_cast hfp_eq_pi_real
  have hvar :=
    variational_inequality_of_eq_projectionPoint_epigraph_of_mem_gammaZero
      hf hproj
  rw [mem_subdifferential_iff]
  intro y
  by_cases hy : y ∈ effectiveDomain f
  · -- On the effective domain, divide the projection inequality by the positive gap `π - ξ`.
    have hvar_y :
        ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
      hvar y hy
    have hinner_le :
        ⟪y - p, x - p⟫_ℝ ≤ ((f y : EReal).toReal - π) * (π - ξ) := by
      nlinarith
    have hscaled :
        ⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ ≤ (f y : EReal).toReal - π := by
      have hdiv :
          ⟪y - p, x - p⟫_ℝ / (π - ξ) ≤ (f y : EReal).toReal - π := by
        refine (div_le_iff₀ hgap_pos).2 ?_
        simpa [mul_comm, mul_left_comm, mul_assoc] using hinner_le
      simpa [div_eq_mul_inv, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using
        hdiv
    have hreal_minor :
        ⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ + π ≤ (f y : EReal).toReal := by
      linarith
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    have hcast :
        ((⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ + π : ℝ) : EReal) ≤
          (((f y : EReal).toReal : ℝ) : EReal) := by
      exact_mod_cast hreal_minor
    -- Rewrite the finite graph contact at `p` and the finite target value at `y` back into
    -- `EReal`.
    change
      ((⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ : EReal) + (f p : EReal)) ≤ (f y : EReal)
    rw [hfp_eq_pi, ← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_add]
    exact hcast
  · -- Outside the effective domain, the target value is `⊤`, so the affine minorant is automatic.
    have hy_top : (f y : EReal) = ⊤ := by
      by_contra hy_ne_top
      exact hy (mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top hy_ne_top))
    change
      ((⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ : EReal) + (f p : EReal)) ≤ (f y : EReal)
    rw [hy_top]
    simp

/-- Helper for Proposition 16 38: the projection of a point placed strictly below the graph is a
graph point whose base point is subdifferentiable. -/
private theorem subdifferentiableAt_and_mem_graph_of_projectionPoint_below_graph
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x p : H} {ξ π : ℝ}
    (hx : x ∈ effectiveDomain f) (hξ : ξ < (f x : EReal).toReal)
    (hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)) :
    SubdifferentiableAt f p ∧ (p, π) ∈ graph f.asEReal := by
  have hp_mem_epigraph :
      (p, π) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    -- The projection point belongs to the epigraph before we sharpen it to graph membership.
    rw [hproj]
    exact
      projectionPoint_mem (epigraph (fun y : H ↦ (f y : EReal)))
        (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  have hp : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_real_epigraph hp_mem_epigraph
  rcases
      strict_lt_value_and_value_eq_height_of_eq_projectionPoint_epigraph_of_mem_gammaZero
        hf hx hξ hproj with
    ⟨_, hfp_eq_pi_real⟩
  have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hfp_bot : (f p : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hgraph : (p, π) ∈ graph f.asEReal := by
    -- Finite contact with the epigraph is exactly graph membership.
    change (f p : EReal) = (π : EReal)
    calc
      (f p : EReal) = (((f p : EReal).toReal : ℝ) : EReal) := by
        symm
        exact EReal.coe_toReal hfp_top hfp_bot
      _ = (π : EReal) := by
        exact_mod_cast hfp_eq_pi_real
  have hsub :
      ((π - ξ)⁻¹ • (x - p)) ∈ (∂ f) p :=
    mem_subdifferential_of_projectionPoint_below_graph hf hx hξ hproj
  constructor
  · -- A single subgradient witness puts `p` in the domain of `∂ f`.
    rw [subdifferentiableAt_iff_mem_dom]
    exact ⟨(π - ξ)⁻¹ • (x - p), hsub⟩
  · exact hgraph

/-- Helper for Proposition 16 38: every graph point can be approximated arbitrarily well by graph
points above subdifferentiability points. -/
private theorem exists_subdifferentiable_graph_point_close
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (q : graph f.asEReal)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : graph f.asEReal, SubdifferentiableAt f r.1.1 ∧ dist (r : H × ℝ) (q : H × ℝ) < ε := by
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let z : H × ℝ := (q.1.1, q.1.2 - δ)
  let proj :=
    projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
      (isChebyshev_epigraph_of_mem_gammaZero hf) z
  let p : H := proj.1
  let π : ℝ := proj.2
  have hq_dom : q.1.1 ∈ effectiveDomain f := by
    -- A graph point has finite value because its second coordinate is an actual real number.
    rw [mem_effectiveDomain_iff]
    exact lt_of_eq_of_lt q.2 (EReal.coe_lt_top q.1.2)
  have hξ : q.1.2 - δ < (f q.1.1 : EReal).toReal := by
    -- The auxiliary point `z` lies strictly below the graph point `q`.
    rw [graph_toReal_eq_snd q]
    exact sub_lt_self _ hδ
  have hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) z := by
    -- The names `p` and `π` are just the coordinates of the projection point.
    simp [p, π, proj]
  rcases
      subdifferentiableAt_and_mem_graph_of_projectionPoint_below_graph
        hf hq_dom hξ hproj with
    ⟨hsub, hgraph⟩
  let r : graph f.asEReal := ⟨(p, π), hgraph⟩
  have hq_epi : ((q : graph f.asEReal) : H × ℝ) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    -- Every graph point is, in particular, an epigraph point.
    exact (mem_epigraph_iff _ _ _).2 (le_of_eq q.2)
  have hzq : dist z ((q : graph f.asEReal) : H × ℝ) = δ := by
    -- The auxiliary point differs from `q` only in the vertical coordinate.
    simpa [z] using
      dist_same_fst_drop_snd_eq (x := q.1.1) (ξ := q.1.2) (δ := δ) hδ.le
  have hproj_le : dist z (p, π) ≤ δ := by
    -- The projection distance is bounded by the distance to the comparison graph point `q`.
    have hbest :=
      projectionPoint_isBestApproximation
        (epigraph (fun y : H ↦ (f y : EReal)))
        (isChebyshev_epigraph_of_mem_gammaZero hf) z
    rw [show (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) z by
      simp [p, π, proj]]
    rw [hbest.2]
    exact le_trans (Metric.infDist_le_dist_of_mem hq_epi) (le_of_eq hzq)
  have hr_close : dist (r : H × ℝ) (q : H × ℝ) < ε := by
    -- Compare the projection point to `q` through the dropped point `z`.
    have hproj_le' : dist (p, π) z ≤ δ := by
      simpa [dist_comm] using hproj_le
    change dist (p, π) ((q : graph f.asEReal) : H × ℝ) < ε
    calc
      dist (p, π) ((q : graph f.asEReal) : H × ℝ) ≤
          dist (p, π) z + dist z ((q : graph f.asEReal) : H × ℝ) := by
        exact dist_triangle _ _ _
      _ ≤ δ + δ := by
        exact add_le_add hproj_le' (le_of_eq hzq)
      _ < ε := by
        dsimp [δ]
        linarith
  exact ⟨r, hsub, hr_close⟩

/-- Proposition 16 38: for `f ∈ Γ₀(H)`, the graph of the constrained function
`f + ι[dom (∂ f)]` is dense in the graph of `f`. -/
theorem graph_subdifferentiableAt_dense_in_graph_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    Dense {p : graph f.asEReal | SubdifferentiableAt f p.1.1} := by
  -- Route correction: first build an explicit nearby graph point above a subdifferentiability
  -- point, then feed that witness into the metric characterization of density on the graph
  -- subtype.
  rw [Metric.dense_iff]
  intro q ε hε
  rcases exists_subdifferentiable_graph_point_close hf q hε with ⟨r, hrsub, hr_close⟩
  refine ⟨r, ?_⟩
  constructor
  · -- The witness lies in the metric ball around `q`.
    simpa using hr_close
  · -- By construction, the witness base point is subdifferentiable.
    exact hrsub

-- Proof sketch: apply the graph-density theorem to the point `(x, (f x).toReal)` of
-- `graph f.asEReal`, then use the metric-space characterization of closure in the graph subtype to
-- extract nearby graph points above subdifferentiability points.
/-- A point of the effective domain can be approximated by subdifferentiability points with both
base points and function values converging. -/
theorem exists_subdifferentiableAt_sequence_tendsto_of_mem_effectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H} (hx : x ∈ effectiveDomain f) :
    ∃ xSeq : ℕ → H,
      (∀ n : ℕ, SubdifferentiableAt f (xSeq n)) ∧
      Tendsto xSeq atTop (𝓝 x) ∧
      Tendsto (fun n : ℕ ↦ (f (xSeq n) : EReal).toReal) atTop (𝓝 ((f x : EReal).toReal)) := by
  let q : graph f.asEReal := ⟨(x, (f x : EReal).toReal), by
    -- Effective-domain membership makes the canonical graph point finite.
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    simpa using (EReal.coe_toReal hx_top hx_bot).symm⟩
  have hs_dense : Dense {p : graph f.asEReal | SubdifferentiableAt f p.1.1} :=
    graph_subdifferentiableAt_dense_in_graph_of_mem_gammaZero hf
  have hq_closure : q ∈ closure {p : graph f.asEReal | SubdifferentiableAt f p.1.1} := by
    -- Density says the canonical graph point lies in the closure of the subdifferentiable graph.
    rw [dense_iff_closure_eq] at hs_dense
    rw [hs_dense]
    simp
  rw [mem_closure_iff_seq_limit] at hq_closure
  rcases hq_closure with ⟨qSeq, hqSeq_mem, hqSeq_tendsto⟩
  have hqSeq_pair_tendsto :
      Tendsto (fun n : ℕ ↦ (qSeq n : H × ℝ)) atTop (𝓝 (q : H × ℝ)) := by
    -- First forget the graph subtype, then project to coordinates.
    exact (continuous_subtype_val.tendsto q).comp hqSeq_tendsto
  refine ⟨fun n : ℕ ↦ (qSeq n).1.1, ?_, ?_, ?_⟩
  · -- Each graph point in the dense subtype has a subdifferentiable base point.
    intro n
    exact hqSeq_mem n
  · -- Convergence in the graph subtype implies convergence of the base coordinates.
    simpa [q] using hqSeq_pair_tendsto.fst_nhds
  · -- The second coordinates are exactly the finite function values along the graph sequence.
    have hvalue_eq :
        (fun n : ℕ ↦ (f ((qSeq n).1.1) : EReal).toReal) =
          fun n : ℕ ↦ (qSeq n : H × ℝ).2 := by
      funext n
      simpa using graph_toReal_eq_snd (qSeq n)
    rw [hvalue_eq]
    simpa [q] using hqSeq_pair_tendsto.snd_nhds

end SubdifferentialCalculus

end ERealFunction
