import Mathlib
import BauschkeLean.Chap02.Definition_2_29
import BauschkeLean.Chap20.Proposition_20_22

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace SetValuedOperator Topology

universe u v

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {B : Type v} [Nonempty B] [Preorder B] [IsDirectedOrder B]

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.37 records mixed strong/weak net closedness as graph-point
  membership statements.
- `core/canonical`: the owner data are maximal monotonicity `Maximal IsMonotone A` and graph
  membership `(x, u) ∈ gra A`.
- `bridge/view`: clause `(2)` is the inverse-coordinate-swap view of clause `(1)`, so it should
  reuse the canonical inverse owner API rather than duplicate the same closure argument. -/

/-- Helper for Proposition 20.37: translating the second coordinate of a bounded graph net by a
fixed vector preserves boundedness. -/
private theorem bounded_range_sub_of_bounded_graph_range
    {x_b u_b : B → H} {v : H}
    (hbounded : Bornology.IsBounded (Set.range fun b ↦ (x_b b, u_b b))) :
    Bornology.IsBounded (Set.range fun b ↦ u_b b - v) := by
  have hsnd :
      Prod.snd '' Set.range (fun b ↦ (x_b b, u_b b)) = Set.range u_b := by
    ext u'
    constructor
    · rintro ⟨p, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨(x_b b, u_b b), ⟨b, rfl⟩, rfl⟩
  have hu_bounded : Bornology.IsBounded (Set.range u_b) := by
    -- Extract boundedness of the graph net's second coordinate.
    rw [← hsnd]
    exact hbounded.image_snd
  rcases isBounded_iff_forall_norm_le.mp hu_bounded with ⟨C, hC⟩
  refine isBounded_iff_forall_norm_le.mpr ?_
  refine ⟨C + ‖v‖, ?_⟩
  rintro z ⟨b, rfl⟩
  -- Translation is controlled by the triangle inequality.
  calc
    ‖u_b b - v‖ ≤ ‖u_b b‖ + ‖v‖ := norm_sub_le _ _
    _ ≤ C + ‖v‖ := add_le_add (hC _ (Set.mem_range_self b)) le_rfl

/-- Helper for Proposition 20.37: weak convergence gives convergence of every fixed inner-product
coordinate, without any completeness hypothesis. -/
private theorem tendsto_inner_right_of_tendsto_weakly
    {u_b : B → H} {u v : H}
    (hu_b :
      Tendsto (fun b ↦ toWeakSpace ℝ H (u_b b)) atTop
        (𝓝 (toWeakSpace ℝ H u))) :
    Tendsto (fun b ↦ ⟪u_b b, v⟫_ℝ) atTop (𝓝 ⟪u, v⟫_ℝ) := by
  have hcont_id : Continuous (fun z : WeakSpace ℝ H ↦ z) := continuous_id
  have hweak_eval :
      Continuous fun z : WeakSpace ℝ H ↦
        StrongDual.toWeakDual (innerSL ℝ v) ((toWeakSpace ℝ H).symm z) :=
    (continuous_iff_forall_weakDual_apply (f := fun z : WeakSpace ℝ H ↦ z)).1 hcont_id
      (StrongDual.toWeakDual (innerSL ℝ v))
  -- Evaluate the weak limit against the fixed functional induced by `v`.
  have hEval := (hweak_eval.tendsto (toWeakSpace ℝ H u)).comp hu_b
  simpa [StrongDual.toWeakDual_apply, innerSL_apply_apply, real_inner_comm] using hEval

/-- Helper for Proposition 20.37: strong convergence in the first slot, weak convergence in the
second slot, and boundedness of the second range imply convergence of the pairings. -/
private theorem tendsto_inner_of_tendsto_of_tendsto_weakly_of_bounded_right
    {x_b u_b : B → H} {x u : H}
    (hx_b : Tendsto x_b atTop (𝓝 x))
    (hu_bounded : Bornology.IsBounded (Set.range u_b))
    (hu_b :
      Tendsto (fun b ↦ toWeakSpace ℝ H (u_b b)) atTop
        (𝓝 (toWeakSpace ℝ H u))) :
    Tendsto (fun b ↦ ⟪x_b b, u_b b⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
  rcases isBounded_iff_forall_norm_le.mp hu_bounded with ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0
  have hC : ∀ b, ‖u_b b‖ ≤ C := by
    intro b
    calc
      ‖u_b b‖ ≤ C₀ := hC₀ _ (Set.mem_range_self b)
      _ ≤ max C₀ 0 := le_max_left _ _
      _ = C := rfl
  have hfixed_swap :
      Tendsto (fun b ↦ ⟪u_b b, x⟫_ℝ) atTop (𝓝 ⟪u, x⟫_ℝ) :=
    tendsto_inner_right_of_tendsto_weakly (v := x) hu_b
  have hfixed :
      Tendsto (fun b ↦ ⟪x, u_b b⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
    -- The fixed-vector pairing converges by weak continuity in the second slot.
    simpa [real_inner_comm] using hfixed_swap
  have hdiff : Tendsto (fun b ↦ x_b b - x) atTop (𝓝 (0 : H)) := by
    simpa using
      hx_b.sub (tendsto_const_nhds : Tendsto (fun _ : B ↦ x) atTop (𝓝 x))
  have hnorm_diff : Tendsto (fun b ↦ ‖x_b b - x‖) atTop (𝓝 0) := by
    simpa using hdiff.norm
  have hmul : Tendsto (fun b ↦ ‖x_b b - x‖ * C) atTop (𝓝 0) := by
    simpa using hnorm_diff.mul_const C
  have hpert_abs :
      Tendsto (fun b ↦ |⟪x_b b - x, u_b b⟫_ℝ|) atTop (𝓝 0) := by
    refine
      squeeze_zero' (f := fun b ↦ |⟪x_b b - x, u_b b⟫_ℝ|)
        (g := fun b ↦ ‖x_b b - x‖ * C)
        (Eventually.of_forall fun b ↦ abs_nonneg _) ?_ ?_
    · filter_upwards with b
      exact le_trans (abs_real_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_left (hC b) (norm_nonneg _))
    · simpa using hmul
  have hpert : Tendsto (fun b ↦ ⟪x_b b - x, u_b b⟫_ℝ) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp] using hpert_abs
  have hsplit :
      (fun b ↦ ⟪x_b b, u_b b⟫_ℝ) =
        fun b ↦ ⟪x_b b - x, u_b b⟫_ℝ + ⟪x, u_b b⟫_ℝ := by
    funext b
    calc
      ⟪x_b b, u_b b⟫_ℝ = ⟪(x_b b - x) + x, u_b b⟫_ℝ := by
        congr 1
        abel
      _ = ⟪x_b b - x, u_b b⟫_ℝ + ⟪x, u_b b⟫_ℝ := by
        rw [inner_add_left]
  -- Split the pairing into a vanishing perturbation term plus the fixed-vector weak limit.
  rw [hsplit]
  simpa using hpert.add hfixed

/-- Helper for Proposition 20.37: testing the limit pair against any fixed graph point yields the
Minty nonnegativity inequality. -/
private theorem pairing_nonneg_against_graph_point_of_limit
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    {x_b u_b : B → H} {x u y v : H}
    (hgraph : ∀ b, (x_b b, u_b b) ∈ gra A)
    (hbounded : Bornology.IsBounded (Set.range fun b ↦ (x_b b, u_b b)))
    (hx_b : Tendsto x_b atTop (𝓝 x))
    (hu_b :
      Tendsto (fun b ↦ toWeakSpace ℝ H (u_b b)) atTop
        (𝓝 (toWeakSpace ℝ H u)))
    (hv : v ∈ A y) :
    0 ≤ ⟪x - y, u - v⟫_ℝ := by
  have hineq : ∀ b, 0 ≤ ⟪x_b b - y, u_b b - v⟫_ℝ := by
    intro b
    have hgraph_b : u_b b ∈ A (x_b b) := by
      simpa using hgraph b
    -- Monotonicity gives the pointwise graph inequalities against `(y, v)`.
    exact (SetValuedOperator.isMonotone_iff A).1 hA.1 hgraph_b hv
  have hx_shift :
      Tendsto (fun b ↦ x_b b - y) atTop (𝓝 (x - y)) := by
    -- Shift the strongly convergent primal variable by the fixed graph point.
    simpa using
      hx_b.sub (tendsto_const_nhds : Tendsto (fun _ : B ↦ y) atTop (𝓝 y))
  have hu_shift :
      Tendsto (fun b ↦ toWeakSpace ℝ H (u_b b - v)) atTop
        (𝓝 (toWeakSpace ℝ H (u - v))) := by
    -- Shift the weakly convergent dual variable inside `WeakSpace`.
    have hsub :
        Tendsto (fun b ↦ toWeakSpace ℝ H (u_b b) - toWeakSpace ℝ H v) atTop
          (𝓝 (toWeakSpace ℝ H u - toWeakSpace ℝ H v)) := by
      exact hu_b.sub
        (tendsto_const_nhds : Tendsto (fun _ : B ↦ toWeakSpace ℝ H v) atTop
          (𝓝 (toWeakSpace ℝ H v)))
    simpa using hsub
  have hu_shift_bounded :
      Bornology.IsBounded (Set.range fun b ↦ u_b b - v) :=
    bounded_range_sub_of_bounded_graph_range (x_b := x_b) (u_b := u_b) (v := v) hbounded
  have hinner :
      Tendsto (fun b ↦ ⟪x_b b - y, u_b b - v⟫_ℝ) atTop
        (𝓝 ⟪x - y, u - v⟫_ℝ) :=
    tendsto_inner_of_tendsto_of_tendsto_weakly_of_bounded_right
      hx_shift hu_shift_bounded hu_shift
  -- Pass the pointwise Minty inequalities to the limit.
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hinner (Filter.Eventually.of_forall hineq)

-- Proof sketch: test maximal monotonicity of `A` against an arbitrary graph point `(y, v)`. The
-- graph inequalities for `(x_b b, u_b b)` pass to the limit because `x_b` converges strongly, `u_b`
-- converges weakly, and the graph net is bounded. The resulting inequality for every `(y, v) ∈ gra
-- A` gives `(x, u) ∈ gra A` by the maximal-monotonicity criterion.
/-- Proposition 20.37 (1): if a bounded net of graph points of a maximally monotone operator
converges strongly in the primal variable and weakly in the dual variable, then its limit pair
still belongs to the graph. -/
theorem Maximal.mem_graph_of_tendsto_of_tendsto_weakly
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    {x_b u_b : B → H} {x u : H}
    (hgraph : ∀ b, (x_b b, u_b b) ∈ gra A)
    (hbounded : Bornology.IsBounded (Set.range fun b ↦ (x_b b, u_b b)))
    (hx_b : Tendsto x_b atTop (𝓝 x))
    (hu_b : Tendsto (fun b ↦ toWeakSpace ℝ H (u_b b)) atTop (𝓝 (toWeakSpace ℝ H u))) :
    (x, u) ∈ gra A := by
  -- Use the Minty criterion and test the limit pair against an arbitrary graph point.
  simpa using (Maximal.mem_iff hA x u).2 fun {y v} hv ↦
    pairing_nonneg_against_graph_point_of_limit hA hgraph hbounded hx_b hu_b hv

-- Proof sketch: apply part (1) to the inverse operator `A.inverse`, whose graph is obtained by
-- swapping the coordinates. Strong convergence of `u_b` and weak convergence of `x_b` translate
-- exactly into the hypotheses of part (1) for the inverse graph, giving `(u, x) ∈ gra A⁻¹` and
-- hence `(x, u) ∈ gra A`.
/-- Proposition 20.37 (2): if a bounded net of graph points of a maximally monotone operator
converges weakly in the primal variable and strongly in the dual variable, then its limit pair
still belongs to the graph. -/
theorem Maximal.mem_graph_of_tendsto_weakly_of_tendsto
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    {x_b u_b : B → H} {x u : H}
    (hgraph : ∀ b, (x_b b, u_b b) ∈ gra A)
    (hbounded : Bornology.IsBounded (Set.range fun b ↦ (x_b b, u_b b)))
    (hx_b : Tendsto (fun b ↦ toWeakSpace ℝ H (x_b b)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hu_b : Tendsto u_b atTop (𝓝 u)) :
    (x, u) ∈ gra A := by
  have hAinv : Maximal IsMonotone A⁻¹ := SetValuedOperator.Maximal.inverse hA
  have hu_range :
      Prod.snd '' Set.range (fun b ↦ (x_b b, u_b b)) = Set.range u_b := by
    ext u'
    constructor
    · rintro ⟨p, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨(x_b b, u_b b), ⟨b, rfl⟩, rfl⟩
  have hx_range :
      Prod.fst '' Set.range (fun b ↦ (x_b b, u_b b)) = Set.range x_b := by
    ext x'
    constructor
    · rintro ⟨p, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨(x_b b, u_b b), ⟨b, rfl⟩, rfl⟩
  have hu_bounded : Bornology.IsBounded (Set.range u_b) := by
    rw [← hu_range]
    exact hbounded.image_snd
  have hx_bounded : Bornology.IsBounded (Set.range x_b) := by
    rw [← hx_range]
    exact hbounded.image_fst
  have hbounded_inv : Bornology.IsBounded (Set.range fun b ↦ (u_b b, x_b b)) := by
    rw [← Bornology.isBounded_image_fst_and_snd]
    constructor
    · have hfst : Prod.fst '' Set.range (fun b ↦ (u_b b, x_b b)) = Set.range u_b := by
        ext u'
        constructor
        · rintro ⟨p, ⟨b, rfl⟩, rfl⟩
          exact ⟨b, rfl⟩
        · rintro ⟨b, rfl⟩
          exact ⟨(u_b b, x_b b), ⟨b, rfl⟩, rfl⟩
      rw [hfst]
      exact hu_bounded
    · have hsnd : Prod.snd '' Set.range (fun b ↦ (u_b b, x_b b)) = Set.range x_b := by
        ext x'
        constructor
        · rintro ⟨p, ⟨b, rfl⟩, rfl⟩
          exact ⟨b, rfl⟩
        · rintro ⟨b, rfl⟩
          exact ⟨(u_b b, x_b b), ⟨b, rfl⟩, rfl⟩
      rw [hsnd]
      exact hx_bounded
  have hgraph_inv : ∀ b, (u_b b, x_b b) ∈ gra A⁻¹ := by
    intro b
    simpa using hgraph b
  have hmem_inv : (u, x) ∈ gra A⁻¹ :=
    SetValuedOperator.Maximal.mem_graph_of_tendsto_of_tendsto_weakly
      hAinv hgraph_inv hbounded_inv hu_b hx_b
  simpa using hmem_inv

end SetValuedOperator
