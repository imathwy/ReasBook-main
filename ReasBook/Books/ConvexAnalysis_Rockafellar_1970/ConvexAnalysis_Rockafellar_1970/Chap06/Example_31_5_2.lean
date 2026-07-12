import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Proposition_5_24_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Proposition_5_24_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Remark_31_5_1

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open scoped Rockafellar SetRel

local notation "IsClosedProperConvex[ℝ]" => @Function.IsClosedProperConvex ℝ

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 31.5.2 records the contraction property of the proximation operator of a
  closed proper convex function.
- `core/canonical`: the relevant owner abstractions are the Chapter 12 owner
  `Function.IsClosedProperConvex`, the proximation operator `Function.prox` from
  `Remark_31_5_1`, and the vector subdifferential owner `Function.subdifferentialAt`.
- `bridge/view`: the explicit minimizer formulation is derived API now owned upstream by
  `Function.prox_isMinOn` and `Function.eq_prox_of_isMinOn`; this file keeps the source-facing
  contraction theorem directly on the canonical proximation operator instead of reintroducing a
  parallel minimizer-level public statement.

Domain-style sampling used here:
- `Function.IsClosedProperConvex`;
- `Function.prox`;
- `Function.prox_isMinOn`;
- `Function.eq_prox_of_isMinOn`;
- `Function.subdifferentialAt`;
- `SetRel.Monotone`.

Primitive data vs derived API:
- primitive input: a closed proper convex function `f`, represented by
  `hf : f.IsClosedProperConvex`;
- primitive source data: two points `z₀` and `z₁`;
- derived output: the contraction estimate for the canonical proximation points
  `prox f hf z₀` and `prox f hf z₁`; any explicit minimizer statement is a companion view obtained
  by rewriting with `eq_prox_of_isMinOn`.

Layer target: `source-facing`, stated directly on the canonical owner `Function.prox`.

Ambient-assumption minimization:
- the proximation owner from Remark 31.5.1 already lives on complete real inner-product spaces;
- finite dimensionality is therefore not primitive for this example and is removed from the public
  statement.
-/

namespace Function

-- Proof sketch: apply Remark 31.5.1 to write the residual vectors
-- `zᵢ - prox f hf zᵢ` as subgradients of `f` at `prox f hf zᵢ`. Monotonicity of the
-- subdifferential then gives
-- `0 ≤ ⟪prox f hf z₁ - prox f hf z₀, (z₁ - prox f hf z₁) - (z₀ - prox f hf z₀)⟫`.
-- Expanding `‖z₁ - z₀‖²` as the norm square of the sum of these two differences yields the
-- contraction estimate.
/-- Example 31.5.2, canonical owner form: the proximation operator is `1`-Lipschitz. -/
theorem prox_lipschitz
    (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) :
    LipschitzWith 1 (prox f hf) := by
  refine lipschitzWith_iff_norm_sub_le.mpr ?_
  intro z₁ z₀
  let x₀ : E := prox f hf z₀
  let x₁ : E := prox f hf z₁
  let g₀ : E := z₀ - x₀
  let g₁ : E := z₁ - x₁
  let Γ : SetRel E E := _root_.subdifferentialGraph (f := f) (Y := E)
  have hg₀_mem : g₀ ∈ Function.subdifferentialAt f x₀ := by
    dsimp [g₀, x₀]
    exact (Function.dual_moreau_gradient_eq_sub f hf z₀) ▸
      (Function.prox_add_dual_moreau_gradient_mem_subdifferential f hf z₀).2
  have hg₁_mem : g₁ ∈ Function.subdifferentialAt f x₁ := by
    dsimp [g₁, x₁]
    exact (Function.dual_moreau_gradient_eq_sub f hf z₁) ▸
      (Function.prox_add_dual_moreau_gradient_mem_subdifferential f hf z₁).2
  have hg₀_graph_vec : x₀ ~[Function.subdifferentialGraph f] g₀ :=
    Function.mem_subdifferentialGraph.mpr hg₀_mem
  have hg₁_graph_vec : x₁ ~[Function.subdifferentialGraph f] g₁ :=
    Function.mem_subdifferentialGraph.mpr hg₁_mem
  have hg₀_graph : x₀ ~[Γ] g₀ := by
    dsimp [Γ]
    rw [_root_.mem_subdifferentialAt_pairing]
    intro z
    have hinner :
        (inner ℝ g₀ (z - x₀) : ℝ) =
          (HasLinearPairing.pairingLinear z g₀ - HasLinearPairing.pairingLinear x₀ g₀) := by
      calc
        (inner ℝ g₀ (z - x₀) : ℝ) = inner ℝ g₀ z - inner ℝ g₀ x₀ := by
          rw [inner_sub_right]
        _ = inner ℝ z g₀ - inner ℝ x₀ g₀ := by
          simp [real_inner_comm]
        _ = (HasLinearPairing.pairingLinear z g₀ - HasLinearPairing.pairingLinear x₀ g₀) := by
          rfl
    simpa [hinner] using
      Function.mem_subdifferentialAt.mp
        (Function.mem_subdifferentialGraph.mp hg₀_graph_vec) z
  have hg₁_graph : x₁ ~[Γ] g₁ := by
    dsimp [Γ]
    rw [_root_.mem_subdifferentialAt_pairing]
    intro z
    have hinner :
        (inner ℝ g₁ (z - x₁) : ℝ) =
          (HasLinearPairing.pairingLinear z g₁ - HasLinearPairing.pairingLinear x₁ g₁) := by
      calc
        (inner ℝ g₁ (z - x₁) : ℝ) = inner ℝ g₁ z - inner ℝ g₁ x₁ := by
          rw [inner_sub_right]
        _ = inner ℝ z g₁ - inner ℝ x₁ g₁ := by
          simp [real_inner_comm]
        _ = (HasLinearPairing.pairingLinear z g₁ - HasLinearPairing.pairingLinear x₁ g₁) := by
          rfl
    simpa [hinner] using
      Function.mem_subdifferentialAt.mp
        (Function.mem_subdifferentialGraph.mp hg₁_graph_vec) z
  have hΓ_mon : Γ.Monotone ℝ := by
    dsimp [Γ]
    exact SetRel.CyclicallyMonotone.monotone
      (subdifferentialGraph_cyclicallyMonotone (Y := E) hf.proper)
  have hnonneg_pair : 0 ≤ (⟪x₁ - x₀, g₁ - g₀⟫ₚ : ℝ) :=
    hΓ_mon.pairing_nonneg hg₀_graph hg₁_graph
  have hnonneg :
      0 ≤ inner ℝ (x₁ - x₀) (g₁ - g₀) := by
    change 0 ≤ (⟪x₁ - x₀, g₁ - g₀⟫ₚ : ℝ)
    exact hnonneg_pair
  have hg_diff : g₁ - g₀ = (z₁ - z₀) - (x₁ - x₀) := by
    dsimp [g₀, g₁]
    abel
  have hmono :
      0 ≤ inner ℝ (x₁ - x₀) ((z₁ - z₀) - (x₁ - x₀)) := by
    simpa [hg_diff] using hnonneg
  have hsq_le_inner :
      ‖x₁ - x₀‖ ^ 2 ≤ inner ℝ (x₁ - x₀) (z₁ - z₀) := by
    have hmono' :
        0 ≤ inner ℝ (x₁ - x₀) (z₁ - z₀) - inner ℝ (x₁ - x₀) (x₁ - x₀) := by
      simpa [inner_sub_right] using hmono
    have hinner_le :
        inner ℝ (x₁ - x₀) (x₁ - x₀) ≤ inner ℝ (x₁ - x₀) (z₁ - z₀) := by
      linarith
    simpa [real_inner_self_eq_norm_sq] using hinner_le
  have hsq_le_mul :
      ‖x₁ - x₀‖ ^ 2 ≤ ‖x₁ - x₀‖ * ‖z₁ - z₀‖ := by
    exact hsq_le_inner.trans (real_inner_le_norm _ _)
  have hnorm_le : ‖x₁ - x₀‖ ≤ ‖z₁ - z₀‖ := by
    by_cases hzero : ‖x₁ - x₀‖ = 0
    · simp [hzero]
    · have hpos : 0 < ‖x₁ - x₀‖ :=
        lt_of_le_of_ne (norm_nonneg (x₁ - x₀)) (Ne.symm hzero)
      have hmul :
          ‖x₁ - x₀‖ * ‖x₁ - x₀‖ ≤ ‖x₁ - x₀‖ * ‖z₁ - z₀‖ := by
        simpa [pow_two] using hsq_le_mul
      exact le_of_mul_le_mul_left hmul hpos
  simpa [x₀, x₁, one_mul] using hnorm_le

/-- Example 31.5.2, pointwise view: the proximation operator is nonexpansive. -/
theorem prox_nonexpansive
    (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) (z₀ z₁ : E) :
    ‖prox f hf z₁ - prox f hf z₀‖ ≤ ‖z₁ - z₀‖ := by
  have h :=
    (lipschitzWith_iff_norm_sub_le.mp (prox_lipschitz f hf)) z₁ z₀
  simpa [one_mul] using h

end Function

end
