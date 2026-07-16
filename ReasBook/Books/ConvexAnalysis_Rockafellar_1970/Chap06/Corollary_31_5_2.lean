import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Proposition_5_24_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Proposition_5_24_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_31_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

open scoped Gradient RealInnerProductSpace Rockafellar SetRel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → WithBotTop ℝ}

local notation "w" => (fun z : E ↦ (((1 / 2 : ℝ) * ‖z‖ ^ 2 : ℝ) : WithBotTop ℝ))
local notation "fStar" => (f⋆ : E → WithBotTop ℝ)
local notation "primalEnvelope" => (f □ w : E → WithBotTop ℝ)
local notation "dualEnvelope" => (fStar □ w : E → WithBotTop ℝ)
local notation "primalEnvelopeReal" => (Function.realBranch primalEnvelope : E → ℝ)
local notation "dualEnvelopeReal" => (Function.realBranch dualEnvelope : E → ℝ)
local notation "IsClosedProperConvex[ℝ]" => @Function.IsClosedProperConvex ℝ

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 31.5.2 asserts that the subdifferential of a closed proper convex
  function on `R^n` is a maximal monotone mapping. This file states the same content on the more
  canonical ambient layer of complete real inner-product spaces, which specializes back to the
  finite-dimensional source setting.
- `core/canonical`: the project already organizes subdifferential mappings as the pairing-level
  relation `gph∂[Y](f)`, monotonicity as `SetRel.Monotone ρ ℝ`, and
  maximality as `Maximal` for the inclusion order on relations.
- `bridge/view`: this item uses Euclidean Moreau identities only as the proof bridge, while the
  theorem surface is stated on the intrinsic self-pairing owner `gph∂[E](f)`.

Domain-style sampling used here:

- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `_root_.subdifferentialGraph` / notation `gph∂[Y](f)` from `Chap05.Definition_5_24_3`;
- `SetRel.CyclicallyMonotone.monotone` from `Chap05.Proposition_5_24_4`;
- `SetRel.Monotone` from `Chap05.Definition_5_24_7`;
- `gradient_dual_moreau_envelope_is_primal_minimizer`,
  `gradient_primal_moreau_envelope_is_dual_minimizer`, and
  `primal_and_dual_moreau_minimizers_iff_euclidean` from
  `Chap06.Theorem_31_5`;
- `Maximal` from mathlib's order API.

Ambient-assumption minimization:
- `subdifferentialGraph_cyclicallyMonotone` uses only properness;
- the Moreau gradient-minimizer theorems already have the canonical `[CompleteSpace E]` owner
  layer;
- `primal_and_dual_moreau_minimizers_iff_euclidean` is the Euclidean bridge theorem needed for the
  graph-level argument here;
- finite dimensionality is therefore derived rather than primitive here, so the public theorem is
  stated directly on complete real inner-product spaces.

Layer target: `source-facing`, stated directly on the canonical relation graph of the
subdifferential.
-/

/-- Corollary 31.5.2: if `f` is a closed proper convex function on a complete real inner-product
space, then its self-pairing subdifferential graph `gph∂[E](f)` is maximal among monotone
relations. The finite-dimensional `R^n` source statement is recovered by specialization. This is
the canonical relation-level form of saying that `∂f` is a maximal monotone mapping. -/
theorem maximal_monotone_subdifferentialGraph
    (hf : IsClosedProperConvex[ℝ] f) :
    Maximal (·.Monotone ℝ) (gph∂[E](f)) := by
  have hgraphMon : (gph∂[E](f)).Monotone ℝ := by
    exact SetRel.CyclicallyMonotone.monotone
      (subdifferentialGraph_cyclicallyMonotone (Y := E) hf.proper)
  refine ⟨hgraphMon, ?_⟩
  intro ρ hρ hgraph_le_ρ p hp
  rcases p with ⟨y, yStar⟩
  let z := y + yStar
  let x := ∇ dualEnvelopeReal z
  let xStar := ∇ primalEnvelopeReal z
  have hxMin : IsMinOn (fun x : E ↦ f x + w (z - x)) Set.univ x := by
    simpa [x] using gradient_dual_moreau_envelope_is_primal_minimizer hf z
  have hxStarMin :
      IsMinOn (fun xStar : E ↦ fStar xStar + w (z - xStar)) Set.univ xStar := by
    simpa [xStar] using gradient_primal_moreau_envelope_is_dual_minimizer hf z
  have hdecomp : z = x + xStar ∧ xStar ∈ ∂ᵥf(x) :=
    (primal_and_dual_moreau_minimizers_iff_euclidean hf z x xStar).mp ⟨hxMin, hxStarMin⟩
  rcases hdecomp with ⟨hz, hxStar_mem⟩
  have hxGraphVec : x ~[Function.subdifferentialGraph f] xStar :=
    Function.mem_subdifferentialGraph.mpr hxStar_mem
  have hxGraph : x ~[gph∂[E](f)] xStar := by
    rw [_root_.mem_subdifferentialGraph, _root_.mem_subdifferentialAt_pairing]
    intro z
    have hinner :
        (inner ℝ xStar (z - x) : ℝ) =
          (HasLinearPairing.pairingLinear z xStar - HasLinearPairing.pairingLinear x xStar) := by
      calc
        (inner ℝ xStar (z - x) : ℝ) = inner ℝ xStar z - inner ℝ xStar x := by
          rw [inner_sub_right]
        _ = inner ℝ z xStar - inner ℝ x xStar := by
          simp [real_inner_comm]
        _ = (HasLinearPairing.pairingLinear z xStar - HasLinearPairing.pairingLinear x xStar) := by
          rfl
    simpa [hinner] using
      Function.mem_subdifferentialAt.mp (Function.mem_subdifferentialGraph.mp hxGraphVec) z
  have hxρ : x ~[ρ] xStar :=
    hgraph_le_ρ hxGraph
  have hnonneg : 0 ≤ (⟪y - x, yStar - xStar⟫ₚ : ℝ) :=
    hρ.pairing_nonneg hxρ hp
  have hsum : (y - x) + (yStar - xStar) = 0 := by
    have hz' : y + yStar = x + xStar := by
      simpa [z] using hz
    calc
      (y - x) + (yStar - xStar) = (y + yStar) - (x + xStar) := by abel
      _ = 0 := by rw [hz']; simp
  have hsub : yStar - xStar = -(y - x) := by
    calc
      yStar - xStar = -(y - x) + ((y - x) + (yStar - xStar)) := by abel
      _ = -(y - x) := by rw [hsum, add_zero]
  have hpair :
      (⟪y - x, yStar - xStar⟫ₚ : ℝ) = -‖y - x‖ ^ 2 := by
    change inner ℝ (y - x) (yStar - xStar) = -‖y - x‖ ^ 2
    rw [hsub, inner_neg_right, real_inner_self_eq_norm_sq]
  have hnorm_sq_le_zero : ‖y - x‖ ^ 2 ≤ 0 := by
    nlinarith [hnonneg, hpair]
  have hnorm_sq_zero : ‖y - x‖ ^ 2 = 0 :=
    le_antisymm hnorm_sq_le_zero (sq_nonneg ‖y - x‖)
  have hyx : y = x := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact sq_eq_zero_iff.mp hnorm_sq_zero
  have hyStarxStar : yStar = xStar := by
    have hz' : y + yStar = x + xStar := by
      simpa [z] using hz
    simpa [hyx] using hz'
  rw [hyx, hyStarxStar]
  exact hxGraph

end
