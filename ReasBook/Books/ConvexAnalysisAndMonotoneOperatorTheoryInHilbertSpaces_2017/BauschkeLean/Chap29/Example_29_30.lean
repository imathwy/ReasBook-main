import Mathlib.Topology.Algebra.Module.WeakDual
import BauschkeLean.Chap06.Example_6_29

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Topology

noncomputable section

universe u

section

variable {I : Type u}

local notation "P_K" =>
  P[l2PositiveOrthant I,
    isChebyshev_of_nonempty_isClosed_convex
      l2PositiveOrthant_nonempty
      l2PositiveOrthant_isClosed
      l2PositiveOrthant_convex]

/- Example 29.30 (1): in `ℓ²(I, ℝ)` with `K = ℓ²₊(I)`, the metric projection onto `K` is the
coordinatewise positive part, i.e. `P_K(ξᵢ)ᵢ = (max {ξᵢ, 0})ᵢ`. -/
#check projectionPoint_l2PositiveOrthant_eq_positivePart

/-- Example 29.30 (2), canonical form: the positive-part map on `ℓ²(I, ℝ)` is weakly
sequentially continuous. -/
theorem l2PositivePart_tendsto_toWeakSpace
    {xSeq : ℕ → ℓ²(I, ℝ)} {x : ℓ²(I, ℝ)}
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ (ℓ²(I, ℝ)) (xSeq n)) atTop
      (𝓝 (toWeakSpace ℝ (ℓ²(I, ℝ)) x))) :
    Tendsto (fun n ↦ toWeakSpace ℝ (ℓ²(I, ℝ)) (l2PositivePart (xSeq n))) atTop
      (𝓝 (toWeakSpace ℝ (ℓ²(I, ℝ)) (l2PositivePart x))) := by
  sorry

/-- Example 29.30 (2): in `ℓ²(I, ℝ)` with `K = ℓ²₊(I)`, weak convergence of a sequence implies weak
convergence of its projected sequence under the metric projection onto `K`. -/
  theorem l2PositiveOrthant_projection_tendsto_toWeakSpace
      {xSeq : ℕ → ℓ²(I, ℝ)} {x : ℓ²(I, ℝ)}
      (hx : Tendsto (fun n ↦ toWeakSpace ℝ (ℓ²(I, ℝ)) (xSeq n)) atTop
        (𝓝 (toWeakSpace ℝ (ℓ²(I, ℝ)) x))) :
      Tendsto (fun n ↦ toWeakSpace ℝ (ℓ²(I, ℝ)) (P_K (xSeq n))) atTop
        (𝓝 (toWeakSpace ℝ (ℓ²(I, ℝ)) (P_K x))) := by
    simpa [projectionPoint_l2PositiveOrthant_eq_positivePart] using
    l2PositivePart_tendsto_toWeakSpace hx

end
