import BauschkeLean.Chap24.Example_24_25
import BauschkeLean.Chap29.Example_29_28

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall: Example 29.27 is the probability-simplex specialization of the
-- support-function/projection identity, and Chapter 24 already provides the canonical
-- coordinate-max owner `Function.toEReal (sum_k_largest_coordinates 1 hN)`.

noncomputable section

open ERealFunction

section

variable {N : ℕ}

section

variable (N) (hN : 0 < N)

local notation "Δ" => stdSimplex ℝ (Fin N)
local notation "P_Δ" => P[Δ, isChebyshev_stdSimplex_fin N hN]
local notation "coordinateMax" =>
  Function.toEReal (sum_k_largest_coordinates 1 (Nat.succ_le_of_lt hN))
local notation "hcoordinateMax" =>
  sum_k_largest_coordinates_one_toEReal_mem_gammaZero (Nat.succ_le_of_lt hN)

/-- Example 29.27 (Probability simplex): if `Δ = stdSimplex ℝ (Fin N)` and
`coordinateMax = Function.toEReal (sum_k_largest_coordinates 1 (Nat.succ_le_of_lt hN))`, then
the metric projection onto `Δ` is given pointwise by `P_Δ x = x - Prox_coordinateMax x`. This
uses the Chapter 24 coordinate-max owner directly instead of a duplicate local wrapper. -/
theorem projectionPoint_stdSimplex_eq_sub_prox_coordinateMax
    (x : EuclideanSpace ℝ (Fin N)) :
    P_Δ x = x - Prox[coordinateMax, hcoordinateMax] x := by
  sorry

end

end
