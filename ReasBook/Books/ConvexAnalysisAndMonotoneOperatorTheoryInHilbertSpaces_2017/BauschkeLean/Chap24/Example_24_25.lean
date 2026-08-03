import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap24.Example_24_64
import BauschkeLean.Chap24.Proposition_24_58

namespace ERealFunction

noncomputable section

open scoped BigOperators EuclideanRearrangement

-- Semantic recall/local precedent: `lean_leansearch` mainly surfaced generic simplex material,
-- while the source statement here depends on the local finite-coordinate owners
-- `euclideanNonincreasingRearrangement`, `permuteCoordVec`, `sum_k_largest_coordinates`, and
-- `Prox`.

/-- Specializing the Chapter 24 owner `sum_k_largest_coordinates` to `k = 1` recovers the
maximum coordinate map from Example 24.25. -/
theorem sum_k_largest_coordinates_one_eq_iSup {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (Fin N)) :
    sum_k_largest_coordinates 1 hN x = ⨆ i : Fin N, x i := sorry

/-- The `Set.Ioi (⊥ : EReal)` packaging of the `k = 1` coordinate-sum owner belongs to
`Γ₀(ℝ^N)`. -/
theorem sum_k_largest_coordinates_one_toEReal_mem_gammaZero {N : ℕ} (hN : 1 ≤ N) :
    (sum_k_largest_coordinates 1 hN).toEReal ∈
      Γ₀(EuclideanSpace ℝ (Fin N)) := sorry

/-- Helper: the prefix averages from formula `(24.21)`, indexed on `Fin N` so that
`example_24_25_eta ξ i` is the textbook quantity `η_(i+1)`. -/
def example_24_25_eta {N : ℕ} (ξ : Fin N → ℝ) (i : Fin N) : ℝ :=
  (((-1 : ℝ) + Finset.sum (Finset.Iic i) ξ) / (i.1 + 1) : ℝ)

/-- Helper: the ordered stopping test from `(24.22)`. For `i < N - 1` this is the strict
inequality `η_(i+1) > ξ_(i+2)`, while for the final index it is `η_N ≤ ξ_N`. -/
def example_24_25_cutCondition {N : ℕ} (ξ : Fin N → ℝ) (i : Fin N) : Prop :=
  if h : i.1 + 1 < N then
    example_24_25_eta ξ i > ξ ⟨i.1 + 1, h⟩
  else
    example_24_25_eta ξ i ≤ ξ i

/-- Helper: the sorted candidate vector from formula `(24.23)`, with the first `n + 1`
coordinates equal to `η_(n+1)` and the remaining coordinates unchanged. -/
def example_24_25_candidate {N : ℕ} (ξ : Fin N → ℝ) (n : Fin N) :
    EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm
    (fun j : Fin N ↦ if j ≤ n then example_24_25_eta ξ n else ξ j)

/-- Evaluating `example_24_25_candidate` exposes the prefix-constant/suffix-original form from
`(24.23)` coordinatewise. -/
@[simp] theorem example_24_25_candidate_apply {N : ℕ} (ξ : Fin N → ℝ)
    (n j : Fin N) :
    example_24_25_candidate ξ n j =
      if j ≤ n then example_24_25_eta ξ n else ξ j := rfl

section CoordinateMax

variable {N : ℕ} (hN : 1 ≤ N)

local notation "coordinateMax" => Function.toEReal (sum_k_largest_coordinates 1 hN)

/-- The proximal map of the coordinate-max function commutes with coordinate permutations. -/
theorem prox_coordinate_max_eq_permuteCoordVec
    (hcoordinateMax : coordinateMax ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    Prox[coordinateMax, hcoordinateMax] (permuteCoordVec σ x) =
      permuteCoordVec σ (Prox[coordinateMax, hcoordinateMax] x) := sorry

/-- Example 24.25 (1): let `x↓` be the nonincreasing rearrangement of `x`, let
`η_(i+1) = (-1 + ∑_{k=0}^i ξ_k) / (i + 1)`, and let `n` be the least index in the ordered list
`η₁ > ξ₂, η₂ > ξ₃, ..., η_(N-1) > ξ_N, η_N ≤ ξ_N`. Then
`Prox_f x↓ = [η_n, ..., η_n, ξ_(n+1), ..., ξ_N]^T`. -/
theorem example_24_25_sorted_prox_eq_prefixAverage_block
    (hcoordinateMax : coordinateMax ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (x : EuclideanSpace ℝ (Fin N)) (n : Fin N)
    (hn :
      IsLeast {i : Fin N | example_24_25_cutCondition x↓ i} n) :
    Prox[coordinateMax, hcoordinateMax] x↓ = example_24_25_candidate x↓ n := sorry

/-- Example 24.25 (2): if the permutation matrix `P` is represented by `σ` with
`permuteCoordVec σ x = x↓`, then the unsorted proximal point is obtained by applying `Pᵀ`,
i.e. by the inverse coordinate permutation, to the sorted proximal point. -/
theorem example_24_25_prox_eq_inverse_permute_sorted_prox
    (hcoordinateMax : coordinateMax ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (x : EuclideanSpace ℝ (Fin N)) (σ : Equiv.Perm (Fin N))
    (hσ : permuteCoordVec σ x = x↓) :
    Prox[coordinateMax, hcoordinateMax] x =
      permuteCoordVec σ.symm (Prox[coordinateMax, hcoordinateMax] x↓) := by
  have hprox := prox_coordinate_max_eq_permuteCoordVec hN hcoordinateMax σ x
  rw [hσ] at hprox
  ext i
  have hcoord := congrArg (fun y : EuclideanSpace ℝ (Fin N) ↦ y (σ i)) hprox
  simpa [permuteCoordVec] using hcoord.symm

end CoordinateMax

end

end ERealFunction
