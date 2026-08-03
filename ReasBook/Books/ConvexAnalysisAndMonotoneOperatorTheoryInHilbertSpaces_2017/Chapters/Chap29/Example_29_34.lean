import BauschkeLean.Chap24.Example_24_25
import BauschkeLean.Chap29.Example_29_28

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators EuclideanSpace Pointwise

-- Semantic recall: `lean_leansearch` surfaced `stdSimplex ℝ (Fin N)` as the canonical simplex
-- owner. This item keeps the source shift map `t ↦ ∑ i, max {x i + t, 0}` explicit and uses the
-- source-facing set `{ξ ∈ ℝ^N | (∀ i, 0 ≤ ξ i) ∧ ∑ i, ξ i = β}` directly on `EuclideanSpace`,
-- with a bridge identifying the positive-mass case with the scaled canonical simplex.

noncomputable section

section

variable {N : ℕ}

/-- The shift function `t ↦ ∑ i, max {x i + t, 0}` used in the simplex projection formula. -/
def simplexProjectionShiftFunction (x : EuclideanSpace ℝ (Fin N)) : ℝ → ℝ :=
  fun t ↦ ∑ i, max (x i + t) 0

/-- The coordinatewise clipped vector `(max {x i + s, 0})_i` attached to a shift `s`. -/
def simplexProjectionPositivePart (x : EuclideanSpace ℝ (Fin N)) (s : ℝ) :
    EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm <| fun i ↦ max (x i + s) 0

/-- Coordinatewise form of `simplexProjectionPositivePart`. -/
@[simp] theorem simplexProjectionPositivePart_apply
    (x : EuclideanSpace ℝ (Fin N)) (s : ℝ) (i : Fin N) :
    simplexProjectionPositivePart x s i = max (x i + s) 0 := by
  simp [simplexProjectionPositivePart]

/-- The source simplex `{ξ ∈ ℝ^N | (∀ i, 0 ≤ ξ i) ∧ ∑ i, ξ i = β}`. -/
def nonnegativeCoordinateSimplex (β : ℝ) : Set (EuclideanSpace ℝ (Fin N)) :=
  {ξ | (∀ i, 0 ≤ ξ i) ∧ ∑ i, ξ i = β}

/-- Membership in the source simplex is the coordinatewise nonnegativity and mass constraint. -/
@[simp] theorem mem_nonnegativeCoordinateSimplex {β : ℝ} {ξ : EuclideanSpace ℝ (Fin N)} :
    ξ ∈ nonnegativeCoordinateSimplex β ↔ (∀ i, 0 ≤ ξ i) ∧ ∑ i, ξ i = β :=
  Iff.rfl

/-- For positive mass `β`, the Euclidean-space coordinates of the source simplex are exactly the
scaled standard simplex. -/
theorem mem_nonnegativeCoordinateSimplex_iff_mem_smul_stdSimplex {β : ℝ} (hβ : 0 < β)
    {ξ : EuclideanSpace ℝ (Fin N)} :
    ξ ∈ nonnegativeCoordinateSimplex β ↔
      EuclideanSpace.equiv (Fin N) ℝ ξ ∈
        β • (stdSimplex ℝ (Fin N) : Set (Fin N → ℝ)) := by
  sorry

/-- The nonnegative coordinate simplex of mass `β` is Chebyshev when `N` and `β` are positive. -/
theorem isChebyshev_nonnegativeCoordinateSimplex (hN : 0 < N) (β : ℝ) (hβ : 0 < β) :
    IsChebyshev (nonnegativeCoordinateSimplex β : Set (EuclideanSpace ℝ (Fin N))) := sorry

/-- Example 29.34 (1): for `x ∈ ℝ^N`, the shift function
`t ↦ ∑ i, max {x i + t, 0}` is continuous. -/
theorem continuous_simplexProjectionShiftFunction (x : EuclideanSpace ℝ (Fin N)) :
    Continuous (simplexProjectionShiftFunction x) := sorry

/-- Example 29.34 (2): for `x ∈ ℝ^N`, the shift function
`t ↦ ∑ i, max {x i + t, 0}` is increasing. -/
theorem monotone_simplexProjectionShiftFunction (x : EuclideanSpace ℝ (Fin N)) :
    Monotone (simplexProjectionShiftFunction x) := sorry

section

variable (hN : 0 < N) (β : ℝ) (hβ : 0 < β)

local notation "Cβ" => (nonnegativeCoordinateSimplex β : Set (EuclideanSpace ℝ (Fin N)))
local notation "coordinateMax" =>
  sum_k_largest_coordinates 1 (Nat.succ_le_of_lt hN)

/-- Example 29.34 (3): if `N` is positive and `β ∈ ℝ_{++}`, then for every `x ∈ ℝ^N` there exists
a unique real `s` such that `∑ i, max {x i + s, 0} = β`. -/
theorem existsUnique_simplexProjectionShift_eq
    (x : EuclideanSpace ℝ (Fin N)) :
    ∃! s : ℝ, simplexProjectionShiftFunction x s = β := sorry

/-- Example 29.34 (4): if `C = {ξ ∈ ℝ^N | (∀ i, 0 ≤ ξ i) ∧ ∑ i, ξ i = β}` and if `s` satisfies
`∑ i, max {x i + s, 0} = β`, then the metric projection of `x` onto `C` is the clipped vector
`(max {x i + s, 0})_i`. -/
theorem projectionPoint_nonnegativeCoordinateSimplex_eq_simplexProjectionPositivePart_of_shift_eq
    (x : EuclideanSpace ℝ (Fin N)) {s : ℝ}
    (hs : simplexProjectionShiftFunction x s = β) :
    P[Cβ, isChebyshev_nonnegativeCoordinateSimplex hN β hβ] x =
      simplexProjectionPositivePart x s := sorry

/-- Example 29.34 (5): if `s` satisfies `∑ i, max {x i + s, 0} = β` and
`coordinateMax = sum_k_largest_coordinates 1 (Nat.succ_le_of_lt hN)`, so that
`coordinateMax x = max_i x i`, then `s ∈ ]-coordinateMax x, β - coordinateMax x]`. -/
theorem simplexProjectionShift_mem_Ioc_coordinateMax_of_shift_eq
    (x : EuclideanSpace ℝ (Fin N)) {s : ℝ}
    (hs : simplexProjectionShiftFunction x s = β) :
    s ∈ Set.Ioc (-coordinateMax x) (β - coordinateMax x) := sorry

end

end

end
