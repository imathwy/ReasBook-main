import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz
import BauschkeLean.Chap24.Proposition_24_60

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- Semantic recall/local precedent: `lean_leansearch` only surfaced generic convex-max and
-- Lipschitz APIs, so this item follows the local Chapter 24 ambient owner
-- `SquareMatrixSpace`, the canonical ordered eigenvalue owner
-- `Matrix.IsHermitian.eigenvalues₀`, and the explicit subset-max coordinate model `(24.125)`.

/-- The subset sum appearing in formula `(24.125)` for a chosen `k`-element index set. -/
private def coordinate_subset_sum {N : ℕ}
    (x : EuclideanSpace ℝ (Fin N)) (J : Finset (Fin N)) : ℝ :=
  J.sum fun i ↦ (EuclideanSpace.equiv (Fin N) ℝ x) i

/-- The function `φ` from `(24.125)`: the maximum of the coordinate sums over all `k`-element
subsets of `Fin N`. -/
def sum_k_largest_coordinates {N : ℕ} (k : ℕ) (hk : k ≤ N)
    (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  let subsets : Finset (Finset (Fin N)) := Finset.univ.powersetCard k
  let hsubsets : subsets.Nonempty := by
    have hk' : k ≤ (Finset.univ : Finset (Fin N)).card := by
      simpa using hk
    simpa [subsets] using
      (Finset.powersetCard_nonempty.2 hk' : (Finset.univ.powersetCard k).Nonempty)
  (subsets.image (coordinate_subset_sum x)).max' (hsubsets.image _)

/-- The coordinate-max model `(24.125)` is invariant under coordinate permutations. -/
theorem sum_k_largest_coordinates_coordinatePermutationInvariant
    {N : ℕ} (k : ℕ) (hk : k ≤ N) :
    CoordinatePermutationInvariant (sum_k_largest_coordinates k hk) := sorry

/-- The source function `A ↦ ∑_{i=1}^k λᵢ(A)`, represented on the ambient Euclidean model of
real symmetric matrices and extended by `0` off the symmetric locus. -/
def sum_k_largest_eigenvalues {N : ℕ} (k : ℕ) (hk : k ≤ N)
    (x : SquareMatrixSpace N) : ℝ :=
  let A := euclideanToMatrix x
  if hA : A.IsHermitian then
    let hk' : k ≤ Fintype.card (Fin N) := by
      simpa using hk
    Finset.univ.sum fun i : Fin k ↦ hA.eigenvalues₀ (i.castLE hk')
  else
    0

/-- On the symmetric-matrix locus, `sum_k_largest_eigenvalues` is the coordinate-max model
`(24.125)` evaluated at the canonical ordered eigenvalue vector. -/
theorem sum_k_largest_eigenvalues_eq_sum_k_largest_coordinates
    {N : ℕ} (k : ℕ) (hk : k ≤ N) {x : SquareMatrixSpace N}
    (hx : (euclideanToMatrix x).IsHermitian) :
    sum_k_largest_eigenvalues k hk x =
      sum_k_largest_coordinates k hk (symmetricMatrixEigenvalues hx) := sorry

/-- Example 24.64 (1): for `k ≤ N`, the map
`A ↦ ∑_{i=1}^k λᵢ(A)` is convex on the real symmetric-matrix locus, represented in the ambient
Euclidean matrix model. -/
theorem sum_k_largest_eigenvalues_convexOn
    {N : ℕ} {k : ℕ} (hk : k ≤ N) :
    _root_.ConvexOn ℝ
      (symmetricMatrixLocus N)
      (sum_k_largest_eigenvalues k hk) := sorry

/-- Example 24.64 (2): for `k ≤ N`, the map
`A ↦ ∑_{i=1}^k λᵢ(A)` is Lipschitz continuous with constant `√k` on the real symmetric-matrix
locus, represented in the ambient Euclidean matrix model. -/
theorem sum_k_largest_eigenvalues_lipschitzOnWith
    {N : ℕ} {k : ℕ} (hk : k ≤ N) :
    LipschitzOnWith (Real.toNNReal (Real.sqrt k))
      (sum_k_largest_eigenvalues k hk)
      (symmetricMatrixLocus N) := sorry
