import Mathlib.Geometry.Manifold.SmoothEmbedding
import SmoothManifolds_Lee_2012.Chap04.Sec04_27.Problem_4_12

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so the statement
-- shapes were fixed from mathlib's `Manifold.IsSmoothEmbedding.of_opens` and the local torus
-- embedding theorem in `Problem_4_12`.

noncomputable section

open Manifold
open scoped Manifold ContDiff

universe uE uH uM

/- Recall for Example 4.17: the canonical mathlib theorem
`Manifold.IsSmoothEmbedding.of_opens` is exactly the statement that the inclusion of an open
submanifold `U ↪ M` is a smooth embedding. -/
#check Manifold.IsSmoothEmbedding.of_opens

section FiniteProductInclusions

variable {k : ℕ}
variable {E : Fin k → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
variable {H : Fin k → Type uH} [∀ i, TopologicalSpace (H i)]
variable {I : ∀ i, ModelWithCorners ℝ (E i) (H i)}
variable {M : Fin k → Type uM} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
variable [∀ i, IsManifold (I i) ∞ (M i)]
variable [IsManifold (ModelWithCorners.pi I) ∞ ((i : Fin k) → M i)]

/-- The inclusion of the `j`-th factor into a finite product of manifolds, obtained by freezing the
other coordinates at the chosen points `p i`. -/
def finite_product_inclusion (p : (i : Fin k) → M i) (j : Fin k) : M j → (i : Fin k) → M i :=
  fun q ↦ Function.update p j q

/-- Example 4.17 (1): fixing points in all but one factor, the inclusion of the remaining factor
into the finite product is a smooth embedding. -/
theorem finite_product_inclusion_isSmoothEmbedding
    (p : (i : Fin k) → M i) (j : Fin k) :
    IsSmoothEmbedding (I j) (ModelWithCorners.pi I) ∞ (finite_product_inclusion p j) := sorry

end FiniteProductInclusions

/-- The standard inclusion `ℝ^n ↪ ℝ^(n+k)` with trailing zero coordinates. -/
def euclidean_zero_tail_inclusion (n k : ℕ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + k)) :=
  fun x ↦ WithLp.toLp 2 (Fin.append x (fun _ : Fin k ↦ (0 : ℝ)))

/-- Example 4.17 (2): the map `ℝ^n ↪ ℝ^(n+k)` sending `(x¹, …, xⁿ)` to
`(x¹, …, xⁿ, 0, …, 0)` is a smooth embedding. -/
theorem euclidean_zero_tail_inclusion_isSmoothEmbedding (n k : ℕ) :
    IsSmoothEmbedding (𝓡 n) (𝓡 (n + k)) ∞ (euclidean_zero_tail_inclusion n k) := sorry

/- Recall for Example 4.17: `Problem_4_12` already proves that the
torus-of-revolution map descends to a smooth embedding `S¹ × S¹ ↪ ℝ³`. -/
#check torus_of_revolution_map_isSmoothEmbedding
