

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_19 (from Chap01/Sec01_03) -/
-- Semantic search note: `lean_leansearch` was unavailable here.
-- Local repo search reused `IsRegularCoordinateBall` from Definition 1.3-extra-1.

open Set TopologicalSpace
open scoped Manifold

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [T2Space M] [SecondCountableTopology M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

-- Proof sketch: start from the countable basis of precompact coordinate balls from Lemma 1.10 and,
-- inside each chosen chart, translate and rescale the Euclidean ball so that the given basis
-- element becomes a concentric ball with compact closure contained in a larger chart ball.
/-- A set of subsets of a manifold that is a countable topological basis consisting of regular
coordinate balls. -/
class IsCountableRegularCoordinateBallBasis (b : Set (Set M)) : Prop where
  countable : b.Countable
  isTopologicalBasis : IsTopologicalBasis b
  regular : ∀ s ∈ b, IsRegularCoordinateBall (EuclideanSpace ℝ (Fin n)) s

/-- Proposition 1.19: every smooth manifold has a countable basis of regular coordinate balls. -/
theorem exists_countable_regular_coordinate_ball_basis :
    ∃ b : Set (Set M), @IsCountableRegularCoordinateBallBasis n M _ _ _ b := sorry
