module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

public section

/-- Example 52.1 (1): Euclidean `n`-space has trivial fundamental group. -/
theorem fundamentalGroup_euclideanSpace (n : ℕ) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Subsingleton (FundamentalGroup (EuclideanSpace ℝ (Fin n)) x₀) := by
  -- Euclidean space is contractible, hence simply connected, so its loop classes are unique.
  infer_instance

namespace Convex

/-- Every convex subset of a real topological vector space has trivial fundamental group at
each basepoint. -/
theorem subsingleton_fundamentalGroup {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] {X : Set E}
    (hX : Convex ℝ X) (x₀ : X) : Subsingleton (FundamentalGroup X x₀) := by
  -- The chosen basepoint supplies the nonemptiness needed for the convex contraction.
  have hXNonempty : X.Nonempty := ⟨x₀, x₀.property⟩
  letI : ContractibleSpace X := hX.contractibleSpace hXNonempty
  -- Contractibility now gives simple connectedness and the fundamental-group subsingleton instance.
  infer_instance

end Convex

/-- Example 52.1 (2): Every convex subset of Euclidean `n`-space has trivial fundamental
group. -/
theorem fundamentalGroup_convexSubset (n : ℕ) {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : Convex ℝ X) (x₀ : X) : Subsingleton (FundamentalGroup X x₀) := by
  -- Apply the general convex-subset contraction result in Euclidean space.
  exact hX.subsingleton_fundamentalGroup x₀

/-- Example 52.1 (3): The closed unit ball in Euclidean `n`-space has trivial fundamental
group. -/
theorem fundamentalGroup_closedUnitBall (n : ℕ)
    (x₀ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Subsingleton
      (FundamentalGroup (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) x₀) := by
  -- The closed unit ball is convex, so the general convex-subset result applies.
  exact (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).subsingleton_fundamentalGroup x₀
