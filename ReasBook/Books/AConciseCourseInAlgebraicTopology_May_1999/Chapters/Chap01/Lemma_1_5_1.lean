import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The fundamental group of `ℝ` is trivial at every basepoint. -/
theorem fundamental_group_real_subsingleton (x : ℝ) :
    Subsingleton (FundamentalGroup ℝ x) := by
  change Subsingleton (Path.Homotopic.Quotient x x)
  infer_instance

/-- Lemma 1.5.1: the fundamental group of `ℝ` based at `0` is trivial. -/
-- Proof sketch: contract `ℝ` to `0` by the straight-line homotopy `(s, t) ↦ (1 - t) * s`,
-- obtain that `ℝ` is contractible and hence simply connected, and then identify the
-- fundamental group at `0` as a subsingleton loop-class group.
theorem fundamental_group_real_zero_subsingleton :
    Subsingleton (FundamentalGroup ℝ 0) :=
  fundamental_group_real_subsingleton 0

/-- Every element of the fundamental group of `ℝ` is the identity. -/
theorem fundamental_group_real_eq_one (x : ℝ) (γ : FundamentalGroup ℝ x) :
    γ = 1 :=
  (fundamental_group_real_subsingleton x).elim γ 1

/-- Every element of the fundamental group of `ℝ` at `0` is the identity. -/
-- Proof sketch: apply the subsingleton statement for `FundamentalGroup ℝ 0` and compare any
-- element with the unit element.
theorem fundamental_group_real_zero_eq_one (γ : FundamentalGroup ℝ 0) :
    γ = 1 :=
  fundamental_group_real_eq_one 0 γ
