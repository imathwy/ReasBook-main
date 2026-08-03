module

public import Topology_Munkres_2000.Book.Theorem_27_4
public import Mathlib.Topology.Algebra.Ring.Real

public section

/-- Remark 27.1. The extreme value theorem for a continuous real-valued function on
a nonempty closed interval. -/
theorem extremeValueTheoremOnIcc {a b : ℝ} (hab : a ≤ b) (f : Set.Icc a b → ℝ)
    (hf : Continuous f) :
    ∃ c d : Set.Icc a b, ∀ x : Set.Icc a b, f c ≤ f x ∧ f x ≤ f d := by
  -- The endpoint inequality supplies the nonemptiness required by the compact-space theorem.
  letI : Nonempty (Set.Icc a b) := Set.nonempty_Icc_subtype hab
  -- Specialize the general extreme value theorem to the compact interval and codomain `ℝ`.
  exact extremeValueTheorem f hf
