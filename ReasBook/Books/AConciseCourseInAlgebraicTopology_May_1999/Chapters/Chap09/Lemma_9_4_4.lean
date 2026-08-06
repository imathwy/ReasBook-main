import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Analysis.Complex.Circle
import Books.AConciseCourseInAlgebraicTopology_May_1999.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Theorem_1_5_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology Topology.Homotopy

-- Semantic recall via `lean_leansearch`: the canonical owner is `π_ n X x`,
-- the shared repository bridge `HomotopyGroup.pi1MulEquivFundamentalGroup` for `π₁`, and the
-- circle-specific computation `FundamentalGroup Circle 1 ≃* Multiplicative ℤ` via
-- `circleFundamentalGroupMulEquivInt.symm`, and
-- records vanishing homotopy groups by `Subsingleton`.

-- Canonical bridge for the first clause: `HomotopyGroup.pi1MulEquivFundamentalGroup` identifies
-- `π_ 1` with the fundamental group multiplicatively, and the local circle computation identifies
-- `FundamentalGroup Circle 1` with `Multiplicative ℤ`.
#check
  (HomotopyGroup.pi1MulEquivFundamentalGroup (1 : Circle) :
    π_ 1 Circle (1 : Circle) ≃* FundamentalGroup Circle 1)
#check
  (circleFundamentalGroupMulEquivInt :
    Multiplicative ℤ ≃* FundamentalGroup Circle (1 : Circle))

/-- Lemma 9.4.4 (1): the first homotopy group `π_ 1(S¹)` is infinite cyclic. -/
noncomputable def circle_pi1_mulEquiv_int :
    π_ 1 Circle (1 : Circle) ≃* Multiplicative ℤ :=
  (HomotopyGroup.pi1MulEquivFundamentalGroup (1 : Circle)).trans
    circleFundamentalGroupMulEquivInt.symm

/-- Evaluating `circle_pi1_mulEquiv_int` on the `π₁`-class of the standard loop recovers the
corresponding integer. -/
theorem circle_pi1_mulEquiv_int_apply_pi1EquivFundamentalGroup_symm_standardLoopClass (n : ℤ) :
    circle_pi1_mulEquiv_int
        (HomotopyGroup.pi1EquivFundamentalGroup.symm (standardLoopClass n)) =
      Multiplicative.ofAdd n := by
  change circleFundamentalGroupMulEquivInt.symm (standardLoopClass n) = Multiplicative.ofAdd n
  apply circleFundamentalGroupMulEquivInt.injective
  rw [MulEquiv.apply_symm_apply, circleFundamentalGroupMulEquivInt_apply]

/-- Lemma 9.4.4 (2): every homotopy group `π_ n(S¹)` with `n ≠ 1` is trivial. -/
instance circleHomotopyGroupSubsingleton {n : ℕ} [Fact (n ≠ 1)] (x : Circle) :
    Subsingleton (π_ n Circle x) := by
  sorry

/-- Companion form of `circleHomotopyGroupSubsingleton` with the inequality supplied explicitly. -/
theorem circleHomotopyGroupSubsingletonOfNeOne {n : ℕ} (hn : n ≠ 1) (x : Circle) :
    Subsingleton (π_ n Circle x) := by
  let _ : Fact (n ≠ 1) := ⟨hn⟩
  infer_instance
