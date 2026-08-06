import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_5_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_5_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_5_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open FundamentalGroup

/-- The standard loop class `standardLoopClass 1` generates `π₁(S¹, 1)`. -/
theorem standardLoopClass_one_zpowers_eq_top :
    Subgroup.zpowers (standardLoopClass 1 : FundamentalGroup Circle 1) = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun γ ↦ ?_
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨circleFundamentalGroupLiftIndex γ, ?_⟩
  apply circleFundamentalGroupLiftIndex_injective
  rw [standardLoopClass_one_zpow, circleFundamentalGroupLiftIndex_standardLoop]

instance : Infinite (FundamentalGroup Circle 1) := by
  have hstandardLoopClass : Function.Injective standardLoopClass := by
    intro m n h
    have hindex := congrArg circleFundamentalGroupLiftIndex h
    change
      circleFundamentalGroupLiftIndex (standardLoopClass m) =
        circleFundamentalGroupLiftIndex (standardLoopClass n) at hindex
    rwa [circleFundamentalGroupLiftIndex_standardLoop, circleFundamentalGroupLiftIndex_standardLoop]
      at hindex
  exact Infinite.of_injective standardLoopClass hstandardLoopClass

/-- Theorem 1.5.11: the standard generator `standardLoopClass 1` identifies `π₁(S¹, 1)` with
`Multiplicative ℤ` via the canonical infinite-cyclic equivalence. -/
noncomputable abbrev circleFundamentalGroupMulEquivInt :
    Multiplicative ℤ ≃* FundamentalGroup Circle (1 : Circle) :=
  intEquivOfZPowersEqTop (standardLoopClass 1) standardLoopClass_one_zpowers_eq_top

/-- Under `circleFundamentalGroupMulEquivInt`, the integer `n` corresponds to the standard loop
class of winding number `n`. -/
@[simp] theorem circleFundamentalGroupMulEquivInt_apply (n : ℤ) :
    circleFundamentalGroupMulEquivInt (Multiplicative.ofAdd n) = standardLoopClass n := by
  rw [circleFundamentalGroupMulEquivInt]
  rw [intEquivOfZPowersEqTop_apply]
  exact standardLoopClass_one_zpow n
