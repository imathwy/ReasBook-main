import Mathlib

namespace CauSeq

section

variable {α β : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv]

/-- Definition 1.2.2: an element `a` is a limit point of the Cauchy sequence `x` if `x` is
equivalent to the constant sequence with value `a`. -/
def HasLimitPoint (x : CauSeq β abv) (a : β) : Prop :=
  x ≈ const abv a

/- Definition 1.2.2: the textbook zero-sequence notion is the canonical owner `CauSeq.LimZero`. -/
#check (LimZero : CauSeq β abv → Prop)

/-- A Cauchy sequence is a zero sequence exactly when `0` is a limit point. -/
theorem hasLimitPoint_zero_iff_limZero (x : CauSeq β abv) :
    x.HasLimitPoint 0 ↔ LimZero x := by
  change LimZero (x - const abv 0) ↔ LimZero x
  simp [LimZero]

/-- A limit point is exactly a value that the Cauchy sequence approaches in the textbook
`ε`-`N` sense. -/
theorem hasLimitPoint_iff_eventually_abv_sub_lt (x : CauSeq β abv) (a : β) :
    x.HasLimitPoint a ↔ ∀ ε : α, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, abv (x n - a) < ε := by
  change LimZero (x - const abv a) ↔ _
  simp [LimZero]

end

section

variable {α β : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α}

/-- A Cauchy sequence is a zero sequence exactly when its terms are eventually arbitrarily close
to `0`. -/
theorem limZero_iff_eventually_abv_lt (x : CauSeq β abv) :
    LimZero x ↔ ∀ ε : α, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, abv (x n) < ε :=
  Iff.rfl

end

end CauSeq
