import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.RealProjectiveSpace

noncomputable section

/-- The induced homomorphism `π₁(RP^m, x) → π₁(RP^n, f x)` is nontrivial exactly when it sends
some loop class to a nonidentity element. -/
theorem realProjectiveSpace_nontrivial_fundamentalGroupMapAtPoint_iff
    {m n : ℕ} (f : C(RealProjectiveSpace m, RealProjectiveSpace n))
    (x : RealProjectiveSpace m) :
    FundamentalGroup.map f x ≠ 1 ↔
      ∃ γ : FundamentalGroup (RealProjectiveSpace m) x, FundamentalGroup.map f x γ ≠ 1 := by
  simp [DFunLike.ne_iff]

/-- If the induced homomorphism `π₁(RP^m, x) → π₁(RP^n, f x)` is nontrivial, then the source
dimension does not exceed the target dimension. -/
theorem realProjectiveSpace_le_of_nontrivial_fundamentalGroupMapAtPoint
    {m n : ℕ} (f : C(RealProjectiveSpace m, RealProjectiveSpace n))
    (x : RealProjectiveSpace m)
    (h_nontrivial : FundamentalGroup.map f x ≠ 1) :
    m ≤ n := sorry

/-- If `f` induces a nontrivial map on `π₁` at some basepoint, then it sends some loop class at
that basepoint to a nonidentity element. -/
theorem realProjectiveSpace_nontrivial_fundamentalGroupMap_iff
    {m n : ℕ} (f : C(RealProjectiveSpace m, RealProjectiveSpace n)) :
    (∃ x : RealProjectiveSpace m, FundamentalGroup.map f x ≠ 1) ↔
      ∃ x : RealProjectiveSpace m,
        ∃ γ : FundamentalGroup (RealProjectiveSpace m) x, FundamentalGroup.map f x γ ≠ 1 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (realProjectiveSpace_nontrivial_fundamentalGroupMapAtPoint_iff f x).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (realProjectiveSpace_nontrivial_fundamentalGroupMapAtPoint_iff f x).mpr hx⟩

/-- Proposition 18.4.2. If `f : RP^m → RP^n` induces a nontrivial map on `π₁`, then `m ≤ n`. -/
theorem realProjectiveSpace_le_of_nontrivial_fundamentalGroupMap
    {m n : ℕ} (f : C(RealProjectiveSpace m, RealProjectiveSpace n))
    (h_nontrivial : ∃ x : RealProjectiveSpace m, FundamentalGroup.map f x ≠ 1) :
    m ≤ n := sorry
