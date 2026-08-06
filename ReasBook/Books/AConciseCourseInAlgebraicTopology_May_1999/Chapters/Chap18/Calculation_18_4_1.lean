import Mathlib.Data.ZMod.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.RealProjectiveSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_3_4

open scoped singularCohomology

noncomputable section

/-- The degree-`q` mod-`2` singular cohomology of `RP^n`. -/
abbrev realProjectiveSpaceModTwoCohomology (n q : ℕ) :=
  Hˢ[q](TopCat.of (RealProjectiveSpace n); ZMod 2)

/-- The `q`th cup-product power of a degree-one class in mod-`2` cohomology of `RP^n`. -/
def realProjectiveSpaceModTwoCohomologyCupPower
    (n : ℕ) : ∀ q : ℕ,
      realProjectiveSpaceModTwoCohomology n 1 →
        realProjectiveSpaceModTwoCohomology n q
  | 0, _ => singularCohomologyOneClass (ZMod 2) (TopCat.of (RealProjectiveSpace n))
  | q + 1, α => realProjectiveSpaceModTwoCohomologyCupPower n q α ⌣ α

/-- The source-facing cup-power notation `α ^ q` for degree-one mod-`2` cohomology classes on
`RP^n`, with `n` inferred from the type of `α`. -/
scoped[RealProjectiveSpaceModTwoCohomology] notation:80 α:81 " ^ " q:80 =>
  realProjectiveSpaceModTwoCohomologyCupPower _ q α

open scoped RealProjectiveSpaceModTwoCohomology

/-- The `0`th cup-product power is the cohomological unit class. -/
theorem realProjectiveSpaceModTwoCohomologyCupPower_zero
    (n : ℕ) (α : realProjectiveSpaceModTwoCohomology n 1) :
    realProjectiveSpaceModTwoCohomologyCupPower n 0 α =
      singularCohomologyOneClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) :=
  rfl

/-- The successor cup-product power is obtained by cupping the previous power with `α`. -/
theorem realProjectiveSpaceModTwoCohomologyCupPower_succ
    (n q : ℕ) (α : realProjectiveSpaceModTwoCohomology n 1) :
    α ^ (q + 1) = (α ^ q) ⌣ α :=
  rfl

/-- `α ^ q` is the unique nonzero degree-`q` mod-`2` cohomology class on `RP^n`. -/
def realProjectiveSpaceModTwoCupPowerIsUniqueNonzero
    (n q : ℕ) (α : realProjectiveSpaceModTwoCohomology n 1) : Prop :=
  α ^ q ≠ singularCohomologyZeroClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) q ∧
    ∀ β : realProjectiveSpaceModTwoCohomology n q,
      β = singularCohomologyZeroClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) q ∨
        β = α ^ q

/-- Unfolding `realProjectiveSpaceModTwoCupPowerIsUniqueNonzero` gives the nonzero-and-uniqueness
criterion for the cup-product power `α ^ q`. -/
theorem realProjectiveSpaceModTwoCupPowerIsUniqueNonzero_iff
    (n q : ℕ) (α : realProjectiveSpaceModTwoCohomology n 1) :
    realProjectiveSpaceModTwoCupPowerIsUniqueNonzero n q α ↔
      α ^ q ≠ singularCohomologyZeroClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) q ∧
        ∀ β : realProjectiveSpaceModTwoCohomology n q,
          β = singularCohomologyZeroClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) q ∨
            β = α ^ q :=
  Iff.rfl

/-- If `α ^ q` is the unique nonzero degree-`q` class, then `α ^ q` itself is nonzero. -/
theorem realProjectiveSpaceModTwoCupPowerIsUniqueNonzero_nonzero
    {n q : ℕ} {α : realProjectiveSpaceModTwoCohomology n 1}
    (hα : realProjectiveSpaceModTwoCupPowerIsUniqueNonzero n q α) :
    α ^ q ≠ singularCohomologyZeroClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) q :=
  hα.1

/-- If `α ^ q` is the unique nonzero degree-`q` class, then every degree-`q` class is either `0`
or `α ^ q`. -/
theorem realProjectiveSpaceModTwoCupPowerIsUniqueNonzero_eq_zero_or_eq
    {n q : ℕ} {α : realProjectiveSpaceModTwoCohomology n 1}
    (hα : realProjectiveSpaceModTwoCupPowerIsUniqueNonzero n q α)
    (β : realProjectiveSpaceModTwoCohomology n q) :
    β = singularCohomologyZeroClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) q ∨
      β = α ^ q :=
  hα.2 β

/-- A degree-one class `α` gives the truncated-polynomial presentation of
`Hˢ[∗](RP^n; ZMod 2)` when `α ^ q` is the unique nonzero degree-`q` class for every `q ≤ n` and
all degree-`q` classes vanish for `q > n`. -/
def IsRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation
    (n : ℕ) (α : realProjectiveSpaceModTwoCohomology n 1) : Prop :=
  (∀ q, q ≤ n → realProjectiveSpaceModTwoCupPowerIsUniqueNonzero n q α) ∧
    ∀ q, n < q → ∀ β : realProjectiveSpaceModTwoCohomology n q,
      β = singularCohomologyZeroClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) q

/-- Unfolding `IsRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation` gives the
degreewise uniqueness of the nonzero cup-product powers up to degree `n` and the vanishing of all
higher-degree classes. -/
theorem isRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation_iff
    (n : ℕ) (α : realProjectiveSpaceModTwoCohomology n 1) :
    IsRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation n α ↔
      (∀ q, q ≤ n → realProjectiveSpaceModTwoCupPowerIsUniqueNonzero n q α) ∧
        ∀ q, n < q → ∀ β : realProjectiveSpaceModTwoCohomology n q,
          β = singularCohomologyZeroClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) q :=
  Iff.rfl

/-- In the truncated-polynomial presentation, `α ^ q` is the unique nonzero degree-`q` class for
every `q ≤ n`. -/
theorem isRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation_uniqueNonzero
    {n : ℕ} {α : realProjectiveSpaceModTwoCohomology n 1}
    (hα : IsRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation n α)
    {q : ℕ} (hq : q ≤ n) :
    realProjectiveSpaceModTwoCupPowerIsUniqueNonzero n q α :=
  hα.1 q hq

/-- In the truncated-polynomial presentation, every degree-`q` class with `q ≤ n` is either `0`
or `α ^ q`. -/
theorem isRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation_eq_zero_or_eq_cupPower
    {n : ℕ} {α : realProjectiveSpaceModTwoCohomology n 1}
    (hα : IsRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation n α)
    {q : ℕ} (hq : q ≤ n) (β : realProjectiveSpaceModTwoCohomology n q) :
    β = singularCohomologyZeroClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) q ∨
      β = α ^ q :=
  realProjectiveSpaceModTwoCupPowerIsUniqueNonzero_eq_zero_or_eq (hα.1 q hq) β

/-- In the truncated-polynomial presentation, every degree-`q` class with `q > n` vanishes. -/
theorem isRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation_eq_zero
    {n : ℕ} {α : realProjectiveSpaceModTwoCohomology n 1}
    (hα : IsRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation n α)
    {q : ℕ} (hq : n < q) (β : realProjectiveSpaceModTwoCohomology n q) :
    β = singularCohomologyZeroClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) q :=
  hα.2 q hq β

/-- In the truncated-polynomial presentation, `α ^ q = 0` in every degree `q > n`. -/
theorem isRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation_cupPower_eq_zero
    {n q : ℕ} {α : realProjectiveSpaceModTwoCohomology n 1}
    (hα : IsRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation n α)
    (hq : n < q) :
    α ^ q = singularCohomologyZeroClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) q :=
  hα.2 q hq (α ^ q)

/-- A degree-one class `α` generates the mod-`2` cohomology ring of `RP^n` when every degree-`q`
class is either `0` or the cup-product power `α ^ q`. -/
def realProjectiveSpaceModTwoCohomologyRingGeneratedByDegreeOne
    (n : ℕ) (α : realProjectiveSpaceModTwoCohomology n 1) : Prop :=
  ∀ q (β : realProjectiveSpaceModTwoCohomology n q),
    β = singularCohomologyZeroClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) q ∨
      β = α ^ q

/-- Unfolding `realProjectiveSpaceModTwoCohomologyRingGeneratedByDegreeOne` gives the degreewise
generation criterion by cup-product powers of a degree-one class. -/
theorem realProjectiveSpaceModTwoCohomologyRingGeneratedByDegreeOne_iff
    (n : ℕ) (α : realProjectiveSpaceModTwoCohomology n 1) :
    realProjectiveSpaceModTwoCohomologyRingGeneratedByDegreeOne n α ↔
      ∀ q (β : realProjectiveSpaceModTwoCohomology n q),
        β = singularCohomologyZeroClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) q ∨
          β = α ^ q :=
  Iff.rfl

/-- If `α` generates `Hˢ[∗](RP^n; ZMod 2)`, then every degree-`q` class is either `0` or `α ^ q`.
-/
theorem realProjectiveSpaceModTwoCohomologyRingGeneratedByDegreeOne_eq_zero_or_eq_cupPower
    {n : ℕ} {α : realProjectiveSpaceModTwoCohomology n 1}
    (hα : realProjectiveSpaceModTwoCohomologyRingGeneratedByDegreeOne n α)
    (q : ℕ) (β : realProjectiveSpaceModTwoCohomology n q) :
    β = singularCohomologyZeroClass (ZMod 2) (TopCat.of (RealProjectiveSpace n)) q ∨
      β = α ^ q :=
  hα q β

/-- A truncated-polynomial presentation gives degree-one generation of
`Hˢ[∗](RP^n; ZMod 2)`. -/
theorem IsRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation.generatedByDegreeOne
    {n : ℕ} {α : realProjectiveSpaceModTwoCohomology n 1}
    (hα : IsRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation n α) :
    realProjectiveSpaceModTwoCohomologyRingGeneratedByDegreeOne n α := by
  intro q β
  by_cases hq : q ≤ n
  · exact
      isRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation_eq_zero_or_eq_cupPower
        hα hq β
  · left
    exact
      isRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation_eq_zero hα
        (Nat.lt_of_not_ge hq) β

/-- Calculation 18.4.1. The mod-`2` cohomology ring of `RP^n` is generated by a degree-one class:
there is `α ∈ Hˢ[1](RP^n; ZMod 2)` whose cup-product powers are the unique nonzero classes in
degrees `q ≤ n`, while all cohomology classes in degrees `q > n` vanish. This is the local
degreewise form of the truncated-polynomial presentation. -/
theorem realProjectiveSpace_modTwoCohomologyRing_generatedByDegreeOne (n : ℕ) :
    ∃ α : realProjectiveSpaceModTwoCohomology n 1,
      IsRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation n α := sorry
