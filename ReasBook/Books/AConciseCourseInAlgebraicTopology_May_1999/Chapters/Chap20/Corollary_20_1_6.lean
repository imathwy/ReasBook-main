import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ComplexProjectiveSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_3_4

open scoped singularCohomology singularCochains

noncomputable section

-- Semantic recall via `lean_leansearch` surfaced no verified canonical integral `CP^n`
-- cohomology-ring presentation in the current environment. Chapter 9 fixes `CP^n` as
-- `ComplexProjectiveSpace n`, and Chapter 18 already supplies the canonical singular-cohomology
-- owner `Hˢ[q](TopCat.of (ComplexProjectiveSpace n); ℤ)`, its zero class, and cup-product
-- notation `⌣`, so the source statement is recorded directly on that surface by explicit
-- cup-product powers of a degree-`2` class, the vanishing of its `(n + 1)`st power, the
-- resulting even-degree generation, and odd-degree vanishing.

/-- The degree bookkeeping identity in the recursive definition of
`complexProjectiveSpaceIntegralCohomologyCupPower`. -/
theorem complexProjectiveSpaceIntegralCohomologyCupPower_degree_succ (q : ℕ) :
    2 * q + 2 = 2 * (q + 1) := by
  simp [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The `q`th cup-product power `α^q` of a degree-`2` class
`α ∈ Hˢ[2](TopCat.of (ComplexProjectiveSpace n); ℤ)`, viewed in degree `2 * q`. -/
def complexProjectiveSpaceIntegralCohomologyCupPower
    (n : ℕ) : ∀ q : ℕ,
      Hˢ[2](TopCat.of (ComplexProjectiveSpace n); ℤ) →
        Hˢ[2 * q](TopCat.of (ComplexProjectiveSpace n); ℤ)
  | 0, _ => singularCohomologyOneClass ℤ (TopCat.of (ComplexProjectiveSpace n))
  | q + 1, α =>
      singularCohomologyClasses.reindex ℤ (TopCat.of (ComplexProjectiveSpace n))
        (complexProjectiveSpaceIntegralCohomologyCupPower_degree_succ q)
        (complexProjectiveSpaceIntegralCohomologyCupPower n q α ⌣ α)

/-- The `0`th cup-product power is the cohomological unit class. -/
theorem complexProjectiveSpaceIntegralCohomologyCupPower_zero
    (n : ℕ) (α : Hˢ[2](TopCat.of (ComplexProjectiveSpace n); ℤ)) :
    complexProjectiveSpaceIntegralCohomologyCupPower n 0 α =
      singularCohomologyOneClass ℤ (TopCat.of (ComplexProjectiveSpace n)) :=
  rfl

/-- The successor cup-product power is obtained by cupping the previous power with `α` and
reindexing along the canonical degree equality `2 * q + 2 = 2 * (q + 1)`. -/
theorem complexProjectiveSpaceIntegralCohomologyCupPower_succ
    (n q : ℕ) (α : Hˢ[2](TopCat.of (ComplexProjectiveSpace n); ℤ)) :
    complexProjectiveSpaceIntegralCohomologyCupPower n (q + 1) α =
      singularCohomologyClasses.reindex ℤ (TopCat.of (ComplexProjectiveSpace n))
        (complexProjectiveSpaceIntegralCohomologyCupPower_degree_succ q)
        (complexProjectiveSpaceIntegralCohomologyCupPower n q α ⌣ α) :=
  rfl

/-- A degree-`2` class `α ∈ H²(CP^n; ℤ)` gives the truncated-polynomial presentation of
`H^*(CP^n; ℤ)` when every even-degree class up to degree `2 * n` is a unique integer multiple of
the corresponding cup-product power `α^q`, every even-degree class above degree `2 * n` is zero,
the relation `α^(n + 1) = 0` holds, and the odd-degree cohomology is zero. -/
def IsComplexProjectiveSpaceIntegralCohomologyTruncatedPolynomialPresentation
    (n : ℕ) (α : Hˢ[2](TopCat.of (ComplexProjectiveSpace n); ℤ)) : Prop :=
  let X := TopCat.of (ComplexProjectiveSpace n)
  (∀ q : ℕ, q ≤ n →
    ∀ β : Hˢ[2 * q](X; ℤ),
      ∃! m : ℤ,
        β =
          singularCohomologyClassZsmul ℤ X (2 * q) m
            (complexProjectiveSpaceIntegralCohomologyCupPower n q α)) ∧
    (∀ q : ℕ, n < q →
      ∀ β : Hˢ[2 * q](X; ℤ),
        β = singularCohomologyZeroClass ℤ X (2 * q)) ∧
    complexProjectiveSpaceIntegralCohomologyCupPower n (n + 1) α =
      singularCohomologyZeroClass ℤ X (2 * (n + 1)) ∧
    (∀ q : ℕ, ∀ β : Hˢ[2 * q + 1](X; ℤ),
      β = singularCohomologyZeroClass ℤ X (2 * q + 1))

/-- Unfolding
`IsComplexProjectiveSpaceIntegralCohomologyTruncatedPolynomialPresentation` gives the degreewise
generation, vanishing, and relation clauses on
`Hˢ[q](TopCat.of (ComplexProjectiveSpace n); ℤ)`. -/
theorem isComplexProjectiveSpaceIntegralCohomologyTruncatedPolynomialPresentation_iff
    (n : ℕ) (α : Hˢ[2](TopCat.of (ComplexProjectiveSpace n); ℤ)) :
    let X := TopCat.of (ComplexProjectiveSpace n)
    IsComplexProjectiveSpaceIntegralCohomologyTruncatedPolynomialPresentation n α ↔
      (∀ q : ℕ, q ≤ n →
        ∀ β : Hˢ[2 * q](X; ℤ),
          ∃! m : ℤ,
            β =
              singularCohomologyClassZsmul ℤ X (2 * q) m
                (complexProjectiveSpaceIntegralCohomologyCupPower n q α)) ∧
        (∀ q : ℕ, n < q →
          ∀ β : Hˢ[2 * q](X; ℤ),
            β = singularCohomologyZeroClass ℤ X (2 * q)) ∧
        complexProjectiveSpaceIntegralCohomologyCupPower n (n + 1) α =
          singularCohomologyZeroClass ℤ X (2 * (n + 1)) ∧
        (∀ q : ℕ, ∀ β : Hˢ[2 * q + 1](X; ℤ),
          β = singularCohomologyZeroClass ℤ X (2 * q + 1)) :=
  Iff.rfl

/-- Corollary 20.1.6. The integral cohomology ring `H^*(CP^n; ℤ)` is `ℤ[α] / (α^(n + 1))` with
`|α| = 2`. On the Chapter 18 singular-cohomology owner
`Hˢ[q](TopCat.of (ComplexProjectiveSpace n); ℤ)`, this is recorded as the existence of a degree-`2`
class `α` whose cup-product powers generate each even degree up to `2 * n` over `ℤ`, whose
even-degree cohomology groups above degree `2 * n` vanish, whose `(n + 1)`st power vanishes, and
whose odd-degree integral cohomology groups are zero. -/
theorem complexProjectiveSpace_integralCohomology_truncatedPolynomialPresentation
    (n : ℕ) :
    ∃ α : Hˢ[2](TopCat.of (ComplexProjectiveSpace n); ℤ),
      IsComplexProjectiveSpaceIntegralCohomologyTruncatedPolynomialPresentation n α := sorry
