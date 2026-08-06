import Mathlib.Algebra.BigOperators.Ring.Finset
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Construction_16_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Construction_18_3_2

open scoped BigOperators TensorProduct singularCochains

noncomputable section

universe u

-- Construction 18.2.2 already fixes `singularCochainComplex R X` as the canonical cochain-complex
-- owner. This file keeps the source-facing simplexwise coboundary surface by transporting that
-- differential across the degreewise identification from Construction 18.3.2 and records the
-- alternating-face formula using the established face-operator owner from Construction 16.1.4.

/-- The singular-cochain coboundary `δ : C^n(X; R) → C^(n + 1)(X; R)` obtained by transporting
the canonical differential on `singularCochainComplex R X` to the source-facing simplexwise
cochain model. -/
noncomputable def singularCochainCoboundary (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    singularCochains R X n →ₗ[R] singularCochains R X (n + 1) :=
  (singularCochainComplexDegreeEquiv R X (n + 1)).toLinearMap.comp
    (((singularCochainComplex R X).d n (n + 1)).hom.comp
      (singularCochainComplexDegreeEquiv R X n).symm.toLinearMap)

namespace singularCochains

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {n : ℕ}

/-- The singular-cochain coboundary operator `δ` on the source-facing simplexwise cochain model. -/
abbrev coboundary (φ : singularCochains R X n) : singularCochains R X (n + 1) :=
  singularCochainCoboundary R X n φ

scoped[singularCochains] prefix:max "δ " => singularCochains.coboundary

end singularCochains

open scoped singularCochains

/-- `singularCochainCoboundary` is the degree-`n` differential of
`singularCochainComplex R X`, transported to the simplexwise cochain model. -/
theorem singularCochainCoboundary_eq_differential
    (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) (φ : singularCochains R X n) :
    δ φ =
      singularCochainComplexDegreeEquiv R X (n + 1)
        (((singularCochainComplex R X).d n (n + 1))
          ((singularCochainComplexDegreeEquiv R X n).symm φ)) :=
  rfl

/-- Evaluating `singularCochainCoboundary` on a singular simplex gives the usual alternating sum
over its codimension-one faces. -/
theorem singularCochainCoboundary_apply (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ)
    (φ : singularCochains R X n) (σ : singularSimplex (n + 1) X) :
    (δ φ) σ =
      ∑ i : Fin (n + 2), (-1 : R) ^ i.1 * φ (singularFaceOperator n i X σ) := sorry

/-- Proposition 18.3.3. The singular-cochain coboundary satisfies the graded Leibniz rule with
respect to the cup product from Construction 18.3.2. -/
theorem singularCochainCoboundary_cup (R : Type u) [CommRing R] (X : TopCat.{u})
    (p q : ℕ) (φ : singularCochains R X p) (ψ : singularCochains R X q) :
    δ (φ ⌣ ψ) =
      (cast (by rw [Nat.add_assoc, Nat.one_add, Nat.add_assoc])
        ((δ φ) ⌣ ψ) :
        singularCochains R X (p + q + 1)) +
      (cast (by rw [Nat.add_assoc])
        (((-1 : R) ^ p) •
          (φ ⌣ δ ψ)) :
        singularCochains R X (p + q + 1)) := sorry
