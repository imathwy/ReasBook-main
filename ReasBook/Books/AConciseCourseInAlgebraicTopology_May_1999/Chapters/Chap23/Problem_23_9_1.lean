import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.RingTheory.Polynomial.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.RealProjectiveSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_3_1

open scoped BigOperators Manifold

noncomputable section

-- The Chapter 23 source-facing owner for `w(RP^q)` is the Stiefel-Whitney family evaluated on
-- the canonical tangent bundle of `RealProjectiveSpace q`. The polynomial model is kept only as a
-- Chapter 20 bridge for the usual `ZMod 2[α] / (α^(q + 1))` presentation.

/-- The standard polynomial representative of `w(RP^q)` in the Chapter 20 presentation
`H^*(RP^q; ZMod 2) ≃ (ZMod 2)[X] / (X^(q + 1))`, obtained by keeping only the degrees `0, …, q`
from the binomial expansion of `(1 + X)^(q + 1)`. -/
def realProjectiveSpaceTotalStiefelWhitneyRepresentative (q : ℕ) : Polynomial (ZMod 2) :=
  ∑ i ∈ Finset.range (q + 1),
    Polynomial.monomial i ((q + 1).choose i : ZMod 2)

/-- The coefficient of `X^i` in the standard representative of `w(RP^q)` is the binomial
coefficient `((q + 1).choose i : ZMod 2)` for `i ≤ q`, and it vanishes in higher degrees. -/
theorem realProjectiveSpaceTotalStiefelWhitneyRepresentative_coeff
    (q i : ℕ) :
    (realProjectiveSpaceTotalStiefelWhitneyRepresentative q).coeff i =
      if i ≤ q then ((q + 1).choose i : ZMod 2) else 0 := sorry

section

variable (q : ℕ)
variable [ChartedSpace (EuclideanSpace ℝ (Fin q)) (RealProjectiveSpace q)]
variable [IsManifold (𝓡 q) ⊤ (RealProjectiveSpace q)]
variable
  [TopologicalSpace
    (Bundle.TotalSpace
      (Fin q → ℝ) (TangentSpace (𝓡 q) : TopCat.of (RealProjectiveSpace q) → Type _))]
variable
  [FiberBundle
    (Fin q → ℝ) (TangentSpace (𝓡 q) : TopCat.of (RealProjectiveSpace q) → Type _)]
variable
  [VectorBundle
    ℝ (Fin q → ℝ) (TangentSpace (𝓡 q) : TopCat.of (RealProjectiveSpace q) → Type _)]

/-- `RP^q` has trivial total Stiefel-Whitney class when all of its positive-degree tangential
Stiefel-Whitney classes vanish. The degree-zero term is omitted because every
`IsStiefelWhitneyTheory` identifies it with the unit class. -/
def realProjectiveSpaceHasTrivialTotalStiefelWhitneyClass
    (H2 : ModTwoCohomologyTheory) (w : StiefelWhitneyClassFamily H2) : Prop :=
  ∀ i : ℕ, 0 < i →
    (w q i).onFamily (TangentSpace (𝓡 q) : RealProjectiveSpace q → Type _) = 0

/-- In the standard Chapter 20 polynomial presentation of `H^*(RP^q; ZMod 2)`, triviality of the
tangential total Stiefel-Whitney class is equivalent to the polynomial representative being `1`.
This theorem is the bridge from the Chapter 23 tangent-bundle owner to the polynomial model. -/
theorem realProjectiveSpaceHasTrivialTotalStiefelWhitneyClass_iff_representative_eq_one
    (H2 : ModTwoCohomologyTheory) (normalizationData : StiefelWhitneyNormalization H2)
    (w : StiefelWhitneyClassFamily H2)
    (h_stiefelWhitney : IsStiefelWhitneyTheory H2 normalizationData w) :
    realProjectiveSpaceHasTrivialTotalStiefelWhitneyClass q H2 w ↔
      realProjectiveSpaceTotalStiefelWhitneyRepresentative q = 1 := sorry

/-- In the standard Chapter 20 polynomial presentation, the polynomial representative of
`w(RP^q)` is `1` exactly when `q = 2^k - 1`. -/
theorem realProjectiveSpaceTotalStiefelWhitneyRepresentative_eq_one_iff (q : ℕ) :
    realProjectiveSpaceTotalStiefelWhitneyRepresentative q = 1 ↔
      ∃ k : ℕ, q = 2 ^ k - 1 := sorry

/-- Problem 23.9.1. The total tangential Stiefel-Whitney class `w(RP^q)` is trivial exactly when
`q = 2^k - 1`. This source-facing statement is recorded on the Chapter 23 tangent-bundle owner
and bridged separately to the Chapter 20 polynomial presentation. -/
theorem realProjectiveSpaceHasTrivialTotalStiefelWhitneyClass_iff
    (H2 : ModTwoCohomologyTheory) (normalizationData : StiefelWhitneyNormalization H2)
    (w : StiefelWhitneyClassFamily H2)
    (h_stiefelWhitney : IsStiefelWhitneyTheory H2 normalizationData w) :
    realProjectiveSpaceHasTrivialTotalStiefelWhitneyClass q H2 w ↔
      ∃ k : ℕ, q = 2 ^ k - 1 := by
  exact
    (realProjectiveSpaceHasTrivialTotalStiefelWhitneyClass_iff_representative_eq_one
      q H2 normalizationData w h_stiefelWhitney).trans
      (realProjectiveSpaceTotalStiefelWhitneyRepresentative_eq_one_iff q)

end
