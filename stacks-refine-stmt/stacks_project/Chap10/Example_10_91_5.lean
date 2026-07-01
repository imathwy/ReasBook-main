import Mathlib
import stacks_project.Chap10.Definition_10_84_1
import stacks_project.Chap10.Definition_10_88_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: if `M` were Mittag-Leffler, then the countably generated module `M` would be a
-- direct sum of countably generated submodules in the trivial one-summand way. Theorem `10.93.3`
-- would then imply that `M` is projective, contradicting `hproj`.
/-- Example 10.91.5: any flat countably generated non-projective `R`-module is not
Mittag-Leffler. This is the criterion used in the example to manufacture explicit
counterexamples. -/
theorem not_mittagLeffler_of_flat_of_countablyGenerated_of_not_projective
    [Flat R M] (hcg : CountablyGenerated R M) (hproj : ¬ Projective R M) :
    ¬ MittagLeffler R M := sorry

-- Proof sketch: Proposition `10.89.5` identifies the Mittag-Leffler condition with injectivity of
-- all tensor-product-to-product maps, while Example `10.89.1` exhibits a specific family
-- `Q_n = ℤ / nℤ` for which the corresponding map for `ℚ` is not injective.
/-- The `ℤ`-module `ℚ` is not Mittag-Leffler. -/
theorem rat_not_mittagLeffler :
    ¬ MittagLeffler ℤ ℚ := sorry

end

section

variable (k : Type u) [Field k]

/-- The quotient `k[[x]] / (x^n)` viewed as a `k[[x]]`-module. -/
abbrev powerSeriesQuotientByXPow (n : ℕ+) :=
  PowerSeries k ⧸ Ideal.span ({(PowerSeries.X : PowerSeries k) ^ (n : ℕ)} : Set (PowerSeries k))

/-- The product `∏_{n ≥ 1} k[[x]] / (x^n)` from the power-series example. -/
abbrev powerSeriesQuotientProduct :=
  (n : ℕ+) → powerSeriesQuotientByXPow k n

/-- The `x`-adic ideal of `k[[x]]`. -/
abbrev powerSeriesXIdeal : Ideal (PowerSeries k) :=
  Ideal.span ({(PowerSeries.X : PowerSeries k)} : Set (PowerSeries k))

/-- The direct sum `⨁_{n ≥ 1} k[[x]] / (x^n)` used before taking `x`-adic completion. -/
abbrev powerSeriesQuotientDirectSum :=
  Π₀ n : ℕ+, powerSeriesQuotientByXPow k n

/-- The `x`-adic completion of `⨁_{n ≥ 1} k[[x]] / (x^n)`. -/
abbrev powerSeriesQuotientDirectSumCompletion :=
  AdicCompletion (powerSeriesXIdeal k) (powerSeriesQuotientDirectSum k)

-- Proof sketch: use the element `ξ` supported at powers of two from the textbook. Its
-- annihilator in `(∏ n, R/(x^n)) / x^l` behaves like `x^(l / 2)` along powers of two, which is
-- incompatible with the annihilator growth permitted by Proposition `10.88.6 (1)` for a
-- Mittag-Leffler module.
/-- The product `∏_{n ≥ 1} k[[x]] / (x^n)` is not Mittag-Leffler over `k[[x]]`. -/
theorem powerSeriesQuotientProduct_not_mittagLeffler :
    ¬ MittagLeffler (PowerSeries k) (powerSeriesQuotientProduct k) := sorry

-- Proof sketch: the same annihilator calculation applies because the element `ξ` from the
-- textbook actually lies in the `x`-adic completion of the direct sum, so the previous
-- contradiction with Proposition `10.88.6 (1)` still goes through.
/-- The `x`-adic completion of `⨁_{n ≥ 1} k[[x]] / (x^n)` is not Mittag-Leffler over `k[[x]]`. -/
theorem powerSeriesQuotientDirectSumCompletion_not_mittagLeffler :
    ¬ MittagLeffler (PowerSeries k) (powerSeriesQuotientDirectSumCompletion k) := sorry

/-- The square-zero quotient ring `k[a, b] / (a^2, ab, b^2)` of the final example. -/
abbrev squareZeroPairRing :=
  MvPolynomial (Fin 2) k ⧸
    Ideal.span
      ({(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2,
        (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1,
        (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ^ 2} : Set (MvPolynomial (Fin 2) k))

/-- The class of `a` in `k[a, b] / (a^2, ab, b^2)`. -/
abbrev squareZeroPairRingA : squareZeroPairRing k :=
  Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The class of `b` in `k[a, b] / (a^2, ab, b^2)`. -/
abbrev squareZeroPairRingB : squareZeroPairRing k :=
  Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The finitely presented algebra `R[t] / (at - b)` over `R = k[a, b] / (a^2, ab, b^2)`. -/
abbrev squareZeroPairAlgebra :=
  Polynomial (squareZeroPairRing k) ⧸
    Ideal.span
      ({Polynomial.C (squareZeroPairRingA k) * Polynomial.X - Polynomial.C (squareZeroPairRingB k)} :
        Set (Polynomial (squareZeroPairRing k)))

local instance squareZeroPairRingCommRing : CommRing (squareZeroPairRing k) :=
  show CommRing (squareZeroPairRing k) from Ideal.Quotient.commRing _

local instance squareZeroPairAlgebraCommRing : CommRing (squareZeroPairAlgebra k) :=
  show CommRing (squareZeroPairAlgebra k) from Ideal.Quotient.commRing _

local instance squareZeroPairAlgebraAlgebra : Algebra (squareZeroPairRing k) (squareZeroPairAlgebra k) :=
  show Algebra (squareZeroPairRing k) (squareZeroPairAlgebra k) from Ideal.instAlgebraQuotient _ _

local instance squareZeroPairAlgebraModule : Module (squareZeroPairRing k) (squareZeroPairAlgebra k) :=
  (algebraMap (squareZeroPairRing k) (squareZeroPairAlgebra k)).toModule

-- Proof sketch: the quotient `R[t] / (at - b)` is generated by the powers of `t`, so it is
-- countably generated as an `R`-module.
/-- The algebra `R[t] / (at - b)` is countably generated as an `R`-module. -/
theorem squareZeroPairAlgebra_countablyGenerated :
    CountablyGenerated (squareZeroPairRing k) (squareZeroPairAlgebra k) := sorry

-- Proof sketch: the ring `squareZeroPairRing k` is Artinian local and hence henselian. If
-- `squareZeroPairAlgebra k` were Mittag-Leffler, Lemma `10.153.13` would split it as a direct sum
-- of finitely presented modules. The textbook notes that this module is indecomposable, so such a
-- decomposition is impossible.
/-- The algebra `R[t] / (at - b)` is not Mittag-Leffler as an `R`-module for
`R = k[a, b] / (a^2, ab, b^2)`. -/
theorem squareZeroPairAlgebra_not_mittagLeffler :
    ¬ MittagLeffler (squareZeroPairRing k) (squareZeroPairAlgebra k) := sorry

end

end Module
