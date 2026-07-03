import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_16_17 (from Items/Chap16) -/
open MeasureTheory ProbabilityTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The canonical truncation function `x ↦ x 1_{|x| < 1}` used in the real
Lévy--Khinchin formula. -/
def levyKhinchinCanonicalCentering (x : ℝ) : ℝ :=
  if |x| < 1 then x else 0

/-- The Lévy--Khinchin exponent written with an arbitrary centering function `f`. -/
def levyKhinchinExponentWithCentering (σ2 b : ℝ) (ν : Measure ℝ) (f : ℝ → ℝ) : ℝ → ℂ :=
  fun t ↦
    (((-(σ2 / 2) * t ^ (2 : ℕ) : ℝ) : ℂ)) +
      (((b * t : ℝ) : ℂ) * Complex.I) +
      ∫ x : ℝ,
        (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
          (((t * f x : ℝ) : ℂ) * Complex.I)) ∂ν

/-- The Lévy--Khinchin exponent associated with a triple `(σ², b, ν)`. -/
def levyKhinchinExponent (τ : LevyKhinchinTriple) : ℝ → ℂ :=
  levyKhinchinExponentWithCentering τ.sigma2 τ.b τ.ν levyKhinchinCanonicalCentering

/-- A triple gives a Lévy--Khinchin representation of `μ` when it is canonical and the
characteristic function of `μ` is the exponential of its Lévy--Khinchin exponent. -/
def HasLevyKhinchinRepresentation
    (μ : ProbabilityMeasure ℝ) (τ : LevyKhinchinTriple) : Prop :=
  IsCanonicalTriple τ ∧
    ∀ t : ℝ, charFun μ t = Complex.exp (levyKhinchinExponent τ t)

namespace HasLevyKhinchinRepresentation

/-- A Lévy--Khinchin representation is, in particular, canonical. -/
theorem isCanonicalTriple
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    IsCanonicalTriple τ :=
  hτ.1

/-- A Lévy--Khinchin representation identifies the characteristic function with the exponential of
the associated exponent. -/
theorem charFun_eq_exp
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
    (hτ : HasLevyKhinchinRepresentation μ τ) (t : ℝ) :
    charFun μ t = Complex.exp (levyKhinchinExponent τ t) :=
  hτ.2 t

end HasLevyKhinchinRepresentation

-- Proof sketch: for the forward direction, use the existence part of the Lévy--Khinchin formula
-- to construct a canonical triple whose exponent realizes the characteristic function of `μ` as
-- `t ↦ exp (ψ(t))`. For the reverse direction, the displayed identity gives a canonical
-- characteristic-function representation, hence infinite divisibility. Uniqueness follows by the
-- standard argument recovering `σ²`, then `ν`, and finally `b` from the exponent.
/-- Theorem 16.17: a probability measure on `ℝ` is infinitely divisible if and only if its
characteristic function admits a unique Lévy--Khinchin representation by a canonical triple
`(σ², b, ν)`; equivalently, `charFun μ = exp ∘ levyKhinchinExponent τ`. Here `ν` is the Lévy
measure, `σ²` the Gaussian coefficient, and `b` the centering constant. -/
theorem isInfinitelyDivisible_iff_exists_unique_levyKhinchin_triple
    (μ : ProbabilityMeasure ℝ) :
    IsInfinitelyDivisible μ ↔
      ∃! τ : LevyKhinchinTriple, HasLevyKhinchinRepresentation μ τ := sorry

end MeasureTheory.ProbabilityMeasure
