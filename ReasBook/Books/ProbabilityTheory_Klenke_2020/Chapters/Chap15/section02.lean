import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_15_2_1 (from Items/Chap15) -/
open MeasureTheory BoundedContinuousFunction

variable {d : ℕ}

/-- The phase-one set for the characteristic-function kernel at frequency `t`; equivalently, the
points `x` with `⟪x, t⟫ ∈ 2πℤ`. -/
def charFunPeriodSet (t : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | Complex.exp (inner ℝ x t * Complex.I) = 1}

/-- Membership in `charFunPeriodSet t` means that the owner Fourier kernel `innerProbChar t`
takes the value `1`. -/
@[simp]
theorem mem_charFunPeriodSet_iff_innerProbChar_eq_one {t x : EuclideanSpace ℝ (Fin d)} :
    x ∈ charFunPeriodSet t ↔ innerProbChar t x = 1 := by
  simp [charFunPeriodSet, innerProbChar_apply]

-- Proof sketch: apply `Complex.exp_eq_one_iff` to the purely imaginary number
-- `inner ℝ x t * Complex.I`, then compare real and imaginary parts.
/-- Membership in `charFunPeriodSet t` is equivalent to the phase `⟪x, t⟫` being an integral
multiple of `2π`. -/
theorem mem_charFunPeriodSet_iff_exists_int {t x : EuclideanSpace ℝ (Fin d)} :
    x ∈ charFunPeriodSet t ↔ ∃ z : ℤ, inner ℝ x t = (2 * Real.pi : ℝ) * z := sorry

-- Proof sketch: decompose `x` into its component orthogonal to `t` plus its projection onto the
-- line spanned by `t`. For `t ≠ 0`, the scalar coordinate along `t` is an integer multiple of
-- `2π / ‖t‖²` exactly when `x ∈ charFunPeriodSet t`.
/-- For `t ≠ 0`, the period set `charFunPeriodSet t` is the union of affine hyperplanes
orthogonal to `t`, translated by integer multiples of `((2π) / ‖t‖²) t`. -/
theorem charFunPeriodSet_eq_orthogonal_translate_set {t : EuclideanSpace ℝ (Fin d)} (ht : t ≠ 0) :
    charFunPeriodSet t =
      {x | ∃ y : EuclideanSpace ℝ (Fin d), ∃ z : ℤ,
        inner ℝ y t = 0 ∧ x = y + z • (((2 * Real.pi) / ‖t‖ ^ 2) • t)} := sorry

variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]

-- Proof sketch: rewrite `charFun μ t = 1` as equality in the triangle inequality
-- for the unit-modulus integrand `x ↦ exp (i \langle x, t \rangle)`, deduce that this integrand
-- is `1` almost everywhere, and translate that condition to `x ∈ charFunPeriodSet t`.
/-- Exercise 15.2.1 (1): if the characteristic function of a probability law on `ℝ^d` takes the
value `1` at frequency `t`, then the law is supported on `H_t = charFunPeriodSet t`. -/
theorem measure_charFunPeriodSet_eq_one_of_charFun_eq_one {t : EuclideanSpace ℝ (Fin d)}
    (hφ : charFun μ t = 1) :
    μ (charFunPeriodSet t) = 1 := sorry

-- Proof sketch: use the support statement above to see that `exp (i \langle x, t \rangle) = 1`
-- for `μ`-almost every `x`, then factor the integrand defining `charFun μ (t + s)`
-- as `exp (i \langle x, s \rangle) * exp (i \langle x, t \rangle)` and simplify almost
-- everywhere.
/-- Exercise 15.2.1 (2): if the characteristic function equals `1` at frequency `t`, then it is
periodic in the direction `t`, so `φ(t + s) = φ(s)` for every `s`. -/
theorem charFun_periodic_of_charFun_eq_one {t : EuclideanSpace ℝ (Fin d)}
    (hφ : charFun μ t = 1) :
    Function.Periodic (charFun μ) t := sorry

/-- Exercise 15.2.1 (2): if the characteristic function equals `1` at frequency `t`, then it is
periodic in the direction `t`, so `φ(t + s) = φ(s)` for every `s`. -/
theorem charFun_add_eq_of_charFun_eq_one {t : EuclideanSpace ℝ (Fin d)}
    (hφ : charFun μ t = 1) (s : EuclideanSpace ℝ (Fin d)) :
    charFun μ (t + s) = charFun μ s := by
  simpa [add_comm] using charFun_periodic_of_charFun_eq_one hφ s

/-! ### Exercise_15_2_2 (from Items/Chap15) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

universe u

noncomputable section

/- Exercise 15.2.2 is `source-facing`: the public item is the existence statement. The relevant
owner abstractions are the canonical mathlib notions `PMF`, `IdentDistrib`, and `IndepFun`. The
finite-support data below stay private; they only record a concrete witness built from a
non-product coupling on `Fin 4 × Fin 4` whose row sums, column sums, and anti-diagonal sums agree
with the uniform product law. -/

private def sameSumCounterexampleWeight : (Fin 4 × Fin 4) → ℝ≥0
  | (0, 0) => 1 / 16
  | (0, 1) => 1 / 32
  | (0, 2) => 3 / 32
  | (0, 3) => 1 / 16
  | (1, 0) => 3 / 32
  | (1, 1) => 1 / 16
  | (1, 2) => 1 / 32
  | (1, 3) => 1 / 16
  | (2, 0) => 1 / 32
  | (2, 1) => 3 / 32
  | (2, 2) => 1 / 16
  | (2, 3) => 1 / 16
  | (_, _) => 1 / 16

private theorem sameSumCounterexampleWeight_sum :
    (∑ x : Fin 4 × Fin 4, sameSumCounterexampleWeight x) = 1 := by
  rw [Fintype.sum_prod_type]
  norm_num [sameSumCounterexampleWeight, Fin.sum_univ_four]

private def sameSumCounterexampleCoupling : PMF (Fin 4 × Fin 4) :=
  PMF.ofFintype (fun x ↦ (sameSumCounterexampleWeight x : ℝ≥0∞)) <| by
    change ((∑ x : Fin 4 × Fin 4, sameSumCounterexampleWeight x : ℝ≥0) : ℝ≥0∞) = 1
    exact_mod_cast sameSumCounterexampleWeight_sum

-- Proof sketch: let `(X, Y)` have the private coupling `sameSumCounterexampleCoupling` on
-- `Fin 4 × Fin 4`, and let `(X', Y')` have the uniform product law
-- `PMF.uniformOfFintype (Fin 4 × Fin 4)`. The row and column sums of the dependent coupling are
-- the same as the marginals of the uniform product law, so `X =ᵈ X'` and `Y =ᵈ Y'`. Its
-- anti-diagonal sums also match those of the uniform product law, so `X + Y =ᵈ X' + Y'`. Since
-- the uniform pair is a product law, `X'` and `Y'` are independent, while the dependent coupling
-- is not the product law, so `X` and `Y` are not independent.
/-- Exercise 15.2.2: there exists a probability space carrying real random variables `X`, `X'`,
`Y`, and `Y'` such that `X =ᵈ X'`, `Y =ᵈ Y'`, `X'` and `Y'` are independent,
`X + Y =ᵈ X' + Y'`, but `X` and `Y` are not independent. -/
theorem exists_same_sum_independent_copy_counterexample :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω),
      IsProbabilityMeasure μ ∧
      ∃ X X' Y Y' : Ω → ℝ,
        IdentDistrib X X' μ μ ∧
        IdentDistrib Y Y' μ μ ∧
        IndepFun X' Y' μ ∧
        IdentDistrib (fun ω ↦ X ω + Y ω) (fun ω ↦ X' ω + Y' ω) μ μ ∧
        ¬ IndepFun X Y μ := sorry

/-! ### Theorem_15_2 (from Items/Chap15) -/
universe u

variable {𝕜 E : Type u} [RCLike 𝕜] [TopologicalSpace E] [CompactSpace E]

/- Theorem 15.2: the Stone--Weierstrass theorem for compact Hausdorff spaces over `ℝ` or `ℂ` is
the canonical mathlib theorem
`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`, formulated for star
subalgebras of `C(E, 𝕜)`; in the real case the star condition is automatic, and in the complex case
it is exactly closure under complex conjugation. -/
recall ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints

/-! ### Exercise_15_2_3 (from Items/Chap15) -/
open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

namespace Measure

/-- A real law is lattice distributed when it is concentrated on some affine lattice `a + d ℤ`. -/
def IsLatticeDistributed (μ : Measure ℝ) : Prop :=
  ∃ a d : ℝ, μ (Set.range fun n : ℤ ↦ a + (n : ℝ) * d) = 1

-- Proof sketch: for the forward direction, write the support condition `μ[a + d ℤ] = 1` and
-- evaluate the characteristic function at a nonzero frequency annihilating the lattice increments.
-- For the converse, equality in the triangle inequality for the oscillatory integral forces the
-- phase `exp (i u x)` to be `μ`-almost surely constant, which implies concentration on an affine
-- lattice.
/-- A real zero-or-probability law is lattice distributed if and only if there exists a nonzero
frequency at which the modulus of its characteristic function is equal to `1`. The probability-law
case is the textbook criterion, while the zero measure handles non-measurable pushforwards
canonically. -/
theorem isLatticeDistributed_iff_exists_ne_zero_norm_charFun_eq_one
    (μ : Measure ℝ) [IsZeroOrProbabilityMeasure μ] :
    IsLatticeDistributed μ ↔
      ∃ u : ℝ, u ≠ 0 ∧ ‖charFun μ u‖ = 1 := sorry

end Measure

/-- A real random variable is lattice distributed when its law is lattice distributed. -/
def IsLatticeDistributed (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  Measure.IsLatticeDistributed (P.map X)

/-- Exercise 15.2.3: a real random variable is lattice distributed if and only if there exists a
nonzero frequency at which the modulus of its characteristic function is equal to `1`. -/
theorem is_lattice_distributed_iff_exists_ne_zero_norm_charFun_eq_one
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) :
    IsLatticeDistributed P X ↔
      ∃ u : ℝ, u ≠ 0 ∧ ‖charFun (P.map X) u‖ = 1 := by
  simpa [IsLatticeDistributed] using
    Measure.isLatticeDistributed_iff_exists_ne_zero_norm_charFun_eq_one (P.map X)

/-! ### Exercise_15_2_4 (from Items/Chap15) -/
open scoped Topology

open MeasureTheory ProbabilityTheory Filter

universe u

namespace MeasureTheory.Measure

section AlongZero

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]
variable {t : ℕ → ℝ}

-- Proof sketch: use the doubling estimate for `1 - Re φ(2 t)` together with the hypothesis
-- `‖φ (t n)‖ = 1` to show that the law `μ` has the characteristic function of a Dirac measure.
/-- Law-level owner form of Exercise 15.2.4 (1): if a real probability law has characteristic
function of modulus `1` along a nonzero sequence of frequencies with `|t_n| ↓ 0`, then the law is
a Dirac mass. -/
theorem eq_dirac_of_charFun_norm_eq_one_along_zero
    (ht_antitone : Antitone fun n ↦ |t n|)
    (ht_zero : Tendsto (fun n ↦ |t n|) atTop (𝓝 0))
    (ht_nonzero : ∀ n, t n ≠ 0)
    (hφ_unit : ∀ n, ‖charFun μ (t n)‖ = 1) :
    ∃ b : ℝ, μ = Measure.dirac b := sorry

-- Proof sketch: apply the first law-level statement, then the additional hypothesis
-- `φ (t n) = 1` forces the Dirac characteristic function to be identically `1`, hence its atom is
-- located at `0`.
/-- Law-level owner form of Exercise 15.2.4 (2): if in addition the characteristic function is
equal to `1` along that same nonzero sequence, then the law is `δ₀`. -/
theorem eq_dirac_zero_of_charFun_eq_one_along_zero
    (ht_antitone : Antitone fun n ↦ |t n|)
    (ht_zero : Tendsto (fun n ↦ |t n|) atTop (𝓝 0))
    (ht_nonzero : ∀ n, t n ≠ 0)
    (hφ_one : ∀ n, charFun μ (t n) = 1) :
    μ = Measure.dirac 0 := sorry

end AlongZero

end MeasureTheory.Measure

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}

section AlongZero

variable (t : ℕ → ℝ)

-- Proof sketch: use the doubling estimate for `1 - Re φ(2 t)` together with the hypothesis
-- `‖φ (t n)‖ = 1` to show that the pushforward law `P.map X` is a Dirac measure, then conclude
-- that `X` is almost surely constant from `HasLaw.ae_iff`.
/-- Exercise 15.2.4 (1): if the characteristic function of a real random variable has modulus
`1` along a nonzero sequence of frequencies with `|t_n| ↓ 0`, then the random variable is almost
surely constant. -/
theorem ae_eq_const_of_charFun_norm_eq_one_along_zero
    (hX : Measurable X)
    (ht_antitone : Antitone fun n ↦ |t n|)
    (ht_zero : Tendsto (fun n ↦ |t n|) atTop (𝓝 0))
    (ht_nonzero : ∀ n, t n ≠ 0)
    (hφ_unit : ∀ n, ‖charFun (P.map X) (t n)‖ = 1) :
    ∃ b : ℝ, X =ᵐ[P] fun _ ↦ b := by
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  obtain ⟨b, hb⟩ :=
    Measure.eq_dirac_of_charFun_norm_eq_one_along_zero ht_antitone ht_zero ht_nonzero hφ_unit
  refine ⟨b, ?_⟩
  let hX_law : HasLaw X (Measure.dirac b) P := ⟨hX.aemeasurable, hb⟩
  exact (hX_law.ae_iff (measurable_id.eq measurable_const)).2 (by simp)

-- Proof sketch: apply the law-level `δ₀` statement to the pushforward law `P.map X`, then use
-- `HasLaw.ae_iff` to transport the almost-everywhere identity under the Dirac law back to `P`.
/-- Exercise 15.2.4 (2): if in addition the characteristic function is equal to `1` along that
same nonzero sequence with `|t_n| ↓ 0`, then the random variable vanishes almost surely. -/
theorem ae_eq_zero_of_charFun_eq_one_along_zero
    (hX : Measurable X)
    (ht_antitone : Antitone fun n ↦ |t n|)
    (ht_zero : Tendsto (fun n ↦ |t n|) atTop (𝓝 0))
    (ht_nonzero : ∀ n, t n ≠ 0)
    (hφ_one : ∀ n, charFun (P.map X) (t n) = 1) :
    X =ᵐ[P] fun _ ↦ 0 := by
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  let hX_law : HasLaw X (Measure.dirac 0) P :=
    ⟨hX.aemeasurable,
      Measure.eq_dirac_zero_of_charFun_eq_one_along_zero
        ht_antitone ht_zero ht_nonzero hφ_one⟩
  exact (hX_law.ae_iff (measurable_id.eq measurable_const)).2 (by simp)

end AlongZero
