import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_18_4_1 (from Items/Chap18) -/
open Polynomial

noncomputable section

namespace ProbabilityTheory

/-- The source-facing shifted family `chi_(N+1)` from Example 18.20, determined by the initial
values `chi_1 = (1 - X)^2`, `chi_2 = -X (1 - X)^2`, and the recursion `(18.15)`. Its canonical
owner is the characteristic polynomial of `gamblerRuinTransitionMatrixReal`, related below by
`gamblerRuinTransitionMatrix_charpoly_eq`. -/
def gamblerRuinCharacteristicPolynomial (r : ℝ) : ℕ → ℝ[X]
  | 0 => (1 - X) ^ 2
  | 1 => -X * (1 - X) ^ 2
  | n + 2 =>
      -X * gamblerRuinCharacteristicPolynomial r (n + 1) -
        C (r * (1 - r)) * gamblerRuinCharacteristicPolynomial r n

-- Proof sketch: unfold the recursive definition at index `0`; this is exactly the chosen initial
-- value corresponding to `chi_1` in Example 18.20.
/-- The initial polynomial `chi_1` in the shifted family. -/
theorem gamblerRuinCharacteristicPolynomial_chi_one (r : ℝ) :
    gamblerRuinCharacteristicPolynomial r 0 = (1 - X) ^ 2 := rfl

-- Proof sketch: unfold the recursive definition at index `1`; this is exactly the chosen initial
-- value corresponding to `chi_2` in Example 18.20.
/-- The initial polynomial `chi_2` in the shifted family. -/
theorem gamblerRuinCharacteristicPolynomial_chi_two (r : ℝ) :
    gamblerRuinCharacteristicPolynomial r 1 = -X * (1 - X) ^ 2 := rfl

-- Proof sketch: unfold the recursive clause of `gamblerRuinCharacteristicPolynomial`; it is the
-- recursion `(18.15)` rewritten in the shifted indexing used by this file.
/-- The recursion `(18.15)` for the shifted characteristic-polynomial family. -/
theorem gamblerRuinCharacteristicPolynomial_recurrence (r : ℝ) (N : ℕ) :
    gamblerRuinCharacteristicPolynomial r (N + 2) =
      -X * gamblerRuinCharacteristicPolynomial r (N + 1) -
        C (r * (1 - r)) * gamblerRuinCharacteristicPolynomial r N := rfl

-- Proof sketch: `Matrix.charpoly` is the canonical owner for characteristic polynomials in
-- mathlib. The source-facing `chi_(N+1)` is the same polynomial as
-- `det (gamblerRuinTransitionMatrixReal (N + 1) r - X • I)`, while `Matrix.charpoly` is
-- `det (X • I - gamblerRuinTransitionMatrixReal (N + 1) r)`; comparing the two determinants gives
-- the sign `(-1)^N` because the matrix size is `N + 2`.
/-- The canonical owner statement for the shifted family `chi_(N+1)`: up to the usual sign change
between `det (A - X • I)` and `det (X • I - A)`, it is the characteristic polynomial of the
real gambler's ruin transition matrix on `{0, ..., N + 1}`. -/
theorem gamblerRuinTransitionMatrix_charpoly_eq (r : ℝ) (N : ℕ) :
    (gamblerRuinTransitionMatrixReal (N + 1) r).charpoly =
      C ((-1 : ℝ) ^ N) * gamblerRuinCharacteristicPolynomial r N := sorry

-- Proof sketch: prove the closed form by induction on `N` using the two initial values and the
-- recurrence `(18.15)`, together with the standard recursion for `Polynomial.Chebyshev.U`.
/-- Exercise 18.4.1: for `r in (0,1)`, the polynomial `chi_(N+1)` from Example 18.20 satisfies
the closed formula `(18.16)` in terms of the Chebyshev polynomial of the second kind. -/
theorem gamblerRuinCharacteristicPolynomial_eq_chebyshevU
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) :
    gamblerRuinCharacteristicPolynomial r (N + 1) =
      C (((-1 : ℝ) ^ N) * ((gamblerRuinSigma r / 2) ^ N)) *
        (1 - X) ^ 2 *
        (Polynomial.Chebyshev.U ℝ (N : ℤ)).comp (C ((gamblerRuinSigma r)⁻¹) * X) := sorry

end ProbabilityTheory

/-! ### Exercise_18_4_2 (from Items/Chap18) -/
open scoped BigOperators

noncomputable section

namespace ProbabilityTheory

-- Proof sketch: rewrite the Chebyshev term in `(18.16)` using the standard identity
-- `U_{n-1}(cos θ) = sin (n θ) / sin θ` with `θ = arccos (x / σ)`, then use
-- `sin (arccos t) = √(1 - t^2)` and the factorization of the Chebyshev polynomial into its real
-- roots `cos (π k / N)` to obtain the product formula.
/-- Exercise 18.4.2: for the gambler's ruin characteristic polynomial from Example 18.20, the
Chebyshev formula from `(18.16)` for `χ_N`, namely
`(gamblerRuinCharacteristicPolynomial r (N - 1)).eval x`, agrees on `(-σ, σ)` both with the
trigonometric de Moivre formula and with the product factorization over the roots
`σ cos (π k / N)`. -/
theorem gamblerRuinCharacteristicPolynomial_eq_trigonometric_and_product_forms
    (r : ℝ) (N : ℕ) (hN : 2 ≤ N) {x : ℝ}
    (hx : x ∈ Set.Ioo (-(gamblerRuinSigma r)) (gamblerRuinSigma r)) :
    (gamblerRuinCharacteristicPolynomial r (N - 1)).eval x =
        (-1 : ℝ) ^ (N - 1) * (gamblerRuinSigma r / 2) ^ (N - 1) * (1 - x) ^ (2 : ℕ) *
          (Real.sin (N * Real.arccos (x / gamblerRuinSigma r)) /
            Real.sqrt (1 - (x / gamblerRuinSigma r) ^ (2 : ℕ))) ∧
      (gamblerRuinCharacteristicPolynomial r (N - 1)).eval x =
        (1 - x) ^ (2 : ℕ) *
          ∏ k ∈ Finset.Icc 1 (N - 1),
            (gamblerRuinSigma r * Real.cos (Real.pi * k / N) - x) := sorry

end ProbabilityTheory

/-! ### Exercise_18_4_3 (from Items/Chap18) -/
open Real intervalIntegral MeasureTheory

noncomputable section

namespace Polynomial.Chebyshev

/-- The probability measure on `[-1, 1]` with density `(2 / π) * √(1 - x ^ 2)` with respect to
Lebesgue measure, expressed canonically as a reweighting of `measureT`. -/
noncomputable def measureU : Measure ℝ :=
  measureT.withDensity (fun x ↦ ENNReal.ofReal ((2 / π) * (1 - x ^ 2)))

-- Proof sketch: expand `measureU` as a weighted Lebesgue measure and then apply the substitution
-- `x = cos θ` on `[-1, 1]`, using `dx = - sin θ dθ` and `√(1 - cos θ ^ 2) = sin θ` for
-- `θ ∈ [0, π]`.
/-- Integrating against `measureU` is the same as integrating along `x = cos θ` on `[0, π]` with
weight `(2 / π) * sin θ ^ 2`. -/
theorem integral_measureU_eq_integral_cos {f : ℝ → ℝ} :
    ∫ x, f x ∂ measureU = ∫ θ in 0..π, f (cos θ) * ((2 / π) * sin θ ^ 2) := sorry

-- Proof sketch: rewrite the `measureU` integral using `integral_measureU_eq_integral_cos`, then
-- use `U_real_cos` to convert each evaluated Chebyshev polynomial into a sine quotient. The
-- factor `sin θ ^ 2` from the measure cancels the denominators, leaving the normalized sine
-- orthogonality integral on `[0, π]`.
/-- Exercise 18.4.3: the Chebyshev polynomials of the second kind are orthonormal with respect to
the measure `measureU`, equivalently
`∫ x, (U_m x) * (U_n x) dν = 1` when `m = n` and `0` otherwise. -/
theorem integral_eval_U_real_mul_eval_U_real_measureU (m n : ℕ) :
    ∫ x, (U ℝ m).eval x * (U ℝ n).eval x ∂ measureU = if m = n then 1 else 0 := sorry

end Polynomial.Chebyshev

/-! ### Exercise_18_4_4 (from Items/Chap18) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory.DiscreteMarkovChain

/-- The transition matrix of the three-state chain from Exercise 18.4.4, written on `Fin 3` with
indices `0`, `1`, `2` corresponding to the textbook states `1`, `2`, `3`. -/
def three_state_transition_matrix : Fin 3 → Fin 3 → ℝ≥0∞ :=
  ![![(1 : ℝ≥0∞) / 2, (1 : ℝ≥0∞) / 3, (1 : ℝ≥0∞) / 6],
    ![(1 : ℝ≥0∞) / 3, (1 : ℝ≥0∞) / 3, (1 : ℝ≥0∞) / 3],
    ![0, (3 : ℝ≥0∞) / 4, (1 : ℝ≥0∞) / 4]]

/-- The same transition matrix regarded as a real matrix for spectral computations. -/
abbrev three_state_transition_matrix_real : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j ↦ (three_state_transition_matrix i j).toReal

/-- The one-step kernel associated with the Exercise 18.4.4 transition matrix. -/
abbrev three_state_transition_kernel : Kernel (Fin 3) (Fin 3) :=
  discreteMatrixKernel three_state_transition_matrix

-- Proof sketch: evaluate the three row sums of `three_state_transition_matrix`; they are
-- `1 / 2 + 1 / 3 + 1 / 6`, `1 / 3 + 1 / 3 + 1 / 3`, and `0 + 3 / 4 + 1 / 4`, each equal to `1`.
/-- The Exercise 18.4.4 transition matrix is stochastic. -/
theorem three_state_transition_matrix_isStochastic :
    IsStochasticMatrix three_state_transition_matrix := sorry

/-- The weights of the invariant distribution of the three-state chain. -/
def three_state_invariant_weights : Fin 3 → ℝ≥0∞ :=
  ![(18 : ℝ≥0∞) / 61, (27 : ℝ≥0∞) / 61, (16 : ℝ≥0∞) / 61]

-- Proof sketch: evaluate the finite sum over the three states and simplify
-- `18 / 61 + 27 / 61 + 16 / 61 = 1`.
/-- The explicit invariant weights form a probability vector. -/
theorem three_state_invariant_weights_sum :
    Finset.univ.sum three_state_invariant_weights = 1 := sorry

/-- Exercise 18.4.4 (1): the invariant distribution of the chain is the probability law assigning
masses `18 / 61`, `27 / 61`, and `16 / 61` to the states `1`, `2`, and `3`. -/
def three_state_invariant_distribution : ProbabilityMeasure (Fin 3) :=
  ⟨(PMF.ofFintype three_state_invariant_weights three_state_invariant_weights_sum).toMeasure,
    inferInstance⟩

-- Proof sketch: compute the image of `three_state_invariant_distribution` under the one-step
-- kernel `three_state_transition_kernel`; the stationarity equations reduce to the three linear
-- identities defining the weights `18 / 61`, `27 / 61`, and `16 / 61`.
/-- The explicit law with weights `18 / 61`, `27 / 61`, and `16 / 61` is invariant for the
one-step kernel of the chain. -/
theorem three_state_invariant_distribution_isInvariant :
    Kernel.Invariant three_state_transition_kernel
      (three_state_invariant_distribution : Measure (Fin 3)) := sorry

/-- Exercise 18.4.4 (2): the exponential convergence rate of the chain is
`(1 + √41) / 24`. -/
def three_state_exponential_convergence_rate : ℝ :=
  (1 + Real.sqrt 41) / 24

-- Proof sketch: compute the characteristic polynomial of `three_state_transition_matrix_real`,
-- factor it as `(x - 1) * (72 x^2 - 6 x - 5) / 72`, and solve the quadratic factor. The two
-- nontrivial eigenvalues are `(1 ± √41) / 24`, so the spectral decay rate is the larger modulus
-- `(1 + √41) / 24`.
/-- The real spectrum of the transition matrix consists of `1` and the two nontrivial eigenvalues
`(1 - √41) / 24` and `(1 + √41) / 24`. -/
theorem three_state_spectrum_eq :
    spectrum ℝ three_state_transition_matrix_real =
      ({1, (1 - Real.sqrt 41) / 24, three_state_exponential_convergence_rate} : Set ℝ) := sorry

end ProbabilityTheory.DiscreteMarkovChain

/-! ### Theorem_18_4 (from Items/Chap18) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- A family `C : ZMod d → Set E` is a cyclic class decomposition for the period-`d` discrete
Markov kernel `p` when the textbook classes `E_i = C i` are nonempty, pairwise disjoint, cover
the whole state space, and one-step transitions move from class `i` to class `i + 1`. -/
def IsPeriodicClassFamily (p : Kernel E E) {d : ℕ+} (C : ZMod d → Set E) : Prop :=
  (∀ i : ZMod d, (C i).Nonempty) ∧
    Pairwise fun i j ↦ Disjoint (C i) (C j) ∧
    (⋃ i, C i) = Set.univ ∧
    ∀ ⦃x y : E⦄ ⦃i : ZMod d⦄, (p x) {y} > 0 → x ∈ C i → y ∈ C (i + 1)

section

variable (p : Kernel E E) [IsMarkovKernel p]
variable [Kernel.IsIrreducible (Measure.count : Measure E) p]

-- Proof sketch: choose a reference state `x₀`, define `E_i` by the congruence class modulo `d`
-- of the length of a path from `x₀` to `x`, and use irreducibility together with the period
-- condition to show that this is well defined, covers all states, and is advanced by one-step
-- transitions.
/-- Theorem 18.4 (1): if a discrete Markov kernel on a nonempty discrete state space is
irreducible and has period `d`, then its state space admits a cyclic decomposition into `d`
pairwise disjoint classes that are advanced by one-step transitions. -/
theorem exists_periodicClassDecomposition
    [Nonempty E] (d : ℕ+) (hperiod : HasPeriod p d) :
    ∃ C : ZMod d → Set E, IsPeriodicClassFamily p C := sorry

-- Proof sketch: fix one state and compare any two decompositions by the class containing that
-- state. Irreducibility forces every other state to lie in the class predicted by the path length
-- modulo `d`, so the two decompositions can differ only by one global cyclic shift.
/-- Theorem 18.4 (2): for an irreducible discrete Markov kernel, any two cyclic decompositions of
the state space indexed by `ZMod d` differ by a cyclic permutation of the class labels. -/
theorem periodicClassDecomposition_unique_up_to_cyclicShift
    (d : ℕ+) (C₁ C₂ : ZMod d → Set E)
    (hC₁ : IsPeriodicClassFamily p C₁) (hC₂ : IsPeriodicClassFamily p C₂) :
    ∃ k : ZMod d, ∀ i : ZMod d, C₁ i = C₂ (i + k) := sorry

end

end ProbabilityTheory

/-! ### Exercise_18_4_5 (from Items/Chap18) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

private theorem fin_pos {N : ℕ} (i : Fin N) : 0 < N :=
  lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.succ_le_of_lt i.2)

private theorem pos_of_two_le {N : ℕ} (hN : 2 ≤ N) : 0 < N :=
  lt_of_lt_of_le (by decide : 0 < 2) hN

/-- The transition matrix of the cyclic lazy walk on `Fin N`: from `i` the chain jumps to the
cyclic successor `finRotate N i` with probability `r` and stays put with probability `1 - r`. The
sum form handles the degenerate one-point cycle as well. -/
def cyclicLazyWalkTransitionMatrix (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : Fin N → Fin N → ℝ≥0∞ :=
  fun i j ↦
    (if j = finRotate N i then ENNReal.ofReal (r : ℝ) else 0) +
      (if j = i then ENNReal.ofReal (1 - (r : ℝ)) else 0)

/-- The Markov kernel associated with the cyclic lazy walk transition matrix. -/
abbrev cyclicLazyWalkKernel (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : Kernel (Fin N) (Fin N) :=
  discreteMatrixKernel (cyclicLazyWalkTransitionMatrix N r)

/-- The uniform probability distribution on the finite cyclic state space `Fin N`. -/
def cyclicLazyWalkInvariantDistribution (N : ℕ) (hN : 0 < N) : ProbabilityMeasure (Fin N) :=
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  ⟨(PMF.uniformOfFintype (Fin N)).toMeasure, inferInstance⟩

/-- The explicit spectral radius of the largest nontrivial Fourier mode of the cyclic lazy walk. -/
def cyclicLazyWalkExponentialRate (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : ℝ :=
  if _ : N ≤ 1 then 0 else Real.sqrt (1 - 4 * r * (1 - r) * Real.sin (Real.pi / N) ^ 2)

-- Proof sketch: this is immediate from the definition of
-- `cyclicLazyWalkTransitionMatrix`.
/-- The cyclic lazy walk matrix is the sum of the jump-to-successor and hold contributions. -/
theorem cyclicLazyWalkTransitionMatrix_apply
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (i j : Fin N) :
    cyclicLazyWalkTransitionMatrix N r i j =
      (if j = finRotate N i then ENNReal.ofReal (r : ℝ) else 0) +
        (if j = i then ENNReal.ofReal (1 - (r : ℝ)) else 0) := rfl

-- Proof sketch: evaluate `cyclicLazyWalkKernel N r i` on the singleton `{j}`, expand the defining
-- sum of Dirac measures, and keep only the `j`-th summand.
/-- Evaluating the cyclic lazy walk kernel at a singleton recovers the corresponding matrix entry.
-/
theorem cyclicLazyWalkKernel_apply_singleton
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (i j : Fin N) :
    cyclicLazyWalkKernel N r i {j} = cyclicLazyWalkTransitionMatrix N r i j := sorry

-- Proof sketch: for each row, only the successor and holding terms can contribute; their masses
-- are nonnegative and add up to `1`.
/-- The cyclic lazy walk transition matrix is stochastic. -/
theorem cyclicLazyWalkTransitionMatrix_isStochastic
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) :
    IsStochasticMatrix (cyclicLazyWalkTransitionMatrix N r) := sorry

/-- The cyclic lazy walk kernel is Markov. -/
instance cyclicLazyWalkKernel.instIsMarkovKernel
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) :
    IsMarkovKernel (cyclicLazyWalkKernel N r) := by
  simpa [cyclicLazyWalkKernel] using
    (discreteMatrixKernel_isMarkovKernel
      (cyclicLazyWalkTransitionMatrix N r)
      (cyclicLazyWalkTransitionMatrix_isStochastic N r))

-- Proof sketch: positive forward-step probability lets the chain reach every state by repeated
-- cyclic increments, so every state communicates with every other.
/-- The cyclic lazy walk is irreducible as soon as the forward jump probability is positive. -/
theorem cyclicLazyWalk_isIrreducible
    (N : ℕ) (hN : 0 < N) (r : Set.Ioo (0 : ℝ) 1) :
    Kernel.IsIrreducible (Measure.count : Measure (Fin N)) (cyclicLazyWalkKernel N r) := sorry

-- Proof sketch: each state has a positive one-step return probability through the holding move,
-- so the period of every state is `1`.
/-- The positive holding probability makes the cyclic lazy walk aperiodic. -/
theorem cyclicLazyWalk_isAperiodic
    (N : ℕ) (hN : 0 < N) (r : Set.Ioo (0 : ℝ) 1) :
    IsAperiodic (cyclicLazyWalkKernel N r) := sorry

-- Proof sketch: the uniform PMF on `Fin N` gives every state the same mass, namely the reciprocal
-- of the cardinality of `Fin N`.
/-- The uniform invariant distribution assigns mass `N⁻¹` to each singleton of `Fin N`. -/
theorem cyclicLazyWalkInvariantDistribution_apply_singleton
    (N : ℕ) (i : Fin N) :
    (cyclicLazyWalkInvariantDistribution N (fin_pos i) : Measure (Fin N)) {i} =
      (N : ℝ≥0∞)⁻¹ := sorry

-- Proof sketch: the transition matrix is circulant, so averaging over all starting states is
-- preserved by one step; equivalently, the uniform law is a left eigenvector with eigenvalue `1`.
/-- The uniform distribution on `Fin N` is invariant for the cyclic lazy walk. -/
theorem cyclicLazyWalkInvariantDistribution_isInvariant
    (N : ℕ) (hN : 0 < N) (r : Set.Ioo (0 : ℝ) 1) :
    Kernel.Invariant (cyclicLazyWalkKernel N r)
      (cyclicLazyWalkInvariantDistribution N hN : Measure (Fin N)) := sorry

-- Proof sketch: the nontrivial Fourier eigenvalues are `1 - r + r ζ` with `ζ^N = 1` and
-- `ζ ≠ 1`; for `2 ≤ N`, their moduli are strictly less than `1`, and the largest
-- one is the declared rate.
/-- The explicit spectral rate of the cyclic lazy walk is strictly smaller than `1` in the
nontrivial lazy regime. -/
theorem cyclicLazyWalkExponentialRate_lt_one
    (N : ℕ) (hN : 2 ≤ N) (r : Set.Ioo (0 : ℝ) 1) :
    cyclicLazyWalkExponentialRate N r < 1 := sorry

-- Proof sketch: diagonalize the circulant kernel by the Fourier basis on `Fin N`; the nontrivial
-- eigenvalues are `1 - r + r ζ`, so their largest modulus is
-- `cyclicLazyWalkExponentialRate N r`; then translate the spectral estimate to the chapter-owner
-- kernel iterate law.
/-- Exercise 18.4.5: for the lazy cyclic random walk on `Fin N` with forward-jump probability
`r ∈ (0,1)`, the walk is irreducible and aperiodic, the uniform distribution is invariant, and the
convergence to equilibrium is exponential with explicit rate
`cyclicLazyWalkExponentialRate N r`. -/

theorem cyclicLazyWalk_exponentialConvergence
    (N : ℕ) (hN : 2 ≤ N) (r : Set.Ioo (0 : ℝ) 1)
    (μ : ProbabilityMeasure (Fin N)) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ n : ℕ,
          let κn : Kernel (Fin N) (Fin N) := cyclicLazyWalkKernel N r ^ n
          totalVariationDistance
            (⟨κn ∘ₘ (μ : Measure (Fin N)), inferInstance⟩ :
              ProbabilityMeasure (Fin N))
            (cyclicLazyWalkInvariantDistribution N (pos_of_two_le hN))
            ≤ C * (cyclicLazyWalkExponentialRate N r) ^ n := sorry

end ProbabilityTheory

/-! ### Exercise_18_4_6 (from Items/Chap18) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- The state space `{0,1}^N`, represented as Boolean-valued functions on `Fin N`. -/
abbrev HypercubeState (N : ℕ) : Type :=
  Fin N → Bool

/-- The vertex obtained from `x` by flipping the coordinate `i`. -/
def hypercubeFlipAt {N : ℕ} (x : HypercubeState N) (i : Fin N) : HypercubeState N :=
  Function.update x i (!(x i))

/-- Exercise 18.4.6 (1): for `N > 0`, the transition matrix of the lazy random walk on
`{0,1}^N` places mass `ε` at the current vertex and mass `(1 - ε) / N` at each vertex obtained by
flipping exactly one coordinate. -/
def hypercubeLazyTransitionMatrix (N : ℕ) [NeZero N] (ε : Set.Ioo (0 : ℝ) 1) :
    HypercubeState N → HypercubeState N → ℝ≥0∞ :=
  fun x y ↦
    if y = x then
      ENNReal.ofReal (ε : ℝ)
    else
      ∑ i : Fin N,
        if y = hypercubeFlipAt x i then
          ENNReal.ofReal ((1 - (ε : ℝ)) / N)
        else
          0

/-- The uniform distribution on the finite hypercube `{0,1}^N`. -/
def hypercubeUniformDistribution (N : ℕ) : ProbabilityMeasure (HypercubeState N) :=
  ⟨(PMF.uniformOfFintype (HypercubeState N)).toMeasure, inferInstance⟩

section LazyHypercube

variable (N : ℕ) [NeZero N] (ε : Set.Ioo (0 : ℝ) 1)

/-- The canonical Markov-kernel view of the lazy hypercube transition matrix. -/
abbrev hypercubeLazyKernel : Kernel (HypercubeState N) (HypercubeState N) :=
  discreteMatrixKernel (hypercubeLazyTransitionMatrix N ε)

/-- The modulus of the largest nontrivial eigenvalue of the lazy hypercube walk. -/
def hypercubeLazyConvergenceFactor : ℝ :=
  max (|1 - 2 * (1 - (ε : ℝ)) / N|) (|2 * (ε : ℝ) - 1|)

-- Proof sketch: for each fixed `x`, there are exactly `N` one-coordinate flips of `x`, each with
-- mass `(1 - ε) / N`, and together with the self-loop mass `ε` these contributions sum to `1`.
/-- The lazy hypercube transition matrix is stochastic. -/
theorem hypercubeLazyTransitionMatrix_isStochastic :
    IsStochasticMatrix (hypercubeLazyTransitionMatrix N ε) := sorry

/-- The lazy hypercube kernel is Markov. -/
theorem hypercubeLazyKernel_isMarkovKernel :
    IsMarkovKernel (hypercubeLazyKernel N ε) := by
  simpa [hypercubeLazyKernel] using
    (discreteMatrixKernel_isMarkovKernel
      (hypercubeLazyTransitionMatrix N ε)
      (hypercubeLazyTransitionMatrix_isStochastic N ε))

-- Proof sketch: every state has a one-step self-loop of probability `ε > 0`, so each state has a
-- positive return time `1`, which forces period `1`.
/-- Exercise 18.4.6 (2): the lazy random walk on the hypercube is aperiodic. -/
theorem hypercubeLazyKernel_isAperiodic :
    IsAperiodic (hypercubeLazyKernel N ε) := sorry

-- Proof sketch: if `x` and `y` differ in `k` coordinates, successively flip those coordinates.
-- Each prescribed flip has probability `(1 - ε) / N > 0`, so concatenating them gives a
-- positive-probability path from `x` to `y`.
/-- Exercise 18.4.6 (3): the lazy random walk on the hypercube is irreducible with respect to
counting measure. -/
theorem hypercubeLazyKernel_isIrreducible :
    Kernel.IsIrreducible (Measure.count : Measure (HypercubeState N)) (hypercubeLazyKernel N ε) :=
  sorry

-- Proof sketch: the transition matrix is symmetric, hence doubly stochastic, so averaging over
-- all hypercube vertices is preserved by one step.
/-- Exercise 18.4.6 (4): the uniform distribution on `{0,1}^N` is invariant for the lazy
hypercube walk. -/
theorem hypercubeUniformDistribution_isInvariant :
    Kernel.Invariant (hypercubeLazyKernel N ε)
      (hypercubeUniformDistribution N : Measure (HypercubeState N)) := sorry

-- Proof sketch: combine the invariance of the uniform law with irreducibility and the Chapter
-- 17 uniqueness theorem for invariant distributions of irreducible discrete kernels.
/-- Any invariant distribution of the lazy hypercube walk is the uniform distribution. -/
theorem hypercubeLazyKernel_invariantDistribution_eq_uniform
    (μ : ProbabilityMeasure (HypercubeState N))
    (hμ : Kernel.Invariant (hypercubeLazyKernel N ε) (μ : Measure (HypercubeState N))) :
    μ = hypercubeUniformDistribution N := by
  let κ : Kernel (HypercubeState N) (HypercubeState N) := hypercubeLazyKernel N ε
  let _ : IsMarkovKernel κ := by
    simpa [κ] using hypercubeLazyKernel_isMarkovKernel N ε
  let _ : Kernel.IsIrreducible (Measure.count : Measure (HypercubeState N)) κ := by
    simpa [κ] using hypercubeLazyKernel_isIrreducible N ε
  refine eq_of_isInvariantDistribution_of_irreducible κ ?_ ?_
  · simpa [κ] using hμ
  · simpa [κ] using hypercubeUniformDistribution_isInvariant N ε

-- Proof sketch: diagonalize the walk by the Walsh basis on `{0,1}^N`; the eigenvalues are
-- `1 - 2 (1 - ε) k / N` for `0 ≤ k ≤ N`, so the largest nontrivial modulus is
-- `hypercubeLazyConvergenceFactor N ε`; translating the spectral estimate to the chapter-owner
-- iterate law gives geometric convergence in total variation.
/-- Exercise 18.4.6 (5): the lazy hypercube walk converges exponentially fast to the uniform
distribution in total variation, with rate given by the largest nontrivial eigenvalue modulus. -/
theorem hypercubeLazyKernel_totalVariation_exponential_bound :
    let _ : IsMarkovKernel (hypercubeLazyKernel N ε) := hypercubeLazyKernel_isMarkovKernel N ε
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ n : ℕ,
          ∀ μ : ProbabilityMeasure (HypercubeState N),
            let κn : Kernel (HypercubeState N) (HypercubeState N) := hypercubeLazyKernel N ε ^ n
            totalVariationDistance
              (⟨κn ∘ₘ (μ : Measure (HypercubeState N)),
                inferInstance⟩ : ProbabilityMeasure (HypercubeState N))
              (hypercubeUniformDistribution N) ≤
            C * hypercubeLazyConvergenceFactor N ε ^ n := sorry

end LazyHypercube

end ProbabilityTheory
