import ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- The finite gambler's ruin transition matrix on `{0, ..., N}` with gain probability `r`,
written in the chapter's canonical `ℝ≥0∞` codomain for discrete Markov chains. -/
def gamblerRuinTransitionMatrix (N : ℕ) (r : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ≥0∞ :=
  fun i j ↦
    if i = 0 then
      if j = 0 then 1 else 0
    else if i = Fin.last N then
      if j = Fin.last N then 1 else 0
    else if j.1 = i.1 + 1 then
      ENNReal.ofReal r
    else if i.1 = j.1 + 1 then
      ENNReal.ofReal (1 - r)
    else
      0

/-- The one-step kernel associated with the gambler's ruin transition matrix. -/
abbrev gamblerRuinKernel (N : ℕ) (r : ℝ) :
    Kernel (Fin (N + 1)) (Fin (N + 1)) :=
  discreteMatrixKernel (gamblerRuinTransitionMatrix N r)

/-- The same transition matrix regarded as a real matrix for characteristic-polynomial and
spectral computations. -/
def gamblerRuinTransitionMatrixReal (N : ℕ) (r : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j ↦
    if i = 0 then
      if j = 0 then 1 else 0
    else if i = Fin.last N then
      if j = Fin.last N then 1 else 0
    else if j.1 = i.1 + 1 then
      r
    else if i.1 = j.1 + 1 then
      1 - r
    else
      0

-- Proof sketch: for `0 ≤ r ≤ 1`, the off-diagonal masses `r` and `1 - r` are nonnegative, so
-- taking `toReal` entrywise on the canonical `ℝ≥0∞` transition matrix recovers the usual real
-- transition matrix used in the linear-algebra calculations.
/-- In the probabilistic regime `0 ≤ r ≤ 1`, the real bridge is obtained by taking `toReal`
entrywise on the canonical gambler's ruin transition matrix. -/
theorem gamblerRuinTransitionMatrixReal_eq_toReal
    (N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    gamblerRuinTransitionMatrixReal N r = fun i j ↦ (gamblerRuinTransitionMatrix N r i j).toReal :=
  sorry

-- Proof sketch: the boundary rows are Dirac masses at `0` and `N`, and each interior row has
-- exactly the two nonzero entries `r` and `1 - r`, which add up to `1`.
/-- The gambler's ruin transition matrix is stochastic whenever `0 ≤ r ≤ 1`. -/
theorem gamblerRuinTransitionMatrix_isStochastic
    (N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IsStochasticMatrix (gamblerRuinTransitionMatrix N r) := sorry

/-- The gambler's ruin kernel is a Markov kernel whenever `0 ≤ r ≤ 1`. -/
theorem gamblerRuinKernel_isMarkovKernel
    (N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IsMarkovKernel (gamblerRuinKernel N r) :=
  discreteMatrixKernel_isMarkovKernel _ (gamblerRuinTransitionMatrix_isStochastic N hr0 hr1)

/-- The step standard deviation `σ = sqrt (4 r (1 - r))`
appearing in the explicit spectrum. -/
def gamblerRuinSigma (r : ℝ) : ℝ :=
  Real.sqrt (4 * r * (1 - r))

/-- The nontrivial eigenvalues of the gambler's ruin transition matrix. -/
def gamblerRuinNontrivialEigenvalue (N : ℕ) (r : ℝ) : Fin (N - 1) → ℝ :=
  fun n ↦ gamblerRuinSigma r * Real.cos ((((n : ℕ) : ℝ) + 1) * Real.pi / N)

/-- The explicit decay rate `σ cos (π / N)` coming from the largest nontrivial eigenvalue. -/
def gamblerRuinDecayRate (N : ℕ) (r : ℝ) : ℝ :=
  gamblerRuinSigma r * Real.cos (Real.pi / (N : ℝ))

-- Proof sketch: conjugate the tridiagonal interior block of
-- `gamblerRuinTransitionMatrixReal N r` to a symmetric Toeplitz matrix with off-diagonal entries
-- `sqrt (r * (1 - r))`; its eigenvectors are the sine modes on `Fin (N - 1)`, which yield the
-- eigenvalues `σ cos (kπ / N)`, and the two absorbing boundary states contribute the eigenvalue
-- `1`.
/-- Example 18.20: the spectrum of the real gambler's ruin transition matrix on `{0, ..., N}`
consists of the absorbing eigenvalue `1` together with the values `σ cos (kπ / N)` for
`k = 1, ..., N - 1`. -/
theorem gamblerRuin_spectrum_eq
    (N : ℕ) (hN : 2 ≤ N) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    spectrum ℝ (gamblerRuinTransitionMatrixReal N r) =
      {1} ∪ Set.range (gamblerRuinNontrivialEigenvalue N r) := sorry

-- Proof sketch: combine `gamblerRuin_spectrum_eq` with the monotonicity of `cos` on `[0, π]`; the
-- nontrivial eigenvalues are `σ cos (kπ / N)` with `1 ≤ k ≤ N - 1`, so the largest modulus among
-- them is attained at `k = 1` and equals `σ cos (π / N)`.
/-- Every non-absorbing spectral value of the gambler's ruin chain is bounded in modulus by the
explicit rate `σ cos (π / N)`. -/
theorem gamblerRuin_nontrivial_spectral_bound
    (N : ℕ) (hN : 2 ≤ N) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {x : ℝ}
    (hx : x ∈ spectrum ℝ (gamblerRuinTransitionMatrixReal N r)) (hx1 : x ≠ 1) :
    |x| ≤ gamblerRuinDecayRate N r := sorry
