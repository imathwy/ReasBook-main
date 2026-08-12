import ProbabilityTheory_Klenke_2020.Chap17.Example_17_55
import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_16
import ProbabilityTheory_Klenke_2020.Chap18.Definition_18_1
import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_43
import ProbabilityTheory_Klenke_2020.Chap17.Theorem_17_49
import ProbabilityTheory_Klenke_2020.Chap18.Theorem_18_13
import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

universe u

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- Example 18.19: the transition matrix of the asymmetric nearest-neighbor random walk on the
finite discrete torus `Fin N`, which jumps one step to the right with probability `r` and one
step to the left with probability `1 - r`. When `N = 2`, the left and right targets coincide, so
both contributions are added. -/
def discrete_torus_walk_transition_matrix
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : Fin N → Fin N → ℝ≥0∞ :=
  fun i j ↦
    (if j = finRotate N i then ENNReal.ofReal (r : ℝ) else 0) +
      if j = (finRotate N).symm i then ENNReal.ofReal (1 - (r : ℝ)) else 0

-- Proof sketch: unfold `discrete_torus_walk_transition_matrix`; the value is the sum of the right
-- jump contribution and the left jump contribution, which only both occur when `N = 2` and the
-- two neighbors coincide.
/-- The torus walk transition matrix is the sum of the right-jump and left-jump masses on the two
adjacent torus neighbors. -/
theorem discrete_torus_walk_transition_matrix_apply
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (i j : Fin N) :
    discrete_torus_walk_transition_matrix N r i j =
      (if j = finRotate N i then ENNReal.ofReal (r : ℝ) else 0) +
        if j = (finRotate N).symm i then ENNReal.ofReal (1 - (r : ℝ)) else 0 := rfl

/-- The canonical Markov-kernel view of the asymmetric torus walk on `Fin N`. -/
abbrev discrete_torus_walk_kernel
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : Kernel (Fin N) (Fin N) :=
  discreteMatrixKernel (discrete_torus_walk_transition_matrix N r)

/-- The uniform distribution on the finite torus `Fin N`. -/
def discrete_torus_walk_uniform_distribution (N : ℕ) [NeZero N] :
    ProbabilityMeasure (Fin N) :=
  ⟨(PMF.uniformOfFintype (Fin N)).toMeasure, inferInstance⟩

/-- The torus walk transition matrix viewed over `ℂ` for Fourier spectral calculations. -/
def discrete_torus_walk_transition_matrix_complex
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j ↦ (discrete_torus_walk_transition_matrix N r i j).toReal

/-- The complex eigenvalue attached to the Fourier mode `k` for the asymmetric torus walk. -/
def discrete_torus_walk_eigenvalue
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (k : Fin N) : ℂ :=
  Real.cos (2 * Real.pi * (k : ℝ) / N) +
    ((2 * (r : ℝ) - 1) * Real.sin (2 * Real.pi * (k : ℝ) / N)) * Complex.I

/-- The odd-period contraction factor `γ = sqrt(1 - 4 r (1-r) sin(π / N)^2)`. -/
def discrete_torus_walk_convergence_factor
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : ℝ :=
  Real.sqrt (1 - 4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin (Real.pi / N) ^ 2)

-- Proof sketch: sum the two one-step transition probabilities from a fixed state; the right and
-- left jump masses add up to `r + (1 - r) = 1`, and the remaining entries vanish.
/-- Every row of the torus walk transition matrix has total mass `1`. -/
theorem discrete_torus_walk_transition_matrix_isStochastic
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) :
    IsStochasticMatrix (discrete_torus_walk_transition_matrix N r) := sorry

/-- The torus walk kernel is Markov. -/
instance discrete_torus_walk_kernel.instIsMarkovKernel
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) :
    IsMarkovKernel (discrete_torus_walk_kernel N r) := by
  simpa [discrete_torus_walk_kernel] using
    (discreteMatrixKernel_isMarkovKernel
      (discrete_torus_walk_transition_matrix N r)
      (discrete_torus_walk_transition_matrix_isStochastic N r))

-- Proof sketch: on the cyclic graph `Fin N`, repeated right and left moves connect every state to
-- every other state, so the counting measure irreducibility criterion holds for the associated
-- discrete matrix kernel.
/-- The torus walk is irreducible on the finite state space `Fin N`. -/
theorem discrete_torus_walk_isIrreducible
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) :
    Kernel.IsIrreducible (Measure.count : Measure (Fin N))
      (discrete_torus_walk_kernel N r) := sorry

-- Proof sketch: the walk has positive odd return times exactly when the cycle length `N` is odd;
-- when `N` is even every return time is even, and when `N` is odd the coprime one-step increments
-- generate period `1`.
/-- The asymmetric torus walk is aperiodic exactly for odd torus size. -/
theorem discrete_torus_walk_isAperiodic_iff_odd
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) :
    IsAperiodic (discrete_torus_walk_kernel N r) ↔ Odd N :=
  sorry

-- Proof sketch: the uniform law is preserved by the doubly stochastic circulant transition matrix,
-- so it is an invariant distribution for the canonical kernel owner.
/-- The uniform distribution on `Fin N` is invariant for the torus walk. -/
theorem discrete_torus_walk_uniform_distribution_isInvariant
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1) :
    Kernel.Invariant (discrete_torus_walk_kernel N r)
      (discrete_torus_walk_uniform_distribution N : Measure (Fin N)) := sorry

-- Proof sketch: combine invariance of the uniform law with irreducibility and Theorem 17.49 for
-- the canonical kernel owner.
/-- The uniform distribution is the unique invariant distribution of the torus walk. -/
theorem discrete_torus_walk_invariantDistribution_eq_uniform
    (N : ℕ) [NeZero N] (r : Set.Ioo (0 : ℝ) 1)
    (μ : ProbabilityMeasure (Fin N))
    (hμ : Kernel.Invariant (discrete_torus_walk_kernel N r) (μ : Measure (Fin N))) :
    μ = discrete_torus_walk_uniform_distribution N := by
  let _ : Kernel.IsIrreducible (Measure.count : Measure (Fin N))
      (discrete_torus_walk_kernel N r) := discrete_torus_walk_isIrreducible N r
  exact eq_of_isInvariantDistribution_of_irreducible
    (discrete_torus_walk_kernel N r)
    hμ
    (discrete_torus_walk_uniform_distribution_isInvariant N r)

-- Proof sketch: rewrite the eigenvalue in trigonometric form and compute its complex modulus.
/-- The modulus of the `k`-th torus-walk eigenvalue is the textbook square-root expression. -/
theorem discrete_torus_walk_eigenvalue_abs
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (k : Fin N) :
    ‖discrete_torus_walk_eigenvalue N r k‖ =
      Real.sqrt
        (1 - 4 * (r : ℝ) * (1 - (r : ℝ)) *
          Real.sin (2 * Real.pi * (k : ℝ) / N) ^ 2) := sorry

-- Proof sketch: diagonalize the complex circulant matrix by the Fourier basis on `Fin N`; the
-- Fourier mode `k` contributes the eigenvalue `discrete_torus_walk_eigenvalue N r k`.
/-- The complex spectrum of the torus walk matrix consists exactly of the Fourier-mode
eigenvalues. -/
theorem discrete_torus_walk_spectrum_eq
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) :
    spectrum ℂ (discrete_torus_walk_transition_matrix_complex N r) =
      Set.range (discrete_torus_walk_eigenvalue N r) := sorry

-- Proof sketch: diagonalize the circulant transition matrix by the Fourier basis, use that all
-- nontrivial eigenvalues have modulus at most `γ`, and translate the spectral estimate to the
-- total-variation distance.
/-- For odd `N`, the torus walk converges exponentially fast to the uniform distribution with rate
`γ`. -/
theorem discrete_torus_walk_totalVariation_bound_of_odd
    (N : ℕ) [NeZero N] (hodd : Odd N) (r : Set.Ioo (0 : ℝ) 1) :
    ∃ C : ℝ,
      0 ≤ C ∧
          ∀ n : ℕ,
          ∀ μ : ProbabilityMeasure (Fin N),
            let κn : Kernel (Fin N) (Fin N) := discrete_torus_walk_kernel N r ^ n
            totalVariationDistance
                (⟨κn ∘ₘ (μ : Measure (Fin N)),
                  inferInstance⟩ : ProbabilityMeasure (Fin N))
                (discrete_torus_walk_uniform_distribution N) ≤
              C * discrete_torus_walk_convergence_factor N r ^ n := sorry

/-- The lazy perturbation `p_ε = (1 - ε) p + ε I` of the asymmetric torus walk. -/
def lazy_discrete_torus_walk_transition_matrix
    (N : ℕ) (r ε : Set.Ioo (0 : ℝ) 1) : Fin N → Fin N → ℝ≥0∞ :=
  fun i j ↦
    ENNReal.ofReal (1 - (ε : ℝ)) * discrete_torus_walk_transition_matrix N r i j +
      if j = i then ENNReal.ofReal (ε : ℝ) else 0

-- Proof sketch: unfold `lazy_discrete_torus_walk_transition_matrix`; it is obtained by scaling the
-- original torus walk by `1 - ε` and adding the diagonal holding mass `ε`.
/-- The lazy torus walk is the convex combination `(1 - ε) p + ε I`. -/
theorem lazy_discrete_torus_walk_transition_matrix_apply
    (N : ℕ) (r ε : Set.Ioo (0 : ℝ) 1) (i j : Fin N) :
    lazy_discrete_torus_walk_transition_matrix N r ε i j =
      ENNReal.ofReal (1 - (ε : ℝ)) * discrete_torus_walk_transition_matrix N r i j +
        if j = i then ENNReal.ofReal (ε : ℝ) else 0 := rfl

/-- The canonical Markov-kernel view of the lazy torus walk. -/
abbrev lazy_discrete_torus_walk_kernel
    (N : ℕ) (r ε : Set.Ioo (0 : ℝ) 1) : Kernel (Fin N) (Fin N) :=
  discreteMatrixKernel (lazy_discrete_torus_walk_transition_matrix N r ε)

/-- The lazy torus walk transition matrix viewed over `ℂ` for spectral calculations. -/
def lazy_discrete_torus_walk_transition_matrix_complex
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (ε : Set.Ioo (0 : ℝ) 1) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j ↦ (lazy_discrete_torus_walk_transition_matrix N r ε i j).toReal

/-- The Fourier eigenvalue of the lazy torus walk at mode `k`. -/
def lazy_discrete_torus_walk_eigenvalue
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (ε : ℝ) (k : Fin N) : ℂ :=
  (1 - ε) * discrete_torus_walk_eigenvalue N r k + ε

-- Proof sketch: the lazy matrix is the convex combination `(1 - ε) p + ε I` of two stochastic
-- matrices, so every row sum remains equal to `1`.
/-- Every row of the lazy torus walk transition matrix has total mass `1`. -/
theorem lazy_discrete_torus_walk_transition_matrix_isStochastic
    (N : ℕ) (r ε : Set.Ioo (0 : ℝ) 1) :
    IsStochasticMatrix (lazy_discrete_torus_walk_transition_matrix N r ε) := sorry

/-- The lazy torus walk kernel is Markov. -/
instance lazy_discrete_torus_walk_kernel.instIsMarkovKernel
    (N : ℕ) (r ε : Set.Ioo (0 : ℝ) 1) :
    IsMarkovKernel (lazy_discrete_torus_walk_kernel N r ε) := by
  simpa [lazy_discrete_torus_walk_kernel] using
    (discreteMatrixKernel_isMarkovKernel
      (lazy_discrete_torus_walk_transition_matrix N r ε)
      (lazy_discrete_torus_walk_transition_matrix_isStochastic N r ε))

-- Proof sketch: adding a positive holding probability preserves connectivity of the underlying
-- torus graph, so irreducibility is unchanged.
/-- Every lazy perturbation of the torus walk is irreducible. -/
theorem lazy_discrete_torus_walk_isIrreducible
    (N : ℕ) [NeZero N] (r ε : Set.Ioo (0 : ℝ) 1) :
    Kernel.IsIrreducible (Measure.count : Measure (Fin N))
      (lazy_discrete_torus_walk_kernel N r ε) := sorry

-- Proof sketch: the positive holding probability gives a one-step return at every state, so the
-- period is `1`.
/-- Every lazy perturbation of the torus walk is aperiodic. -/
theorem lazy_discrete_torus_walk_isAperiodic
    (N : ℕ) [NeZero N] (r ε : Set.Ioo (0 : ℝ) 1) :
    IsAperiodic (lazy_discrete_torus_walk_kernel N r ε) :=
  sorry

/-- The threshold `ε₀` separating the two formulas for the second-largest modulus in the even
case. -/
def lazy_discrete_torus_walk_threshold
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : ℝ :=
  ((1 - (2 * (r : ℝ) - 1) ^ 2) * Real.sin (2 * Real.pi / N) ^ 2) /
    (((1 - (2 * (r : ℝ) - 1) ^ 2) * Real.sin (2 * Real.pi / N) ^ 2) +
      2 * Real.cos (2 * Real.pi / N))

/-- The modulus of the second largest eigenvalue of the lazy torus walk, written in the textbook's
piecewise form. -/
def lazy_discrete_torus_walk_second_modulus
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (ε : ℝ) : ℝ :=
  if ε ≤ lazy_discrete_torus_walk_threshold N r then
    1 - 2 * ε
  else
    Real.sqrt
      (((1 - ε) * Real.cos (2 * Real.pi / N) + ε) ^ 2 +
        (((1 - ε) * (2 * (r : ℝ) - 1) * Real.sin (2 * Real.pi / N)) ^ 2))

-- Proof sketch: the holding probability adds `ε` to each eigenvalue after scaling the original
-- spectrum by `1 - ε`; the Fourier modes still diagonalize the walk.
/-- The complex spectrum of the lazy torus walk matrix consists exactly of the lazy Fourier-mode
eigenvalues. -/
theorem lazy_discrete_torus_walk_spectrum_eq
    (N : ℕ) (r ε : Set.Ioo (0 : ℝ) 1) :
    spectrum ℂ (lazy_discrete_torus_walk_transition_matrix_complex N r ε) =
      Set.range (lazy_discrete_torus_walk_eigenvalue N r (ε : ℝ)) := sorry

-- Proof sketch: combine `lazy_discrete_torus_walk_spectrum_eq` with the even-cycle ordering of the
-- Fourier moduli; the nontrivial mode of largest modulus is either the `N / 2`-mode or the
-- first mode, and the threshold `ε₀` is exactly where those two branches cross.
/-- For even `N`, the textbook piecewise quantity `γ_ε` is exactly the largest modulus among the
nontrivial spectral values of the lazy torus walk. -/
theorem lazy_discrete_torus_walk_second_modulus_spec
    (N : ℕ) [NeZero N] (heven : Even N) (r : Set.Ioo (0 : ℝ) 1) (ε : Set.Ioo (0 : ℝ) 1) :
    (∀ z : ℂ,
        z ∈ spectrum ℂ (lazy_discrete_torus_walk_transition_matrix_complex N r ε) →
        z ≠ 1 →
        ‖z‖ ≤ lazy_discrete_torus_walk_second_modulus N r (ε : ℝ)) ∧
      ∃ z : ℂ,
        z ∈ spectrum ℂ (lazy_discrete_torus_walk_transition_matrix_complex N r ε) ∧
        z ≠ 1 ∧
        ‖z‖ = lazy_discrete_torus_walk_second_modulus N r (ε : ℝ) := sorry

-- Proof sketch: the lazy perturbation is irreducible and aperiodic for every `ε > 0`; combine the
-- spectral description of the even case with the finite-state convergence estimate to get the
-- total-variation bound.
/-- For even `N`, every lazy perturbation converges exponentially fast to the uniform distribution
with rate `γ_ε`. -/
theorem lazy_discrete_torus_walk_totalVariation_bound_of_even
    (N : ℕ) [NeZero N] (heven : Even N) (r ε : Set.Ioo (0 : ℝ) 1) :
    ∃ C : ℝ,
      0 ≤ C ∧
          ∀ n : ℕ,
          ∀ μ : ProbabilityMeasure (Fin N),
            let κn : Kernel (Fin N) (Fin N) := lazy_discrete_torus_walk_kernel N r ε ^ n
            totalVariationDistance
                (⟨κn ∘ₘ (μ : Measure (Fin N)),
                  inferInstance⟩ : ProbabilityMeasure (Fin N))
                (discrete_torus_walk_uniform_distribution N) ≤
              C * lazy_discrete_torus_walk_second_modulus N r (ε : ℝ) ^ n := sorry

-- Proof sketch: the function `ε ↦ |λ_{ε,N/2}|` decreases, the function `ε ↦ |λ_{ε,1}|` increases,
-- and the two branches meet exactly at `ε₀`, so the piecewise second-modulus function is minimized
-- there.
/-- In the even case, the lazy torus walk has the best exponential convergence rate at the
threshold `ε₀`. -/
theorem lazy_discrete_torus_walk_second_modulus_minimized_at_threshold
    (N : ℕ) [NeZero N] (heven : Even N) (r : Set.Ioo (0 : ℝ) 1) {ε : ℝ}
    (hε₀ : 0 < lazy_discrete_torus_walk_threshold N r)
    (hε₁ : lazy_discrete_torus_walk_threshold N r < 1)
    (hε : 0 < ε) (hε' : ε < 1) :
    lazy_discrete_torus_walk_second_modulus N r (lazy_discrete_torus_walk_threshold N r) ≤
      lazy_discrete_torus_walk_second_modulus N r ε := sorry

end ProbabilityTheory
