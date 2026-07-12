import ProbabilityTheory_Klenke_2020.Items.Chap14.Corollary_14_43
import ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_41

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Finset
open scoped ProbabilityTheory

noncomputable section

universe u

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

/-- The finite-dimensional coordinate projection of a path indexed by `NNReal`. -/
def finiteDimensionalProjection {n : ℕ} (times : Fin (n + 1) → NNReal) :
    (NNReal → E) → Fin (n + 1) → E :=
  fun ω i ↦ ω (times i)

-- Proof sketch: each component of the projection is evaluation at the measurable coordinate
-- `times i`; measurability of the tuple-valued map follows from `measurable_pi_lambda`.
/-- Finite-dimensional projections of the canonical path space are measurable. -/
theorem measurable_finiteDimensionalProjection {n : ℕ} (times : Fin (n + 1) → NNReal) :
    Measurable
      (finiteDimensionalProjection times : (NNReal → E) → Fin (n + 1) → E) := sorry

private def iicEquivFin (n : ℕ) : Finset.Iic n ≃ Fin (n + 1) where
  toFun i := ⟨i.1, Nat.lt_succ_of_le <| Finset.mem_Iic.mp i.2⟩
  invFun i := ⟨i.1, Finset.mem_Iic.mpr <| Nat.le_of_lt_succ i.2⟩
  left_inv i := by
    cases i
    rfl
  right_inv i := by
    cases i
    rfl

private def orderedTimeChain {n : ℕ} (times : Fin (n + 1) → NNReal) :
    Π _ : Finset.Iic n, NNReal :=
  fun i ↦ times (iicEquivFin n i)

private theorem orderedTimeChain_strictMono {n : ℕ} {times : Fin (n + 1) → NNReal}
    (htimes : StrictMono times) :
    StrictMono (orderedTimeChain times) := by
  intro i j hij
  exact htimes (by simpa [orderedTimeChain, iicEquivFin] using hij)

/-- The ordered finite-dimensional distribution kernel attached to a family of transition kernels
`κ t`, started from a fixed initial state and indexed by a strictly increasing time tuple. -/
def markovSemigroupFiniteDimKernel (κ : NNReal → Kernel E E) {n : ℕ}
    (times : Fin (n + 1) → NNReal) (htimes : StrictMono times) :
    Kernel E (Fin (n + 1) → E) :=
  (consistentFamilyFiniteDimensionalKernel (fun {s t : NNReal} _ ↦ κ (t - s))
      (orderedTimeChain times) (orderedTimeChain_strictMono htimes)).map
    (fun x i ↦ x ((iicEquivFin n).symm i))

-- Proof sketch: apply Lemma 14.41 to the owner abstraction `IsMarkovSemigroup` to obtain the
-- consistent time-difference kernel family from Theorem 14.42, then use Corollary 14.43 for the
-- corresponding path-space measure statement. Uniqueness is determined by the ordered
-- finite-dimensional marginals.
/-- Corollary 14.44 (1): a Markov semigroup on a Polish space determines a unique path-space
stochastic kernel whose finite-dimensional marginals are the iterated transition laws along every
strictly increasing time tuple starting at `0`. -/
theorem existsUnique_markovPathKernel
    (κ : NNReal → Kernel E E) [IsMarkovSemigroup κ] :
    ∃! pathKernel : Kernel E (NNReal → E),
      IsMarkovKernel pathKernel ∧
        ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
          times 0 = 0 → ∀ htimes : StrictMono times,
            pathKernel.map (finiteDimensionalProjection times) =
              markovSemigroupFiniteDimKernel κ times htimes := sorry

-- Proof sketch: compose the path kernel from the first clause with the initial law `μ`. The
-- resulting measure is a probability measure, and its finite-dimensional marginals are the mixed
-- laws obtained from the finite-dimensional kernel by integrating against `μ`.
/-- Corollary 14.44 (2): every initial probability measure induces a unique probability law on the
path space whose finite-dimensional marginals are obtained by averaging the semigroup kernel from
Corollary 14.44 (1) against the initial law. -/
theorem existsUnique_markovPathMeasure
    (κ : NNReal → Kernel E E) [IsMarkovSemigroup κ] (μ : Measure E)
    [IsProbabilityMeasure μ] :
    ∃! pathMeasure : Measure (NNReal → E),
      IsProbabilityMeasure pathMeasure ∧
        ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
          times 0 = 0 → ∀ htimes : StrictMono times,
            pathMeasure.map (finiteDimensionalProjection times) =
              markovSemigroupFiniteDimKernel κ times htimes ∘ₘ μ := sorry
