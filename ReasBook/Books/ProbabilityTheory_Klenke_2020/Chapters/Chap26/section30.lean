import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_26_30 (from Items/Chap26) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

local notation "PathSpace" => EuclideanPathSpace 1

/- Domain-style sampling for Remark 26.30:
- primary domain: rescaled Moran chains and their Wright--Fisher diffusion limit on continuous
  path space;
- sampled owner declarations: `moranTransitionMatrix`,
  `finiteDimensionalDistribution_eq_of_same_stochasticMatrix`,
  `WeakSDESolution.statePathLaw`,
  `wrightFisher_existsStrongMarkovSolutionFamily_nonneg`, and
  `exists_wrightFisherWeakSolution_in_unitInterval`;
- owner abstraction: the discrete side is organized around the Chapter 17 owner
  `moranTransitionMatrix N` and `IsMarkovProcessRealization`, while the limit side is organized
  around the Chapter 26 path-law owner `WeakSDESolution.statePathLaw` carried by
  `GeneralizedWeakSDESolution`;
- primitive data kept here: the rescaled Moran frequency process `rescaledMoranProcess`;
- bridge/view data kept here: the linear-interpolation upgrade
  `rescaledMoranInterpolatedValue`, the resulting continuous-path lift `rescaledMoranPath`, and
  its pushed-forward path law `rescaledMoranPathLaw`;
- derived API kept here: the matrix-level identification of a chain with the canonical Moran
  transition matrix, the induced finite-dimensional-distribution uniqueness statement, the
  source-facing Wright--Fisher finite-dimensional limit theorem for `rescaledMoranProcess`, and
  the path-law bridge theorem for `rescaledMoranPath`.

Layer triage:
- source-facing: `rescaledMoranProcess`, the matrix-characterization theorem, the induced
  finite-dimensional-distribution uniqueness theorem, and the main finite-dimensional
  Wright--Fisher limit theorem below;
- core/canonical: `moranTransitionMatrix`, `IsMarkovProcessRealization`,
  `finiteDimensionalDistribution_eq_of_same_stochasticMatrix`,
  `WeakSDESolution.statePathLaw`, and `GeneralizedWeakSDESolution`;
- bridge/view: `rescaledMoranInterpolatedValue`, `rescaledMoranPath`, `rescaledMoranPathLaw`,
  and the final path-law convergence theorem, which packages the source-facing rescaled Moran
  chains into the canonical continuous path-space owner used by the Wright--Fisher weak-solution
  API.
-/

/-- The rescaled Moran frequency process
`\tilde M_t^N = M^N_{\lfloor N^2 t \rfloor} / N`, written through the canonical Chapter 17
frequency map `moranFrequency`. -/
def rescaledMoranProcess {Ω : Type u} (N : ℕ+) (M : ℕ → Ω → Fin (N + 1)) :
    NNReal → Ω → ℝ :=
  fun t ω ↦ moranFrequency N (M (Nat.floor ((N : ℝ) ^ (2 : ℕ) * (t : ℝ))) ω)

/-- The scalar linear interpolation of the rescaled Moran frequencies at diffusive time scale
`N²t`. At integer mesh points this recovers the source-frequency values
`moranFrequency N (M k ω)`. -/
def rescaledMoranInterpolatedValue {Ω : Type u} (N : ℕ+) (M : ℕ → Ω → Fin (N + 1))
    (ω : Ω) : NNReal → ℝ :=
  fun t ↦
    let x : ℝ := (N : ℝ) ^ (2 : ℕ) * (t : ℝ)
    let k : ℕ := Nat.floor x
    ((k + 1 : ℝ) - x) * moranFrequency N (M k ω) +
      (x - k) * moranFrequency N (M (k + 1) ω)

/-- Bridge/view layer: the linearly interpolated rescaled Moran path on the chapter's
one-dimensional path space. -/
def rescaledMoranPathFun {Ω : Type u} (N : ℕ+) (M : ℕ → Ω → Fin (N + 1))
    (ω : Ω) : NNReal → Fin 1 → ℝ :=
  fun t _ ↦ rescaledMoranInterpolatedValue N M ω t

-- Proof sketch: on each interval `[k / N², (k + 1) / N²]` the displayed formula is affine in
-- `t`, and neighboring affine pieces agree at the mesh points because both evaluate to the same
-- Moran frequency `moranFrequency N (M k ω)`.
/-- For each sample point `ω`, the interpolated rescaled Moran formula defines a continuous
one-dimensional path. -/
theorem continuous_rescaledMoranPathFun {Ω : Type u} (N : ℕ+) (M : ℕ → Ω → Fin (N + 1))
    (ω : Ω) :
    Continuous (rescaledMoranPathFun N M ω) := sorry

/-- Bridge/view layer: the path-valued version of the interpolated rescaled Moran process. -/
def rescaledMoranPath {Ω : Type u} (N : ℕ+) (M : ℕ → Ω → Fin (N + 1)) : Ω → PathSpace :=
  fun ω ↦ ⟨rescaledMoranPathFun N M ω, continuous_rescaledMoranPathFun N M ω⟩

/-- The path law of the interpolated rescaled Moran process started from the probability law `P`.
-/
def rescaledMoranPathLaw {Ω : Type u} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (N : ℕ+) (M : ℕ → Ω → Fin (N + 1)) : Measure PathSpace :=
  (P : Measure Ω).map (rescaledMoranPath N M)

/-- Remark 26.30, discrete uniqueness input: if a stochastic transition matrix on
`{0, 1 / N, ..., 1}` has the Moran support, zero drift, and the square-variation density from
Example 17.22 at every state, then it is exactly the canonical Moran transition matrix. -/
theorem moranTransitionMatrix_eq_of_martingale_and_squareVariationCharacterization
    {N : ℕ+} {p : Fin (N + 1) → Fin (N + 1) → ℝ≥0∞} (hp : IsStochasticMatrix p)
    (h_support :
      ∀ i : Fin (N + 1), ∀ j : Fin (N + 1), p i j ≠ 0 →
        (j : ℕ) = (i : ℕ) + 1 ∨ j = i ∨ (i : ℕ) = (j : ℕ) + 1)
    (h_drift :
      ∀ i : Fin (N + 1),
        ∑' j : Fin (N + 1),
            ((moranFrequency N j - moranFrequency N i) * (p i j).toReal) = 0)
    (h_squareVariation :
      ∀ i : Fin (N + 1),
        ∑' j : Fin (N + 1),
            (((moranFrequency N j - moranFrequency N i) ^ (2 : ℕ)) * (p i j).toReal) =
          moranSquareVariationDensity N i) :
    p = moranTransitionMatrix N := by
  funext i
  exact moranTransitionMatrix_row_of_squareVariationFormula hp (h_support i) (h_drift i)
    (h_squareVariation i)

/-- Remark 26.30, process form: the martingale and square-variation characterization determines
the law of the Moran chain uniquely. Any discrete-time realization with those one-step
characteristics has the same ordered finite-dimensional distributions as the canonical Moran
chain. -/
theorem finiteDimensionalDistribution_eq_of_moran_martingale_and_squareVariationCharacterization
    {N : ℕ+} {p : Fin (N + 1) → Fin (N + 1) → ℝ≥0∞} (hp : IsStochasticMatrix p)
    (h_support :
      ∀ i : Fin (N + 1), ∀ j : Fin (N + 1), p i j ≠ 0 →
        (j : ℕ) = (i : ℕ) + 1 ∨ j = i ∨ (i : ℕ) = (j : ℕ) + 1)
    (h_drift :
      ∀ i : Fin (N + 1),
        ∑' j : Fin (N + 1),
            ((moranFrequency N j - moranFrequency N i) * (p i j).toReal) = 0)
    (h_squareVariation :
      ∀ i : Fin (N + 1),
        ∑' j : Fin (N + 1),
            (((moranFrequency N j - moranFrequency N i) ^ (2 : ℕ)) * (p i j).toReal) =
          moranSquareVariationDensity N i)
    {Ω : Type u} [MeasurableSpace Ω] {Ω' : Type v} [MeasurableSpace Ω']
    {P : Fin (N + 1) → ProbabilityMeasure Ω}
    {Q : Fin (N + 1) → ProbabilityMeasure Ω'}
    {X : ℕ → Ω → Fin (N + 1)} {Y : ℕ → Ω' → Fin (N + 1)}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (moranTransitionMatrix N) ^ n) Q Y]
    (i : Fin (N + 1)) {n : ℕ} (times : Fin (n + 1) → ℕ)
    (h_zero : times 0 = 0) (htimes : StrictMono times) :
    (P i : Measure Ω).map (fun ω x ↦ X (times x) ω) =
      (Q i : Measure Ω').map (fun ω x ↦ Y (times x) ω) := by
  have hp_eq : p = moranTransitionMatrix N :=
    moranTransitionMatrix_eq_of_martingale_and_squareVariationCharacterization hp h_support
      h_drift h_squareVariation
  subst p
  simpa using
    finiteDimensionalDistribution_eq_of_same_stochasticMatrix (moranTransitionMatrix N) i times
      h_zero htimes

local notation "σWF" => oneDimensionalDiffusion (wrightFisherScalarDiffusionCoeff 2)
local notation "bWF" => oneDimensionalDrift (fun _ _ ↦ (0 : ℝ))

/-- Remark 26.30, source-facing scaling limit: if the initial Moran frequencies converge to
`x ∈ [0, 1]`, then the rescaled Moran step processes
`\tilde M_t^N = M_{\lfloor N^2 t \rfloor}^N / N` converge in finite-dimensional distributions to
the scalar coordinate process of the Wright--Fisher diffusion with parameter `γ = 2` started from
`x`. -/
theorem exists_wrightFisher_limit_of_rescaledMoranProcesses
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {ΩN : ℕ → Type u} [∀ n : ℕ, MeasurableSpace (ΩN n)]
    (P : ∀ n : ℕ, Fin (Nat.succPNat n + 1) → ProbabilityMeasure (ΩN n))
    (M : ∀ n : ℕ, ℕ → ΩN n → Fin (Nat.succPNat n + 1))
    (hM :
      ∀ n : ℕ,
        IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel (moranTransitionMatrix (Nat.succPNat n)) ^ k)
          (P n) (M n))
    (i0 : ∀ n : ℕ, Fin (Nat.succPNat n + 1))
    (hi0 : Tendsto (fun n : ℕ ↦ moranFrequency (Nat.succPNat n) (i0 n)) atTop (nhds x)) :
    ∃ L :
        GeneralizedWeakSDESolution
          (Measure.dirac (oneDimensionalState x))
          σWF bWF,
      L.IsWeaklyUnique ∧
        ((fun n : ℕ ↦ P n (i0 n)),
            fun n : ℕ ↦ rescaledMoranProcess (Nat.succPNat n) (M n))
          ⟶[fdd]
            ((⟨L.μ, inferInstance⟩ : ProbabilityMeasure L.Ω), fun t ω ↦ L ω t 0) := sorry

/-- Bridge/view companion to Remark 26.30: packaging the same rescaled Moran chains by linear
interpolation yields continuous-path laws that converge weakly on the chapter's canonical
one-dimensional path space to the state-path law of the Wright--Fisher diffusion with parameter
`γ = 2` started from `x`. -/
theorem exists_wrightFisher_pathLimit_of_rescaledMoranProcesses
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {ΩN : ℕ → Type u} [∀ n : ℕ, MeasurableSpace (ΩN n)]
    (P : ∀ n : ℕ, Fin (Nat.succPNat n + 1) → ProbabilityMeasure (ΩN n))
    (M : ∀ n : ℕ, ℕ → ΩN n → Fin (Nat.succPNat n + 1))
    (hM :
      ∀ n : ℕ,
        IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel (moranTransitionMatrix (Nat.succPNat n)) ^ k)
          (P n) (M n))
    (i0 : ∀ n : ℕ, Fin (Nat.succPNat n + 1))
    (hi0 : Tendsto (fun n : ℕ ↦ moranFrequency (Nat.succPNat n) (i0 n)) atTop (nhds x)) :
    ∃ L :
        GeneralizedWeakSDESolution
          (Measure.dirac (oneDimensionalState x))
          σWF bWF,
      L.IsWeaklyUnique ∧
        TendstoInDistribution
          (fun n : ℕ ↦ rescaledMoranPath (Nat.succPNat n) (M n))
          atTop
          L.X
          (fun n : ℕ ↦ (P n (i0 n) : Measure (ΩN n)))
          L.μ := sorry

end ProbabilityTheory
