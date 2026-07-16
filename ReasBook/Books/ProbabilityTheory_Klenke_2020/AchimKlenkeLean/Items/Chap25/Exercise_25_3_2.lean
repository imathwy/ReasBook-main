import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_66
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Exercise_21_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ

/- Domain-style sampling for the scalar pathwise Stratonovich layer:
* primary domain: pathwise stochastic integration along admissible partition sequences;
* primitive data: `partitionStratonovichApproximationUpTo`;
* source-facing owner: `HasPathwiseStratonovichIntegralAlong`;
* core/canonical bridge: `pathwiseStratonovichIntegralAlong`;
* square-variation owner abstraction: `HasContinuousSquareVariationAlongPartition`;
* source-facing set view: `𝒞_qvAlong`;
* chosen square-variation bridge: `HasSquareVariationAlongPartition`;
* relevant chapter owners in the same domain: `HasPathwiseItoIntegralAlong`,
  `pathwiseItoIntegralAlong`, and `IsContinuousLocalMartingale`. -/

/-- The midpoint partition sum on `[0,T]` for the pathwise Stratonovich integral of the integrand
`f (X)` along the admissible partition sequence `P`. -/
def partitionStratonovichApproximationUpTo
    (f : ℝ → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    f ((X (partitionNextPointUpTo P n k T) + X (P n k)) / 2) *
      (X (partitionNextPointUpTo P n k T) - X (P n k))

-- Proof sketch: unfold `partitionStratonovichApproximationUpTo`; this is exactly the finite
-- midpoint Riemann sum over the truncated `n`-th partition row.
/-- Expanding `partitionStratonovichApproximationUpTo` gives the midpoint partition sum on
`[0,T]`. -/
theorem partitionStratonovichApproximationUpTo_def
    (f : ℝ → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    partitionStratonovichApproximationUpTo f X P T n =
      Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
        f ((X (partitionNextPointUpTo P n k T) + X (P n k)) / 2) *
          (X (partitionNextPointUpTo P n k T) - X (P n k)) := rfl

/-- `HasPathwiseStratonovichIntegralAlong f X P I` means that the midpoint partition sums of `f`
against `X` along the admissible partition sequence `P` converge pointwise to the function `I`. -/
def HasPathwiseStratonovichIntegralAlong
    (f : ℝ → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (I : NNReal → ℝ) : Prop :=
  ∀ T : NNReal,
    Tendsto (partitionStratonovichApproximationUpTo f X P T) atTop (nhds (I T))

-- Proof sketch: evaluate the defining predicate `HasPathwiseStratonovichIntegralAlong` at the
-- time horizon `T`.
/-- A pathwise Stratonovich integral realization yields convergence of the midpoint partition sums
at each fixed time horizon. -/
theorem HasPathwiseStratonovichIntegralAlong.tendsto
    {f : ℝ → ℝ} {X : PathSpace} {P : ℕ → ℕ → NNReal}
    [IsAdmissiblePartitionSequence P] {I : NNReal → ℝ}
    (hI : HasPathwiseStratonovichIntegralAlong f X P I) (T : NNReal) :
    Tendsto (partitionStratonovichApproximationUpTo f X P T) atTop (nhds (I T)) :=
  hI T

/-- The canonical bridge/view `pathwiseStratonovichIntegralAlong f X P` is the pointwise
`limUnder` realization of the midpoint partition sums. -/
noncomputable def pathwiseStratonovichIntegralAlong
    (f : ℝ → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    NNReal → ℝ :=
  fun T ↦ limUnder atTop (partitionStratonovichApproximationUpTo f X P T)

/-- Any chosen realization of the midpoint partition sums agrees with the canonical `limUnder`
bridge `pathwiseStratonovichIntegralAlong f X P`. -/
theorem HasPathwiseStratonovichIntegralAlong.eq_pathwiseStratonovichIntegralAlong
    {f : ℝ → ℝ} {X : PathSpace} {P : ℕ → ℕ → NNReal} [IsAdmissiblePartitionSequence P]
    {I : NNReal → ℝ}
    (hI : HasPathwiseStratonovichIntegralAlong f X P I) :
    pathwiseStratonovichIntegralAlong f X P = I := by
  ext T
  simpa [pathwiseStratonovichIntegralAlong] using (hI T).limUnder_eq

namespace ProbabilityTheory

-- Proof sketch: compare the midpoint sums with the left-point Itô sums and use a second-order
-- Taylor expansion of `F` along each partition interval. The quadratic-variation convergence of
-- `X` along `P` controls the correction term and yields convergence of the midpoint sums.
/-- If `V` is a chosen square-variation process of `X` along `P` and `F ∈ C²(ℝ)`, then the
midpoint sums for `F' (X)` admit the canonical pathwise Stratonovich-integral realization
`pathwiseStratonovichIntegralAlong (deriv F) X P`. -/
theorem hasPathwiseStratonovichIntegralAlong_deriv_of_hasSquareVariationAlongPartition
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] {V : PathwiseProcess}
    (hX : HasSquareVariationAlongPartition X P V) :
    HasPathwiseStratonovichIntegralAlong
      (deriv F)
      X
      P
      (pathwiseStratonovichIntegralAlong (deriv F) X P) := by
  intro T
  exact tendsto_nhds_limUnder <| by
    sorry

/-- For `X ∈ 𝒞_qv^P` and `F ∈ C²(ℝ)`, the midpoint sums for `F' (X)` admit the canonical
pathwise Stratonovich-integral realization `pathwiseStratonovichIntegralAlong (deriv F) X P`. -/
theorem hasPathwiseStratonovichIntegralAlong_deriv
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P) :
    HasPathwiseStratonovichIntegralAlong
      (deriv F)
      X
      P
      (pathwiseStratonovichIntegralAlong (deriv F) X P) := by
  rcases hX with ⟨V, hV⟩
  exact
    hasPathwiseStratonovichIntegralAlong_deriv_of_hasSquareVariationAlongPartition
      F hF X P hV

-- Proof sketch: apply the canonical realization from
-- `hasPathwiseStratonovichIntegralAlong_deriv` and rewrite the integrand using `hf`.
/-- Exercise 25.3.2 (1): if `P` is admissible, `X ∈ 𝒞_qv^P`, `F ∈ C²(ℝ)`, and `f = F'`, then the
midpoint partition sums defining the Stratonovich integral of `f (X)` admit a pathwise
realization on every interval `[0,T]`. -/
theorem exists_pathwiseStratonovichIntegralAlong
    (f F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hf : f = deriv F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P) :
    ∃ I : NNReal → ℝ, HasPathwiseStratonovichIntegralAlong f X P I := by
  simpa [hf] using
    (show
      ∃ I : NNReal → ℝ, HasPathwiseStratonovichIntegralAlong (deriv F) X P I from
        ⟨pathwiseStratonovichIntegralAlong (deriv F) X P,
          hasPathwiseStratonovichIntegralAlong_deriv F hF X P hX⟩)

/-- Source-facing `𝒞_qv^P` form of Exercise 25.3.2 (1). -/
theorem exists_pathwiseStratonovichIntegralAlong_of_mem_𝒞_qvAlong
    (f F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hf : f = deriv F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : X ∈ 𝒞_qvAlong P) :
    ∃ I : NNReal → ℝ, HasPathwiseStratonovichIntegralAlong f X P I := by
  simpa [mem_𝒞_qvAlong_iff] using
    exists_pathwiseStratonovichIntegralAlong f F hF hf X P
      ((mem_𝒞_qvAlong_iff X).1 hX)

-- Proof sketch: telescope the midpoint Taylor expansion
-- `F(X_{t'}) - F(X_t) = F'((X_t + X_{t'}) / 2) (X_{t'} - X_t) + o(|X_{t'} - X_t|²)`, sum over the
-- partition row, and use the quadratic-variation control to show that the remainder vanishes.
/-- If `V` is a chosen square-variation process of `X` along `P` and `F ∈ C²(ℝ)`, then the
canonical pathwise Stratonovich integral realization of `F' (X)` along `P` satisfies the
classical substitution rule on `[0,T]`. -/
theorem pathwiseStratonovich_substitution_formula_of_hasSquareVariationAlongPartition
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] {V : PathwiseProcess}
    (hX : HasSquareVariationAlongPartition X P V)
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseStratonovichIntegralAlong (deriv F) X P T := sorry

/-- For `X ∈ 𝒞_qv^P` and `F ∈ C²(ℝ)`, the canonical pathwise Stratonovich integral realization of
`F' (X)` along `P` satisfies the classical substitution rule on `[0,T]`. -/
theorem pathwiseStratonovich_substitution_formula
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P)
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseStratonovichIntegralAlong (deriv F) X P T := by
  rcases hX with ⟨V, hV⟩
  exact
    pathwiseStratonovich_substitution_formula_of_hasSquareVariationAlongPartition
      F hF X P hV T

/-- Source-facing `𝒞_qv^P` form of the pathwise Stratonovich substitution formula. -/
theorem pathwiseStratonovich_substitution_formula_of_mem_𝒞_qvAlong
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : X ∈ 𝒞_qvAlong P)
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseStratonovichIntegralAlong (deriv F) X P T := by
  simpa [mem_𝒞_qvAlong_iff] using
    pathwiseStratonovich_substitution_formula F hF X P
      ((mem_𝒞_qvAlong_iff X).1 hX) T

/-- Every chosen realization of the midpoint sums for `F' (X)` agrees with the canonical bridge
`pathwiseStratonovichIntegralAlong`, so the substitution formula also holds in the textbook form
for an arbitrary pathwise Stratonovich-integral realization `I`. -/
theorem pathwiseStratonovich_substitution_formula_of_hasPathwiseStratonovichIntegralAlong
    (f F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hf : f = deriv F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P)
    {I : NNReal → ℝ} (hI : HasPathwiseStratonovichIntegralAlong f X P I)
    (T : NNReal) :
    F (X T) - F (X 0) = I T := by
  rw [← hI.eq_pathwiseStratonovichIntegralAlong]
  simpa [hf] using pathwiseStratonovich_substitution_formula F hF X P hX T

-- Proof sketch: take a nonconstant continuous local martingale, for instance Brownian motion,
-- and realize its Stratonovich self-integral along an admissible partition sequence. Applying the
-- substitution formula to `F(x) = x^2 / 2` identifies the canonical self-integral on a
-- full-measure set of sample paths with the explicit square process
-- `t ↦ (M_t^2 - M_0^2) / 2`, which is not a local martingale in general because the Itô
-- correction coming from the quadratic variation has been absorbed.
/-- Exercise 25.3.2 (3): in contrast with the Itô integral, the Stratonovich integral with
respect to a continuous local martingale is not a local martingale in general; concretely, there
exists a filtered probability space carrying a continuous local martingale whose square process,
equivalently its Stratonovich self-integral on an almost-sure set of sample paths, fails to be a
local martingale. -/
theorem exists_continuousLocalMartingale_with_non_localMartingale_stratonovich_square :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (Q : ProbabilityMeasure Ω')
      (ℱ : Filtration NNReal mΩ') (M : NNReal → Ω' → ℝ) (P : ℕ → ℕ → NNReal),
        ∃ (_ : IsAdmissiblePartitionSequence P)
          (hM : IsContinuousLocalMartingale ℱ (Q : Measure Ω') M),
            (∀ᵐ ω ∂(Q : Measure Ω'),
              HasPathwiseStratonovichIntegralAlong
                id
                ⟨fun t ↦ M t ω, hM.continuous ω⟩
                P
                (fun t ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2)) ∧
            ¬ IsLocalMartingale
              ℱ
              (Q : Measure Ω')
              (fun t ω ↦ ((M t ω) ^ 2 - (M 0 ω) ^ 2) / 2) := sorry

end ProbabilityTheory
