import Mathlib
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_58
import ProbabilityTheory_Klenke_2020.Chap21.Exercise_21_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ

/- Definition 21.58: recall the dyadic square-variation class `𝒞_qv`, whose source-facing role
is used in the pathwise Itô discussion below. -/
#check 𝒞_qv

/- Domain-style sampling for the scalar pathwise Itô layer:
* primary domain: pathwise stochastic integration along admissible partition sequences;
* source-facing square-variation owner: `HasContinuousSquareVariationAlongPartition`;
* source-facing set view: `𝒞_qvAlong`;
* primitive data: `partitionPathwiseItoApproximationUpTo` and
  `weightedPartitionQuadraticVariationApproximationUpTo`;
* canonical derived objects: `pathwiseItoIntegralAlong` and `pathwiseItoCorrectionAlong`;
* bridge/view: Stieltjes-measure formulas for a chosen continuous square-variation path. -/

/-- The left-point partition sum `∑ H_t (X_{t'} - X_t)` on `[0, T]` along the `n`-th row of an
admissible partition sequence `P`. -/
def partitionPathwiseItoApproximationUpTo
    (H : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    H (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k))

/-- `HasPathwiseItoIntegralAlong H X P I` means that the left-point partition sums of `H` against
`X` along the admissible partition sequence `P` converge pointwise to the chosen realization `I`.
-/
def HasPathwiseItoIntegralAlong
    (H : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (I : NNReal → ℝ) : Prop :=
  ∀ T : NNReal,
    Tendsto (partitionPathwiseItoApproximationUpTo H X P T) atTop (nhds (I T))

/- A pathwise Itô integral realization yields the defining convergence statement at each fixed
time horizon. -/
theorem HasPathwiseItoIntegralAlong.tendsto
    {H : NNReal → ℝ} {X : PathSpace} {P : ℕ → ℕ → NNReal}
    [IsAdmissiblePartitionSequence P] {I : NNReal → ℝ}
    (hI : HasPathwiseItoIntegralAlong H X P I) (T : NNReal) :
    Tendsto (partitionPathwiseItoApproximationUpTo H X P T) atTop (nhds (I T)) :=
  hI T

/-- The canonical bridge/view `pathwiseItoIntegralAlong H X P` is the pointwise `limUnder`
realization of the left-point partition sums. -/
noncomputable def pathwiseItoIntegralAlong
    (H : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    NNReal → ℝ :=
  fun T ↦ limUnder atTop (partitionPathwiseItoApproximationUpTo H X P T)

/-- Any chosen realization of the left-point partition sums agrees with the canonical `limUnder`
bridge `pathwiseItoIntegralAlong H X P`. -/
theorem HasPathwiseItoIntegralAlong.eq_pathwiseItoIntegralAlong
    {H : NNReal → ℝ} {X : PathSpace} {P : ℕ → ℕ → NNReal} [IsAdmissiblePartitionSequence P]
    {I : NNReal → ℝ}
    (hI : HasPathwiseItoIntegralAlong H X P I) :
    pathwiseItoIntegralAlong H X P = I := by
  ext T
  simpa [pathwiseItoIntegralAlong] using (hI T).limUnder_eq

/-- The canonical quadratic correction in the scalar pathwise Itô formula is the pointwise
`limUnder` of the weighted quadratic partition sums with weight `F''(X_t)`, multiplied by
`1 / 2`. -/
noncomputable def pathwiseItoCorrectionAlong
    (F : ℝ → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    NNReal → ℝ :=
  fun T ↦
    (1 / 2 : ℝ) *
      limUnder atTop
        (weightedPartitionQuadraticVariationApproximationUpTo
          (fun t ↦ iteratedDeriv 2 F (X t))
          X
          P
          T)

/-- Evaluating `pathwiseItoCorrectionAlong F X P` gives the `limUnder` of the weighted quadratic
partition sums defining the scalar Itô correction term. -/
theorem pathwiseItoCorrectionAlong_def
    (F : ℝ → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) :
    pathwiseItoCorrectionAlong F X P T =
      (1 / 2 : ℝ) *
        limUnder atTop
          (weightedPartitionQuadraticVariationApproximationUpTo
            (fun t ↦ iteratedDeriv 2 F (X t))
            X
            P
            T) := rfl

-- Proof sketch: telescope the Taylor expansion
-- `F(X_{t'}) - F(X_t) = F'(X_t) ΔX + ½ F''(X_t) (ΔX)^2 + R`, control the remainder using the
-- continuity of `iteratedDeriv 2 F` on the compact range of `X` over `[0,T]`, and use the
-- quadratic-variation convergence of `X` along `P` to identify the second-order term and obtain
-- a pathwise Itô-integral realization for `t ↦ deriv F (X t)`.

/-- For `X ∈ 𝒞_qv^P` and `F ∈ C²(ℝ)`, the left-point sums for `F' (X)` admit the canonical
pathwise Itô-integral realization `pathwiseItoIntegralAlong (fun t ↦ deriv F (X t)) X P`. -/
theorem hasPathwiseItoIntegralAlong_comp_deriv
    (F : ℝ → ℝ) (hf : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P) :
    HasPathwiseItoIntegralAlong
      (fun t ↦ deriv F (X t))
      X
      P
      (pathwiseItoIntegralAlong (fun t ↦ deriv F (X t)) X P) := by
  rcases hX with ⟨V, hV⟩
  intro T
  exact tendsto_nhds_limUnder <| by
    sorry

/-- The canonical pathwise Itô integral realization of `F' (X)` along `P` gives the convergence
of the left-point partition sums at each fixed horizon `T`. -/
theorem tendsto_partitionPathwiseItoApproximationUpTo_comp_deriv
    (F : ℝ → ℝ) (hf : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P)
    (T : NNReal) :
    Tendsto
      (partitionPathwiseItoApproximationUpTo
        (fun t ↦ deriv F (X t))
        X
        P
        T)
      atTop
      (nhds (pathwiseItoIntegralAlong (fun t ↦ deriv F (X t)) X P T)) :=
  (hasPathwiseItoIntegralAlong_comp_deriv F hf X P hX).tendsto T

-- Proof sketch: telescope the Taylor expansion of `F ∘ X` along the partition row, identify the
-- first-order term with `pathwiseItoIntegralAlong (fun t ↦ deriv F (X t)) X P T`, and collect
-- the second-order contributions into the canonical correction object
-- `pathwiseItoCorrectionAlong F X P T`.
/-- Theorem 25.25: for an admissible partition sequence `P`, a path
`X ∈ 𝒞_qv^P`, and a `C²` function `F`, the canonical pathwise Itô integral realization of the
left-point sums for `F' (X)` along `P` satisfies the pathwise Itô formula on `[0, T]` with the
canonical quadratic correction term `pathwiseItoCorrectionAlong F X P T`. -/
theorem pathwiseItoFormula
    (F : ℝ → ℝ) (hf : ContDiff ℝ 2 F)
    (X : PathSpace)
    (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P)
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseItoIntegralAlong (fun t ↦ deriv F (X t)) X P T +
        pathwiseItoCorrectionAlong F X P T := sorry

/-- Source-facing `𝒞_qv^P` form of Theorem 25.25. -/
theorem pathwiseItoFormula_of_mem_𝒞_qvAlong
    (F : ℝ → ℝ) (hf : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : X ∈ 𝒞_qvAlong P)
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseItoIntegralAlong (fun t ↦ deriv F (X t)) X P T +
        pathwiseItoCorrectionAlong F X P T := by
  simpa [mem_𝒞_qvAlong_iff] using
    pathwiseItoFormula F hf X P ((mem_𝒞_qvAlong_iff X).1 hX) T

-- Proof sketch: the `C²` hypothesis makes the weight `t ↦ F''(X_t)` continuous, so Exercise
-- 21.10.2 applies to the chosen continuous square-variation path `V`.
/-- If `F ∈ C²(ℝ)` and a chosen continuous square-variation path `V = ⟨X⟩` along `P` is
represented by a Stieltjes measure `μV`, then the canonical scalar Itô correction agrees with the
corresponding Lebesgue--Stieltjes integral. -/
theorem pathwiseItoCorrectionAlong_eq_lebesgueStieltjesIntegral
    (F : ℝ → ℝ) (hf : ContDiff ℝ 2 F)
    (X : PathSpace) (V : PathSpace) (μV : Measure NNReal)
    (hμV :
      ∀ T : NNReal,
        V T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μV)
    (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasSquareVariationAlongPartition X P V)
    (T : NNReal) :
    pathwiseItoCorrectionAlong F X P T =
      (1 / 2 : ℝ) *
        ∫ s in Set.Icc 0 T, iteratedDeriv 2 F (X s) ∂μV := sorry

/-- If a chosen continuous square-variation path of `X` is represented by a Stieltjes measure,
then Theorem 25.25 rewrites to the corresponding Lebesgue--Stieltjes form. -/
theorem pathwiseItoFormula_of_squareVariationMeasureRepresentation
    (F : ℝ → ℝ) (hf : ContDiff ℝ 2 F)
    (X : PathSpace) (V : PathSpace) (μV : Measure NNReal)
    (hμV :
      ∀ T : NNReal,
        V T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μV)
    (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasSquareVariationAlongPartition X P V)
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseItoIntegralAlong (fun t ↦ deriv F (X t)) X P T +
        (1 / 2 : ℝ) *
          ∫ s in Set.Icc 0 T, iteratedDeriv 2 F (X s) ∂μV := by
  rw [← pathwiseItoCorrectionAlong_eq_lebesgueStieltjesIntegral F hf X V μV hμV P hX T]
  exact pathwiseItoFormula F hf X P ⟨V, hX⟩ T

/-- Every chosen realization of the left-point sums for `F' (X)` agrees with the canonical
bridge `pathwiseItoIntegralAlong`, so the Stieltjes-measure form of Theorem 25.25 also holds for
an arbitrary pathwise Itô-integral realization `I`. -/
theorem pathwiseItoFormula_of_hasPathwiseItoIntegralAlong
    (F : ℝ → ℝ) (hf : ContDiff ℝ 2 F)
    (X : PathSpace) (V : PathSpace) (μV : Measure NNReal)
    (hμV :
      ∀ T : NNReal,
        V T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μV)
    (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasSquareVariationAlongPartition X P V)
    {I : NNReal → ℝ}
    (hI : HasPathwiseItoIntegralAlong (fun t ↦ deriv F (X t)) X P I)
    (T : NNReal) :
    F (X T) - F (X 0) =
      I T +
        (1 / 2 : ℝ) *
          ∫ s in Set.Icc 0 T, iteratedDeriv 2 F (X s) ∂μV := by
  rw [← hI.eq_pathwiseItoIntegralAlong]
  exact pathwiseItoFormula_of_squareVariationMeasureRepresentation F hf X V μV hμV P hX T
