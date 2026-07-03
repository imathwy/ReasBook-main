import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_58
import ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_54

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ

/-- The dyadic left-point sum approximating the integral of `H` against the quadratic
covariation of `F` and `G` on `[0, T]`. -/
noncomputable def dyadicQuadraticCovariationIntegralApproximationUpTo
    (H : NNReal → ℝ) (F G : PathSpace) (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
    H (dyadicPartitionSequence n k) *
      (F (partitionNextPointUpTo dyadicPartitionSequence n k T) - F (dyadicPartitionSequence n k)) *
      (G (partitionNextPointUpTo dyadicPartitionSequence n k T) - G (dyadicPartitionSequence n k))

/-- Expanding `dyadicQuadraticCovariationIntegralApproximationUpTo` gives the defining dyadic
left-point sum on `[0, T]`. -/
theorem dyadicQuadraticCovariationIntegralApproximationUpTo_def
    (H : NNReal → ℝ) (F G : PathSpace) (T : NNReal) (n : ℕ) :
    dyadicQuadraticCovariationIntegralApproximationUpTo H F G T n =
      Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
        H (dyadicPartitionSequence n k) *
          (F (partitionNextPointUpTo dyadicPartitionSequence n k T) -
            F (dyadicPartitionSequence n k)) *
          (G (partitionNextPointUpTo dyadicPartitionSequence n k T) -
            G (dyadicPartitionSequence n k)) := rfl

/-- The canonical dyadic pathwise integral of `H` against the quadratic covariation of `F` and
`G` is the process obtained by taking the `limUnder` of the left-point mixed-increment sums at
each horizon `T`. -/
noncomputable def pathwiseQuadraticCovariationIntegral
    (H : NNReal → ℝ) (F G : PathSpace) : PathwiseProcess :=
  fun T ↦ limUnder atTop (dyadicQuadraticCovariationIntegralApproximationUpTo H F G T)

/-- Evaluating `pathwiseQuadraticCovariationIntegral` gives the `limUnder` of the dyadic
left-point mixed-increment sums at horizon `T`. -/
theorem pathwiseQuadraticCovariationIntegral_def
    (H : NNReal → ℝ) (F G : PathSpace) (T : NNReal) :
    pathwiseQuadraticCovariationIntegral H F G T =
      limUnder atTop (dyadicQuadraticCovariationIntegralApproximationUpTo H F G T) := rfl

/-- The canonical Euclidean model of a continuous `d`-dimensional path on `[0,∞)`. -/
abbrev VectorPathSpace (d : ℕ) := C(NNReal, EuclideanSpace ℝ (Fin d))

variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "StateCoords" => (EuclideanSpace.equiv (Fin d) ℝ : State ≃L[ℝ] Fin d → ℝ)

/-- The `i`-th real-valued coordinate path of a continuous vector-valued path. -/
abbrev vectorPathComponent (X : VectorPathSpace d) (i : Fin d) : PathSpace :=
  { toFun := fun t ↦ X t i
    continuous_toFun := by
      have hX : Continuous fun t ↦ StateCoords (X t) :=
        (StateCoords : State →L[ℝ] Fin d → ℝ).continuous.comp X.continuous
      simpa using (continuous_apply i).comp hX }

-- Proof sketch: unfold `vectorPathComponent`; it is the continuous map whose underlying function
-- evaluates `X` in the coordinate `i`.
/-- Evaluating `vectorPathComponent X i` at time `t` returns the `i`-th coordinate `X t i`. -/
theorem vectorPathComponent_apply
    (X : VectorPathSpace d) (i : Fin d) (t : NNReal) :
    vectorPathComponent X i t = X t i := rfl

/-- The primitive dyadic quadratic-covariation owner property for a continuous
`d`-dimensional path. -/
def HasContinuousQuadraticCovariations (X : VectorPathSpace d) : Prop :=
  ∀ i j : Fin d,
    ∃ cov : PathSpace,
      HasQuadraticCovariationAlong
        (vectorPathComponent X i)
        (vectorPathComponent X j)
        cov

/-- The textbook class `𝒞_qv^d` of continuous `d`-dimensional paths whose coordinate pairs admit
dyadic quadratic covariations represented by continuous paths. -/
abbrev ContinuousQuadraticCovariationClass (d : ℕ) : Set (VectorPathSpace d) :=
  HasContinuousQuadraticCovariations

notation "𝒞_qv^" d => ContinuousQuadraticCovariationClass d

/- Membership in `𝒞_qv^d` is the source-facing set-level view of the primitive owner property
`HasContinuousQuadraticCovariations`. -/
theorem mem_𝒞_qv_d_iff (X : VectorPathSpace d) :
    X ∈ (𝒞_qv^d) ↔ HasContinuousQuadraticCovariations X :=
  Iff.rfl

/-- Membership in `𝒞_qv^d` is equivalent to choosing a continuous dyadic quadratic-covariation
path for each coordinate pair. -/
theorem mem_𝒞_qv_d_iff_exists_family
    (X : VectorPathSpace d) :
    X ∈ (𝒞_qv^d) ↔
      ∃ cov : Fin d → Fin d → PathSpace,
        ∀ i j : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent X i)
            (vectorPathComponent X j)
            (cov i j) := by
  constructor
  · intro hX
    classical
    choose cov hcov using hX
    exact ⟨cov, hcov⟩
  · rintro ⟨cov, hcov⟩ i j
    exact ⟨cov i j, hcov i j⟩

/-- The partial derivative `∂ᵢF` computed by varying only the `i`-th coordinate. -/
noncomputable def partialDeriv
    (F : State → ℝ) (i : Fin d) : State → ℝ :=
  fun x ↦ deriv (fun t ↦ F (x + EuclideanSpace.single i (t - x i))) (x i)

notation:max "∂[" i "] " F:arg => partialDeriv F i

-- Proof sketch: unfold `partialDeriv`; the derivative is taken along the coordinate line obtained
-- by varying only the `i`-th Euclidean coordinate of `x`.
/-- Evaluating `(∂[i] F)` at `x` gives the one-variable derivative along the `i`-th
coordinate line through `x`. -/
theorem partialDeriv_def
    (F : State → ℝ) (i : Fin d) (x : State) :
    (∂[i] F) x =
      deriv (fun t ↦ F (x + EuclideanSpace.single i (t - x i))) (x i) := rfl

/-- The mixed second partial derivative `∂ⱼ∂ᵢF` computed by iterating coordinate derivatives. -/
noncomputable def secondPartialDeriv
    (F : State → ℝ) (i j : Fin d) : State → ℝ :=
  fun x ↦ deriv (fun t ↦ (∂[i] F) (x + EuclideanSpace.single j (t - x j))) (x j)

notation:max "∂²[" i "," j "] " F:arg => secondPartialDeriv F i j

-- Proof sketch: unfold `secondPartialDeriv`; it differentiates the `i`-th partial derivative of
-- `F` along the `j`-th coordinate line through `x`.
/-- Evaluating `(∂²[i, j] F)` at `x` gives the iterated coordinate derivative
`∂ⱼ∂ᵢF(x)`. -/
theorem secondPartialDeriv_def
    (F : State → ℝ) (i j : Fin d) (x : State) :
    (∂²[i, j] F) x =
      deriv (fun t ↦ (∂[i] F) (x + EuclideanSpace.single j (t - x j))) (x j) := rfl

/-- The dyadic left-point Riemann sum for the pathwise multidimensional Itô integral of `∇F(X)`
on `[0,T]`. -/
noncomputable def dyadicMultidimensionalItoApproximationUpTo
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
    ∑ i : Fin d,
      (∂[i] F) (X (dyadicPartitionSequence n k)) *
        (X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
          X (dyadicPartitionSequence n k) i)

-- Proof sketch: unfold `dyadicMultidimensionalItoApproximationUpTo`; this is exactly the finite
-- sum of the coordinate partial derivatives at the left endpoints against the coordinate
-- increments along the dyadic partition of `[0,T]`.
/-- Expanding `dyadicMultidimensionalItoApproximationUpTo` gives the dyadic left-point gradient
sum on `[0,T]`. -/
theorem dyadicMultidimensionalItoApproximationUpTo_def
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) :
    dyadicMultidimensionalItoApproximationUpTo F X T n =
      Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
        ∑ i : Fin d,
          (∂[i] F) (X (dyadicPartitionSequence n k)) *
            (X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
              X (dyadicPartitionSequence n k) i) := rfl

/-- The dyadic second-order correction sum in the multidimensional pathwise Itô formula on
`[0,T]`. -/
noncomputable def dyadicMultidimensionalItoCorrectionApproximationUpTo
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) *
    Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
      ∑ i : Fin d, ∑ j : Fin d,
          (∂²[i, j] F) (X (dyadicPartitionSequence n k)) *
            (X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
              X (dyadicPartitionSequence n k) i) *
            (X (partitionNextPointUpTo dyadicPartitionSequence n k T) j -
              X (dyadicPartitionSequence n k) j)

-- Proof sketch: unfold
-- `dyadicMultidimensionalItoCorrectionApproximationUpTo`; this is exactly the finite second-order
-- Taylor correction sum along the dyadic partition of `[0,T]`.
/-- Expanding `dyadicMultidimensionalItoCorrectionApproximationUpTo` gives the dyadic second-order
correction sum on `[0,T]`. -/
theorem dyadicMultidimensionalItoCorrectionApproximationUpTo_def
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) :
    dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n =
      (1 / 2 : ℝ) *
        Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
          ∑ i : Fin d, ∑ j : Fin d,
              (∂²[i, j] F) (X (dyadicPartitionSequence n k)) *
                (X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
                  X (dyadicPartitionSequence n k) i) *
                (X (partitionNextPointUpTo dyadicPartitionSequence n k T) j -
                  X (dyadicPartitionSequence n k) j) := rfl

/-- The pathwise multidimensional Itô integral is the process obtained from the `limUnder` of the
dyadic left-point sums. -/
noncomputable def pathwiseMultidimensionalItoIntegral
    (F : State → ℝ) (X : VectorPathSpace d) : PathwiseProcess :=
  fun T ↦ limUnder atTop (dyadicMultidimensionalItoApproximationUpTo F X T)

-- Proof sketch: unfold `pathwiseMultidimensionalItoIntegral`; by definition it is the `limUnder`
-- of the dyadic multidimensional Itô approximations.
/-- Evaluating `pathwiseMultidimensionalItoIntegral` gives the `limUnder` of the dyadic
multidimensional Itô sums. -/
theorem pathwiseMultidimensionalItoIntegral_def
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) :
    pathwiseMultidimensionalItoIntegral F X T =
      limUnder atTop (dyadicMultidimensionalItoApproximationUpTo F X T) := rfl

/-- The quadratic correction in the multidimensional pathwise Itô formula is the sum of the
pairwise pathwise quadratic-covariation integrals of the Hessian entries. -/
noncomputable def pathwiseMultidimensionalItoCorrection
    (F : State → ℝ) (X : VectorPathSpace d) : PathwiseProcess :=
  fun T ↦
    (1 / 2 : ℝ) *
      ∑ i : Fin d, ∑ j : Fin d,
          pathwiseQuadraticCovariationIntegral
            (fun s ↦ (∂²[i, j] F) (X s))
            (vectorPathComponent X i)
            (vectorPathComponent X j)
            T

-- Proof sketch: unfold `pathwiseMultidimensionalItoCorrection`; by definition it is the finite
-- sum of the pairwise pathwise quadratic-covariation integrals of the Hessian entries.
/-- Expanding `pathwiseMultidimensionalItoCorrection` gives the sum of the pairwise pathwise
quadratic-covariation integrals of the Hessian entries. -/
theorem pathwiseMultidimensionalItoCorrection_def
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) :
    pathwiseMultidimensionalItoCorrection F X T =
      (1 / 2 : ℝ) *
        ∑ i : Fin d, ∑ j : Fin d,
            pathwiseQuadraticCovariationIntegral
              (fun s ↦ (∂²[i, j] F) (X s))
              (vectorPathComponent X i)
              (vectorPathComponent X j)
              T := rfl

/-- If `F ∈ C²(ℝ^d)` and `X ∈ 𝒞_qv^d`, then the dyadic second-order correction sums converge to
the source-facing quadratic-covariation correction term
`pathwiseMultidimensionalItoCorrection F X T`. -/
theorem pathwiseMultidimensionalItoCorrection_spec
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d) (hX : X ∈ (𝒞_qv^d)) (T : NNReal) :
    Tendsto
      (fun n ↦ dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n)
      atTop
      (nhds (pathwiseMultidimensionalItoCorrection F X T)) := sorry

-- Proof sketch: apply the scalar pathwise Itô formula to the one-dimensional paths obtained by
-- freezing all but one coordinate, sum the first-order terms over the coordinates, and identify
-- the second-order contributions with the pairwise signed covariation measures `d⟨Xⁱ,Xʲ⟩`.
/-- The dyadic left-point sums defining the multidimensional pathwise Itô integral converge on
`[0,T]` for any path in `𝒞_qv^d`. -/
theorem tendsto_dyadicMultidimensionalItoApproximationUpTo
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d)
    (hX : X ∈ (𝒞_qv^d)) (T : NNReal) :
    Tendsto
      (fun n ↦ dyadicMultidimensionalItoApproximationUpTo F X T n)
      atTop
      (nhds (pathwiseMultidimensionalItoIntegral F X T)) := sorry

-- Proof sketch: expand the second-order Taylor formula of `F` along the dyadic increments of the
-- vector path `X`, identify the first-order term with the limit of the dyadic gradient sums, and
-- collect the second-order contributions into the named quadratic-covariation correction object
-- `pathwiseMultidimensionalItoCorrection F X T`.
/-- If `X ∈ 𝒞_qv^d` and `F ∈ C²(ℝ^d)`, then the pathwise multidimensional Itô formula holds with
the named quadratic-covariation correction term `pathwiseMultidimensionalItoCorrection F X T`. -/
theorem pathwiseMultidimensionalItoFormula_eq_canonicalCorrection
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d)
    (hX : X ∈ (𝒞_qv^d))
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseMultidimensionalItoIntegral F X T +
        pathwiseMultidimensionalItoCorrection F X T := sorry

-- Proof sketch: the dyadic mixed-increment integral against a quadratic covariation path agrees
-- with the corresponding Lebesgue--Stieltjes integral whenever that path is represented by a
-- signed measure.
/-- If a quadratic covariation path `⟨Y, Z⟩` is represented by a signed Stieltjes measure, then
the canonical pathwise integral against `d⟨Y, Z⟩` agrees with the corresponding signed
Lebesgue--Stieltjes integral. -/
theorem pathwiseQuadraticCovariationIntegral_eq_lebesgueStieltjesIntegral
    (H : NNReal → ℝ) {Y Z : PathSpace}
    (cov : PathwiseProcess)
    (hcov : HasQuadraticCovariationAlong Y Z cov)
    (covariationMeasure : SignedMeasure ℝ)
    (hcovariationMeasure :
      ∀ T : NNReal,
        cov T =
          signedLebesgueStieltjesIntegralUpTo (fun _ ↦ (1 : ℝ)) covariationMeasure T)
    :
    pathwiseQuadraticCovariationIntegral H Y Z =
      fun T ↦
        signedLebesgueStieltjesIntegralUpTo
          (fun s ↦ H s.toNNReal)
          covariationMeasure
          T := by
  ext T
  sorry

-- Proof sketch: rewrite each pairwise pathwise quadratic-covariation integral using the supplied
-- signed-measure realization of the corresponding covariation path and sum over all coordinates.
/-- If the pairwise quadratic covariation paths are represented by signed Stieltjes measures, then
the quadratic correction term of Theorem 25.30 agrees with the corresponding sum of signed
Lebesgue--Stieltjes integrals. -/
theorem pathwiseMultidimensionalItoCorrection_eq_sum_lebesgueStieltjesIntegral
    (F : State → ℝ)
    (X : VectorPathSpace d)
    (cov : Fin d → Fin d → PathwiseProcess)
    (hcov :
      ∀ i j : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent X i)
          (vectorPathComponent X j)
          (cov i j))
    (covariationMeasure : Fin d → Fin d → SignedMeasure ℝ)
    (hcovariationMeasure :
      ∀ i j : Fin d, ∀ T : NNReal,
        cov i j T =
          signedLebesgueStieltjesIntegralUpTo
            (fun _ ↦ (1 : ℝ))
            (covariationMeasure i j)
            T)
    :
    pathwiseMultidimensionalItoCorrection F X =
      fun T ↦
        (1 / 2 : ℝ) *
          ∑ i : Fin d, ∑ j : Fin d,
              signedLebesgueStieltjesIntegralUpTo
                (fun s ↦ (∂²[i, j] F) (X s.toNNReal))
                (covariationMeasure i j)
                T := by
  ext T
  sorry

-- Proof sketch: this is exactly
-- `pathwiseMultidimensionalItoFormula_eq_canonicalCorrection` with the named correction expanded.
/-- Theorem 25.30: if `X ∈ 𝒞_qv^d` and `F ∈ C²(ℝ^d)`, then
`F (X_T) - F (X_0) = ∫_0^T ∇ F(X_s) dX_s +
  (1 / 2) ∑_{i,j} ∫_0^T ∂ᵢ∂ⱼ F(X_s) d⟨Xⁱ, Xʲ⟩_s`,
where the last term is expressed by the canonical dyadic pathwise quadratic-covariation
integrals. -/
theorem pathwiseMultidimensionalItoFormula
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d)
    (hX : X ∈ (𝒞_qv^d))
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseMultidimensionalItoIntegral F X T +
        (1 / 2 : ℝ) *
          ∑ i : Fin d, ∑ j : Fin d,
              pathwiseQuadraticCovariationIntegral
                (fun s ↦ (∂²[i, j] F) (X s))
                (vectorPathComponent X i)
                (vectorPathComponent X j)
                T := by
  simpa [pathwiseMultidimensionalItoCorrection] using
    pathwiseMultidimensionalItoFormula_eq_canonicalCorrection F hf X hX T

/-- If the pairwise quadratic covariation paths are represented by signed Stieltjes measures, then
Theorem 25.30 rewrites to the corresponding sum of signed Lebesgue--Stieltjes integrals. -/
theorem pathwiseMultidimensionalItoFormula_of_covariationMeasureRepresentation
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d)
    (hX : X ∈ (𝒞_qv^d))
    (cov : Fin d → Fin d → PathwiseProcess)
    (hcov :
      ∀ i j : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent X i)
          (vectorPathComponent X j)
          (cov i j))
    (covariationMeasure : Fin d → Fin d → SignedMeasure ℝ)
    (hcovariationMeasure :
      ∀ i j : Fin d, ∀ T : NNReal,
        cov i j T =
          signedLebesgueStieltjesIntegralUpTo
            (fun _ ↦ (1 : ℝ))
            (covariationMeasure i j)
            T)
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseMultidimensionalItoIntegral F X T +
        (1 / 2 : ℝ) *
          ∑ i : Fin d, ∑ j : Fin d,
              signedLebesgueStieltjesIntegralUpTo
                (fun s ↦ (∂²[i, j] F) (X s.toNNReal))
                (covariationMeasure i j)
                T := by
  have hcorr :
      pathwiseMultidimensionalItoCorrection F X T =
        (1 / 2 : ℝ) *
          ∑ i : Fin d, ∑ j : Fin d,
              signedLebesgueStieltjesIntegralUpTo
                (fun s ↦ (∂²[i, j] F) (X s.toNNReal))
                (covariationMeasure i j)
                T := by
    simpa using
      congrArg
        (fun correction : PathwiseProcess ↦ correction T)
        (pathwiseMultidimensionalItoCorrection_eq_sum_lebesgueStieltjesIntegral
          F X cov hcov covariationMeasure hcovariationMeasure)
  rw [← hcorr]
  exact pathwiseMultidimensionalItoFormula_eq_canonicalCorrection F hf X hX T
