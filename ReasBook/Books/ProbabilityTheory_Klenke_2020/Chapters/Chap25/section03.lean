import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_25_3_1 (from Items/Chap25) -/
open MeasureTheory
open scoped Topology

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)

section Exercise2531

variable {X : PathSpace}
variable (g : C(NNReal × NNReal, ℝ))

/- Domain-style sampling for Exercise 25.3.1:
* primary domain: dyadic pathwise Itô integration against a continuous square-variation path with
  deterministic bounded-variation section kernels;
* sampled chapter owners in this domain: `HasPathwiseItoIntegralAlong`,
  `pathwiseItoIntegralAlong`,
  `hasSquareVariationAlong_zero_of_locallyFiniteVariation`, and
  `dyadic_pathwise_product_rule_of_continuous_square_variation`;
* owner abstraction: the canonical pathwise integral `pathwiseItoIntegralAlong`, with
  `HasPathwiseItoIntegralAlong` as its realization predicate;
* primitive data: `X ∈ 𝒞_qv`, the continuous kernel `g`, and the boundary-compatible owner
  hypothesis `LocallyBoundedVariationOn (g.curry u) univ` for each section;
* derived API: deterministic integration against `indefiniteIntegralPath`, the sectionwise
  realization theorem, and the auxiliary realization lemmas supporting the two Fubini
  equalities.

Layer triage:
* source-facing: `timeAccumulation g t`, `triangularAccumulation g`, the section paths
  `g.curry u`, and the Fubini equalities for their pathwise Itô integrals;
* core/canonical: `pathwiseItoIntegralAlong` together with the owner predicate
  `HasPathwiseItoIntegralAlong`;
* bridge/view: the deterministic `indefiniteIntegralPath` lemma and the auxiliary
  `HasPathwiseItoIntegralAlong` realizations used to derive the equalities. -/

/-- For fixed `t`, the source-facing time-integrated kernel
`v ↦ ∫_0^t g(u, v) du` as a continuous path on `[0, ∞)`. -/
def timeAccumulation (t : NNReal) : PathSpace where
  toFun v := ∫ u in Set.Icc (0 : ℝ) (t : ℝ), g (u.toNNReal, v)
  continuous_toFun := by
    sorry

@[simp] theorem timeAccumulation_apply (t v : NNReal) :
    timeAccumulation g t v = ∫ u in Set.Icc (0 : ℝ) (t : ℝ), g (u.toNNReal, v) :=
  rfl

/-- The source-facing triangular kernel
`v ↦ ∫_0^v g(u, v) du` as a continuous path on `[0, ∞)`. -/
def triangularAccumulation : PathSpace where
  toFun v := ∫ u in Set.Icc (0 : ℝ) (v : ℝ), g (u.toNNReal, v)
  continuous_toFun := by
    sorry

@[simp] theorem triangularAccumulation_apply (v : NNReal) :
    triangularAccumulation g v = ∫ u in Set.Icc (0 : ℝ) (v : ℝ), g (u.toNNReal, v) :=
  rfl

-- Proof sketch: for continuous `H`, the left-point sums against
-- `indefiniteIntegralPath f` are ordinary Riemann sums for the continuous density
-- `r ↦ H(r.toNNReal) * f r` on each compact interval `[0,s]`. This gives a
-- `HasPathwiseItoIntegralAlong` realization first; the canonical `limUnder` formula is then the
-- derived companion via `HasPathwiseItoIntegralAlong.eq_pathwiseItoIntegralAlong`.
/-- Owner-level deterministic realization: for continuous `H`, integrating against the
bounded-variation path `t ↦ ∫_0^t f(r) dr` admits the ordinary time integral
`s ↦ ∫_0^s H(r) f(r) dr` as a pathwise Itô realization. -/
theorem hasPathwiseItoIntegralAlong_indefiniteIntegralPath
    (H : NNReal → ℝ) (hH : Continuous H) {f : ℝ → ℝ} (hf : Continuous f) :
    HasPathwiseItoIntegralAlong
      H
      (indefiniteIntegralPath f)
      dyadicPartitionSequence
      (fun s ↦ ∫ r in Set.Icc (0 : ℝ) (s : ℝ), H r.toNNReal * f r) := by
  sorry

/-- Derived canonical bridge for continuous integrands: the canonical `limUnder` realization of
the pathwise Itô integral against `indefiniteIntegralPath f` agrees with the ordinary time
integral of `H(r) f(r)`. -/
theorem pathwiseItoIntegralAlong_indefiniteIntegralPath
    (H : NNReal → ℝ) (hH : Continuous H) {f : ℝ → ℝ} (hf : Continuous f) (s : NNReal) :
    pathwiseItoIntegralAlong H (indefiniteIntegralPath f) dyadicPartitionSequence s =
      ∫ r in Set.Icc (0 : ℝ) (s : ℝ), H r.toNNReal * f r := by
  simpa using
    congrArg
      (fun I : NNReal → ℝ ↦ I s)
      (hasPathwiseItoIntegralAlong_indefiniteIntegralPath H hH hf).eq_pathwiseItoIntegralAlong

-- Proof sketch: for fixed `u`, the section path `g.curry u` is already assumed to satisfy the
-- owner regularity hypothesis `LocallyBoundedVariationOn ... univ`. Pairing this
-- bounded-variation section with the continuous square-variation path `X` in Corollary 25.32
-- gives the required dyadic pathwise Itô realization.
/-- A boundary-compatible bounded-variation hypothesis on the sections of `g` yields a
source-facing dyadic Itô realization for each section `v ↦ g(u, v)` against `X`. -/
theorem hasPathwiseItoIntegralAlong_sectionKernel
    (hX : X ∈ 𝒞_qv)
    (hsection : ∀ u : NNReal, LocallyBoundedVariationOn (g.curry u) univ)
    (u : NNReal) :
    HasPathwiseItoIntegralAlong
      (g.curry u)
      X
      dyadicPartitionSequence
      (pathwiseItoIntegralAlong (g.curry u) X dyadicPartitionSequence) := by
  sorry

-- Proof sketch: combine the sectionwise realizations from
-- `hasPathwiseItoIntegralAlong_sectionKernel` with the product rule on each fixed-`u` section,
-- integrate the resulting identity in `u`, and use deterministic Fubini to identify the outer
-- realization with the time-accumulated kernel.
/-- Auxiliary owner-level realization for the time-accumulated kernel in Exercise 25.3.1 (1). -/
theorem hasPathwiseItoIntegralAlong_timeAccumulation
    (hX : X ∈ 𝒞_qv)
    (hsection : ∀ u : NNReal, LocallyBoundedVariationOn (g.curry u) univ)
    (t : NNReal) :
    HasPathwiseItoIntegralAlong
      (timeAccumulation g t)
      X
      dyadicPartitionSequence
      (fun s ↦
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          pathwiseItoIntegralAlong
            (g.curry u.toNNReal)
            X
            dyadicPartitionSequence
            s) := by
  sorry

-- Proof sketch: evaluate the auxiliary realization from
-- `hasPathwiseItoIntegralAlong_timeAccumulation` at `s` and rewrite it through
-- `HasPathwiseItoIntegralAlong.eq_pathwiseItoIntegralAlong`.
/-- Exercise 25.3.1 (1): the pathwise Itô integral of the time-accumulated kernel equals the
time integral of the sectionwise pathwise Itô integrals. -/
theorem pathwise_stochastic_integral_time_fubini
    (hX : X ∈ 𝒞_qv)
    (hsection : ∀ u : NNReal, LocallyBoundedVariationOn (g.curry u) univ)
    (t s : NNReal) :
    pathwiseItoIntegralAlong (timeAccumulation g t) X dyadicPartitionSequence s =
      ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        pathwiseItoIntegralAlong
          (g.curry u.toNNReal)
          X
          dyadicPartitionSequence
          s := by
  simpa using
    congrArg
      (fun I : NNReal → ℝ ↦ I s)
      (hasPathwiseItoIntegralAlong_timeAccumulation g hX hsection t).eq_pathwiseItoIntegralAlong

-- Proof sketch: rewrite the triangular kernel as the time-integrated kernel over the triangular
-- region `{(u, v) | 0 ≤ u ≤ v ≤ s}`, use the sectionwise source-facing Itô realizations from
-- `hasPathwiseItoIntegralAlong_sectionKernel`, and exchange the remaining ordinary integrals on
-- the triangle.
/-- Auxiliary owner-level realization for the triangular kernel in Exercise 25.3.1 (2). -/
theorem hasPathwiseItoIntegralAlong_triangularAccumulation
    (hX : X ∈ 𝒞_qv)
    (hsection : ∀ u : NNReal, LocallyBoundedVariationOn (g.curry u) univ)
    :
    HasPathwiseItoIntegralAlong
      (triangularAccumulation g)
      X
      dyadicPartitionSequence
      (fun s ↦
        ∫ u in Set.Icc (0 : ℝ) (s : ℝ),
          (pathwiseItoIntegralAlong
              (g.curry u.toNNReal)
              X
              dyadicPartitionSequence
              s -
            pathwiseItoIntegralAlong
              (g.curry u.toNNReal)
              X
              dyadicPartitionSequence
              u.toNNReal)) := by
  sorry

-- Proof sketch: evaluate the auxiliary realization from
-- `hasPathwiseItoIntegralAlong_triangularAccumulation` at `s` and rewrite through
-- `HasPathwiseItoIntegralAlong.eq_pathwiseItoIntegralAlong`.
/-- Exercise 25.3.1 (2): the pathwise Itô integral of the triangularly accumulated kernel equals
the triangular Fubini expression built from the sectionwise pathwise Itô integrals. -/
theorem pathwise_stochastic_integral_triangular_fubini
    (hX : X ∈ 𝒞_qv)
    (hsection : ∀ u : NNReal, LocallyBoundedVariationOn (g.curry u) univ)
    (s : NNReal) :
    pathwiseItoIntegralAlong (triangularAccumulation g) X dyadicPartitionSequence s =
      ∫ u in Set.Icc (0 : ℝ) (s : ℝ),
        (pathwiseItoIntegralAlong
            (g.curry u.toNNReal)
            X
            dyadicPartitionSequence
            s -
          pathwiseItoIntegralAlong
            (g.curry u.toNNReal)
            X
            dyadicPartitionSequence
            u.toNNReal) := by
  simpa using
    congrArg
      (fun I : NNReal → ℝ ↦ I s)
      (hasPathwiseItoIntegralAlong_triangularAccumulation g hX hsection).eq_pathwiseItoIntegralAlong

end Exercise2531

/-! ### Exercise_25_3_2 (from Items/Chap25) -/
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

/-! ### Definition_25_3 (from Items/Chap25) -/
open scoped BigOperators

noncomputable section

universe u

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "ContinuousFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

/-
Definition 25.3 is `source-facing`: it defines the elementary Brownian Itô integral on the
canonical owner `PredictableSimpleProcess ℱ` from Definition 25.2. The namespace
`PredictableStepRepresentation` is only the `bridge/view` layer that records the explicit finite
increment sum for a chosen predictable-step presentation and proves that this formula depends only
on the underlying owner process.
-/

namespace PredictableStepRepresentation

variable {ℱ : ContinuousFiltration}

/-- The stopped Itô sum attached to a predictable-step representation. This is the
representation-level formula underlying Definition 25.3. -/
def brownianElementaryIntegral (H : PredictableStepRepresentation ℱ) (W : Process) : Process :=
  fun t ω ↦
    ∑ i : Fin H.n,
      H.coeff i ω *
        (W (min (H.times i.succ) t) ω - W (min (H.times i.castSucc) t) ω)

/-- The terminal Itô sum attached to a predictable-step representation, obtained by evaluating
the stopped integral at the final partition time. -/
def brownianElementaryIntegralAtInfinity
    (H : PredictableStepRepresentation ℱ) (W : Process) : Ω → ℝ :=
  PredictableStepRepresentation.brownianElementaryIntegral H W (H.times (Fin.last H.n))

/-- The stopped Brownian increment sum depends only on the underlying predictable simple process,
not on the chosen predictable-step representation. -/
theorem brownianElementaryIntegral_congr
    (W : Process) {H K : PredictableStepRepresentation ℱ} (hHK : H.toProcess = K.toProcess) :
    PredictableStepRepresentation.brownianElementaryIntegral H W =
      PredictableStepRepresentation.brownianElementaryIntegral K W := by
  sorry

/-- The terminal Brownian increment sum depends only on the underlying predictable simple process,
not on the chosen predictable-step representation. -/
theorem brownianElementaryIntegralAtInfinity_congr
    (W : Process) {H K : PredictableStepRepresentation ℱ} (hHK : H.toProcess = K.toProcess) :
    PredictableStepRepresentation.brownianElementaryIntegralAtInfinity H W =
      PredictableStepRepresentation.brownianElementaryIntegralAtInfinity K W := by
  sorry

/-- Evaluating the stopped elementary Brownian integral gives the defining truncated increment
sum. -/
@[simp] theorem brownianElementaryIntegral_apply {ℱ : ContinuousFiltration}
    (H : PredictableStepRepresentation ℱ) (W : Process) (t : NNReal) (ω : Ω) :
    PredictableStepRepresentation.brownianElementaryIntegral H W t ω =
      ∑ i : Fin H.n,
        H.coeff i ω *
          (W (min (H.times i.succ) t) ω - W (min (H.times i.castSucc) t) ω) :=
  rfl

/-- Evaluating the terminal elementary Brownian integral gives the full increment sum over the
partition of `H`. -/
@[simp] theorem brownianElementaryIntegralAtInfinity_apply
    (H : PredictableStepRepresentation ℱ) (W : Process) (ω : Ω) :
    PredictableStepRepresentation.brownianElementaryIntegralAtInfinity H W ω =
      ∑ i : Fin H.n,
        H.coeff i ω * (W (H.times i.succ) ω - W (H.times i.castSucc) ω) := by
  sorry

/- For times at or beyond the last partition point of `H`, all truncations in
`H.brownianElementaryIntegral W t` disappear, so the stopped Itô sum has stabilized at its
terminal value. -/
theorem brownianElementaryIntegral_eq_atInfinity
    (H : PredictableStepRepresentation ℱ) (W : Process)
    {t : NNReal} (ht : H.times (Fin.last H.n) ≤ t) :
    PredictableStepRepresentation.brownianElementaryIntegral H W t =
      PredictableStepRepresentation.brownianElementaryIntegralAtInfinity H W := by
  sorry

end PredictableStepRepresentation

/-- Definition 25.3: for an elementary integrand `H ∈ 𝓔` and a real process `W`, the stopped Itô
integral `brownianElementaryIntegral W H t` is obtained from a finite predictable-step
representation of `H` by the usual truncated increment sum. The representation-level formula is
recorded separately by `PredictableStepRepresentation.brownianElementaryIntegral`. -/
noncomputable def brownianElementaryIntegral {ℱ : ContinuousFiltration} (W : Process)
    (H : PredictableSimpleProcess ℱ) : Process :=
  let representation : PredictableStepRepresentation ℱ :=
    Classical.choose (PredictableSimpleProcess.exists_representation H)
  PredictableStepRepresentation.brownianElementaryIntegral representation W

/-- The terminal Itô integral `I_∞^W(H)` from Definition 25.3 for an elementary integrand
`H ∈ 𝓔`. -/
noncomputable def brownianElementaryIntegralAtInfinity {ℱ : ContinuousFiltration} (W : Process)
    (H : PredictableSimpleProcess ℱ) : Ω → ℝ :=
  let representation : PredictableStepRepresentation ℱ :=
    Classical.choose (PredictableSimpleProcess.exists_representation H)
  PredictableStepRepresentation.brownianElementaryIntegralAtInfinity representation W

/-- Any predictable-step representation of `H` computes the stopped Brownian integral from
Definition 25.3. -/
theorem brownianElementaryIntegral_spec {ℱ : ContinuousFiltration} (W : Process)
    (H : PredictableSimpleProcess ℱ) {representation : PredictableStepRepresentation ℱ}
    (hrepresentation : (H : Process) = representation.toProcess) :
    brownianElementaryIntegral W H =
      PredictableStepRepresentation.brownianElementaryIntegral representation W := by
  sorry

/-- Any predictable-step representation of `H` computes the terminal Brownian integral from
Definition 25.3. -/
theorem brownianElementaryIntegralAtInfinity_spec {ℱ : ContinuousFiltration} (W : Process)
    (H : PredictableSimpleProcess ℱ) {representation : PredictableStepRepresentation ℱ}
    (hrepresentation : (H : Process) = representation.toProcess) :
    brownianElementaryIntegralAtInfinity W H =
      PredictableStepRepresentation.brownianElementaryIntegralAtInfinity representation W := by
  sorry

/-- On the canonical predictable simple process attached to a predictable-step representation,
Definition 25.3 recovers the representation-level stopped increment sum. -/
@[simp] theorem brownianElementaryIntegral_toPredictableSimpleProcess
    {ℱ : ContinuousFiltration} (W : Process) (representation : PredictableStepRepresentation ℱ) :
    brownianElementaryIntegral W representation.toPredictableSimpleProcess =
      PredictableStepRepresentation.brownianElementaryIntegral representation W :=
  brownianElementaryIntegral_spec W representation.toPredictableSimpleProcess
    representation.toPredictableSimpleProcess_coe

/-- On the canonical predictable simple process attached to a predictable-step representation,
Definition 25.3 recovers the representation-level terminal increment sum. -/
@[simp] theorem brownianElementaryIntegralAtInfinity_toPredictableSimpleProcess
    {ℱ : ContinuousFiltration} (W : Process) (representation : PredictableStepRepresentation ℱ) :
    brownianElementaryIntegralAtInfinity W representation.toPredictableSimpleProcess =
      PredictableStepRepresentation.brownianElementaryIntegralAtInfinity representation W :=
  brownianElementaryIntegralAtInfinity_spec W representation.toPredictableSimpleProcess
    representation.toPredictableSimpleProcess_coe

end MeasureTheory

end
