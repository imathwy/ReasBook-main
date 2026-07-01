import AchimKlenkeLean.Items.Chap21.Remark_21_54
import AchimKlenkeLean.Items.Chap25.Corollary_25_32

-- Declarations for this item will be appended below by the statement pipeline.

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
