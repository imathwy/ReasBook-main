import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_38
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_15_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexFunctionPolar Pointwise RealInnerProductSpace Rockafellar

section

variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the proposition identifies the positive sublevel sets of the obverse `g` of a
  Chapter 15 function `f` as homothetic copies of the reciprocal-level sublevel sets of `f`, and
  then, under the stronger polarity ambient, applies the same statement to the pair `(f*, fᵒ)`.
- `core/canonical`: the owner abstractions are `obverse`, `Function.rightScalarMul`,
  `f⋆`, `convex_function_polar`, and the class
  `Function.IsNonnegativeClosedConvexZero`, imported through `Text_15_0_38`.
- `bridge/view`: `Text_15_0_38` already supplies the two atomic equalities used here: the
  unit-scalar specialization from the obverse sublevel set to the unit sublevel set of
  the positive right scalar multiple corresponding to `f_α`, under the standing Chapter 15
  assumptions, and the general
  perspective-level rewrite of that unit sublevel set as a homothetic image.

Domain-style sampling used here:
- `obverse_sublevelSet_eq_perspectiveScale_unitSublevelSet`;
- `perspectiveScale_unitSublevelSet_eq_smul_sublevelSet`;
- `obverse`;
- `f⋆`;
- `convex_function_polar`;
- `Function.IsNonnegativeClosedConvexZero`.

Primitive data vs derived API:
- primitive inputs: the positive scalar `α` and the existing owner constructions `obverse`,
  `Function.rightScalarMul`, `f⋆`, and `convex_function_polar`; the standing Chapter 15
  hypothesis class enters both the main obverse-sublevel theorem and the later
  polar/conjugate specialization.
- derived API: the first theorem composes the two upstream atomic equalities from `Text_15_0_38`,
  and the second theorem specializes that source-facing result to the polar/conjugate pair.

Layer target: the first theorem is `source-facing`, derived directly from the existing owner-level
Chapter 15 module API, while the second theorem is the corresponding source-facing
polar/conjugate specialization on the finite-dimensional real inner-product layer required by
Theorem 15.5.
Ambient minimization: the sublevel-set identity for `obverse` itself lives on
`[TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]`, matching `Text_15_0_37`; only the
polar/conjugate specialization uses the stronger ambient from `Theorem_15_5`.
-/

-- Proof sketch: compose the two atomic equalities already isolated in `Text_15_0_38`. Under the
-- Chapter 15 standing hypotheses on `f`, the `α`-sublevel set of `obverse f` is the unit
-- sublevel set of the positive right scalar multiple corresponding to `f_α`; for every `f`,
-- that unit sublevel set is
-- `α • {u | f u ≤ α⁻¹}`.
/-- Text 15.0.36: if `f : R^n → [0, +∞]` is convex, lower semicontinuous, and satisfies `f 0 = 0`,
then for every positive scalar `α`, the `α`-sublevel set of the obverse of `f` is the homothetic
image by `α` of the `α⁻¹`-sublevel set of `f`. Specializing `E` to
`EuclideanSpace ℝ (Fin n)` recovers the source statement on `R^n`. -/
theorem obverse_sublevelSet_eq_smul_sublevelSet
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero) (α : NNRealˣ) :
    {x : E | obverse f x ≤ ((α : ℝ) : EReal)} =
      (α : ℝ) • {x : E | f x ≤ (((α⁻¹ : NNRealˣ) : ℝ) : EReal)} := by
  have h₁ :
      {x : E | obverse f x ≤ ((α : ℝ) : EReal)} =
        {x : E | ((α : NNReal) •ʳ f) x ≤ (1 : EReal)} :=
    obverse_sublevelSet_eq_perspectiveScale_unitSublevelSet f hf α
  have h₂ :
      {x : E | ((α : NNReal) •ʳ f) x ≤ (1 : EReal)} =
        (α : ℝ) • {x : E | f x ≤ (((α⁻¹ : NNRealˣ) : ℝ) : EReal)} :=
    perspectiveScale_unitSublevelSet_eq_smul_sublevelSet f α
  exact h₁.trans h₂

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: Theorem 15.5 identifies `fᵒ` with the obverse of
-- `f⋆`. Theorems 12.2 and 14.7 show that `f⋆` again belongs to the
-- standing Chapter 15 class. Applying the first theorem to `f⋆` at the positive
-- scalar `α⁻¹` then rewrites the left-hand side to the displayed reciprocal-level statement.
/-- For a function `f` in the class of Theorem 15.5, the `α⁻¹`-sublevel set of the polar `fᵒ` is
the homothetic image by `α⁻¹` of the `α`-sublevel set of the Fenchel conjugate `f*`. Specializing
`E` to `EuclideanSpace ℝ (Fin n)` recovers the source statement on `R^n`. -/
theorem polar_sublevelSet_eq_inv_smul_conjugate_sublevelSet_of_nonnegative_closed_convex_zero
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero) (α : NNRealˣ) :
    {xStar : E | fᵒ xStar ≤ (((α⁻¹ : NNRealˣ) : ℝ) : EReal)} =
      (((α⁻¹ : NNRealˣ) : ℝ)) • {xStar : E | f⋆ xStar ≤ ((α : ℝ) : EReal)} := by
  letI : f.IsNonnegativeClosedConvexZero := hf
  letI : (f⋆ : E → EReal).IsNonnegativeClosedConvexZero := inferInstance
  have hpolar : fᵒ = obverse f⋆ := by
    refine (obverse_obverse_eq_of_nonnegative_closed_convex_zero fᵒ inferInstance).symm.trans ?_
    exact
      congrArg obverse
        (obverse_convex_function_polar_eq_convexConjugate_of_nonnegative_closed_convex_zero
          f hf)
  rw [hpolar]
  simpa using obverse_sublevelSet_eq_smul_sublevelSet f⋆ inferInstance (α⁻¹)

end
