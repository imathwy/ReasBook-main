import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_25_1_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Gradient RealInnerProductSpace

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 25.1.3 identifies the coordinates of the gradient in finite
  Euclidean coordinates `ℝ^ι` with the
  standard-basis partial derivatives, then rewrites Rockafellar's directional derivative as the
  corresponding coordinate sum.
- `core/canonical`: the chapter owner is already `Function.directionalDerivativeAt` on
  `f.toWithBotTop`, with existence/value API from Theorem 25.1.1;
  the ambient Euclidean derivative data
  are the gradient notation `∇` and the canonical basis vectors `EuclideanSpace.basisFun ι ℝ j`.
- `bridge/view`: the textbook partial derivative `∂f/∂ξ_j (x)` is read through the shared owner
  `Function.partialDeriv f x j` from Theorem 25.1.2, while mathlib's real-valued
  `lineDeriv ℝ f x y`
  remains only a comparison companion.

Domain-style sampling used here:
- `Function.partialDeriv`;
- `Function.HasDirectionalDerivativeAt`;
- `Function.directionalDerivativeAt`;
- `Function.directionalDerivativeAt_toWithTopBot_eq_inner_gradient`;
- `∇`;
- `EuclideanSpace.basisFun`.

Primitive data vs derived API:
- primitive input at the reusable layer: a differentiable map
  `f : EuclideanSpace 𝕜 ι → F` at `x`;
- core owner bridge reused from upstream: `Function.partialDeriv f x j`;
- core/canonical output in this item: coordinate decomposition of `fderiv` and `lineDeriv`
  through `Function.partialDeriv`;
- source-facing derived API: real-gradient and Chapter 23 directional-derivative coordinate
  formulas.

Layer target: `core/canonical` for the `fderiv`/`lineDeriv` coordinate decomposition through
`Function.partialDeriv`, with the Rockafellar gradient and
`Function.directionalDerivativeAt f.toWithBotTop` formulas as `bridge/view` specializations.
The textbook side condition `y ≠ 0` is redundant for both owner and bridge formulations and is
omitted from the public statement.
-/

section

namespace Function

-- Proof sketch: expand `y` in the canonical `PiLp.single` coordinates and use linearity of
-- `fderiv`, then rewrite each coordinate-direction value via
-- `partialDeriv_eq_fderiv_piLpBasisFun`.
/-- Canonical coordinate decomposition of the Fréchet derivative on finite Euclidean coordinates:
for differentiable `f`, evaluating `fderiv` on a direction `y` is the coordinate sum of the
textbook partial derivatives weighted by the coordinates of `y`. -/
theorem fderiv_eq_sum_smul_partialDeriv
    {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : EuclideanSpace 𝕜 ι → F} {x y : EuclideanSpace 𝕜 ι}
    (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 f x y = ∑ j, y j • partialDeriv f x j := by
  classical
  calc
    fderiv 𝕜 f x y = fderiv 𝕜 f x
        (∑ j, y j • ((PiLp.single (p := (2 : ENNReal)) j (1 : 𝕜)) : EuclideanSpace 𝕜 ι)) := by
      simpa [PiLp.basisFun_apply] using
        congrArg (fderiv 𝕜 f x) ((PiLp.basisFun (2 : ENNReal) 𝕜 ι).sum_repr y).symm
    _ = ∑ j, y j • fderiv 𝕜 f x
        (((PiLp.single (p := (2 : ENNReal)) j (1 : 𝕜)) : EuclideanSpace 𝕜 ι)) := by
      simp [map_sum]
    _ = ∑ j, y j • partialDeriv f x j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact congrArg (fun z => y j • z) <|
        by
          simpa [PiLp.basisFun_apply] using
            (partialDeriv_eq_fderiv_piLpBasisFun (hf := hf) (j := j)).symm

-- Proof sketch: rewrite `lineDeriv` by `DifferentiableAt.lineDeriv_eq_fderiv`, then apply
-- `fderiv_eq_sum_smul_partialDeriv`.
/-- Canonical coordinate decomposition companion for `lineDeriv` on finite Euclidean
coordinates. -/
theorem lineDeriv_eq_sum_smul_partialDeriv
    {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : EuclideanSpace 𝕜 ι → F} {x y : EuclideanSpace 𝕜 ι}
    (hf : DifferentiableAt 𝕜 f x) :
    lineDeriv 𝕜 f x y = ∑ j, y j • partialDeriv f x j := by
  calc
    lineDeriv 𝕜 f x y = fderiv 𝕜 f x y := hf.lineDeriv_eq_fderiv
    _ = ∑ j, y j • partialDeriv f x j := fderiv_eq_sum_smul_partialDeriv hf

end Function

-- Proof sketch: specialize `Function.fderiv_eq_sum_smul_partialDeriv` to scalar codomain and
-- rewrite scalar multiplication as multiplication.
/-- Scalar-valued specialization of the canonical `fderiv` coordinate decomposition. -/
theorem fderiv_eq_sum_partialDeriv_mul
    {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    {f : EuclideanSpace 𝕜 ι → 𝕜}
    {x y : EuclideanSpace 𝕜 ι} (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 f x y = ∑ j, Function.partialDeriv f x j * y j := by
  calc
    fderiv 𝕜 f x y = ∑ j, y j • Function.partialDeriv f x j := by
      simpa using (Function.fderiv_eq_sum_smul_partialDeriv (f := f) (x := x) (y := y) hf)
    _ = ∑ j, Function.partialDeriv f x j * y j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [smul_eq_mul, mul_comm]

-- Proof sketch: apply the coordinate-owner formula `partialDeriv_eq_gradient_apply` from
-- Theorem 25.1.2 and rewrite.
/-- The `j`-th coordinate of the gradient is the derivative of `f` along the `j`-th standard
basis line through `x`. -/
theorem gradient_apply_eq_partialDeriv
    {ι : Type*} [Fintype ι] {f : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
    (hf : DifferentiableAt ℝ f x) (j : ι) :
    ∇ f x j = Function.partialDeriv f x j := by
  simpa using (partialDeriv_eq_gradient_apply (hf := hf) (j := j)).symm

-- Proof sketch: identify the gradient itself with its coordinate function on `ι`, then apply
-- extensionality together with `gradient_apply_eq_partialDeriv`.
/-- Theorem 25.1.3: if `f : EuclideanSpace ℝ ι → ℝ` is differentiable at `x`, then the
gradient `∇ f x` has coordinates given by the textbook partial derivatives
`Function.partialDeriv f x j = ∂f / ∂ξ_j (x)`. -/
theorem gradient_eq_partialDeriv
    {ι : Type*} [Fintype ι] {f : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
    (hf : DifferentiableAt ℝ f x) :
    ∇ f x = Function.partialDeriv f x := by
  ext j
  simpa using gradient_apply_eq_partialDeriv hf j

-- Proof sketch: rewrite the gradient by `gradient_eq_partialDeriv`, then expand the Euclidean
-- inner product as the finite sum of coordinatewise products.
/-- The gradient pairing with a direction vector is the coordinate sum of the textbook partial
derivatives weighted by that direction. -/
theorem inner_gradient_eq_sum_partialDeriv_mul
    {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] {f : EuclideanSpace 𝕜 ι → 𝕜}
    {x y : EuclideanSpace 𝕜 ι} (hf : DifferentiableAt 𝕜 f x) :
    inner 𝕜 (∇ f x) y = ∑ j, Function.partialDeriv f x j * y j := by
  calc
    inner 𝕜 (∇ f x) y = fderiv 𝕜 f x y := by
      simpa using (inner_gradient_left hf)
    _ = ∑ j, Function.partialDeriv f x j * y j := fderiv_eq_sum_partialDeriv_mul hf

namespace Function

-- Proof sketch: combine the Chapter 23 owner formula from Theorem 25.1.1 with the scalar-valued
-- specialization `fderiv_eq_sum_partialDeriv_mul`.
/-- Theorem 25.1.3 on the canonical Chapter 23 owner surface: the directional derivative of
`f.toWithBotTop` at `x` in direction `y` is the coordinate sum of the standard-basis partial
derivatives weighted by `y`. -/
theorem hasDirectionalDerivativeAt_toWithBotTop_sum_partialDeriv_mul
    {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
    [TopologicalSpace (WithBotTop 𝕜)] [T2Space (WithBotTop 𝕜)] [Fintype ι]
    {f : EuclideanSpace 𝕜 ι → 𝕜}
    {x y : EuclideanSpace 𝕜 ι} (hf : DifferentiableAt 𝕜 f x) :
    HasDirectionalDerivativeAt f.toWithBotTop x y
      (↑(∑ j, Function.partialDeriv f x j * y j : 𝕜) : WithBotTop 𝕜) := by
  have hsum : fderiv 𝕜 f x y = ∑ j, Function.partialDeriv f x j * y j :=
    fderiv_eq_sum_partialDeriv_mul hf
  simpa [hsum] using
    (Function.hasDirectionalDerivativeAt_toWithBotTop_of_differentiableAt
      (f := f) (x := x) (y := y) hf)

-- Proof sketch: evaluate the owner `directionalDerivativeAt` at the limit supplied by
-- `hasDirectionalDerivativeAt_toWithBotTop_sum_partialDeriv_mul`.
/-- Theorem 25.1.3 on the canonical Chapter 23 owner surface: the directional derivative of
`f.toWithBotTop` at `x` in direction `y` is the coordinate sum of the standard-basis partial
derivatives weighted by `y`. -/
theorem directionalDerivativeAt_toWithBotTop_eq_sum_partialDeriv_mul
    {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
    [TopologicalSpace (WithBotTop 𝕜)] [T2Space (WithBotTop 𝕜)] [Fintype ι]
    {f : EuclideanSpace 𝕜 ι → 𝕜}
    {x y : EuclideanSpace 𝕜 ι} (hf : DifferentiableAt 𝕜 f x) :
    directionalDerivativeAt f.toWithBotTop x y =
      (↑(∑ j, Function.partialDeriv f x j * y j : 𝕜) : WithBotTop 𝕜) := by
  simpa [HasDirectionalDerivativeAt, directionalDerivativeAt] using
    (hasDirectionalDerivativeAt_toWithBotTop_sum_partialDeriv_mul hf).limUnder_eq

end Function

-- Proof sketch: specialize the canonical coordinate theorem
-- `Function.lineDeriv_eq_sum_smul_partialDeriv` to scalar codomain, then rewrite scalar
-- multiplication as multiplication.
/-- Comparison companion for Theorem 25.1.3: mathlib's scalar-valued `lineDeriv` equals the
same coordinate sum as the canonical Chapter 23 directional-derivative owner. -/
theorem lineDeriv_eq_sum_partialDeriv_mul
    {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] {f : EuclideanSpace 𝕜 ι → 𝕜}
    {x y : EuclideanSpace 𝕜 ι} (hf : DifferentiableAt 𝕜 f x) :
    lineDeriv 𝕜 f x y = ∑ j, Function.partialDeriv f x j * y j := by
  calc
    lineDeriv 𝕜 f x y = ∑ j, y j • Function.partialDeriv f x j := by
      simpa using (Function.lineDeriv_eq_sum_smul_partialDeriv (f := f) (x := x) (y := y) hf)
    _ = ∑ j, Function.partialDeriv f x j * y j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [smul_eq_mul, mul_comm]

end
