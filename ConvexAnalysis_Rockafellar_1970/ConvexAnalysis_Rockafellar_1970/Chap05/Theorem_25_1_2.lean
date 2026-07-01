import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_25_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient RealInnerProductSpace

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 25.1.2 is the standard-basis partial-derivative identity on Euclidean
  coordinates: for differentiable `f`, the `j`-th partial derivative is `fderiv` applied to the
  coordinate direction `e_j`; the canonical orthonormal basis vector
  `EuclideanSpace.basisFun ι 𝕜 j` is used as a bridge view.
- `core/canonical`: the ambient owner abstractions are mathlib's `DifferentiableAt`,
  `DifferentiableAt.lineDeriv_eq_fderiv`, and `LineDifferentiableAt` / `lineDeriv`.
- `bridge/view`: the real inner-product gradient formulas are thin corollaries via the
  recalled Chapter 23 gradient-value theorem
  `Function.directionalDerivativeAt_toWithTopBot_eq_inner_gradient`,
  the comparison theorem `Function.lineDeriv_toWithBotTop_eq_directionalDerivativeAt`,
  `∇`, and `EuclideanSpace.inner_basisFun_real`.
- `bridge/view`: this file owns the thin source-facing bridge
  `Function.partialDeriv f x j` for the
  textbook partial derivative `∂f/∂ξ_j (x)`, obtained by specializing the canonical line
  derivative to the coordinate direction `PiLp.single`.

Domain-style sampling used here:
- `DifferentiableAt`;
- `LineDifferentiableAt`;
- `lineDeriv`;
- `DifferentiableAt.lineDeriv_eq_fderiv`;
- `fderiv`;
- `PiLp.single`;
- `Function.lineDeriv_toWithBotTop_eq_directionalDerivativeAt`;
- `Function.directionalDerivativeAt_toWithTopBot_eq_inner_gradient`;
- `∇`;
- `EuclideanSpace.basisFun`.

Primitive data vs derived API:
- primitive input: a differentiable function `f` at `x`;
- derived API: the partial-derivative owner `Function.partialDeriv f x j`, the existence predicate
  `Function.HasPartialDerivAt f x j`, the differentiability-to-existence bridge
  `DifferentiableAt.hasPartialDerivAt`, the canonical basis-value bridge theorem
  `partialDeriv_eq_fderiv_basisFun`, and the real gradient bridge formulas.

Layer target: the owner theorem is `core/canonical` at the `fderiv` layer via
`DifferentiableAt.lineDeriv_eq_fderiv`; Euclidean basis and gradient-coordinate formulas are
`bridge/view`
corollaries.

Notation evaluation:
- the textbook symbol `∂f / ∂ξ_j (x)` is not introduced as Lean notation: `∂` already has heavy
  derivative-related parser use in mathlib, and the short owner
  `Function.partialDeriv f x j`
  gives a cleaner stable theorem surface than a custom parameterized notation.

Scalar/ambient minimality note:
- the core partial-derivative owner layer (`Function.partialDeriv`,
  `Function.HasPartialDerivAt`, `DifferentiableAt.hasPartialDerivAt`) is
  scalar/codomain-generic on finite Euclidean coordinates (`𝕜` with
  `[NontriviallyNormedField 𝕜]`, codomain `F` with `[NormedSpace 𝕜 F]`),
  because only line-derivative primitives are needed there.
- the basis theorem `partialDeriv_eq_fderiv_basisFun` and real gradient formulas are bridge-only
  consequences from Theorem 25.1.1.
-/

section

namespace Function

/-- The textbook `j`-th partial derivative of `f` at `x`. -/
abbrev partialDeriv {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : EuclideanSpace 𝕜 ι → F)
    (x : EuclideanSpace 𝕜 ι) (j : ι) : F := by
  classical
  exact lineDeriv 𝕜 f x ((PiLp.single (p := (2 : ENNReal)) j (1 : 𝕜)) : EuclideanSpace 𝕜 ι)

/-- The `j`-th partial derivative of `f` exists at `x`. -/
abbrev HasPartialDerivAt {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : EuclideanSpace 𝕜 ι → F)
    (x : EuclideanSpace 𝕜 ι) (j : ι) : Prop := by
  classical
  exact LineDifferentiableAt 𝕜 f x
    ((PiLp.single (p := (2 : ENNReal)) j (1 : 𝕜)) : EuclideanSpace 𝕜 ι)

end Function

-- Proof sketch: apply mathlib's canonical differentiability-to-line-differentiability owner
-- theorem in the intrinsic coordinate direction given by `PiLp.single`.
/-- Differentiability at `x` implies existence of each textbook standard-basis partial derivative
at `x`. -/
theorem DifferentiableAt.hasPartialDerivAt
    {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : EuclideanSpace 𝕜 ι → F} {x : EuclideanSpace 𝕜 ι}
    (hf : DifferentiableAt 𝕜 f x) (j : ι) :
    Function.HasPartialDerivAt f x j := by
  classical
  simpa [Function.HasPartialDerivAt] using
    (show LineDifferentiableAt 𝕜 f x
        ((PiLp.single (p := (2 : ENNReal)) j (1 : 𝕜)) : EuclideanSpace 𝕜 ι) from
      hf.lineDifferentiableAt)

-- Proof sketch: rewrite `Function.partialDeriv` using the canonical `PiLp` basis vector, then
-- apply `DifferentiableAt.lineDeriv_eq_fderiv` in that primitive direction.
/-- Primitive bridge form of Theorem 25.1.2: for a differentiable map on finite Euclidean
coordinates, the `j`-th textbook partial derivative is `fderiv` applied to the coordinate
direction from `PiLp.basisFun`. -/
theorem partialDeriv_eq_fderiv_piLpBasisFun
    {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : EuclideanSpace 𝕜 ι → F} {x : EuclideanSpace 𝕜 ι}
    (hf : DifferentiableAt 𝕜 f x) (j : ι) :
    Function.partialDeriv f x j =
      fderiv 𝕜 f x (((PiLp.basisFun (2 : ENNReal) 𝕜 ι) j) : EuclideanSpace 𝕜 ι) := by
  classical
  simpa [Function.partialDeriv] using
    (show lineDeriv 𝕜 f x (((PiLp.basisFun (2 : ENNReal) 𝕜 ι) j) : EuclideanSpace 𝕜 ι) =
        fderiv 𝕜 f x (((PiLp.basisFun (2 : ENNReal) 𝕜 ι) j) : EuclideanSpace 𝕜 ι) from
      by simpa [PiLp.basisFun_apply] using hf.lineDeriv_eq_fderiv)

-- Proof sketch: rewrite `Function.partialDeriv` by `PiLp.single`, then use
-- `DifferentiableAt.lineDeriv_eq_fderiv` and identify `PiLp.single` with
-- `EuclideanSpace.basisFun ι 𝕜 j`.
/-- Theorem 25.1.2 as the standard-orthonormal-basis bridge: for a differentiable map on
Euclidean coordinates, the `j`-th textbook partial derivative is `fderiv` applied to
`EuclideanSpace.basisFun ι 𝕜 j`. -/
theorem partialDeriv_eq_fderiv_basisFun
    {𝕜 ι F : Type*} [RCLike 𝕜] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : EuclideanSpace 𝕜 ι → F} {x : EuclideanSpace 𝕜 ι}
    (hf : DifferentiableAt 𝕜 f x) (j : ι) :
    Function.partialDeriv f x j = fderiv 𝕜 f x (EuclideanSpace.basisFun ι 𝕜 j) := by
  classical
  simpa [Function.partialDeriv, EuclideanSpace.basisFun_apply] using
    (show lineDeriv 𝕜 f x ((PiLp.single (p := (2 : ENNReal)) j (1 : 𝕜)) : EuclideanSpace 𝕜 ι) =
        fderiv 𝕜 f x (EuclideanSpace.basisFun ι 𝕜 j) from
      by simpa [EuclideanSpace.basisFun_apply] using hf.lineDeriv_eq_fderiv)

end

section

-- Proof sketch: compare `lineDeriv` with the Chapter 23 owner, then rewrite by the recalled
-- gradient-value theorem, specialized to `e_j`.
/-- Real-gradient bridge companion to Theorem 25.1.2: for real Euclidean coordinates, the
`j`-th partial derivative equals the gradient pairing with the `j`-th basis vector. -/
theorem partialDeriv_eq_inner_gradient
    {ι : Type*} [Fintype ι] {f : EuclideanSpace ℝ ι → ℝ}
    {x : EuclideanSpace ℝ ι} (hf : DifferentiableAt ℝ f x) (j : ι) :
    Function.partialDeriv f x j = ⟪∇ f x, EuclideanSpace.basisFun ι ℝ j⟫ := by
  classical
  apply WithBotTop.coe_eq_coe_iff.mp
  calc
    (↑(Function.partialDeriv f x j) : WithBotTop ℝ) =
        (↑(lineDeriv ℝ f x (EuclideanSpace.basisFun ι ℝ j)) : WithBotTop ℝ) := by
      simp [Function.partialDeriv, EuclideanSpace.basisFun_apply]
    _ = Function.directionalDerivativeAt f.toWithBotTop x
          (EuclideanSpace.basisFun ι ℝ j) := by
      simpa using
        (Function.lineDeriv_toWithBotTop_eq_directionalDerivativeAt
          (f := f) (x := x) (y := EuclideanSpace.basisFun ι ℝ j) hf)
    _ = (⟪∇ f x, EuclideanSpace.basisFun ι ℝ j⟫ : WithBotTop ℝ) := by
      simpa using
        (Function.directionalDerivativeAt_toWithTopBot_eq_inner_gradient
          (f := f) (x := x) (y := EuclideanSpace.basisFun ι ℝ j) hf)

-- Proof sketch: combine the inner-product bridge above with
-- `EuclideanSpace.inner_basisFun_real`.
/-- Real-coordinate bridge companion to Theorem 25.1.2: at each coordinate index `j`, the
partial derivative is the `j`-th coordinate of the Euclidean gradient. -/
theorem partialDeriv_eq_gradient_apply
    {ι : Type*} [Fintype ι] {f : EuclideanSpace ℝ ι → ℝ}
    {x : EuclideanSpace ℝ ι} (hf : DifferentiableAt ℝ f x) (j : ι) :
    Function.partialDeriv f x j = ∇ f x j := by
  calc
    Function.partialDeriv f x j = ⟪∇ f x, EuclideanSpace.basisFun ι ℝ j⟫ :=
      partialDeriv_eq_inner_gradient hf j
    _ = ∇ f x j := by
      simp [EuclideanSpace.inner_basisFun_real]

end
