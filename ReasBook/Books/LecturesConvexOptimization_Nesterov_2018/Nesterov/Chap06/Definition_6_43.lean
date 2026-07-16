import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_42

-- Declarations for this item will be appended below by the statement pipeline.

open RealSymmetricMatrixSpace
open scoped BigOperators RealSymmetricMatrixSpace

noncomputable section

/- Definition 6.43 lies in the chapter's symmetric-matrix spectral-power-series domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` and `RealSymmetricMatrixSpace.eigenvalues`, the canonical symmetric-matrix and
  spectral owners already used throughout the chapter;
- Chapter 6 `RealSymmetricMatrixSpace.powerTrace`, written `π[k]`, the chapter owner for the
  trace-power coordinates of a symmetric matrix;
- mathlib `FormalMultilinearSeries.ofScalars`, `FormalMultilinearSeries.ofScalarsSum`, and
  `FormalMultilinearSeries.hasFPowerSeriesOnBall`, the canonical scalar power-series owner, its
  sum, and its convergence theorem on the open ball of radius `p.radius`.

Best owner abstraction:
- source-facing: a scalar power series with positive radius of convergence and coefficients
  nonnegative in degrees `k ≥ 2`, together with its induced spectral function on the natural
  matrix domain;
- core/canonical: `FormalMultilinearSeries.ofScalars ℝ coeff` and the chapter owners `𝕊^n`,
  `eigenvalues`, and `π[k]`;
- bridge/view: the scalar and matrix convergence domains together with the trace-power series
  expansion on `π[k]`.

Primitive data:
- a coefficient sequence `coeff : ℕ → ℝ`;
- a witness that the canonical scalar power series `FormalMultilinearSeries.ofScalars ℝ coeff`
  has strictly positive radius of convergence;
- the sign condition `0 ≤ coeff k` for all `k ≥ 2`.

Derived API:
- the genuine convergence radius `Φ.radius`;
- the scalar convergence domain `Φ.scalarDom`, used exactly where the canonical convergence API
  needs a domain membership witness for `FormalMultilinearSeries.ofScalarsSum Φ.coeff`;
- for each `n`, the matrix spectral domain `Φ.dom` together with the induced spectral sum
  `Φ.matrixFun X`;
- the bridge theorem that rewrites `Φ.matrixFun` as the Chapter 6 trace-power series in `π[k]`.

The previous version stored a free positive number called `radius`, defined the scalar function by
an unsupported global `tsum`, and then rebuilt a parallel matrix-level surface from that data. The
refinement below keeps the source-facing power-series object, but derives its radius and its
source domain and matrix spectral owner directly from mathlib's canonical scalar-series owner and
from the existing chapter spectral owners, without extra public aliases or proof-irrelevant domain
arguments in the public function surface.
-/

/-- Definition 6.43: an analytic symmetric spectral function is given by a real power series
`f(τ) = a_0 + ∑_{k=1}^∞ a_k τ^k` whose genuine radius of convergence is positive and whose
coefficients are nonnegative for every degree `k ≥ 2`. It induces a scalar function on the open
interval of convergence and, for each `n`, a spectral function on the symmetric matrices whose
eigenvalues lie in that interval. -/
structure AnalyticSymmetricSpectralFunction where
  coeff : ℕ → ℝ
  has_pos_radius : 0 < (FormalMultilinearSeries.ofScalars ℝ coeff).radius
  coeff_nonneg (k : ℕ) (hk : 2 ≤ k) : 0 ≤ coeff k

namespace AnalyticSymmetricSpectralFunction

variable (Φ : AnalyticSymmetricSpectralFunction)

/-- The genuine radius of convergence of `Φ`. -/
abbrev radius : ENNReal :=
  (FormalMultilinearSeries.ofScalars ℝ Φ.coeff).radius

/-- The scalar convergence domain `(-Φ.radius, Φ.radius)`, written in the canonical `eball`
language used by mathlib's scalar-series API. -/
def scalarDom : Set ℝ :=
  Metric.eball (0 : ℝ) Φ.radius

/-- The scalar function induced by `Φ` is the canonical sum of its scalar formal power series. -/
def scalarFun : ℝ → ℝ :=
  FormalMultilinearSeries.ofScalarsSum Φ.coeff

/-- An analytic symmetric spectral function can be evaluated as its induced scalar function. -/
instance : CoeFun AnalyticSymmetricSpectralFunction (fun _ ↦ ℝ → ℝ) where
  coe Φ := Φ.scalarFun

/-- The induced matrix spectral domain: every eigenvalue lies in the scalar convergence domain. -/
def dom {n : ℕ} : Set (𝕊^n) :=
  {X | ∀ i : Fin n, eigenvalues X i ∈ Φ.scalarDom}

/-- The spectral function induced by `Φ`. Its natural source-domain restriction is recorded
separately by `Φ.dom`; the underlying scalar-series owner is the total canonical sum
`FormalMultilinearSeries.ofScalarsSum Φ.coeff`. -/
def matrixFun {n : ℕ} (X : 𝕊^n) : ℝ :=
  ∑ i : Fin n, FormalMultilinearSeries.ofScalarsSum Φ.coeff (eigenvalues X i)

/-- The canonical radius of convergence attached to `Φ` is strictly positive. -/
theorem radius_pos : 0 < Φ.radius :=
  Φ.has_pos_radius

/-- The scalar function of `Φ` is represented by its canonical scalar formal power series on the
open ball of radius `Φ.radius`. -/
theorem hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall
      (FormalMultilinearSeries.ofScalarsSum Φ.coeff)
      (FormalMultilinearSeries.ofScalars ℝ Φ.coeff)
      0
      Φ.radius := by
  simpa [radius] using
    (FormalMultilinearSeries.ofScalars ℝ Φ.coeff).hasFPowerSeriesOnBall Φ.radius_pos

/-- The scalar function attached to `Φ` has the expected convergent power-series expansion at every
point of the scalar domain. -/
theorem scalar_hasSum {τ : ℝ} (hτ : τ ∈ Φ.scalarDom) :
    HasSum (fun k : ℕ ↦ Φ.coeff k * τ ^ k) (Φ τ) := by
  simpa [smul_eq_mul, mul_comm] using
    FormalMultilinearSeries.hasSum (FormalMultilinearSeries.ofScalars ℝ Φ.coeff) hτ

/-- Evaluating `Φ` as a function returns the canonical scalar-series sum attached to its
coefficients. -/
@[simp] theorem coe_apply (τ : ℝ) :
    Φ τ = FormalMultilinearSeries.ofScalarsSum Φ.coeff τ :=
  rfl

@[simp] theorem mem_dom_iff {n : ℕ} {X : 𝕊^n} :
    X ∈ Φ.dom ↔ ∀ i : Fin n, eigenvalues X i ∈ Φ.scalarDom :=
  Iff.rfl

@[simp] theorem matrixFun_apply {n : ℕ} {X : 𝕊^n} :
    Φ.matrixFun X = ∑ i : Fin n, FormalMultilinearSeries.ofScalarsSum Φ.coeff (eigenvalues X i) :=
  rfl

-- Proof sketch: for each eigenvalue `λᵢ(X)`, use `scalar_hasSum` on the scalar-domain witness
-- coming from `hX i`; summing over `i` and exchanging the finite spectral sum with the convergent
-- scalar series identifies the resulting coefficient of degree `k` with
-- `a_k * ∑ᵢ λᵢ(X)^k = a_k * π_k(X)`.
/-- The matrix spectral function of `Φ` is the Chapter 6 trace-power series attached to the owner
`π[k]`. This is the thin bridge from the source-facing spectral sum to the existing trace-power
owners. -/
theorem matrixFun_hasSum_powerTrace {n : ℕ} {X : 𝕊^n} (hX : X ∈ Φ.dom) :
    HasSum (fun k : ℕ ↦ Φ.coeff k * π[k] X) (Φ.matrixFun X) := by
  sorry

end AnalyticSymmetricSpectralFunction
