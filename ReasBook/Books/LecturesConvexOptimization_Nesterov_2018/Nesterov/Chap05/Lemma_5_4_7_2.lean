import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_3_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_4_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped MatrixOrder RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n
local notation "Point" => SymmMat × SymmMat
local notation "Z" => WithLp 2 Point
local notation "ofZ" => (WithLp.ofLp : Z → Point)

/- Lemma 5.4.7.2 lies in the Chapter 5 self-concordant-barrier / symmetric-matrix inverse-epigraph
domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Chap05/Definition_5_3_2`, the chapter owner for
  `ν`-self-concordant barriers;
* `IsSelfConcordantBarrierOnWith.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions`
  in `Chap05/Theorem_5_4_1_2`, the canonical owner of the recession-direction barrier lower
  bound;
* mathlib `WithLp.prodContinuousLinearEquiv`, the canonical `L²` product bridge between raw pairs
  and the ambient Hilbert-space owner;
* `RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup`,
  `RealSymmetricMatrixSpace.symmetricMatrixNormedSpace`, and
  `RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace` in `Chap05/Definition_5_4_4_2`, the
  chapter owner layer for the intrinsic Frobenius geometry on `𝕊^n`;
* `𝕊^n` in `Chap05/Definition_5_4_4_1`, the chapter owner for real symmetric matrices;
* `𝕊^n₊` in `Chap05/Definition_5_4_4_3`, the positive-semidefinite cone owner;
* `𝕊^n₊₊` in `Chap05/Definition_5_4_4_5`, the intrinsic strict positive-definite cone owner.

Best owner abstraction:
* source-facing: the inverse epigraph `𝓘_n = {(X, Y) | X ≻ 0, Y ⪰ X⁻¹}`;
* core/canonical: the barrier owner on the canonical ambient product `Z = WithLp 2 (𝕊^n × 𝕊^n)`;
* bridge/view: the source-facing raw-pair set `matrixInverseEpigraph` and its pullback along
  `WithLp.ofLp`.

Primitive data:
* `n : ℕ`;
* the source-facing set `matrixInverseEpigraph : Set (𝕊^n × 𝕊^n)`.

Derived API:
* the membership theorem `mem_matrixInverseEpigraph_iff`;
* the barrier-parameter lower bound
  `matrixInverseEpigraph_barrierParameter_ge_two_mul_dimension`.

The previous file encoded points of `𝓘_n` as raw coordinates in the full matrix-entry Euclidean
space and rebuilt projection/instance scaffolding just to recover the symmetric matrices. That
ambient level is too low: the source mathematics is about symmetric matrices and the chapter
already owns `𝕊^n`, `𝕊^n₊₊`, and their Frobenius Hilbert-space structure. This refinement
therefore keeps the public set owner on the intrinsic product `𝕊^n × 𝕊^n`, but moves the barrier
theorem itself to the canonical `L²` product owner `Z = WithLp 2 (𝕊^n × 𝕊^n)` via the bridge
`WithLp.ofLp`. Downstream users now reuse the chapter owner instances directly instead of carrying
any parallel local ambient geometry.
-/

/-- The inverse-epigraph set `𝓘_n = {(X, Y) | X ≻ 0, Y ⪰ X⁻¹}` of symmetric real `n × n`
matrices. -/
def matrixInverseEpigraph : Set Point :=
  {XY | XY.1 ∈ 𝕊^n₊₊ ∧ (XY.1 : Mat)⁻¹ ≤ (XY.2 : Mat)}

/-- A pair `(X, Y)` belongs to `matrixInverseEpigraph` exactly when `X` is positive definite and
`Y` dominates `X⁻¹` in the Löwner order. -/
@[simp] theorem mem_matrixInverseEpigraph_iff (XY : Point) :
    XY ∈ matrixInverseEpigraph ↔
      XY.1 ∈ 𝕊^n₊₊ ∧ (XY.1 : Mat)⁻¹ ≤ (XY.2 : Mat) :=
  Iff.rfl

-- Proof sketch: apply
-- `barrierParameter_ge_sum_alpha_div_beta_of_recession_directions` to
-- `matrixInverseEpigraph` with base point `(γ I, γ I)` for `γ > 1`, recession directions the
-- `2n` rank-one directions `(eᵢ eᵢᵀ, 0)` and `(0, eᵢ eᵢᵀ)`, backward-step coefficients
-- `β = γ - 1 / γ`, and forward coefficients `α = γ - 1`. The combined step reaches `(I, I)`,
-- giving `ν ≥ 2n * γ / (1 + γ)`; letting `γ → ∞` yields `ν ≥ 2n`.
/-- Lemma 5.4.7.2: any self-concordant barrier for the inverse-epigraph set
`𝓘_n = {(X, Y) | X ≻ 0, Y ⪰ X⁻¹}` has parameter at least `2 n`. -/
theorem matrixInverseEpigraph_barrierParameter_ge_two_mul_dimension
    {ν : NNReal} {F : Z → ℝ}
    (hF : IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior matrixInverseEpigraph) ν F) :
    (2 * n : ℝ) ≤ (ν : ℝ) := by
  let Q : Set Z := ofZ ⁻¹' matrixInverseEpigraph
  have hQ_interior :
      interior Q = ofZ ⁻¹' interior matrixInverseEpigraph := by
    simpa [Q] using
      ((WithLp.prodContinuousLinearEquiv 2 ℝ SymmMat SymmMat).toHomeomorph.preimage_interior
        matrixInverseEpigraph).symm
  have hF' : IsSelfConcordantBarrierOnWith (interior Q) ν F := by
    simpa [hQ_interior] using hF
  letI : IsSelfConcordantBarrierOnWith (interior Q) ν F := hF'
  sorry

end
