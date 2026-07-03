

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_45 (from Chap06) -/
noncomputable section

open Matrix
open RealSymmetricMatrixSpace
open scoped BigOperators RealSymmetricMatrixSpace

variable {n : ℕ}

/- Definition 6.45 lies in Chapter 6's real symmetric / Hermitian spectral log-sum-exp domain.

Primary domain:
- entropy smoothing of the maximal eigenvalue on real symmetric matrices.

Sampled owner-style declarations:
- `entropySmoothing` in `Chap06/Proposition_6_35`, the existing Chapter 6 owner for
  `X ↦ log (∑ i, exp (λᵢ(X)))` on the canonical carrier `𝕊^n`;
- `entropySmoothing_apply` in `Chap06/Proposition_6_35`, the source-facing expansion theorem for
  that owner;
- `RealSymmetricMatrixSpace.eigenvalues` in `Chap05/Definition_5_4_4_1`, the chapter owner for
  the ordered eigenvalues of a real symmetric matrix;
- mathlib `Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff`, the canonical proof-irrelevance
  bridge showing that the ordered eigenvalue list depends only on the underlying Hermitian matrix.

Best owner abstraction:
- source-facing: Definition 6.45's entropy smoothing formula;
- core/canonical: `entropySmoothing : 𝕊^n → ℝ`;
- bridge/view: restriction of that owner along the real-Hermitian-to-symmetric identification.

Primitive data:
- a real Hermitian matrix `X`.

Derived API:
- the symmetric-matrix view of `X`;
- the bridge theorem below identifying the recalled owner with the textbook Hermitian formula.

Source/core/bridge triage:
- source-facing: the Hermitian-form formula in
  `entropySmoothing_eq_log_sum_exp_eigenvalues`;
- core/canonical: `entropySmoothing`;
- bridge/view: the canonical subtype inclusion of a real Hermitian matrix into `𝕊^n`.

The previous file rebuilt two parallel owners, `eigenvalueExponentialSum` and
`entropySmoothedMaxEigenvalue`, for a notion already owned upstream by `entropySmoothing`.
This refinement removes those duplicate definitions and keeps only the minimal bridge from the
source-facing Hermitian presentation to the existing symmetric-matrix owner.
-/

namespace RealSymmetricMatrixSpace

/-- The canonical view of a real Hermitian matrix as an element of `𝕊^n`. -/
abbrev ofHermitian
    (X : {X : Matrix (Fin n) (Fin n) ℝ // X.IsHermitian}) : 𝕊^n :=
  ⟨X.1, by
    rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using X.2⟩

/-- Passing from a real Hermitian matrix to its canonical element of `𝕊^n` does not change the
ordered eigenvalue list. -/
theorem eigenvalues_ofHermitian
    (X : {X : Matrix (Fin n) (Fin n) ℝ // X.IsHermitian}) :
    eigenvalues (ofHermitian X) = X.2.eigenvalues := by
  exact
    (X.2.eigenvalues_eq_eigenvalues_iff (isHermitian (ofHermitian X))).2 rfl

end RealSymmetricMatrixSpace

/- Definition 6.45 is recalled directly from the Chapter 6 owner `entropySmoothing`. -/
#check (entropySmoothing : 𝕊^n → ℝ)

/-- Definition 6.45, source-facing bridge: on a real Hermitian matrix, the recalled owner
`entropySmoothing` is the logarithm of the sum of the exponentials of the ordered eigenvalues. -/
theorem entropySmoothing_eq_log_sum_exp_eigenvalues
    (X : {X : Matrix (Fin n) (Fin n) ℝ // X.IsHermitian}) :
    entropySmoothing (ofHermitian X) =
      Real.log (∑ i : Fin n, Real.exp (X.2.eigenvalues i)) := by
  simpa [eigenvalues_ofHermitian X] using entropySmoothing_apply (ofHermitian X)

end

/-! ### Proposition_6_45 (from Chap06) -/
noncomputable section

universe u v

/- Proposition 6.45 lies in the chapter's structured saddle-slice / attained weak-duality-gap
domain.

Mandatory domain-style sampling before refinement:
- `StructuredObjectiveModel.saddleFunction` in `Chap06/Definition_6_6`, the Chapter 6 owner for
  the saddle map `Ψ`;
- `StructuredObjectiveModel.objective` in `Chap06/Definition_6_6`, the canonical primal outer
  value `x ↦ sup_u Ψ(x, u)`;
- `StructuredObjectiveModel.adjointObjective` in `Chap06/Definition_6_6`, the canonical dual
  outer value `u ↦ inf_x Ψ(x, u)`;
- mathlib `IsGreatest` and `IsLeast`, the canonical order-theoretic owners for attained maxima
  and minima of the two saddle slices.

Best owner abstraction:
- source-facing: the attained-extrema weak-duality-gap inequality from Proposition 6.45;
- core/canonical: `StructuredObjectiveModel.saddleFunction`;
- bridge/view: the order-theoretic comparison between an attained maximum of `u ↦ Ψ(x, u)` and an
  attained minimum of `y ↦ Ψ(y, u)`.

Primitive data:
- `problem : StructuredObjectiveModel E₁ E₂`;
- a primal point `x : problem.primalSet`;
- a dual point `u : problem.dualSet`.

Derived API:
- the fixed-`x` saddle slice `problem.saddleFunction x`;
- the fixed-`u` saddle slice `fun y : problem.primalSet ↦ problem.saddleFunction y u`;
- attained extrema of those slices, expressed canonically by `IsGreatest` and `IsLeast`.

Source/core/bridge triage:
- source-facing: the proposition below on attained slice extrema;
- core/canonical: the Chapter 6 owner `StructuredObjectiveModel`;
- bridge/view: this real-valued attained-extrema corollary of the saddle slices.

The previous version kept the concrete Hilbert-space formula
`ψ(x) + ⟪A x, u⟫ - g(u)` as the main theorem surface. The mathematical content here is only the
order relation between the two slices of a saddle map, so the refined theorem is stated directly
on the Chapter 6 owner `StructuredObjectiveModel.saddleFunction`; the concrete bilinear formula is
already recovered elsewhere by `StructuredObjectiveModel.saddleFunction_apply`.
-/

namespace StructuredObjectiveModel

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- Proposition 6.45: if `f̄(x)` is the attained maximum of the fixed-`x` saddle slice
`u ↦ Ψ(x, u)` on `Q₂` and `ḡ(u)` is the attained minimum of the fixed-`u` saddle slice
`y ↦ Ψ(y, u)` on `Q₁`, then the weak-duality gap `f̄(x) - ḡ(u)` is nonnegative. -/
theorem weakDualityGap_nonneg_of_attainedExtrema
    {problem : StructuredObjectiveModel E₁ E₂}
    (x : problem.primalSet) (u : problem.dualSet) {fBar gBar : ℝ}
    (hprimal : IsGreatest (Set.range (problem.saddleFunction x)) fBar)
    (hdual :
      IsLeast
        (Set.range fun y : problem.primalSet ↦ problem.saddleFunction y u)
        gBar) :
    0 ≤ fBar - gBar := by
  exact sub_nonneg.mpr <|
    (hdual.2 <| Set.mem_range_self x).trans (hprimal.2 <| Set.mem_range_self u)

end StructuredObjectiveModel

end
