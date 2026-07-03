import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_41 (from Chap06) -/
noncomputable section

open Matrix
open RealSymmetricMatrixSpace
open scoped MatrixOrder RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 6.41 lies in the chapter's real symmetric-matrix spectral-calculus domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` and `RealSymmetricMatrixSpace.eigenvalues`, the canonical carrier and ordered
  eigenvalue owner for real symmetric matrices;
- Chapter 5 `⟪·, ·⟫_F`, the existing Frobenius inner-product owner on `𝕊^n`;
- mathlib `Matrix.diagonal`, the canonical diagonal-matrix owner already matching the textbook
  notation `D(λ)`;
- mathlib `CFC.abs`, the canonical functional-calculus absolute value on self-adjoint matrices;
- mathlib `WithLp.toLp`, the canonical finite-dimensional `ℓ_p` owner for vectors indexed by
  `Fin n`.

Best owner abstraction:
- source-facing: the symmetric-matrix absolute value `|X|` and the spectral `p`-norm
  `‖X‖_(p)` on `𝕊^n`;
- core/canonical: `𝕊^n`, `eigenvalues`, `CFC.abs`, and `WithLp.toLp`;
- bridge/view: the ambient matrix order statement `0 ≤ |X|` and the eigenvalue-norm formulas.

Primitive data:
- the chapter carrier `𝕊^n` from Chapter 5;
- a spectral exponent `p ∈ [1, ∞]`.

Derived API:
- the source-facing absolute-value owner `RealSymmetricMatrixSpace.abs`, written `|X|`;
- the source-facing spectral `p`-norm owner `symmetricMatrixSpectralPNorm`;
- the bridge theorem rewriting `‖X‖_(p)` through the eigenvalues of `|X|`.

This refinement reuses the canonical Chapter 5 symmetric-matrix carrier and eigenvalue owner,
keeps the textbook absolute value as a source-facing operation on `𝕊^n`, and defines the matrix
spectral `p`-norm directly from the `WithLp` norm of the ordered eigenvalue vector. It does not
introduce a public owner for the auxiliary diagonalization matrix `U(X)`, since that choice is
noncanonical and serves only to describe the same intrinsic functional-calculus construction.
-/

namespace RealSymmetricMatrixSpace

-- Proof sketch: `CFC.abs` preserves self-adjointness. Specializing the ambient matrix order to
-- real matrices, the ambient absolute value of a symmetric matrix is Hermitian and therefore
-- symmetric, so it lies back in `𝕊^n`.
/-- The ambient functional-calculus absolute value of a real symmetric matrix is again a point of
`𝕊^n`. -/
private theorem abs_mem (X : SymmMat) :
    CFC.abs (X : Mat) ∈ 𝕊^n := sorry

/-- The source-facing absolute value on `𝕊^n`, induced by the ambient functional-calculus absolute
value. -/
def abs (X : SymmMat) : SymmMat :=
  ⟨CFC.abs (X : Mat), abs_mem X⟩

/- Lean surface notation for the textbook matrix absolute value on `𝕊^n`. -/
scoped macro:max "|" x:term:max "|" : term => `(RealSymmetricMatrixSpace.abs $x)

-- Proof sketch: unfold `RealSymmetricMatrixSpace.abs`; the subtype carrier is definitionally the
-- ambient matrix absolute value `CFC.abs (X : Mat)`.
/-- Expanding `|X|` on `𝕊^n` recovers the ambient functional-calculus absolute value. -/
@[simp] theorem coe_abs (X : SymmMat) :
    ((|X| : SymmMat) : Mat) = CFC.abs (X : Mat) := sorry

-- Proof sketch: `CFC.abs_nonneg` gives the ambient matrix-order nonnegativity of `CFC.abs (X)`,
-- and `coe_abs` identifies this ambient matrix with the source-facing matrix `|X|`.
/-- The source-facing absolute value `|X|` is positive semidefinite in the ambient matrix order. -/
theorem abs_nonneg (X : SymmMat) :
    0 ≤ ((|X| : SymmMat) : Mat) := sorry

end RealSymmetricMatrixSpace

/-- Definition 6.41 [Chapter6_2.json:96]: for `p ∈ [1, ∞]`, the spectral `p`-norm of a real
symmetric matrix `X ∈ 𝕊^n` is the `ℓ_p` norm of its ordered eigenvalue vector `λ(X)`. The
Frobenius pairing and the auxiliary diagonal matrix notation `D(λ)` are reused from the canonical
Chapter 5 Frobenius owner and mathlib's diagonal-matrix API. -/
def symmetricMatrixSpectralPNorm
    (p : Set.Ici (1 : ENNReal)) (X : SymmMat) : ℝ :=
  ‖WithLp.toLp (p : ENNReal) (eigenvalues X)‖

-- Proof sketch: unfold `symmetricMatrixSpectralPNorm`; the right-hand side is exactly the
-- defining `WithLp` norm of the ordered eigenvalue vector.
/-- Expanding `symmetricMatrixSpectralPNorm p X` gives the `ℓ_p` norm of the ordered eigenvalue
vector `λ(X)`. -/
theorem symmetricMatrixSpectralPNorm_eq_eigenvalueNorm
    (p : Set.Ici (1 : ENNReal)) (X : SymmMat) :
    symmetricMatrixSpectralPNorm p X =
      ‖WithLp.toLp (p : ENNReal) (eigenvalues X)‖ := sorry

-- Proof sketch: the matrix absolute value `|X|` has eigenvalues `|λ_i(X)|`, so the same
-- `WithLp` norm computes the spectral `p`-norm from the ordered eigenvalues of `|X|`.
/-- The spectral `p`-norm can equally be computed from the ordered eigenvalues of `|X|`. -/
theorem symmetricMatrixSpectralPNorm_eq_abs_eigenvalueNorm
    (p : Set.Ici (1 : ENNReal)) (X : SymmMat) :
    symmetricMatrixSpectralPNorm p X =
      ‖WithLp.toLp (p : ENNReal) (eigenvalues (|X|))‖ := sorry

/-! ### Proposition_6_41 (from Chap06) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 6.41 lies in the chapter's constrained-subdifferential / affine-optimality domain.

Sampled owner-style declarations:
- `constrainedSubdifferential` together with the notation `∂[Q] f(x)` in
  `Chap03/Definition_3_1_5`;
- `mem_constrainedSubdifferential_iff` in `Chap03/Definition_3_1_5`, the atomic bridge from the
  owner to the raw affine lower-support inequality;
- `ConvexOn.isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential` in
  `Chap03/Theorem_3_1_23`, a downstream owner-level consumer of the same constrained
  subdifferential;
- `subdifferentialWithin` in `Chap03/Theorem_3_44`, the real-valued bridge/view built on the same
  owner.

Best owner abstraction:
- source-facing: Proposition 6.41's affine optimality criterion for an extended-valued constrained
  subgradient;
- core/canonical: `constrainedSubdifferential`;
- bridge/view: `mem_constrainedSubdifferential_iff`.

Primitive data:
- a feasible set `Q`, extended-valued objective `Ψ`, and feasible base point `v ∈ Q`;
- finiteness of the base value `Ψ v < ⊤`;
- the affine optimality inequality on `Q`.

Derived API:
- the owner-level conclusion `-s ∈ ∂[Q] Ψ(v)`.

Source/core/bridge triage:
- source-facing: the proposition below, written directly on the chapter owner notation `∂[Q] Ψ(v)`;
- core/canonical: `constrainedSubdifferential`;
- bridge/view: the raw affine inequality hypothesis and the membership lemma
  `mem_constrainedSubdifferential_iff`.

The previous file duplicated the Chapter 3 owner locally and omitted the owner feasibility
condition `v ∈ Q`. This refinement removes the duplicate wheel, states the proposition directly
with the canonical owner surface, and keeps only the textbook affine inequality as the bridge
assumption.
-/

/-- Proposition 6.41: if a feasible point `v ∈ Q` satisfies the affine optimality inequality
`⟪s, x - v⟫ + Ψ(x) ≥ Ψ(v)` for every `x ∈ Q`, then `-s` belongs to the constrained
subdifferential of `Ψ` at `v` relative to `Q`. -/
-- Proof sketch: unfold the owner membership criterion
-- `mem_constrainedSubdifferential_iff`. The finiteness hypothesis gives `v ∈ dom Ψ`, and the
-- assumed inequality rearranges to the defining affine lower-support inequality for `-s`.
theorem neg_mem_constrainedSubdifferential_of_affine_optimality
    {Q : Set E} {Ψ : E → WithTop ℝ} {s v : E}
    (hvQ : v ∈ Q)
    (hv_finite : Ψ v < ⊤)
    (hoptimal :
      ∀ ⦃x : E⦄, x ∈ Q →
        (((inner ℝ s (x - v) : ℝ) : WithTop ℝ) + Ψ x) ≥ Ψ v) :
    -s ∈ ∂[Q] Ψ(v) := by
  rw [mem_constrainedSubdifferential_iff]
  refine ⟨hvQ, by simpa, ?_⟩
  intro x hx
  by_cases hx_finite : Ψ x < ⊤
  · rcases WithTop.ne_top_iff_exists.mp (ne_of_lt hv_finite) with ⟨rv, hrv⟩
    rcases WithTop.ne_top_iff_exists.mp (ne_of_lt hx_finite) with ⟨rx, hrx⟩
    have hopt := hoptimal hx
    rw [← hrv, ← hrx] at hopt ⊢
    norm_num at hopt ⊢
    have hreal : rv ≤ inner ℝ s (x - v) + rx := by
      exact_mod_cast hopt
    have hminorant : rv + -inner ℝ s (x - v) ≤ rx := by
      linarith
    exact_mod_cast hminorant
  · have hx_top : Ψ x = ⊤ := by
      simpa [lt_top_iff_ne_top] using hx_finite
    simp [hx_top]

end
