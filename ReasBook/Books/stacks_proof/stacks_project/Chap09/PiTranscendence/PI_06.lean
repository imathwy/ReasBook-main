import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial

universe u

-- Semantic recall note: `lean_leansearch` was unavailable in this environment; the bridge below
-- was checked directly against the canonical symmetric-polynomial owner
-- `MvPolynomial.esymmAlgHom` and its finite surjectivity theorem.

/-- Lemma PI-06: if `A(Y₁, …, Yₙ)` is a symmetric multivariate polynomial over a commutative ring
`R`, then `A` is obtained by evaluating some polynomial in `n` variables at the elementary
symmetric polynomials `e₁(Y), …, eₙ(Y)`. -/
theorem exists_esymm_polynomial_of_isSymmetric {R : Type u} [CommRing R] (n : ℕ)
    (A : MvPolynomial (Fin n) R) (hA : A.IsSymmetric) :
    ∃ B : MvPolynomial (Fin n) R,
      aeval (fun i : Fin n ↦ esymm (Fin n) R (i + 1)) B = A := by
  have hsurj : Function.Surjective (esymmAlgHom (Fin n) R n) :=
    esymmAlgHom_fin_surjective R le_rfl
  obtain ⟨B, hB⟩ := hsurj ⟨A, hA⟩
  refine ⟨B, ?_⟩
  simpa [esymmAlgHom_apply] using congrArg Subtype.val hB
