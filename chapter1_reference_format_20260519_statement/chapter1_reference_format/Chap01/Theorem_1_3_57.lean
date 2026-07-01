import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace MvPolynomial

/-- Theorem 1.3.57: every symmetric polynomial in `K[X₁, …, Xₙ]` is uniquely a polynomial in the
elementary symmetric polynomials `esymm (Fin n) K 1, …, esymm (Fin n) K n`. Equivalently, if
`P` is symmetric, then there is a unique `Φ` with `P = Φ(Σ₁, …, Σₙ)`. -/
theorem existsUnique_aeval_esymm_eq_of_isSymmetric {K : Type u} [CommRing K] {n : ℕ}
    {P : MvPolynomial (Fin n) K} (hP : P.IsSymmetric) :
    ∃! Φ : MvPolynomial (Fin n) K,
      aeval (fun i : Fin n ↦ esymm (Fin n) K (i + 1)) Φ = P := by
  let P' : symmetricSubalgebra (Fin n) K := ⟨P, hP⟩
  obtain ⟨Φ, hΦ⟩ := (esymmAlgHom_fin_bijective K n).2 P'
  refine ⟨Φ, ?_, ?_⟩
  · change aeval (fun i : Fin n ↦ esymm (Fin n) K (i + 1)) Φ = P
    rw [← esymmAlgHom_apply Φ]
    exact congrArg Subtype.val <| by simpa [P'] using hΦ
  · intro Ψ hΨ
    apply (esymmAlgHom_fin_bijective K n).1
    apply Subtype.ext
    rw [esymmAlgHom_apply, hΨ]
    symm
    exact congrArg Subtype.val <| by simpa [P'] using hΦ

end MvPolynomial
