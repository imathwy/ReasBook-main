import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

section

variable {m n : ℕ}

-- Proof sketch: reduce this formulation to the first Farkas lemma by adjoining the inequality
-- `-dotProduct c x ≤ -1` to `A *ᵥ x ≤ 0`, and conversely evaluate the certificate
-- `Aᵀ *ᵥ y = c` on any `x` with `A *ᵥ x ≤ 0` to obtain `dotProduct c x ≤ 0` from the
-- coordinatewise nonnegativity of `y`.
/-- Lemma 2.5: Farkas's lemma in the implication form. For a real matrix `A` and vector `c`, the
implication `A x ≤ 0 → cᵀ x ≤ 0` for every `x` is equivalent to the existence of a nonnegative
vector `y` with `Aᵀ y = c`; here `ℝ^m_+` is rendered as `Set.Ici (0 : Fin m → ℝ)`. -/
theorem farkas_lemma_second_formulation
    (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    (∀ x : Fin n → ℝ, A *ᵥ x ≤ (0 : Fin m → ℝ) → dotProduct c x ≤ 0) ↔
      ∃ y ∈ Set.Ici (0 : Fin m → ℝ), Aᵀ *ᵥ y = c := sorry

/-- Bridge/view: the certificate in Lemma 2.5 is equivalently membership of `c` in the image of
the positive pointed cone under the transpose linear map `Aᵀ`. -/
theorem farkas_lemma_second_formulation_iff_mem_positive_map
    (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    (∀ x : Fin n → ℝ, A *ᵥ x ≤ (0 : Fin m → ℝ) → dotProduct c x ≤ 0) ↔
      c ∈ (PointedCone.positive ℝ (Fin m → ℝ)).map Aᵀ.mulVecLin := by
  have h_certificate :
      (∃ y ∈ Set.Ici (0 : Fin m → ℝ), Aᵀ *ᵥ y = c) ↔
        c ∈ (PointedCone.positive ℝ (Fin m → ℝ)).map Aᵀ.mulVecLin := by
    rw [PointedCone.mem_map]
    constructor
    · rintro ⟨y, hy, hyc⟩
      refine ⟨y, ?_, ?_⟩
      · simpa using hy
      have hyc' : y ᵥ* A = c := (Matrix.mulVec_transpose A y).symm.trans hyc
      simpa [Matrix.mulVecLin_apply] using hyc'
    · rintro ⟨y, hy, hyc⟩
      refine ⟨y, ?_, ?_⟩
      · simpa using hy
      have hyc' : y ᵥ* A = c := by
        simpa [Matrix.mulVecLin_apply] using hyc
      exact (Matrix.mulVec_transpose A y).trans hyc'
  exact (farkas_lemma_second_formulation c A).trans h_certificate

end
