import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.BilinearForm.Properties

open LinearMap (BilinForm)
open Module

universe u

-- Mathlib recall: `QuadraticForm.equivalent_one_neg_one_weighted_sum_squared` gives the real
-- quadratic-form normal form; the source-facing statement here records the corresponding
-- basis-level bilinear formulation.

/-- Lemma 21.2.1: a symmetric nondegenerate bilinear form over `ℝ` admits a basis in which the
diagonal entries are `1` or `-1` and the off-diagonal entries vanish. -/
theorem exists_basis_isOrthoᵢ_eq_neg_one_or_one
    {M : Type u} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    (B : BilinForm ℝ M) (hBsymm : B.IsSymm) (hBnondeg : B.Nondegenerate) :
    ∃ b : Basis (Fin (Module.finrank ℝ M)) ℝ M,
      B.IsOrthoᵢ b ∧ ∀ i, B (b i) (b i) = -1 ∨ B (b i) (b i) = 1 := by
  let Q : QuadraticForm ℝ M := B.toQuadraticMap
  have hBsymm' : LinearMap.IsSymm B := (LinearMap.BilinForm.isSymm_iff).mp hBsymm
  have hQsep : (QuadraticMap.associated Q).SeparatingLeft := by
    simpa [Q, QuadraticMap.associated_left_inverse ℝ hBsymm.eq] using
      hBnondeg.1
  obtain ⟨w, hw, ⟨e⟩⟩ := Q.equivalent_one_neg_one_weighted_sum_squared hQsep
  let b : Basis (Fin (Module.finrank ℝ M)) ℝ M :=
    (Pi.basisFun ℝ (Fin (Module.finrank ℝ M))).map e.symm
  have hstd_diag (i : Fin (Module.finrank ℝ M)) :
      ∑ x, w x *
        (Pi.basisFun ℝ (Fin (Module.finrank ℝ M)) i x *
          Pi.basisFun ℝ (Fin (Module.finrank ℝ M)) i x) = w i := by
    rw [Finset.sum_eq_single_of_mem i (by simp)]
    · simp [Pi.basisFun_apply]
    · intro j _ hj
      simp [Pi.basisFun_apply, hj]
  refine ⟨b, ?_, ?_⟩
  · rw [LinearMap.isOrthoᵢ_def]
    intro i j hij
    rw [← LinearMap.isOrtho_def, ← LinearMap.BilinForm.toQuadraticMap_isOrtho hBsymm',
      QuadraticMap.isOrtho_def,
      ← e.map_app (b i + b j), ← e.map_app (b i), ← e.map_app (b j), map_add]
    have hji : j ≠ i := fun h ↦ hij h.symm
    classical
    simp [b, QuadraticMap.weightedSumSquares_apply, Pi.single_apply, hij, hji, mul_add,
      Finset.sum_add_distrib]
  · intro i
    have hdiag : B (b i) (b i) = w i := by
      change Q (b i) = w i
      rw [← e.map_app (b i)]
      simpa [Q, b, QuadraticMap.weightedSumSquares_apply, Pi.basisFun_apply] using hstd_diag i
    rcases hw i with hwi | hwi
    · exact Or.inl (hdiag.trans hwi)
    · exact Or.inr (hdiag.trans hwi)

/-- Lemma 21.2.1 in expanded form: the same basis can be chosen so that the off-diagonal matrix
entries of `B` vanish and each diagonal entry is `-1` or `1`. -/
theorem exists_basis_offDiag_eq_zero_and_diag_eq_neg_one_or_one
    {M : Type u} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    (B : BilinForm ℝ M) (hBsymm : B.IsSymm) (hBnondeg : B.Nondegenerate) :
    ∃ b : Basis (Fin (Module.finrank ℝ M)) ℝ M,
      (∀ i j, i ≠ j → B (b i) (b j) = 0) ∧
        ∀ i, B (b i) (b i) = -1 ∨ B (b i) (b i) = 1 := by
  obtain ⟨b, hbOrtho, hbDiag⟩ := exists_basis_isOrthoᵢ_eq_neg_one_or_one B hBsymm hBnondeg
  refine ⟨b, ?_, hbDiag⟩
  simpa [LinearMap.isOrthoᵢ_def] using hbOrtho
