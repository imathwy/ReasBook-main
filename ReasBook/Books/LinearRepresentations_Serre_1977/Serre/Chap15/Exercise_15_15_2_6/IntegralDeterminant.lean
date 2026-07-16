import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_6.Foundations

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped Pointwise TensorProduct

universe u v w

variable {E : Type v} [AddCommGroup E] [Module ℤ E]

section IntegralLatticeAmbient

variable [Module.Free ℤ E] [Module.Finite ℤ E]

attribute [local instance] Classical.decEq

/-- Helper for Exercise 15-15.2-6: if the Gram determinant is `1` in one integral basis, then the
same determinant condition holds in every integral basis. This is the current owner-level
replacement for self-duality of the integral lattice. -/
theorem isSelfDualIntegralLattice_of_det_eq_one_basis
    (B : BilinForm ℤ E)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ E)
    (hdet : Matrix.det (B.toMatrix b) = 1) :
    B.IsSelfDualIntegralLattice := by
  intro n c
  classical
  -- Reindex the target basis to the source index type so that the basis-change formula applies.
  have hcard : Fintype.card ι = Fintype.card (Fin n) := by
    rw [← Module.finrank_eq_card_basis b, ← Module.finrank_eq_card_basis c]
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin n) := Fintype.card_eq.mp hcard
  let c' : Module.Basis ι ℤ E := c.reindex e.symm
  have hchange :
      (b.toMatrix c').transpose * B.toMatrix b * b.toMatrix c' = B.toMatrix c' := by
    simpa [c'] using LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b c' B
  have hu : IsUnit (Matrix.det (b.toMatrix c')) := by
    simpa [Module.Basis.det_apply, c'] using Module.Basis.isUnit_det b c'
  have hdet' : Matrix.det (B.toMatrix c') = 1 := by
    have hdet_det := congrArg Matrix.det hchange
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet] at hdet_det
    -- Over `ℤ`, the determinant of a basis-change matrix is a unit, hence its square is `1`.
    calc
      Matrix.det (B.toMatrix c') =
          Matrix.det (b.toMatrix c') * Matrix.det (b.toMatrix c') := by
            symm
            simpa [mul_assoc] using hdet_det
      _ = 1 := Int.isUnit_mul_self hu
  have hreindex :
      B.toMatrix c' = Matrix.reindex e.symm e.symm (B.toMatrix c) := by
    ext i j
    simp [c', LinearMap.BilinForm.toMatrix_apply]
  -- Reindexing does not change the determinant, so the original `Fin n` basis also has Gram
  -- determinant `1`.
  calc
    Matrix.det (B.toMatrix c) = Matrix.det (Matrix.reindex e.symm e.symm (B.toMatrix c)) := by
      symm
      exact Matrix.det_reindex_self e.symm (B.toMatrix c)
    _ = Matrix.det (B.toMatrix c') := by rw [← hreindex]
    _ = 1 := hdet'

/-- Helper for Exercise 15-15.2-6: once the self-dual integral-lattice owner is available, the
Gram determinant in any finite basis is exactly `1`. -/
theorem thompson_bilinForm_det_eq_one
    (B : BilinForm ℤ E) (h_symm : B.IsSymm) (h_pos : B.toQuadraticMap.PosDef)
    (hselfDual : B.IsSelfDualIntegralLattice)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E) :
    Matrix.det (B.toMatrix b) = 1 := by
  -- The repaired self-duality owner already records the determinant-one conclusion in every
  -- integral basis, so we just read it back at the chosen basis.
  let _ := h_symm
  let _ := h_pos
  exact hselfDual n b

end IntegralLatticeAmbient
