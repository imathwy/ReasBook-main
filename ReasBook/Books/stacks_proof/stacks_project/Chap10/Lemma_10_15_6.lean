import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

variable {R : Type _} [CommRing R] {m l : ℕ}

/-- The lower block of `A * A.toRows₁.adjugate` is given entrywise by determinants of the
row-replacement matrices obtained from the top square block. In the Stacks Project formulation,
this is the determinant of the corresponding maximal minor, up to sign. -/
theorem lowerBlock_mul_adjugate_apply (A : Matrix (Fin m ⊕ Fin l) (Fin m) R)
    (i : Fin l) (j : Fin m) :
    (A.toRows₂ * A.toRows₁.adjugate) i j = (A.toRows₁.updateRow j (A.toRows₂ i)).det := by
  calc
    (A.toRows₂ * A.toRows₁.adjugate) i j = (A.toRows₂ i ᵥ* A.toRows₁.adjugate) j := by
      simp [vecMul, mul_apply, dotProduct]
    _ = (A.toRows₁ᵀ.adjugate *ᵥ A.toRows₂ i) j := by
      rw [← adjugate_transpose, ← mulVec_transpose]
    _ = (A.toRows₁ᵀ.cramer (A.toRows₂ i)) j := by
      simpa using (congr_fun (cramer_eq_adjugate_mulVec A.toRows₁ᵀ (A.toRows₂ i)).symm j)
    _ = (A.toRows₁.updateRow j (A.toRows₂ i)).det := by
      simpa using cramer_transpose_apply A.toRows₁ (A.toRows₂ i) j

/-- Lemma 10.15.6: multiplying a block matrix by the adjugate of its top square block yields a
row-partitioned matrix whose top block is `det(A₁) • 1`; the companion theorem
`lowerBlock_mul_adjugate_apply` identifies the lower block entries with the row-replacement
determinants from the textbook statement. -/
@[stacks 080R]
theorem mul_adjugate_top_block_eq_fromRows (A : Matrix (Fin m ⊕ Fin l) (Fin m) R) :
    A * A.toRows₁.adjugate =
      fromRows (A.toRows₁.det • 1)
        (A.toRows₂ * A.toRows₁.adjugate) := by
  simpa [fromRows_toRows, A.toRows₁.mul_adjugate] using
    (fromRows_mul A.toRows₁ A.toRows₂ A.toRows₁.adjugate)
