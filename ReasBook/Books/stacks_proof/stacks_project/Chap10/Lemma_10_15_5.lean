import StacksProject_2024.Chap15.Lemma_15_8_1
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Matrix

section

variable {R : Type u} [CommRing R]
variable {m n : ℕ}

/-- Helper for Lemma 10.15.5: the adjugate of a chosen `m × m` row submatrix yields a left witness
for its determinant. -/
lemma adjugate_projection_mul_eq_row_minor_smul_one
    (A : Matrix (Fin n) (Fin m) R) (e : Fin m ↪ Fin n) :
    ((A.submatrix e id).adjugate * ((1 : Matrix (Fin n) (Fin n) R).submatrix e id)) * A =
      (A.submatrix e id).det • (1 : Matrix (Fin m) (Fin m) R) := by
  -- First project `A` to the chosen rows, then use the adjugate identity on that square matrix.
  rw [Matrix.mul_assoc]
  have hproj :
      ((1 : Matrix (Fin n) (Fin n) R).submatrix e id) * A = A.submatrix e id := by
    simpa using Matrix.one_submatrix_mul e (Equiv.refl (Fin n)) A
  rw [hproj]
  simpa using Matrix.adjugate_mul (A.submatrix e id)

/-- Helper for Lemma 10.15.5: every maximal minor of `A` gives an explicit matrix `B` with
`B * A = det(minor) • 1`. -/
lemma exists_mul_eq_smul_one_of_maximal_minor
    (A : Matrix (Fin n) (Fin m) R) (e₁ : Fin m ↪ Fin n) (e₂ : Fin m ↪ Fin m) :
    ∃ B : Matrix (Fin m) (Fin n) R, B * A = (A.submatrix e₁ e₂).det • 1 := by
  let σ : Fin m ≃ Fin m :=
    Equiv.ofBijective e₂ ((Finite.injective_iff_bijective (f := e₂)).mp e₂.injective)
  let B : Matrix (Fin m) (Fin n) R :=
    (↑(Equiv.Perm.sign σ) : R) •
      ((A.submatrix e₁ id).adjugate * ((1 : Matrix (Fin n) (Fin n) R).submatrix e₁ id))
  refine ⟨B, ?_⟩
  have hdet :
      (A.submatrix e₁ e₂).det =
        (↑(Equiv.Perm.sign σ) : R) * (A.submatrix e₁ id).det := by
    -- Permuting the columns of the square submatrix changes the determinant by the sign.
    simpa [σ, Matrix.submatrix_submatrix, Function.comp_id]
      using Matrix.det_permute' σ (A.submatrix e₁ id)
  -- Scale the standard adjugate witness by the same sign appearing in the determinant comparison.
  calc
    B * A =
        (↑(Equiv.Perm.sign σ) : R) •
          (((A.submatrix e₁ id).adjugate * ((1 : Matrix (Fin n) (Fin n) R).submatrix e₁ id)) * A) := by
      simp [B, Matrix.smul_mul]
    _ =
        (↑(Equiv.Perm.sign σ) : R) •
          ((A.submatrix e₁ id).det • (1 : Matrix (Fin m) (Fin m) R)) := by
      rw [adjugate_projection_mul_eq_row_minor_smul_one]
    _ = ((↑(Equiv.Perm.sign σ) : R) * (A.submatrix e₁ id).det) • (1 : Matrix (Fin m) (Fin m) R) := by
      rw [smul_smul]
    _ = (A.submatrix e₁ e₂).det • (1 : Matrix (Fin m) (Fin m) R) := by
      rw [hdet]

/-- Helper for Lemma 10.15.5: when `m ≤ n`, extend `B` by zero rows so that
`minorIdeal_mul_left_le` applies to `det (B * A)`. -/
lemma det_mul_mem_minorIdeal_of_le
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) (h : m ≤ n) :
    Matrix.det (B * A) ∈ minorIdeal m A := by
  let C : Matrix (Fin n) (Fin n) R :=
    fun i j ↦ if hi : (i : ℕ) < m then B ⟨i, hi⟩ j else 0
  have hsub : C.submatrix (Fin.castLEEmb h) (Equiv.refl (Fin n)) = B := by
    -- On the first `m` rows, the zero-row extension is exactly `B`.
    ext i j
    simp [C]
  have htop : (C * A).submatrix (Fin.castLEEmb h) (Function.Embedding.refl (Fin m)) = B * A := by
    -- Restricting the product back to those rows recovers the square matrix `B * A`.
    rw [Matrix.submatrix_mul C A (Fin.castLEEmb h) (Equiv.refl (Fin n))
      (Function.Embedding.refl (Fin m))
      (Equiv.refl (Fin n)).bijective]
    rw [hsub]
    have hA : A.submatrix (Equiv.refl (Fin n)) (Function.Embedding.refl (Fin m)) = A := by
      ext i j
      rfl
    rw [hA]
  have hdet : Matrix.det (B * A) ∈ minorIdeal m (C * A) := by
    -- This determinant is one of the `m × m` minors of the extended product.
    have hminor :=
      Matrix.det_submatrix_mem_minorIdeal m (C * A) (Fin.castLEEmb h) (Function.Embedding.refl _)
    rw [htop] at hminor
    exact hminor
  -- Left multiplication by the square extension `C` cannot enlarge the `m`-minor ideal.
  exact Matrix.minorIdeal_mul_left_le m C A hdet

/-- Lemma 10.15.5: if `f ∈ I_(m)(A)` for an `n × m` matrix `A`, then some `m × n` matrix `B`
satisfies `B * A = f • 1`. When `m ≤ n`, these are exactly the maximal minors; when `m > n`,
`I_(m)(A) = ⊥`, so no separate inequality hypothesis is needed. -/
-- Proof sketch: write `f` as a finite `R`-linear combination of `m × m` minors. For each chosen
-- row submatrix use its adjugate matrix, extend it back to an `m × n` matrix, and sum these
-- contributions to obtain a matrix `B` whose product with `A` is `f • 1`.
@[stacks 07DQ]
theorem exists_mul_eq_smul_one_of_mem_minorIdeal
    (A : Matrix (Fin n) (Fin m) R) {f : R} (hf : f ∈ minorIdeal m A) :
    ∃ B : Matrix (Fin m) (Fin n) R, B * A = f • 1 := by
  let P : R → Prop := fun g ↦ ∃ B : Matrix (Fin m) (Fin n) R, B * A = g • 1
  have hgen :
      ∀ x ∈ Set.range (fun p : (Fin m ↪ Fin n) × (Fin m ↪ Fin m) ↦ (A.submatrix p.1 p.2).det),
        P x := by
    intro x hx
    rcases hx with ⟨⟨e₁, e₂⟩, rfl⟩
    -- Each generator is handled by the explicit adjugate construction above.
    exact exists_mul_eq_smul_one_of_maximal_minor A e₁ e₂
  have hzero : P 0 := by
    -- The zero scalar is realized by the zero matrix.
    refine ⟨0, ?_⟩
    simp
  have hadd : ∀ x y, P x → P y → P (x + y) := by
    intro x y hx hy
    rcases hx with ⟨Bx, hBx⟩
    rcases hy with ⟨By, hBy⟩
    refine ⟨Bx + By, ?_⟩
    -- Adding witnesses adds the resulting scalar matrices.
    rw [Matrix.add_mul, hBx, hBy, add_smul]
  have hsmul : ∀ a x, P x → P (a * x) := by
    intro a x hx
    rcases hx with ⟨B, hB⟩
    refine ⟨a • B, ?_⟩
    -- Scaling the witness scales the scalar on the right-hand side.
    rw [Matrix.smul_mul, hB, smul_smul]
  unfold Matrix.minorIdeal at hf
  -- The admissible scalars form a submodule containing the generating set of `minorIdeal m A`.
  exact Submodule.span_induction (p := fun x _ ↦ P x) hgen hzero
    (fun x y _ _ hx hy ↦ hadd x y hx hy) (fun a x _ hx ↦ hsmul a x hx) hf

/-- Matrix-level form of Lemma 10.15.5: a left inverse up to the scalar `f` forces `f ^ m` to lie
in the maximal-minor ideal of `A`. In the Stacks Project wording this is membership in the ideal
generated by the `m × m` row minors, which agrees with `I_(m)(A)`. This is the atomic
determinantal statement from which the existential formulation follows immediately. -/
-- Route correction: `minorIdeal_mul_left_le` only applies directly after extending a rectangular
-- left factor to a square one. When `n < m`, the clean route is instead the rectangular
-- characteristic-polynomial identity `charpoly_mul_comm_of_le`.
theorem pow_mem_minorIdeal_of_mul_eq_smul_one
    (A : Matrix (Fin n) (Fin m) R) {f : R}
    (B : Matrix (Fin m) (Fin n) R) (hBA : B * A = f • 1) :
    f ^ m ∈ minorIdeal m A := by
  by_cases hmn : m ≤ n
  · have hdet : Matrix.det (B * A) ∈ minorIdeal m A :=
      det_mul_mem_minorIdeal_of_le A B hmn
    -- For a scalar matrix, the determinant is exactly the required power `f ^ m`.
    simpa [hBA, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] using hdet
  · have hlt : n < m := Nat.lt_of_not_ge hmn
    have hchar :
        Matrix.charpoly (B * A) = Polynomial.X ^ (m - n) * Matrix.charpoly (A * B) := by
      simpa [Fintype.card_fin] using
        Matrix.charpoly_mul_comm_of_le B A (by simpa [Fintype.card_fin] using hlt.le)
    have hcoeff : (Matrix.charpoly (B * A)).coeff 0 = 0 := by
      -- A positive power of `X` kills the constant coefficient.
      rw [hchar, Polynomial.coeff_X_pow_mul']
      simp [Nat.not_le_of_gt (Nat.sub_pos_of_lt hlt)]
    have hdetZero : Matrix.det (B * A) = 0 := by
      -- The determinant is the constant term of the characteristic polynomial up to sign.
      rw [Matrix.det_eq_sign_charpoly_coeff, hcoeff]
      simp
    have hpowZero : f ^ m = 0 := by
      -- Rewrite the determinant of `B * A` using the scalar-matrix hypothesis.
      simpa [hBA, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] using hdetZero
    simpa [hpowZero] using (show 0 ∈ minorIdeal m A from Ideal.zero_mem _)

/-- Existential companion to `pow_mem_minorIdeal_of_mul_eq_smul_one`. -/
theorem pow_mem_minorIdeal_of_exists_mul_eq_smul_one
    (A : Matrix (Fin n) (Fin m) R) {f : R}
    (hBA : ∃ B : Matrix (Fin m) (Fin n) R, B * A = f • 1) :
    f ^ m ∈ minorIdeal m A := by
  rcases hBA with ⟨B, hB⟩
  -- Unpack the witness and apply the matrix-level statement.
  exact pow_mem_minorIdeal_of_mul_eq_smul_one A B hB

end
