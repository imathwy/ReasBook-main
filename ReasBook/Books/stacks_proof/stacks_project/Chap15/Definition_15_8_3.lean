import Mathlib.RingTheory.Finiteness.Cardinality
import StacksProject_2024.Chap15.Lemma_15_8_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Matrix

/-
Domain-style sampling for Definition 15.8.3:
- primary domain: determinantal/Fitting ideals of modules over a commutative ring, built from
  finite free presentations;
- sampled owner-level declarations:
  `Matrix.minorIdeal`,
  `presentationFittingIdeal`,
  `fittingIdeal`,
  `fittingIdealNegOne`,
  `fittingIdeal_eq_presentationFittingIdeal`;
- best owner abstraction: `presentationFittingIdeal` is the presentation-level owner attached to a
  chosen surjective finite free presentation, while `fittingIdeal` is the source-facing intrinsic
  finite-module owner obtained by taking the infimum over all such presentations, together with the
  source convention `Fit_{-1}(M) = 0`;
- primitive data: a surjective finite free presentation `π : R^n → M` for the presentation-level
  owner;
- derived API: presentation independence, the induced intrinsic module-level Fitting ideal, and
  the owner-side predecessor helper `precedingFittingIdeal`.

Source/core/bridge triage:
- `source-facing`: `fittingIdeal`, `fittingIdealNegOne`;
- `core/canonical`: `presentationFittingIdeal`;
- `bridge/view`: `fittingIdeal_eq_presentationFittingIdeal`, `precedingFittingIdeal`. -/

section

variable (R : Type u) [CommRing R]

/-- Definition 15.8.3 also fixes the convention `Fit_{-1}(M) = 0`. -/
@[stacks 07Z9]
abbrev fittingIdealNegOne : Ideal R :=
  (⊥ : Ideal R)

@[simp] theorem fittingIdealNegOne_eq_bot :
    fittingIdealNegOne R = (⊥ : Ideal R) :=
  rfl

end

section

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The `k`th Fitting ideal attached to a finite free presentation map `R^n → M`, using the
kernel-vector matrix and the chapter's determinantal-ideal owner `Matrix.minorIdeal`. Surjectivity
is imposed only when relating this presentation-level construction to the intrinsic Fitting ideal
of `M`. -/
def presentationFittingIdeal (k : ℕ) {n : ℕ} (π : (Fin n → R) →ₗ[R] M) : Ideal R :=
  I_((n - k))((fun i x ↦ x.1 i : Matrix (Fin n) (LinearMap.ker π) R))

/-- Helper for Definition 15.8.3: the `0`th minor ideal of any matrix is the unit ideal. -/
private theorem matrix_minorIdeal_zero_eq_top {ι : Type*} {κ : Type*} (A : Matrix ι κ R) :
    Matrix.minorIdeal 0 A = ⊤ := by
  classical
  -- The empty minor contributes determinant `1`, so the span already contains a unit.
  rw [Matrix.minorIdeal]
  refine Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
  let e₁ : Fin 0 ↪ ι := ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
  let e₂ : Fin 0 ↪ κ := ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
  have hmem :
      (1 : R) ∈
        Set.range
          (fun p : (Fin 0 ↪ ι) × (Fin 0 ↪ κ) ↦
            Matrix.det (Matrix.submatrix A p.1 p.2)) := by
    refine ⟨⟨e₁, e₂⟩, ?_⟩
    simp [e₁, e₂, Matrix.det_fin_zero]
  exact Ideal.subset_span hmem

/-- Helper for Definition 15.8.3: once `k` reaches the source rank, the presentation Fitting
ideal is the unit ideal. -/
theorem presentationFittingIdeal_eq_top_of_le {n k : ℕ} (hk : n ≤ k)
    (π : (Fin n → R) →ₗ[R] M) :
    presentationFittingIdeal R M k π = ⊤ := by
  -- For `k ≥ n`, the owner asks for `0 × 0` minors of the kernel-vector matrix.
  rw [presentationFittingIdeal, Nat.sub_eq_zero_of_le hk]
  simpa using
    matrix_minorIdeal_zero_eq_top (R := R)
      (A := (fun i x ↦ x.1 i : Matrix (Fin n) (LinearMap.ker π) R))

/-- Helper for Definition 15.8.3: a surjective coordinate presentation lifts any other coordinate
presentation through it. -/
private theorem exists_presentation_lift {n n' : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (π' : (Fin n' → R) →ₗ[R] M)
    (hπ' : Function.Surjective π') :
    ∃ σ : (Fin n → R) →ₗ[R] (Fin n' → R), π'.comp σ = π := by
  classical
  -- Choose preimages of the standard basis vectors of the source free module under the surjection
  -- `π'`, then extend linearly from that basis.
  choose v hv using fun i : Fin n ↦ hπ' (π (Pi.basisFun R (Fin n) i))
  let σ : (Fin n → R) →ₗ[R] (Fin n' → R) := (Pi.basisFun R (Fin n)).constr R v
  refine ⟨σ, ?_⟩
  -- Two linear maps out of `R^n` agree once they agree on the standard basis.
  refine (Pi.basisFun R (Fin n)).ext fun i ↦ ?_
  simpa [σ, LinearMap.comp_apply] using hv i

/-- Helper for Definition 15.8.3: a lift between two presentations restricts to their kernels. -/
private theorem presentation_lift_maps_ker {n n' : ℕ}
    {π : (Fin n → R) →ₗ[R] M} {π' : (Fin n' → R) →ₗ[R] M}
    {σ : (Fin n → R) →ₗ[R] (Fin n' → R)} (hσ : π'.comp σ = π) :
    ∀ x : LinearMap.ker π, σ x.1 ∈ LinearMap.ker π' := by
  intro x
  -- Evaluating the comparison identity on a kernel vector shows that its image still maps to
  -- zero.
  have hx : π x = 0 := x.2
  have hσx : π' (σ x) = π x := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun f : (Fin n → R) →ₗ[R] M ↦ f x) hσ
  change π' (σ x) = 0
  exact hσx.trans hx

/-- Helper for Definition 15.8.3: the chosen lifts induce the stabilized ambient source
automorphism used in the textbook Schanuel comparison. -/
private def presentation_stabilized_source_linearEquiv_of_lifts {n n' : ℕ}
    (σ : (Fin n → R) →ₗ[R] (Fin n' → R))
    (τ : (Fin n' → R) →ₗ[R] (Fin n → R)) :
    ((Fin n → R) × (Fin n' → R)) ≃ₗ[R] ((Fin n → R) × (Fin n' → R)) where
  toFun x := (x.1 + τ x.2, σ (x.1 + τ x.2) - x.2)
  invFun x := (x.1 - τ (σ x.1 - x.2), σ x.1 - x.2)
  left_inv x := by
    -- Solve the forward formulas for the original coordinates and simplify.
    ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  right_inv x := by
    -- The same explicit coordinate calculation shows the inverse formulas undo the stabilization.
    ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_add' x y := by
    -- Both coordinates are linear combinations of `σ`, `τ`, and the product coordinates.
    ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' a x := by
    -- Scalar multiplication distributes through the same coordinate formulas.
    ext <;> simp [sub_eq_add_neg, add_comm]

/-- Helper for Definition 15.8.3: the forward stabilized formula lands in the second kernel. -/
private theorem presentation_stabilized_second_mem_ker {n n' : ℕ}
    {π : (Fin n → R) →ₗ[R] M} {π' : (Fin n' → R) →ₗ[R] M}
    {σ : (Fin n → R) →ₗ[R] (Fin n' → R)}
    {τ : (Fin n' → R) →ₗ[R] (Fin n → R)}
    (hσ : π'.comp σ = π) (hτ : π.comp τ = π')
    (x : LinearMap.ker π) (y : Fin n' → R) :
    σ (x.1 + τ y) - y ∈ LinearMap.ker π' := by
  -- Evaluate the presentation identities on the stabilized vector and cancel the added summand.
  change π' (σ (x.1 + τ y) - y) = 0
  have hσxy : π' (σ (x.1 + τ y)) = π (x.1 + τ y) := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun f : (Fin n → R) →ₗ[R] M ↦ f (x.1 + τ y)) hσ
  have hτy : π (τ y) = π' y := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun f : (Fin n' → R) →ₗ[R] M ↦ f y) hτ
  calc
    π' (σ (x.1 + τ y) - y) = π' (σ (x.1 + τ y)) - π' y := by
      simp
    _ = π (x.1 + τ y) - π' y := by
      rw [hσxy]
    _ = (π x.1 + π (τ y)) - π' y := by
      simp
    _ = (0 + π' y) - π' y := by
      rw [x.2, hτy]
    _ = 0 := by
      simp

/-- Helper for Definition 15.8.3: the inverse stabilized formula lands back in the first kernel. -/
private theorem presentation_stabilized_first_mem_ker {n n' : ℕ}
    {π : (Fin n → R) →ₗ[R] M} {π' : (Fin n' → R) →ₗ[R] M}
    {σ : (Fin n → R) →ₗ[R] (Fin n' → R)}
    {τ : (Fin n' → R) →ₗ[R] (Fin n → R)}
    (hσ : π'.comp σ = π) (hτ : π.comp τ = π')
    (x : Fin n → R) (z : LinearMap.ker π') :
    x - τ (σ x - z.1) ∈ LinearMap.ker π := by
  -- Rewrite through the two lift identities and use that `z` already maps to zero under `π'`.
  change π (x - τ (σ x - z.1)) = 0
  have hσx : π' (σ x) = π x := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun f : (Fin n → R) →ₗ[R] M ↦ f x) hσ
  have hτz : π (τ (σ x - z.1)) = π' (σ x - z.1) := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun f : (Fin n' → R) →ₗ[R] M ↦ f (σ x - z.1)) hτ
  calc
    π (x - τ (σ x - z.1)) = π x - π (τ (σ x - z.1)) := by
      simp
    _ = π x - π' (σ x - z.1) := by
      rw [hτz]
    _ = π x - (π' (σ x) - π' z.1) := by
      simp
    _ = π x - (π x - 0) := by
      rw [hσx, z.2]
    _ = 0 := by
      simp

/-- Helper for Definition 15.8.3: the stabilized automorphism restricts to the product of the two
kernels appearing in the source proof. -/
private def presentation_kernel_stabilization_equiv_of_surjective {n n' : ℕ}
    {π : (Fin n → R) →ₗ[R] M} {π' : (Fin n' → R) →ₗ[R] M}
    (σ : (Fin n → R) →ₗ[R] (Fin n' → R))
    (τ : (Fin n' → R) →ₗ[R] (Fin n → R))
    (hσ : π'.comp σ = π) (hτ : π.comp τ = π') :
    (LinearMap.ker π × (Fin n' → R)) ≃ₗ[R] ((Fin n → R) × LinearMap.ker π') :=
  sorry

/-- Helper for Definition 15.8.3: the left kernel product includes into the stabilized ambient
free module by forgetting the kernel proof on the first factor. -/
private def presentation_kernel_left_inclusion {n n' : ℕ}
    (π : (Fin n → R) →ₗ[R] M) :
    (LinearMap.ker π × (Fin n' → R)) →ₗ[R] ((Fin n → R) × (Fin n' → R)) where
  toFun x := (x.1.1, x.2)
  map_add' x y := by
    rfl
  map_smul' a x := by
    rfl

/-- Helper for Definition 15.8.3: the right kernel product includes into the stabilized ambient
free module by forgetting the kernel proof on the second factor. -/
private def presentation_kernel_right_inclusion {n n' : ℕ}
    (π' : (Fin n' → R) →ₗ[R] M) :
    ((Fin n → R) × LinearMap.ker π') →ₗ[R] ((Fin n → R) × (Fin n' → R)) where
  toFun x := (x.1, x.2.1)
  map_add' x y := by
    rfl
  map_smul' a x := by
    rfl

/-- Helper for Definition 15.8.3: the stabilized kernel equivalence is literally the restriction
of the ambient stabilized automorphism to the two kernel-product inclusions. -/
private theorem presentation_kernel_stabilization_ambient_compat {n n' : ℕ}
    {π : (Fin n → R) →ₗ[R] M} {π' : (Fin n' → R) →ₗ[R] M}
    (σ : (Fin n → R) →ₗ[R] (Fin n' → R))
    (τ : (Fin n' → R) →ₗ[R] (Fin n → R))
    (hσ : π'.comp σ = π) (hτ : π.comp τ = π') :
    (presentation_stabilized_source_linearEquiv_of_lifts (R := R) σ τ).toLinearMap.comp
        (presentation_kernel_left_inclusion (R := R) (M := M) (n' := n') π) =
      (presentation_kernel_right_inclusion (R := R) (M := M) (n := n) π').comp
        (presentation_kernel_stabilization_equiv_of_surjective
          (R := R) (M := M) σ τ hσ hτ).toLinearMap := by
  sorry

/-- Helper for Definition 15.8.3: the full-size minor ideal of the identity matrix is the unit
ideal. -/
private theorem matrix_minorIdeal_one_eq_top (n : ℕ) :
    Matrix.minorIdeal n (1 : Matrix (Fin n) (Fin n) R) = ⊤ := by
  -- The full identity minor has determinant `1`, so the ideal contains a unit.
  refine Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
  simpa using
    (Matrix.det_submatrix_mem_minorIdeal n (1 : Matrix (Fin n) (Fin n) R)
      (Function.Embedding.refl _) (Function.Embedding.refl _))

/-- Helper for Definition 15.8.3: the free summand added in the stabilization argument contributes
the coordinate matrix `Bfree i y = y i`. -/
private def freeCoordinateMatrix (n : ℕ) : Matrix (Fin n) (Fin n → R) R :=
  fun i y ↦ y i

/-- Helper for Definition 15.8.3: after choosing `q` standard basis columns, the corresponding
submatrix of the free-coordinate block is the identity. -/
private theorem freeCoordinateMatrix_submatrix_eq_one_of_le {n q : ℕ} [Nontrivial R] (hq : q ≤ n) :
    ∃ e₁ : Fin q ↪ Fin n, ∃ e₂ : Fin q ↪ (Fin n → R),
      Matrix.submatrix (freeCoordinateMatrix (R := R) n) e₁ e₂ = 1 := by
  classical
  let e₁ : Fin q ↪ Fin n := Fin.castLEEmb hq
  let e₂ : Fin q ↪ (Fin n → R) :=
    ⟨fun j ↦ Pi.basisFun R (Fin n) (e₁ j), by
    intro i j hij
    by_cases hji : j = i
    · simpa [hji]
    · exfalso
      have hEval := congrArg (fun y : Fin n → R ↦ y (e₁ i)) hij
      have hne : e₁ j ≠ e₁ i := by
        intro h
        exact hji (e₁.injective h)
      simp [Pi.basisFun, hne] at hEval⟩
  refine ⟨e₁, e₂, ?_⟩
  -- The chosen basis columns evaluate to the Kronecker delta on the selected rows.
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.submatrix_apply, freeCoordinateMatrix, e₂]
  · have hne : e₁ j ≠ e₁ i := by
      intro h
      exact hij (e₁.injective h.symm)
    simp [Matrix.submatrix_apply, freeCoordinateMatrix, e₂, hij]

/-- Helper for Definition 15.8.3: the free-coordinate block contributes a unit minor in every
admissible size. -/
private theorem free_coordinate_minorIdeal_eq_top_of_le {n q : ℕ} (hq : q ≤ n) :
    Matrix.minorIdeal q (freeCoordinateMatrix (R := R) n) = ⊤ := by
  classical
  by_cases hR : Nontrivial R
  · letI := hR
    obtain ⟨e₁, e₂, hsub⟩ :=
      freeCoordinateMatrix_submatrix_eq_one_of_le (R := R) hq
    -- The selected identity minor has determinant `1`, so the ideal already contains a unit.
    refine Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
    have hmem :
        (Matrix.submatrix (freeCoordinateMatrix (R := R) n) e₁ e₂).det ∈
          Matrix.minorIdeal q (freeCoordinateMatrix (R := R) n) :=
      Matrix.det_submatrix_mem_minorIdeal q (freeCoordinateMatrix (R := R) n) e₁ e₂
    simpa [hsub] using hmem
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact Subsingleton.elim _ _

/-- Helper for Definition 15.8.3: if the requested minor size exceeds the free rank, then there
are no row embeddings at all, so the free-coordinate block has zero minor ideal. -/
private theorem free_coordinate_minorIdeal_eq_bot_of_lt {n q : ℕ} (hq : n < q) :
    Matrix.minorIdeal q (freeCoordinateMatrix (R := R) n) = ⊥ := by
  -- Any purported `q × q` minor would require an impossible embedding `Fin q ↪ Fin n`.
  rw [Matrix.minorIdeal, Ideal.span_eq_bot]
  intro x hx
  rcases hx with ⟨⟨e₁, _⟩, rfl⟩
  exfalso
  have hle : q ≤ n := by
    simpa using (Fintype.card_le_of_embedding e₁)
  exact Nat.not_le_of_gt hq hle

/-- Helper for Definition 15.8.3: restricting a matrix to selected rows and columns can only
shrink the corresponding determinantal ideal. -/
private theorem minorIdeal_submatrix_le {ι : Type*} {ι' : Type*} {κ : Type*} {κ' : Type*}
    (r : ℕ) (A : Matrix ι κ R) (er : ι' ↪ ι) (ec : κ' ↪ κ) :
    Matrix.minorIdeal r (A.submatrix er ec) ≤ Matrix.minorIdeal r A := by
  -- A selected minor of the restricted matrix is the corresponding selected minor of `A`.
  refine Ideal.span_le.2 ?_
  rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
  simpa [Matrix.submatrix_submatrix, Function.comp_def] using
    Matrix.det_submatrix_mem_minorIdeal r A (e₁.trans er) (e₂.trans ec)

/-- Helper for Definition 15.8.3: transposing a matrix does not change the ideal generated by its
`r × r` minors. -/
private theorem minorIdeal_transpose_eq {ι : Type*} {κ : Type*} (r : ℕ) (A : Matrix ι κ R) :
    Matrix.minorIdeal r Aᵀ = Matrix.minorIdeal r A := by
  refine le_antisymm ?_ ?_
  · -- Every selected minor of `Aᵀ` is the transpose of a selected minor of `A`.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    change (Aᵀ.submatrix e₁ e₂).det ∈ Matrix.minorIdeal r A
    have hdet : (Aᵀ.submatrix e₁ e₂).det = (A.submatrix e₂ e₁).det := by
      calc
        (Aᵀ.submatrix e₁ e₂).det = ((A.submatrix e₂ e₁)ᵀ).det := by
          rw [Matrix.transpose_submatrix]
        _ = (A.submatrix e₂ e₁).det := by
          rw [Matrix.det_transpose]
    rw [hdet]
    exact Matrix.det_submatrix_mem_minorIdeal r A e₂ e₁
  · -- Apply the same argument to `Aᵀ` and rewrite back.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    change (A.submatrix e₁ e₂).det ∈ Matrix.minorIdeal r Aᵀ
    have hdet : (A.submatrix e₁ e₂).det = (Aᵀ.submatrix e₂ e₁).det := by
      calc
        (A.submatrix e₁ e₂).det = ((A.submatrix e₁ e₂)ᵀ).det := by
          rw [Matrix.det_transpose]
        _ = (Aᵀ.submatrix e₂ e₁).det := by
          rw [Matrix.transpose_submatrix]
    rw [hdet]
    exact Matrix.det_submatrix_mem_minorIdeal r Aᵀ e₂ e₁

/-- Helper for Definition 15.8.3: allowing repeated chosen columns still produces an element of
the same determinantal ideal. -/
private theorem det_submatrix_mem_minorIdeal_of_colMap {ι : Type*} {κ : Type*}
    (r : ℕ) (A : Matrix ι κ R) (e₁ : Fin r ↪ ι) (f : Fin r → κ) :
    (A.submatrix e₁ f).det ∈ Matrix.minorIdeal r A := by
  -- Transpose the repeated-column statement into the imported repeated-row statement.
  have hmem :
      (Aᵀ.submatrix f e₁).det ∈ Matrix.minorIdeal r Aᵀ :=
    Matrix.det_submatrix_mem_minorIdeal_of_rowMap r Aᵀ f e₁
  have hdet : (Aᵀ.submatrix f e₁).det = (A.submatrix e₁ f).det := by
    calc
      (Aᵀ.submatrix f e₁).det = ((A.submatrix e₁ f)ᵀ).det := by
        rw [Matrix.transpose_submatrix]
      _ = (A.submatrix e₁ f).det := by
        rw [Matrix.det_transpose]
  rw [minorIdeal_transpose_eq (R := R) r A] at hmem
  rwa [hdet] at hmem

/-- Helper for Definition 15.8.3: right-multiplying a chosen row-restricted matrix only forms an
`R`-linear combination of `r × r` minors of the ambient matrix. -/
private theorem det_submatrix_mul_right_mem_minorIdeal_of_colMap
    {ι : Type*} {κ : Type*} {α : Type*} [Fintype α]
    (r : ℕ) (A : Matrix ι κ R) (e₁ : Fin r ↪ ι) (g : α → κ)
    (T : Matrix α (Fin r) R) :
    (((A.submatrix e₁ g) * T).det) ∈ Matrix.minorIdeal r A := by
  classical
  let M : Matrix (Fin r) α R := A.submatrix e₁ g
  rw [show (((A.submatrix e₁ g) * T).det) = (M * T).det by rfl]
  rw [show (M * T).det =
      ∑ p : Fin r → α, ∑ σ : Equiv.Perm (Fin r),
        ↑(Equiv.Perm.sign σ) * ∏ i, M (σ i) (p i) * T (p i) i by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
        Fintype.piFinset_univ]
      rw [Finset.sum_comm]]
  refine (Matrix.minorIdeal r A).sum_mem fun p _ ↦ ?_
  have hp_det :
      ∑ σ : Equiv.Perm (Fin r), ↑(Equiv.Perm.sign σ) * ∏ i, M (σ i) (p i) =
        (M.submatrix id p).det := by
    symm
    exact Matrix.det_apply' (M.submatrix id p)
  have hp_factor :
      (∑ σ : Equiv.Perm (Fin r), ↑(Equiv.Perm.sign σ) * ∏ i, M (σ i) (p i) * T (p i) i) =
        (∏ i, T (p i) i) * (M.submatrix id p).det := by
    -- Pull the `T`-coefficient out of the permutation sum and keep the determinant core.
    calc
      (∑ σ : Equiv.Perm (Fin r), ↑(Equiv.Perm.sign σ) * ∏ i, M (σ i) (p i) * T (p i) i) =
          ∑ σ : Equiv.Perm (Fin r),
            (∏ i, T (p i) i) * (↑(Equiv.Perm.sign σ) * ∏ i, M (σ i) (p i)) := by
            refine Finset.sum_congr rfl fun σ _ ↦ ?_
            simp [Finset.prod_mul_distrib, mul_assoc, mul_comm]
      _ = (∏ i, T (p i) i) * ∑ σ : Equiv.Perm (Fin r),
            ↑(Equiv.Perm.sign σ) * ∏ i, M (σ i) (p i) := by
            rw [Finset.mul_sum]
      _ = (∏ i, T (p i) i) * (M.submatrix id p).det := by
            rw [hp_det]
  rw [hp_factor]
  have hminor : (M.submatrix id p).det ∈ Matrix.minorIdeal r A := by
    -- The selected columns of `M` are selected columns of the ambient matrix `A`.
    simpa [M, Matrix.submatrix_submatrix, Function.comp_def] using
      det_submatrix_mem_minorIdeal_of_colMap (R := R) r A e₁ (g ∘ p)
  exact Ideal.mul_mem_left _ _ hminor

/-- Helper for Definition 15.8.3: a fixed product-column submatrix factors through the matching
selected `fromBlocks` submatrix and a sparse selector matrix. -/
private theorem prod_columns_submatrix_eq_fromBlocks_submatrix_mul_selector
    {ι₁ : Type*} {ι₂ : Type*} {κ₁ : Type*} {κ₂ : Type*}
    (r : ℕ) (A : Matrix ι₁ κ₁ R) (B : Matrix ι₂ κ₂ R)
    (e₁ : Fin r ↪ (ι₁ ⊕ ι₂)) (f : Fin r → κ₁ × κ₂) :
    let C : Matrix (ι₁ ⊕ ι₂) (κ₁ × κ₂) R :=
      fun i x ↦ Sum.elim (fun a ↦ A a x.1) (fun b ↦ B b x.2) i
    let g : Fin r ⊕ Fin r → κ₁ ⊕ κ₂ :=
      fun z ↦ Sum.elim (fun j ↦ Sum.inl ((f j).1)) (fun j ↦ Sum.inr ((f j).2)) z
    let S : Matrix (Fin r ⊕ Fin r) (Fin r) R :=
      fun z j ↦ Sum.elim
        (fun l ↦ if l = j then (1 : R) else 0)
        (fun l ↦ if l = j then (1 : R) else 0) z
    C.submatrix e₁ f =
      ((Matrix.fromBlocks A 0 0 B).submatrix e₁ g) * S := by
  classical
  dsimp
  -- Split the selector sum over the left and right summands and collapse the sparse matrix `S`.
  ext i j
  cases hrow : e₁ i with
  | inl a =>
      simp only [hrow, Matrix.submatrix_apply, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Sum.elim_inl,
        Sum.elim_inr, zero_mul]
      simp
  | inr b =>
      simp only [hrow, Matrix.submatrix_apply, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Sum.elim_inl,
        Sum.elim_inr, zero_mul]
      simp

/-- Helper for Definition 15.8.3: every minor of the normalized product-column matrix expands into
minors of the corresponding block-diagonal matrix. -/
private theorem minorIdeal_prod_columns_le_fromBlocks
    {ι₁ : Type*} {ι₂ : Type*} {κ₁ : Type*} {κ₂ : Type*}
    (r : ℕ) (A : Matrix ι₁ κ₁ R) (B : Matrix ι₂ κ₂ R) :
    Matrix.minorIdeal r
        (fun i x ↦ Sum.elim (fun a ↦ A a x.1) (fun b ↦ B b x.2) i :
          Matrix (ι₁ ⊕ ι₂) (κ₁ × κ₂) R) ≤
      Matrix.minorIdeal r (Matrix.fromBlocks A 0 0 B) := by
  classical
  refine Ideal.span_le.2 ?_
  rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
  change
    (Matrix.submatrix
        (fun i x ↦ Sum.elim (fun a ↦ A a x.1) (fun b ↦ B b x.2) i :
          Matrix (ι₁ ⊕ ι₂) (κ₁ × κ₂) R) e₁ e₂).det ∈
      Matrix.minorIdeal r (Matrix.fromBlocks A 0 0 B)
  simpa [prod_columns_submatrix_eq_fromBlocks_submatrix_mul_selector (R := R) r A B e₁ e₂] using
    (det_submatrix_mul_right_mem_minorIdeal_of_colMap (R := R) r
      (Matrix.fromBlocks A 0 0 B) e₁
      (fun z : Fin r ⊕ Fin r ↦
        Sum.elim (fun j ↦ Sum.inl ((e₂ j).1)) (fun j ↦ Sum.inr ((e₂ j).2)) z)
      (fun z j ↦ Sum.elim
        (fun l ↦ if l = j then (1 : R) else 0)
        (fun l ↦ if l = j then (1 : R) else 0) z))

/-- Helper for Definition 15.8.3: the block-diagonal matrix is a literal column submatrix of the
normalized product-column matrix. -/
private theorem minorIdeal_fromBlocks_le_prod_columns
    {ι₁ : Type*} {ι₂ : Type*} {κ₁ : Type*} {κ₂ : Type*}
    [Zero κ₁] [Zero κ₂]
    (r : ℕ) (A : Matrix ι₁ κ₁ R) (B : Matrix ι₂ κ₂ R) :
    Matrix.minorIdeal r (Matrix.fromBlocks A 0 0 B) ≤
      Matrix.minorIdeal r
        (fun i x ↦ Sum.elim (fun a ↦ A a x.1) (fun b ↦ B b x.2) i :
          Matrix (ι₁ ⊕ ι₂) (κ₁ × κ₂) R) := by
  -- TODO: proving the reverse comparison needs a source-faithful expansion of a selected
  -- `fromBlocks` minor into determinants of the product-column matrix; the naive literal-column
  -- inclusion route is not definitionally available for this encoding.
  sorry

/-- Helper for Definition 15.8.3: the normalized product-column matrix and the corresponding
block-diagonal matrix define the same determinantal ideal. -/
private theorem minorIdeal_prod_columns_eq_fromBlocks
    {ι₁ : Type*} {ι₂ : Type*} {κ₁ : Type*} {κ₂ : Type*}
    [Zero κ₁] [Zero κ₂]
    (r : ℕ) (A : Matrix ι₁ κ₁ R) (B : Matrix ι₂ κ₂ R) :
    Matrix.minorIdeal r
        (fun i x ↦ Sum.elim (fun a ↦ A a x.1) (fun b ↦ B b x.2) i :
          Matrix (ι₁ ⊕ ι₂) (κ₁ × κ₂) R) =
      Matrix.minorIdeal r (Matrix.fromBlocks A 0 0 B) := by
  -- TODO: combine the proved forward inclusion with the missing reverse block-to-product expansion.
  sorry

/-- Helper for Definition 15.8.3: the normalized left stabilization collapses to the original
presentation Fitting ideal after the block-minor computation. -/
private theorem presentationFittingIdeal_left_stabilization_eq_normalized {n n' k : ℕ}
    (π : (Fin n → R) →ₗ[R] M) :
    Matrix.minorIdeal (n + n' - k)
      (fun i x ↦ Sum.elim (fun a ↦ x.1.1 a) (fun b ↦ x.2 b) i :
        Matrix (Fin n ⊕ Fin n') (LinearMap.ker π × (Fin n' → R)) R) =
      presentationFittingIdeal R M k π := by
  sorry

/-- Helper for Definition 15.8.3: the normalized right stabilization collapses to the original
presentation Fitting ideal of `π'` after the same block-minor computation. -/
private theorem presentationFittingIdeal_right_stabilization_eq_normalized {n n' k : ℕ}
    (π' : (Fin n' → R) →ₗ[R] M) :
    Matrix.minorIdeal (n + n' - k)
      (fun i x ↦ Sum.elim (fun a ↦ x.1 a) (fun b ↦ x.2.1 b) i :
        Matrix (Fin n ⊕ Fin n') ((Fin n → R) × LinearMap.ker π') R) =
      presentationFittingIdeal R M k π' := by
  sorry

/-- Helper for Definition 15.8.3: the normalized left columns are the sum-arrow form of the
ambient left inclusion. -/
private theorem left_normalized_column_eq_sumArrow_symm {n n' : ℕ}
    {π : (Fin n → R) →ₗ[R] M} (z : LinearMap.ker π × (Fin n' → R)) :
    (fun i : Fin n ⊕ Fin n' ↦ Sum.elim (fun a ↦ z.1.1 a) (fun b ↦ z.2 b) i) =
      (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n') R R).symm
        (presentation_kernel_left_inclusion (R := R) (M := M) (n' := n') π z) := by
  -- Both descriptions are the same vector in the split source coordinates.
  ext i
  cases i with
  | inl a =>
      simp [presentation_kernel_left_inclusion,
        LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl]
  | inr b =>
      simp [presentation_kernel_left_inclusion,
        LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]

/-- Helper for Definition 15.8.3: the normalized right columns are the sum-arrow form of the
ambient right inclusion. -/
private theorem right_normalized_column_eq_sumArrow_symm {n n' : ℕ}
    {π' : (Fin n' → R) →ₗ[R] M} (z : (Fin n → R) × LinearMap.ker π') :
    (fun i : Fin n ⊕ Fin n' ↦ Sum.elim (fun a ↦ z.1 a) (fun b ↦ z.2.1 b) i) =
      (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n') R R).symm
        (presentation_kernel_right_inclusion (R := R) (M := M) (n := n) π' z) := by
  -- The right normalized matrix is the same split vector, now with the kernel on the right.
  ext i
  cases i with
  | inl a =>
      simp [presentation_kernel_right_inclusion,
        LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl]
  | inr b =>
      simp [presentation_kernel_right_inclusion,
        LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]

/-- Helper for Definition 15.8.3: the sum-indexed matrix of the stabilized ambient automorphism
acts on normalized left columns by the Schanuel comparison. -/
private theorem presentationFittingIdeal_stabilized_transport_eq_normalized {n n' k : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (π' : (Fin n' → R) →ₗ[R] M)
    (σ : (Fin n → R) →ₗ[R] (Fin n' → R))
    (τ : (Fin n' → R) →ₗ[R] (Fin n → R))
    (hσ : π'.comp σ = π) (hτ : π.comp τ = π') :
    Matrix.minorIdeal (n + n' - k)
      (fun i x ↦ Sum.elim (fun a ↦ x.1.1 a) (fun b ↦ x.2 b) i :
        Matrix (Fin n ⊕ Fin n') (LinearMap.ker π × (Fin n' → R)) R) =
    Matrix.minorIdeal (n + n' - k)
      (fun i x ↦ Sum.elim (fun a ↦ x.1 a) (fun b ↦ x.2.1 b) i :
        Matrix (Fin n ⊕ Fin n') ((Fin n → R) × LinearMap.ker π') R) := by
  sorry

-- Proof sketch: stabilize two surjective finite free presentations by adding trivial summands and
-- compare the resulting kernel-vector determinant ideals after changing bases in the source free
-- modules. The determinant ideals are invariant under these operations, so the presentation ideal
-- depends only on `M` and `k`.
/-- Any two surjective finite free presentations of `M` determine the same presentation Fitting
ideal. -/
theorem presentationFittingIdeal_eq_of_surjective {n n' k : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (π' : (Fin n' → R) →ₗ[R] M)
    (hπ : Function.Surjective π) (hπ' : Function.Surjective π') :
    presentationFittingIdeal R M k π = presentationFittingIdeal R M k π' := by
  obtain ⟨σ, hσ⟩ := exists_presentation_lift (R := R) (M := M) π π' hπ'
  obtain ⟨τ, hτ⟩ := exists_presentation_lift (R := R) (M := M) π' π hπ
  -- The two presentations become equal after adding free summands and transporting across the
  -- Schanuel comparison.
  calc
    presentationFittingIdeal R M k π =
        Matrix.minorIdeal (n + n' - k)
          (fun i x ↦ Sum.elim (fun a ↦ x.1.1 a) (fun b ↦ x.2 b) i :
            Matrix (Fin n ⊕ Fin n') (LinearMap.ker π × (Fin n' → R)) R) := by
      symm
      exact presentationFittingIdeal_left_stabilization_eq_normalized (R := R) (M := M) π
    _ =
        Matrix.minorIdeal (n + n' - k)
          (fun i x ↦ Sum.elim (fun a ↦ x.1 a) (fun b ↦ x.2.1 b) i :
            Matrix (Fin n ⊕ Fin n') ((Fin n → R) × LinearMap.ker π') R) := by
      exact presentationFittingIdeal_stabilized_transport_eq_normalized
        (R := R) (M := M) (k := k) π π' σ τ hσ hτ
    _ = presentationFittingIdeal R M k π' := by
      exact presentationFittingIdeal_right_stabilization_eq_normalized (R := R) (M := M) π'

section

variable [Module.Finite R M]

private abbrev SurjectivePresentation :=
  Σ n : ℕ, { π : (Fin n → R) →ₗ[R] M // Function.Surjective π }

/-- Definition 15.8.3: for a finite `R`-module `M`, the `k`th Fitting ideal is the intrinsic
ideal obtained from the presentation-independent construction of Lemma 15.8.2; concretely, it is
the infimum of `presentationFittingIdeal k π` over all surjective maps `π : R^n → M`. -/
@[stacks 07Z9]
def fittingIdeal : ℕ → Ideal R := fun k ↦
  sInf <| Set.range fun P : SurjectivePresentation R M ↦ presentationFittingIdeal R M k P.2.1

namespace FittingIdeal

scoped notation "Fit[" R "]_(" k ")(" M ")" => fittingIdeal R M k

end FittingIdeal

open scoped FittingIdeal

/-- The Fitting ideal one step below `Fit_r(M)`, using the owner convention `Fit_{-1}(M) = 0`. -/
abbrev precedingFittingIdeal (r : ℕ) : Ideal R :=
  if r = 0 then fittingIdealNegOne R else Fit[R]_(r - 1)(M)

omit [Module.Finite R M] in
@[simp] theorem precedingFittingIdeal_zero :
    precedingFittingIdeal R M 0 = ⊥ := by
  simp [precedingFittingIdeal]

omit [Module.Finite R M] in
@[simp] theorem precedingFittingIdeal_succ (r : ℕ) :
    precedingFittingIdeal R M (r + 1) = Fit[R]_(r)(M) := by
  simp [precedingFittingIdeal]

-- Proof sketch: a surjective presentation `π` contributes the ideal
-- `presentationFittingIdeal k π` to the defining family for `fittingIdeal`. Any other
-- surjective presentation contributes the same ideal by
-- `presentationFittingIdeal_eq_of_surjective`, so the infimum of the family is exactly this
-- common value.
omit [Module.Finite R M] in
/-- The intrinsic Fitting ideal agrees with the Fitting ideal computed from any surjective finite
free presentation. -/
theorem fittingIdeal_eq_presentationFittingIdeal (k : ℕ) {n : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π) :
    Fit[R]_(k)(M) = presentationFittingIdeal R M k π := by
  -- The chosen surjective presentation is one member of the defining infimum family.
  refine le_antisymm ?_ ?_
  · change
      sInf (Set.range fun P : SurjectivePresentation R M ↦ presentationFittingIdeal R M k P.2.1) ≤
        presentationFittingIdeal R M k π
    refine sInf_le ?_
    exact ⟨⟨n, ⟨π, hπ⟩⟩, rfl⟩
  · change
      presentationFittingIdeal R M k π ≤
        sInf (Set.range fun P : SurjectivePresentation R M ↦ presentationFittingIdeal R M k P.2.1)
    refine le_sInf ?_
    rintro _ ⟨⟨n', ⟨π', hπ'⟩⟩, rfl⟩
    -- Presentation independence identifies every other defining term with the chosen one.
    change presentationFittingIdeal R M k π ≤ presentationFittingIdeal R M k π'
    rw [presentationFittingIdeal_eq_of_surjective (R := R) (M := M) (k := k) π' π hπ' hπ]

omit [Module.Finite R M] in
/-- Helper for Definition 15.8.3: postcomposing a presentation with a linear equivalence does not
change the corresponding presentation Fitting ideal. -/
lemma presentationFittingIdeal_comp_linearEquiv {M' : Type*} [AddCommGroup M'] [Module R M']
    (k : ℕ) {n : ℕ} (e : M ≃ₗ[R] M') (π : (Fin n → R) →ₗ[R] M) :
    presentationFittingIdeal R M' k ((e : M →ₗ[R] M').comp π) =
      presentationFittingIdeal R M k π := by
  -- The matrix formula depends only on the kernel submodule of the presentation map.
  simpa [presentationFittingIdeal] using
    congrArg
      (fun K : Submodule R (Fin n → R) ↦
        I_((n - k))((fun i x ↦ x.1 i : Matrix (Fin n) K R)))
      (LinearEquiv.ker_comp (e'' := e) π)

/-- The intrinsic Fitting ideal is invariant under linear equivalence of finite modules. -/
theorem fittingIdeal_eq_of_linearEquiv {M' : Type*} [AddCommGroup M'] [Module R M']
    (k : ℕ) (e : M ≃ₗ[R] M') :
    let _ : Module.Finite R M' := Module.Finite.of_surjective (e : M →ₗ[R] M') e.surjective
    Fit[R]_(k)(M) = Fit[R]_(k)(M') := by
  let _ : Module.Finite R M' := Module.Finite.of_surjective (e : M →ₗ[R] M') e.surjective
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  have hcomp : Function.Surjective ((e : M →ₗ[R] M').comp π) := by
    intro y
    rcases e.surjective y with ⟨x, rfl⟩
    rcases hπ x with ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  -- Compute both intrinsic ideals from the same source presentation, transported through `e`.
  calc
    Fit[R]_(k)(M) = presentationFittingIdeal R M k π := by
      exact fittingIdeal_eq_presentationFittingIdeal (R := R) (M := M) k π hπ
    _ = presentationFittingIdeal R M' k ((e : M →ₗ[R] M').comp π) := by
      symm
      exact presentationFittingIdeal_comp_linearEquiv (R := R) (M := M) (M' := M') k e π
    _ = Fit[R]_(k)(M') := by
      symm
      exact fittingIdeal_eq_presentationFittingIdeal (R := R) (M := M') k
        ((e : M →ₗ[R] M').comp π) hcomp

end

end
