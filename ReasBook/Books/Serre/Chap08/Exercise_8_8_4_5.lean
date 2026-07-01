import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open Matrix.GeneralLinearGroup

noncomputable section

universe u

section UpperUnitriangularSubgroup

variable (k : Type u) [CommRing k] (n : ℕ)

-- Source/core/bridge triage for Exercise 8-8.4-5:
-- * source-facing: the subgroup of `GL_n(k)` of upper unitriangular matrices and the resulting
--   Sylow statement over a finite field.
-- * core/canonical owners sampled in this domain: `Matrix.BlockTriangular` for upper-triangular
--   structure, `Matrix.diag` for diagonal data, `Matrix.blockTriangular_inv_of_blockTriangular`
--   for inversion, and `Sylow.ofCard` for the Sylow constructor.
-- * bridge/view: cutting out the source-facing subgroup inside `GL (Fin n) k` via those canonical
--   matrix predicates.
-- * primitive data: the subgroup `upperUnitriangularSubgroup k n`.
-- * derived API: the membership simplification lemma and the Sylow packaging theorem.

local notation "Mₙ" => Matrix (Fin n) (Fin n) k

/-- The identity matrix of `GL_n(k)` is upper unitriangular. -/
-- Proof sketch: the identity matrix has zero off-diagonal entries and all diagonal entries equal
-- to `1`.
private theorem upperUnitriangular_one :
    ((1 : Mₙ).BlockTriangular id) ∧ (1 : Mₙ).diag = 1 := by
  constructor
  · simpa using
      (Matrix.blockTriangular_one : Matrix.BlockTriangular (1 : Mₙ) id)
  · simp

/-- The product of two upper unitriangular matrices is upper unitriangular. -/
-- Proof sketch: inspect the matrix entries of the product; below the diagonal every summand
-- vanishes, while on the diagonal only the diagonal summand survives and equals `1`.
private theorem upperUnitriangular_mul {A B : Mₙ}
    (hA : A.BlockTriangular id ∧ A.diag = 1) (hB : B.BlockTriangular id ∧ B.diag = 1) :
    (A * B).BlockTriangular id ∧ (A * B).diag = 1 := by
  refine ⟨hA.1.mul hB.1, ?_⟩
  ext i
  have hAii : A i i = 1 := by
    simpa [Matrix.diag_apply] using congrFun hA.2 i
  have hBii : B i i = 1 := by
    simpa [Matrix.diag_apply] using congrFun hB.2 i
  rw [Matrix.diag_apply, Matrix.mul_apply, Finset.sum_eq_single i]
  · simp [hAii, hBii]
  · intro j _ hij
    rcases lt_or_gt_of_ne hij with hji | hij'
    · simp [hA.1 hji]
    · simp [hB.1 hij']
  · intro hi
    simp at hi

/-- Helper for Exercise 8-8.4-5: the inverse of an upper unitriangular matrix is again upper
unitriangular. -/
-- Proof sketch: use the canonical inverse-closure theorem for block-triangular matrices to keep
-- the upper-triangular condition, then read the diagonal entries from `(g⁻¹) * g = 1`.
private theorem upperUnitriangular_inv {g : GL (Fin n) k}
    (hg : ((g : Mₙ).BlockTriangular id) ∧ (g : Mₙ).diag = 1) :
    (((g⁻¹ : GL (Fin n) k) : Mₙ).BlockTriangular id) ∧
      (((g⁻¹ : GL (Fin n) k) : Mₙ).diag = 1) := by
  letI := g.invertible
  have htri :
      (((g⁻¹ : GL (Fin n) k) : Mₙ).BlockTriangular id) := by
    -- Invoke the canonical inverse-closure theorem directly on the underlying matrix.
    simpa [GeneralLinearGroup.coe_inv] using
      (Matrix.blockTriangular_inv_of_blockTriangular hg.1 :
        ((g : Mₙ)⁻¹).BlockTriangular id)
  refine ⟨htri, ?_⟩
  · -- The diagonal is forced to be `1` because `(g⁻¹) * g = 1`.
    ext i
    have hgii : (g : Mₙ) i i = 1 := by
      simpa [Matrix.diag_apply] using congrFun hg.2 i
    have hmul :
        (((g⁻¹ : GL (Fin n) k) : Mₙ) * (g : Mₙ)) = (1 : Mₙ) := by
      simpa [GeneralLinearGroup.coe_mul] using
        (show (((g⁻¹ : GL (Fin n) k) * g : GL (Fin n) k) : Mₙ) = (1 : Mₙ) by simp)
    have hi :
        (((((g⁻¹ : GL (Fin n) k) : Mₙ) * (g : Mₙ)) i i)) = 1 := by
      simpa using congrFun (congrFun hmul i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at hi
    · simpa [Matrix.diag_apply, hgii] using hi
    · intro j _ hij
      rcases lt_or_gt_of_ne hij with hji | hij'
      · simp [htri hji]
      · simp [hg.1 hij']
    · intro hi'
      simp at hi'

/-- The subgroup of `GL_n(k)` consisting of upper triangular matrices whose diagonal entries are all
`1`. -/
def upperUnitriangularSubgroup : Subgroup (GL (Fin n) k) where
  carrier := { g | ((g : Mₙ).BlockTriangular id) ∧ (g : Mₙ).diag = 1 }
  one_mem' := upperUnitriangular_one k n
  mul_mem' := by
    intro g h hg hh
    simpa [GeneralLinearGroup.coe_mul] using upperUnitriangular_mul k n hg hh
  inv_mem' := by
    intro g hg
    exact upperUnitriangular_inv k n hg

-- Proof sketch: unfold `upperUnitriangularSubgroup`.
/-- An element of `GL_n(k)` lies in `upperUnitriangularSubgroup` exactly when it is upper
unitriangular, expressed using the canonical matrix owners `Matrix.BlockTriangular` and
`Matrix.diag`. -/
@[simp]
theorem mem_upperUnitriangularSubgroup_iff (g : GL (Fin n) k) :
    g ∈ upperUnitriangularSubgroup k n ↔
      ((g : Mₙ).BlockTriangular id) ∧ (g : Mₙ).diag = 1 := Iff.rfl

end UpperUnitriangularSubgroup

section Sylow

variable (k : Type u) [Field k] (n p : ℕ) [Finite k] [CharP k p]

local notation "Mₙ" => Matrix (Fin n) (Fin n) k

/-- Helper for Exercise 8-8.4-5: the row index `Fin j` in column `j` viewed inside `Fin n`. -/
private def strictUpperRowEmbedding (j : Fin n) : Fin j → Fin n :=
  fun i ↦ ⟨i.1, lt_trans i.2 j.2⟩

/-- Helper for Exercise 8-8.4-5: the upper unitriangular matrix determined by strict-upper column
data. -/
private def upperUnitriangularMatrix (f : (j : Fin n) → Fin j → k) : Mₙ :=
  fun i j ↦ if h : i < j then f j ⟨i.1, h⟩ else if i = j then 1 else 0

/-- Helper for Exercise 8-8.4-5: on a strict-upper position, the matrix built from the column data
returns exactly the chosen parameter. -/
-- Proof sketch: the defining `if` selects the strict-upper branch.
private theorem upperUnitriangularMatrix_apply_strictUpper
    (f : (j : Fin n) → Fin j → k) (j : Fin n) (i : Fin j) :
    upperUnitriangularMatrix k n f (strictUpperRowEmbedding n j i) j = f j i := by
  -- The row index lies strictly above the diagonal in column `j`.
  have hlt : strictUpperRowEmbedding n j i < j := i.2
  rw [upperUnitriangularMatrix, dif_pos hlt]
  apply congrArg (f j)
  ext
  rfl

/-- Helper for Exercise 8-8.4-5: on the diagonal, the matrix built from the column data has entry
`1`. -/
-- Proof sketch: the strict-upper branch is impossible on the diagonal, so the defining formula
-- falls through to the diagonal branch.
private theorem upperUnitriangularMatrix_apply_diag
    (f : (j : Fin n) → Fin j → k) (i : Fin n) :
    upperUnitriangularMatrix k n f i i = 1 := by
  -- Diagonal entries land in the explicit `1` branch.
  simp [upperUnitriangularMatrix]

/-- Helper for Exercise 8-8.4-5: below the diagonal, the matrix built from the column data
vanishes. -/
-- Proof sketch: both the strict-upper and diagonal branches are impossible below the diagonal.
private theorem upperUnitriangularMatrix_apply_lower
    (f : (j : Fin n) → Fin j → k) {i j : Fin n} (hji : j < i) :
    upperUnitriangularMatrix k n f i j = 0 := by
  -- Lower-triangular entries land in the zero branch.
  have hij : ¬ i < j := Nat.not_lt_of_ge (Nat.le_of_lt hji)
  rw [upperUnitriangularMatrix, dif_neg hij]
  by_cases hEq : i = j
  · exact (hji.ne hEq.symm).elim
  · simp [hEq]

/-- Helper for Exercise 8-8.4-5: the matrix built from the column data is upper triangular. -/
-- Proof sketch: every strictly lower entry is forced to be `0` by construction.
private theorem upperUnitriangularMatrix_blockTriangular
    (f : (j : Fin n) → Fin j → k) :
    (upperUnitriangularMatrix k n f).BlockTriangular id := by
  -- The defining formula vanishes on lower entries.
  intro i j hij
  exact upperUnitriangularMatrix_apply_lower k n f hij

/-- Helper for Exercise 8-8.4-5: the matrix built from the column data has diagonal equal to `1`.
-/
-- Proof sketch: each diagonal entry is explicitly set to `1`.
private theorem upperUnitriangularMatrix_diag
    (f : (j : Fin n) → Fin j → k) :
    (upperUnitriangularMatrix k n f).diag = 1 := by
  -- Evaluate the diagonal entrywise.
  ext i
  simpa [Matrix.diag_apply] using upperUnitriangularMatrix_apply_diag k n f i

/-- Helper for Exercise 8-8.4-5: the determinant of the matrix built from the column data is `1`.
-/
-- Proof sketch: the matrix is upper triangular, so its determinant is the product of its diagonal
-- entries, which are all `1`.
private theorem upperUnitriangularMatrix_det
    (f : (j : Fin n) → Fin j → k) :
    (upperUnitriangularMatrix k n f).det = 1 := by
  -- Reduce the determinant to the diagonal product.
  rw [Matrix.det_of_upperTriangular (upperUnitriangularMatrix_blockTriangular k n f)]
  simp [upperUnitriangularMatrix_apply_diag]

/-- Helper for Exercise 8-8.4-5: the explicit matrix from strict-upper column data determines an
element of the upper unitriangular subgroup. -/
-- Proof sketch: package the matrix into `GL` using `det = 1`, then record the upper-triangular and
-- diagonal conditions already proved.
private noncomputable def upperUnitriangularElement
    (f : (j : Fin n) → Fin j → k) : upperUnitriangularSubgroup k n :=
  ⟨GeneralLinearGroup.mk'' (upperUnitriangularMatrix k n f) <|
      by simpa [upperUnitriangularMatrix_det k n f],
    by
      exact ⟨upperUnitriangularMatrix_blockTriangular k n f,
        upperUnitriangularMatrix_diag k n f⟩⟩

/-- Helper for Exercise 8-8.4-5: upper unitriangular matrices are determined by their strict-upper
entries, grouped column by column. -/
-- Proof sketch: record each free strict-upper entry in its column, and reconstruct the matrix by
-- placing those entries above the diagonal while forcing the diagonal to `1` and the lower part to
-- `0`.
private noncomputable def upperUnitriangularSubgroupEquivColumnFunctions :
    upperUnitriangularSubgroup k n ≃ ((j : Fin n) → Fin j → k) where
  toFun g := fun j i ↦
    (((g : GL (Fin n) k) : Mₙ) (strictUpperRowEmbedding n j i) j)
  invFun := upperUnitriangularElement k n
  left_inv g := by
    -- Compare the reconstructed matrix with the original one entrywise.
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change upperUnitriangularMatrix k n
        (fun j i ↦ (((g : GL (Fin n) k) : Mₙ) (strictUpperRowEmbedding n j i) j)) i j =
      (((g : GL (Fin n) k) : Mₙ) i j)
    rcases lt_trichotomy i j with hij | rfl | hji
    · -- On a strict-upper entry, reconstruction uses exactly the recorded coordinate.
      rw [upperUnitriangularMatrix, dif_pos hij]
      change (((g : GL (Fin n) k) : Mₙ) (strictUpperRowEmbedding n j ⟨i.1, hij⟩) j) =
        (((g : GL (Fin n) k) : Mₙ) i j)
      simp [strictUpperRowEmbedding]
    · -- On the diagonal, both matrices have entry `1`.
      have hdiag : (((g : GL (Fin n) k) : Mₙ) i i) = 1 := by
        simpa [Matrix.diag_apply] using congrFun g.2.2 i
      simp [upperUnitriangularMatrix, hdiag]
    · -- Below the diagonal, both matrices vanish.
      have hzero : (((g : GL (Fin n) k) : Mₙ) i j) = 0 := g.2.1 hji
      have hij : ¬ i < j := Nat.not_lt_of_ge (Nat.le_of_lt hji)
      simp [upperUnitriangularMatrix, hij, hji.ne', hzero]
  right_inv f := by
    -- Reconstruction returns the original column data on every strict-upper coordinate.
    funext j
    ext i
    change upperUnitriangularMatrix k n f (strictUpperRowEmbedding n j i) j = f j i
    exact upperUnitriangularMatrix_apply_strictUpper k n f j i

/-- Helper for Exercise 8-8.4-5: counting the upper unitriangular subgroup reduces to counting one
free `k`-valued function on each column above the diagonal. -/
-- Proof sketch: apply the explicit column-parameter equivalence and then count a dependent
-- function space column by column.
private theorem upperUnitriangularSubgroup_card_eq_column_product :
    Nat.card (upperUnitriangularSubgroup k n) = ∏ j : Fin n, Nat.card k ^ (j : ℕ) := by
  -- The column-data equivalence identifies the subgroup with a dependent function type.
  rw [Nat.card_congr (upperUnitriangularSubgroupEquivColumnFunctions k n), Nat.card_pi]
  refine Finset.prod_congr rfl ?_
  intro j hj
  -- Each column contributes one function space `Fin j → k`.
  simpa using (Nat.card_fun (α := Fin j) (β := k))

/-- Helper for Exercise 8-8.4-5: the `p`-part of a finite product is the product of the `p`-parts,
provided every factor is nonzero. -/
-- Proof sketch: induct over the finite product and use the multiplicativity of `ordProj`.
private theorem ordProj_finset_prod {α : Type*} (s : Finset α) (f : α → ℕ)
    (hf : ∀ a ∈ s, f a ≠ 0) :
    ordProj[p] (Finset.prod s f) = Finset.prod s (fun a ↦ ordProj[p] (f a)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      rw [Nat.ordProj_mul p (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))]
      rw [ih (fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))]

/-- Helper for Exercise 8-8.4-5: each factor `q^n - q^i` in the cardinality formula for
`GL_n(q)` has `p`-part exactly `q^i` when `q` is a power of `p`. -/
-- Proof sketch: factor `q^n - q^i` as `q^i (q^(n-i) - 1)`, observe the second factor is prime to
-- `p`, and note that `q^i` is itself a pure `p`-power.
private theorem gl_factor_ordProj (i : Fin n) :
    ordProj[p] (Nat.card k ^ n - Nat.card k ^ (i : ℕ)) = Nat.card k ^ (i : ℕ) := by
  letI := Fintype.ofFinite k
  let q := Fintype.card k
  have hk : Nat.card k = q := Nat.card_eq_fintype_card
  have hq_ne_zero : q ≠ 0 := by
    simp [q]
  obtain ⟨m, hp, hq : q = p ^ (m : ℕ)⟩ := FiniteField.card k p
  have hq_one_lt : 1 < q := by
    exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hni_ne_zero : n - (i : ℕ) ≠ 0 := (Nat.sub_pos_of_lt i.2).ne'
  have hsplit : q ^ n - q ^ (i : ℕ) = q ^ (i : ℕ) * (q ^ (n - (i : ℕ)) - 1) := by
    -- Pull out the common factor `q^i`.
    calc
      q ^ n - q ^ (i : ℕ) = q ^ (i : ℕ) * q ^ (n - (i : ℕ)) - q ^ (i : ℕ) := by
        rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt i.2)]
      _ = q ^ (i : ℕ) * q ^ (n - (i : ℕ)) - q ^ (i : ℕ) * 1 := by
        rw [mul_one]
      _ = q ^ (i : ℕ) * (q ^ (n - (i : ℕ)) - 1) := by
        rw [Nat.mul_sub_left_distrib]
  have hfactor_ne_zero : q ^ (n - (i : ℕ)) - 1 ≠ 0 := by
    exact Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hni_ne_zero hq_one_lt)
  have hpdvdq : p ∣ q := by
    simpa [hq] using dvd_pow_self p (m : ℕ).ne'
  have hnotdvd : ¬ p ∣ q ^ (n - (i : ℕ)) - 1 := by
    -- If `p` divided both `q^(n-i)` and `q^(n-i) - 1`, it would divide `1`.
    intro hminus
    have hpowdvd : p ∣ q ^ (n - (i : ℕ)) := by
      exact dvd_trans hpdvdq (dvd_pow_self q hni_ne_zero)
    have hone : p ∣ q ^ (n - (i : ℕ)) - (q ^ (n - (i : ℕ)) - 1) := by
      exact Nat.dvd_sub hpowdvd hminus
    have hsub : q ^ (n - (i : ℕ)) - (q ^ (n - (i : ℕ)) - 1) = 1 := by
      omega
    exact hp.not_dvd_one (hsub ▸ hone)
  have hfactor_zero : (q ^ (n - (i : ℕ)) - 1).factorization p = 0 := by
    -- Prime-to-`p` means the `p`-adic exponent is zero.
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact hnotdvd ((hp.dvd_iff_one_le_factorization hfactor_ne_zero).2 (Nat.succ_le_of_lt hpos))
  have hord_right : ordProj[p] (q ^ (n - (i : ℕ)) - 1) = 1 := by
    simp [hfactor_zero]
  have hord_left : ordProj[p] (q ^ (i : ℕ)) = q ^ (i : ℕ) := by
    rw [hq, ← Nat.pow_mul]
    simpa using (Nat.ordProj_self_pow hp (k := (m : ℕ) * (i : ℕ)))
  rw [hk]
  calc
    ordProj[p] (q ^ n - q ^ (i : ℕ)) = ordProj[p] (q ^ (i : ℕ) * (q ^ (n - (i : ℕ)) - 1)) := by
      rw [hsplit]
    _ = ordProj[p] (q ^ (i : ℕ)) * ordProj[p] (q ^ (n - (i : ℕ)) - 1) := by
      simpa using (Nat.ordProj_mul p (pow_ne_zero _ hq_ne_zero) hfactor_ne_zero :
        ordProj[p] (q ^ (i : ℕ) * (q ^ (n - (i : ℕ)) - 1)) =
          ordProj[p] (q ^ (i : ℕ)) * ordProj[p] (q ^ (n - (i : ℕ)) - 1))
    _ = q ^ (i : ℕ) := by
      rw [hord_left, hord_right, mul_one]

/-- Helper for Exercise 8-8.4-5: the `p`-part of `|GL_n(k)|` is exactly the product of the
column-by-column powers `(#k)^j`. -/
-- Proof sketch: rewrite `|GL_n(k)|` using `Matrix.card_GL_field`, push `ordProj` through the
-- finite product, and evaluate each factor with `gl_factor_ordProj`.
private theorem gl_card_p_part_eq_column_product :
    p ^ (Nat.card (GL (Fin n) k)).factorization p = ∏ j : Fin n, Nat.card k ^ (j : ℕ) := by
  letI := Fintype.ofFinite k
  let q := Fintype.card k
  have hcard : Nat.card (GL (Fin n) k) = ∏ j : Fin n, (q ^ n - q ^ (j : ℕ)) := by
    simpa [q] using Matrix.card_GL_field (𝔽 := k) n
  -- Switch to the `ordProj` notation for the `p`-part and compute factorwise.
  change ordProj[p] (Nat.card (GL (Fin n) k)) = ∏ j : Fin n, Nat.card k ^ (j : ℕ)
  rw [hcard]
  change ordProj[p] (∏ j : Fin n, (q ^ n - q ^ (j : ℕ))) = ∏ j : Fin n, Nat.card k ^ (j : ℕ)
  rw [ordProj_finset_prod (p := p) (s := Finset.univ)
    (f := fun j : Fin n ↦ q ^ n - q ^ (j : ℕ))]
  · refine Finset.prod_congr rfl ?_
    intro j hj
    simpa [q, Nat.card_eq_fintype_card] using
      gl_factor_ordProj (k := k) (n := n) (p := p) j
  · intro j hj
    obtain ⟨m, hp, hq : q = p ^ (m : ℕ)⟩ := FiniteField.card k p
    have hq_one_lt : 1 < q := by
      exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
    have hnj_ne_zero : n - (j : ℕ) ≠ 0 := (Nat.sub_pos_of_lt j.2).ne'
    have hsplit : q ^ n - q ^ (j : ℕ) = q ^ (j : ℕ) * (q ^ (n - (j : ℕ)) - 1) := by
      calc
        q ^ n - q ^ (j : ℕ) = q ^ (j : ℕ) * q ^ (n - (j : ℕ)) - q ^ (j : ℕ) := by
          rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt j.2)]
        _ = q ^ (j : ℕ) * q ^ (n - (j : ℕ)) - q ^ (j : ℕ) * 1 := by
          rw [mul_one]
        _ = q ^ (j : ℕ) * (q ^ (n - (j : ℕ)) - 1) := by
          rw [Nat.mul_sub_left_distrib]
    have hfactor_ne_zero : q ^ (n - (j : ℕ)) - 1 ≠ 0 := by
      exact Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hnj_ne_zero hq_one_lt)
    rw [hsplit]
    exact mul_ne_zero (pow_ne_zero _ (by simp [q])) hfactor_ne_zero

-- Proof sketch: count the free entries strictly above the diagonal; there are `n * (n - 1) / 2`
-- of them, and `Fintype.card k` is a power of `p` because `k` is a finite field of characteristic
-- `p`. Comparing with `Matrix.card_GL_field` gives the required `p`-part of `|GL_n(k)|`.
/-- The upper unitriangular subgroup has the full `p`-power cardinality occurring in `GL_n(k)`. -/
theorem upperUnitriangularSubgroup_card_eq :
    Nat.card (upperUnitriangularSubgroup k n) =
      p ^ (Nat.card (GL (Fin n) k)).factorization p := by
  -- Match the subgroup count with the `p`-part of the ambient group cardinality.
  exact (upperUnitriangularSubgroup_card_eq_column_product (k := k) (n := n)).trans
    (gl_card_p_part_eq_column_product (k := k) (n := n) (p := p)).symm

/-- Exercise 8-8.4-5: in `GL_n(k)` over a finite field `k` of characteristic `p`, the subgroup of
upper triangular matrices with diagonal entries all equal to `1` is a Sylow `p`-subgroup. -/
theorem upperUnitriangularSubgroup_isSylow :
    ∃ P : Sylow p (GL (Fin n) k), ↑P = upperUnitriangularSubgroup k n := by
  letI : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  exact ⟨Sylow.ofCard (upperUnitriangularSubgroup k n) (upperUnitriangularSubgroup_card_eq k n p),
    Sylow.coe_ofCard (upperUnitriangularSubgroup k n) (upperUnitriangularSubgroup_card_eq k n p)⟩

end Sylow
