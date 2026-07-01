import Mathlib
import FirstOrderMethodsinOptimization.Chap06.Definition_6_1
import FirstOrderMethodsinOptimization.Chap06.Definition_6_2
import FirstOrderMethodsinOptimization.Chap06.Example_6_19
import FirstOrderMethodsinOptimization.Chap06.Lemma_6_5
import FirstOrderMethodsinOptimization.Chap06.Theorem_6_6
import FirstOrderMethodsinOptimization.Chap12.Definition_12_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix Matrix.Norms.Frobenius
open WithLp

noncomputable section

section

variable {m n : ℕ}

local notation "Mmn" => Matrix (Fin m) (Fin n) ℝ
local notation "Hmn" => Matrix (Fin m) (Fin (n - 1)) ℝ
local notation "Vmn" => Matrix (Fin (m - 1)) (Fin n) ℝ
local notation "TVSpace" => WithLp 2 (Hmn × Vmn)

/-- Helper for Proposition 12.4: the horizontal-difference matrix space carries its canonical
Frobenius norm. -/
local instance hmnNormedAddCommGroup : NormedAddCommGroup Hmn :=
  Matrix.frobeniusNormedAddCommGroup

/-- Helper for Proposition 12.4: scalar multiplication on the horizontal-difference matrix space
is compatible with the Frobenius norm. -/
local instance hmnNormedSpace : NormedSpace ℝ Hmn :=
  Matrix.frobeniusNormedSpace

/-- Helper for Proposition 12.4: the vertical-difference matrix space carries its canonical
Frobenius norm. -/
local instance vmnNormedAddCommGroup : NormedAddCommGroup Vmn :=
  Matrix.frobeniusNormedAddCommGroup

/-- Helper for Proposition 12.4: scalar multiplication on the vertical-difference matrix space is
compatible with the Frobenius norm. -/
local instance vmnNormedSpace : NormedSpace ℝ Vmn :=
  Matrix.frobeniusNormedSpace

/-- Helper for Proposition 12.4: the dual TV space uses the canonical `L²` product of the two
Frobenius matrix norms. -/
local instance tvSpaceNormedAddCommGroup : NormedAddCommGroup TVSpace :=
  inferInstance

/-- Helper for Proposition 12.4: scalar multiplication on the `L²` product TV space is compatible
with the horizontal and vertical Frobenius norms. -/
local instance tvSpaceNormedSpace : NormedSpace ℝ TVSpace :=
  inferInstance

/- Proposition 12.4 is `source-facing` in the two-dimensional total-variation denoising model.

Domain sampling identifies the relevant owner declarations:
- mathlib's `WithLp.linearEquiv` and `WithLp.fst` / `WithLp.snd`, which make `WithLp 2 (Hmn × Vmn)`
  the canonical `L²` product owner of the horizontal/vertical dual pair;
- mathlib's `ProdLp.prod_norm_eq_of_L2`, which is the correct Hilbert norm formula on that owner;
- Chapter 12 Proposition 12.5, which likewise packages the TV dual variables through a canonical
  Euclidean `L²` owner rather than the raw product.

The primitive data are the horizontal and vertical difference arrays `p` and `q`. Pairing them
into the ambient dual space is derived API through the canonical `WithLp` bridge. Using the raw
product `Hmn × Vmn` would equip the dual space with the max norm, which is not the norm used by
Chapter 6's proximal operator. -/

/-- Helper for Proposition 12.4: the squared `L²` distance on `TVSpace` splits into the squared
horizontal and vertical Frobenius distances. -/
lemma tvspace_sqdist_split (p u : Hmn) (q v : Vmn) :
    ‖toLp 2 (u, v) - toLp 2 (p, q)‖ ^ (2 : ℕ) =
      ‖u - p‖ ^ (2 : ℕ) + ‖v - q‖ ^ (2 : ℕ) := by
  -- Expand the `WithLp 2` product norm and simplify the two coordinate projections.
  simpa using (WithLp.prod_norm_sq_eq_of_L2 (toLp 2 (u, v) - toLp 2 (p, q)))

/-- The horizontal forward-difference operator `x ↦ p^x`, with
`p^x_(i,j) = x_(i,j) - x_(i,j+1)`. -/
def two_dimensional_total_variation_horizontal_difference : Mmn →ₗ[ℝ] Hmn where
  toFun x := fun i j ↦ x i (Fin.castLE (Nat.sub_le n 1) j) - x i ⟨(j : ℕ) + 1, by omega⟩
  map_add' x y := by
    ext i j
    simp [sub_eq_add_neg]
    abel_nf
  map_smul' a x := by
    ext i j
    simp [sub_eq_add_neg]
    ring_nf

-- Proof sketch: unfold `two_dimensional_total_variation_horizontal_difference`; the entry at
-- `(i, j)` is exactly the difference between adjacent horizontal neighbors in row `i`.
/-- Evaluating the horizontal forward-difference array gives
`p^x_(i,j) = x_(i,j) - x_(i,j+1)`. -/
@[simp] theorem two_dimensional_total_variation_horizontal_difference_apply
    (x : Mmn) (i : Fin m) (j : Fin (n - 1)) :
    two_dimensional_total_variation_horizontal_difference x i j =
      x i (Fin.castLE (Nat.sub_le n 1) j) - x i ⟨(j : ℕ) + 1, by omega⟩ := rfl

/-- The vertical forward-difference operator `x ↦ q^x`, with
`q^x_(i,j) = x_(i,j) - x_(i+1,j)`. -/
def two_dimensional_total_variation_vertical_difference : Mmn →ₗ[ℝ] Vmn where
  toFun x := fun i j ↦ x (Fin.castLE (Nat.sub_le m 1) i) j - x ⟨(i : ℕ) + 1, by omega⟩ j
  map_add' x y := by
    ext i j
    simp [sub_eq_add_neg]
    abel_nf
  map_smul' a x := by
    ext i j
    simp [sub_eq_add_neg]
    ring_nf

-- Proof sketch: unfold `two_dimensional_total_variation_vertical_difference`; the entry at
-- `(i, j)` is exactly the difference between adjacent vertical neighbors in column `j`.
/-- Evaluating the vertical forward-difference array gives
`q^x_(i,j) = x_(i,j) - x_(i+1,j)`. -/
@[simp] theorem two_dimensional_total_variation_vertical_difference_apply
    (x : Mmn) (i : Fin (m - 1)) (j : Fin n) :
    two_dimensional_total_variation_vertical_difference x i j =
      x (Fin.castLE (Nat.sub_le m 1) i) j - x ⟨(i : ℕ) + 1, by omega⟩ j := rfl

/-- The discrete two-dimensional total-variation difference operator
`A(x) = (p^x, q^x)`, where `p^x` records horizontal forward differences and `q^x` records vertical
forward differences. -/
def two_dimensional_total_variation_difference : Mmn →ₗ[ℝ] TVSpace :=
  ((WithLp.linearEquiv 2 ℝ (Hmn × Vmn)).symm.toLinearMap).comp
    (two_dimensional_total_variation_horizontal_difference.prod
      two_dimensional_total_variation_vertical_difference)

/- Textbook notation for the canonical two-dimensional TV difference operator and its Hilbert
adjoint belongs at this owner source. -/
set_option quotPrecheck false in
notation:max "A[" m "," n "]" =>
  (show Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ]
      WithLp 2 (Matrix (Fin m) (Fin (n - 1)) ℝ × Matrix (Fin (m - 1)) (Fin n) ℝ) from
    two_dimensional_total_variation_difference)

set_option quotPrecheck false in
notation:max "Aᵀ[" m "," n "]" =>
  (A[m, n]).adjoint

-- Proof sketch: unfold `A[m, n]`; the first component of `A(x)` is definitionally `p^x`.
/-- The horizontal component of the discrete two-dimensional TV operator is the
horizontal-difference array `p^x`. -/
@[simp] theorem two_dimensional_total_variation_difference_fst
    (x : Mmn) :
    (A[m, n] x).fst =
      two_dimensional_total_variation_horizontal_difference x := rfl

-- Proof sketch: unfold `A[m, n]`; the second component of `A(x)` is definitionally `q^x`.
/-- The vertical component of the discrete two-dimensional TV operator is the vertical-difference
array `q^x`. -/
@[simp] theorem two_dimensional_total_variation_difference_snd
    (x : Mmn) :
    (A[m, n] x).snd =
      two_dimensional_total_variation_vertical_difference x := rfl

-- Proof sketch: this is the Chapter 12 denoising owner formula specialized to the TV operator
-- `A[m, n]` and the real-valued regularizer `g`, via `denoising_problem_objective_apply`.
/-- Proposition 12.4 in the Chapter 12 denoising-owner formulation: evaluating the matrix
objective with the two-dimensional forward-difference operator `A[m, n]` gives the textbook
formula `x ↦ (1 / 2) ‖x - d‖_F^2 + λ g(A x)`. Taking `g` to be the isotropic or anisotropic
regularizer below gives the two textbook cases. -/
@[simp] theorem two_dimensional_total_variation_denoising_problem_objective_apply
    (g : TVSpace → ℝ) (d : Mmn) (lam : ℝ) (x : Mmn) :
    denoising_problem_objective d
      (fun z : TVSpace ↦ ↑(lam * g z))
      A[m, n] x =
      ((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) + ↑(lam * g (A[m, n] x)) := rfl

/-- The isotropic two-dimensional total-variation regularizer `g₁` on the canonical `L²`
product of the horizontal and vertical difference spaces. -/
def two_dimensional_total_variation_isotropic_regularizer (z : TVSpace) : ℝ :=
  let p := z.fst
  let q := z.snd
  (∑ i : Fin m, ∑ j : Fin (n - 1),
      if hi : (i : ℕ) + 1 < m then
        Real.sqrt (p i j ^ (2 : ℕ) +
          q (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi)) (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ))
      else
        |p i j|) +
    ∑ i : Fin (m - 1), ∑ j : Fin n, if (j : ℕ) + 1 < n then (0 : ℝ) else |q i j|

-- Proof sketch: unfold `two_dimensional_total_variation_isotropic_regularizer`; the interior
-- indices contribute Euclidean norms, the last row contributes `|p_(m,j)|`, and the last column
-- contributes `|q_(i,n)|`.
/-- Expanding `g₁` gives the textbook isotropic TV formula with interior Euclidean norms and
boundary absolute values. -/
@[simp] theorem two_dimensional_total_variation_isotropic_regularizer_apply
    (p : Hmn) (q : Vmn) :
    two_dimensional_total_variation_isotropic_regularizer (toLp 2 (p, q)) =
      (∑ i : Fin m, ∑ j : Fin (n - 1),
        if hi : (i : ℕ) + 1 < m then
          Real.sqrt (p i j ^ (2 : ℕ) +
            q (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi)) (Fin.castLE (Nat.sub_le n 1) j) ^
              (2 : ℕ))
        else
          |p i j|) +
        ∑ i : Fin (m - 1), ∑ j : Fin n, if (j : ℕ) + 1 < n then (0 : ℝ) else |q i j| := rfl

/-- The anisotropic two-dimensional total-variation regularizer `g_{ℓ¹}` on the canonical `L²`
product of the horizontal and vertical difference spaces. -/
def two_dimensional_total_variation_anisotropic_regularizer (z : TVSpace) : ℝ :=
  let p := z.fst
  let q := z.snd
  (∑ i : Fin m, ∑ j : Fin (n - 1), |p i j|) +
    ∑ i : Fin (m - 1), ∑ j : Fin n, |q i j|

-- Proof sketch: unfold `two_dimensional_total_variation_anisotropic_regularizer`; the formula is
-- exactly the sum of absolute values of all horizontal and vertical difference entries.
/-- Expanding `g_{ℓ¹}` gives the textbook anisotropic TV formula as the sum of the absolute values
of all horizontal and vertical differences. -/
@[simp] theorem two_dimensional_total_variation_anisotropic_regularizer_apply
    (p : Hmn) (q : Vmn) :
    two_dimensional_total_variation_anisotropic_regularizer (toLp 2 (p, q)) =
      (∑ i : Fin m, ∑ j : Fin (n - 1), |p i j|) +
        ∑ i : Fin (m - 1), ∑ j : Fin n, |q i j| := rfl

/-- The isotropic interior shrinkage factor
`1 - λ / max {sqrt (p^2 + q^2), λ}` appearing in the proximal formula for `g₁`. -/
def two_dimensional_total_variation_isotropic_shrink_factor
    (lam p q : ℝ) : ℝ :=
  1 - lam / max (Real.sqrt (p ^ (2 : ℕ) + q ^ (2 : ℕ))) lam

/-- Helper for Proposition 12.4: the interior isotropic shrink factor is exactly the Example 6.19
radial shrinkage factor for the pair `toLp 2 (a, b)`. -/
lemma isotropic_shrink_factor_eq_pair_shrinkage (lam a b : ℝ) :
    two_dimensional_total_variation_isotropic_shrink_factor lam a b =
      1 - lam / max ‖toLp 2 (a, b)‖ lam := by
  -- Rewrite the `WithLp 2` norm of a scalar pair as the textbook square-root expression.
  have hnorm : ‖toLp 2 (a, b)‖ = Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
    simpa [Real.norm_eq_abs, sq_abs] using (WithLp.prod_norm_eq_of_L2 (toLp 2 (a, b)))
  rw [two_dimensional_total_variation_isotropic_shrink_factor, hnorm]

/-- The explicit proximal point of `λ g₁` at `(p, q)`, obtained by isotropic shrinkage on
interior index pairs and soft-thresholding on the boundary entries. -/
def two_dimensional_total_variation_isotropic_prox_point
    (lam : ℝ) (p : Hmn) (q : Vmn) : TVSpace :=
  toLp 2
    ((fun i j ↦
        if hi : (i : ℕ) + 1 < m then
          two_dimensional_total_variation_isotropic_shrink_factor lam (p i j)
            (q (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi)) (Fin.castLE (Nat.sub_le n 1) j)) *
            p i j
        else
          𝒯[lam] (p i j)),
      fun i j ↦
        if hj : (j : ℕ) + 1 < n then
          two_dimensional_total_variation_isotropic_shrink_factor lam
            (p (Fin.castLE (Nat.sub_le m 1) i) (j.castLT (Nat.lt_sub_iff_add_lt.mpr hj)))
            (q i j) * q i j
        else
          𝒯[lam] (q i j))

-- Proof sketch: unfold `two_dimensional_total_variation_isotropic_prox_point`; the first
-- component uses the isotropic shrinkage factor on interior indices and soft-thresholding on the
-- last row.
/-- The horizontal component of the isotropic proximal point has the textbook entrywise formula. -/
@[simp] theorem two_dimensional_total_variation_isotropic_prox_point_fst_apply
    (lam : ℝ) (p : Hmn) (q : Vmn) (i : Fin m) (j : Fin (n - 1)) :
    (two_dimensional_total_variation_isotropic_prox_point lam p q).fst i j =
      if hi : (i : ℕ) + 1 < m then
        two_dimensional_total_variation_isotropic_shrink_factor lam (p i j)
          (q (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi)) (Fin.castLE (Nat.sub_le n 1) j)) * p i j
      else
        𝒯[lam] (p i j) := rfl

-- Proof sketch: unfold `two_dimensional_total_variation_isotropic_prox_point`; the second
-- component uses the isotropic shrinkage factor on interior indices and soft-thresholding on the
-- last column.
/-- The vertical component of the isotropic proximal point has the textbook entrywise formula. -/
@[simp] theorem two_dimensional_total_variation_isotropic_prox_point_snd_apply
    (lam : ℝ) (p : Hmn) (q : Vmn) (i : Fin (m - 1)) (j : Fin n) :
    (two_dimensional_total_variation_isotropic_prox_point lam p q).snd i j =
      if hj : (j : ℕ) + 1 < n then
        two_dimensional_total_variation_isotropic_shrink_factor lam
          (p (Fin.castLE (Nat.sub_le m 1) i) (j.castLT (Nat.lt_sub_iff_add_lt.mpr hj)))
          (q i j) * q i j
      else
        𝒯[lam] (q i j) := rfl

/-- The explicit proximal point of `λ g_{ℓ¹}` at `(p, q)`, obtained by entrywise
soft-thresholding. -/
def two_dimensional_total_variation_anisotropic_prox_point
    (lam : ℝ) (p : Hmn) (q : Vmn) : TVSpace :=
  toLp 2 (fun i j ↦ 𝒯[lam] (p i j), fun i j ↦ 𝒯[lam] (q i j))

-- Proof sketch: unfold `two_dimensional_total_variation_anisotropic_prox_point`; the first
-- component is coordinatewise soft-thresholding of `p`.
/-- The horizontal component of the anisotropic proximal point is entrywise soft-thresholding. -/
@[simp] theorem two_dimensional_total_variation_anisotropic_prox_point_fst_apply
    (lam : ℝ) (p : Hmn) (q : Vmn) (i : Fin m) (j : Fin (n - 1)) :
    (two_dimensional_total_variation_anisotropic_prox_point lam p q).fst i j =
      𝒯[lam] (p i j) := rfl

-- Proof sketch: unfold `two_dimensional_total_variation_anisotropic_prox_point`; the second
-- component is coordinatewise soft-thresholding of `q`.
/-- The vertical component of the anisotropic proximal point is entrywise soft-thresholding. -/
@[simp] theorem two_dimensional_total_variation_anisotropic_prox_point_snd_apply
    (lam : ℝ) (p : Hmn) (q : Vmn) (i : Fin (m - 1)) (j : Fin n) :
    (two_dimensional_total_variation_anisotropic_prox_point lam p q).snd i j =
      𝒯[lam] (q i j) := rfl

/-- Helper for Proposition 12.4: coercing a finite real sum into `EReal` commutes with the sum. -/
lemma ereal_coe_sum_local {κ : Type*} (s : Finset κ) (φ : κ → ℝ) :
    (((∑ i ∈ s, φ i : ℝ) : EReal)) = ∑ i ∈ s, ((φ i : ℝ) : EReal) := by
  classical
  -- Induct over the finite set and push the coercion through one inserted term at a time.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, hs]

/-- Helper for Proposition 12.4: coercing a finite double real sum into `EReal` commutes with the
two nested finite sums. -/
lemma ereal_coe_double_sum_local {ι κ : Type*} (s : Finset ι) (t : Finset κ) (φ : ι → κ → ℝ) :
    (((∑ i ∈ s, ∑ j ∈ t, φ i j : ℝ) : EReal)) =
      ∑ i ∈ s, ∑ j ∈ t, ((φ i j : ℝ) : EReal) := by
  classical
  -- Push the coercion through the outer finite sum, then through each inner finite sum.
  rw [ereal_coe_sum_local (s := s) (φ := fun i ↦ ∑ j ∈ t, φ i j)]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simpa using (ereal_coe_sum_local (s := t) (φ := φ i))

/-- Helper for Proposition 12.4: a finite sum over `Fin m` splits into the interior indices
`0, ..., m - 2` and the boundary index detected by `¬ ((i : ℕ) + 1 < m)`. -/
lemma fin_sum_split_last {α : Type*} [AddCommMonoid α] (g : Fin m → α) :
    (∑ i : Fin m, g i) =
      (∑ i : Fin (m - 1), g (Fin.castLE (Nat.sub_le m 1) i)) +
        ∑ i : Fin m, if hrow : (i : ℕ) + 1 < m then 0 else g i := by
  classical
  cases m with
  | zero =>
      simp
  | succ m =>
      -- Split `Fin (m + 1)` into `Fin m` and the last boundary index.
      have hcast :
          (∑ i : Fin m, g (Fin.castLE (Nat.sub_le (m + 1) 1) i)) =
            ∑ i : Fin m, g i.castSucc := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        apply congrArg g
        ext
        simp [Fin.castLE]
      have hboundary :
          (∑ i : Fin (m + 1), if hi : (i : ℕ) + 1 < m + 1 then 0 else g i) = g (Fin.last m) := by
        rw [Fin.sum_univ_castSucc]
        simp
      calc
        (∑ i : Fin (m + 1), g i) = (∑ i : Fin m, g i.castSucc) + g (Fin.last m) := by
            rw [Fin.sum_univ_castSucc]
        _ = (∑ i : Fin m, g (Fin.castLE (Nat.sub_le (m + 1) 1) i)) +
              ∑ i : Fin (m + 1), if hi : (i : ℕ) + 1 < m + 1 then 0 else g i := by
              rw [hcast, hboundary]

/-- Helper for Proposition 12.4: embedding an interior row index into `Fin m` still satisfies the
strict interior inequality needed to access the isotropic `ℓ²` block. -/
lemma castLE_row_succ_lt (i : Fin (m - 1)) :
    ((Fin.castLE (Nat.sub_le m 1) i : Fin m) : ℕ) + 1 < m := by
  exact Nat.lt_sub_iff_add_lt.mp i.is_lt

/-- Helper for Proposition 12.4: embedding an interior column index into `Fin n` still satisfies
the strict interior inequality needed to access the isotropic `ℓ²` block. -/
lemma castLE_col_succ_lt (j : Fin (n - 1)) :
    ((Fin.castLE (Nat.sub_le n 1) j : Fin n) : ℕ) + 1 < n := by
  exact Nat.lt_sub_iff_add_lt.mp j.is_lt

/-- Helper for Proposition 12.4: converting an interior row index to `Fin m` and back to
`Fin (m - 1)` recovers the original row. -/
lemma castLE_row_castLT_eq (i : Fin (m - 1)) :
    (Fin.castLE (Nat.sub_le m 1) i).castLT (Nat.lt_sub_iff_add_lt.mpr (castLE_row_succ_lt i)) = i := by
  ext
  rfl

/-- Helper for Proposition 12.4: converting an interior column index to `Fin n` and back to
`Fin (n - 1)` recovers the original column. -/
lemma castLE_col_castLT_eq (j : Fin (n - 1)) :
    (Fin.castLE (Nat.sub_le n 1) j).castLT (Nat.lt_sub_iff_add_lt.mpr (castLE_col_succ_lt j)) = j := by
  ext
  rfl

/-- Helper for Proposition 12.4: squaring the horizontal Frobenius distance is the entrywise sum
of the squared coordinate differences. -/
lemma horizontal_frobenius_sqdist_eq_entrywise_sum (p u : Hmn) :
    ‖u - p‖ ^ (2 : ℕ) = ∑ i : Fin m, ∑ j : Fin (n - 1), (u i j - p i j) ^ (2 : ℕ) := by
  have hnorm :
      ‖u - p‖ = Real.sqrt (∑ i : Fin m, ∑ j : Fin (n - 1), ‖(u - p) i j‖ ^ (2 : ℕ)) := by
    simpa [Real.sqrt_eq_rpow] using (Matrix.frobenius_norm_def (u - p))
  -- Rewrite the Frobenius norm through the entrywise formula and square the resulting root.
  calc
    ‖u - p‖ ^ (2 : ℕ)
        = Real.sqrt (∑ i : Fin m, ∑ j : Fin (n - 1), ‖(u - p) i j‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
            rw [hnorm]
    _ = ∑ i : Fin m, ∑ j : Fin (n - 1), ‖(u - p) i j‖ ^ (2 : ℕ) := by
          exact Real.sq_sqrt (by positivity)
    _ = ∑ i : Fin m, ∑ j : Fin (n - 1), (u i j - p i j) ^ (2 : ℕ) := by
          simp [Matrix.sub_apply, Real.norm_eq_abs, sq_abs]

/-- Helper for Proposition 12.4: squaring the vertical Frobenius distance is the entrywise sum of
the squared coordinate differences. -/
lemma vertical_frobenius_sqdist_eq_entrywise_sum (q v : Vmn) :
    ‖v - q‖ ^ (2 : ℕ) = ∑ i : Fin (m - 1), ∑ j : Fin n, (v i j - q i j) ^ (2 : ℕ) := by
  have hnorm :
      ‖v - q‖ = Real.sqrt (∑ i : Fin (m - 1), ∑ j : Fin n, ‖(v - q) i j‖ ^ (2 : ℕ)) := by
    simpa [Real.sqrt_eq_rpow] using (Matrix.frobenius_norm_def (v - q))
  -- Rewrite the Frobenius norm through the entrywise formula and square the resulting root.
  calc
    ‖v - q‖ ^ (2 : ℕ)
        = Real.sqrt (∑ i : Fin (m - 1), ∑ j : Fin n, ‖(v - q) i j‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
            rw [hnorm]
    _ = ∑ i : Fin (m - 1), ∑ j : Fin n, ‖(v - q) i j‖ ^ (2 : ℕ) := by
          exact Real.sq_sqrt (by positivity)
    _ = ∑ i : Fin (m - 1), ∑ j : Fin n, (v i j - q i j) ^ (2 : ℕ) := by
          simp [Matrix.sub_apply, Real.norm_eq_abs, sq_abs]

/-- Helper for Proposition 12.4: the isotropic interior contribution at `(i, j)` is exactly the
two-dimensional `norm_penalty` proximal block on the canonical `L²` pair owner. -/
lemma isotropic_interior_block_proximal_objective_eq
    (lam : ℝ) (p u : Hmn) (q v : Vmn) (i : Fin (m - 1)) (j : Fin (n - 1)) :
    proximal_objective (norm_penalty lam)
      (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) i) j,
        q i (Fin.castLE (Nat.sub_le n 1) j)))
      (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) i) j,
        v i (Fin.castLE (Nat.sub_le n 1) j))) =
      ((lam *
          Real.sqrt ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
            (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) +
          (1 / 2 : ℝ) *
            (((u (Fin.castLE (Nat.sub_le m 1) i) j -
                p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
              ((v i (Fin.castLE (Nat.sub_le n 1) j) -
                q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) : ℝ) : ℝ) : EReal) := by
  -- Route correction: first name one canonical `WithLp 2 (ℝ × ℝ)` interior block, then rewrite
  -- its norm and squared-distance terms directly instead of reopening the full TV-space sum.
  let a := u (Fin.castLE (Nat.sub_le m 1) i) j
  let b := v i (Fin.castLE (Nat.sub_le n 1) j)
  let c := p (Fin.castLE (Nat.sub_le m 1) i) j
  let d := q i (Fin.castLE (Nat.sub_le n 1) j)
  have hnorm : ‖toLp 2 (a, b)‖ = Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
    -- The canonical `L²` norm of a scalar pair is the textbook Euclidean square root.
    simpa [a, b, WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs] using
      (WithLp.prod_norm_eq_of_L2 (toLp 2 (a, b)))
  have hsqdist :
      ‖toLp 2 (a, b) - toLp 2 (c, d)‖ ^ (2 : ℕ) =
        (a - c) ^ (2 : ℕ) + (b - d) ^ (2 : ℕ) := by
    -- The squared `L²` distance on the pair owner splits into the two scalar squares.
    simpa [a, b, c, d, WithLp.toLp_fst, WithLp.toLp_snd, Prod.fst_sub, Prod.snd_sub,
      Real.norm_eq_abs, sq_abs] using
      (WithLp.prod_norm_sq_eq_of_L2 (toLp 2 (a, b) - toLp 2 (c, d)))
  rw [proximal_objective_apply, norm_penalty_apply, hnorm, hsqdist, EReal.coe_add]

/-- Helper for Proposition 12.4: the interior isotropic algebra combines the rowwise and
columnwise squares in `ℝ` before any `EReal` coercion. -/
lemma interior_norm_proximal_sum_eq_real
    (lam : ℝ) (p u : Hmn) (q v : Vmn) :
    lam *
        (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          Real.sqrt
            ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
              (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) +
      (1 / 2 : ℝ) *
        ((∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
              (u (Fin.castLE (Nat.sub_le m 1) i) j -
                p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
          ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
              (v i (Fin.castLE (Nat.sub_le n 1) j) -
                q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) =
      ∑ i : Fin (m - 1), (lam *
          (∑ j : Fin (n - 1),
            Real.sqrt
              ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
                (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) +
        (1 / 2 : ℝ) *
          ((∑ j : Fin (n - 1),
              (u (Fin.castLE (Nat.sub_le m 1) i) j -
                p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
            ∑ j : Fin (n - 1),
              (v i (Fin.castLE (Nat.sub_le n 1) j) -
                q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) := by
  -- Distribute the outer scalar coefficients across the two finite sums and regroup rowwise.
  have hsplitBC :
      ((∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
            (u (Fin.castLE (Nat.sub_le m 1) i) j -
              p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
          ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
            (v i (Fin.castLE (Nat.sub_le n 1) j) -
              q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) =
        ∑ i : Fin (m - 1),
          ((∑ j : Fin (n - 1),
              (u (Fin.castLE (Nat.sub_le m 1) i) j -
                p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
            ∑ j : Fin (n - 1),
              (v i (Fin.castLE (Nat.sub_le n 1) j) -
                q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) := by
    rw [← Finset.sum_add_distrib]
  calc
    lam *
        (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          Real.sqrt
            ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
              (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) +
      (1 / 2 : ℝ) *
        ((∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
              (u (Fin.castLE (Nat.sub_le m 1) i) j -
                p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
          ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
              (v i (Fin.castLE (Nat.sub_le n 1) j) -
                q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) =
      (∑ i : Fin (m - 1), lam *
          (∑ j : Fin (n - 1),
            Real.sqrt
              ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
                (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)))) +
        (1 / 2 : ℝ) *
          (∑ i : Fin (m - 1),
            ((∑ j : Fin (n - 1),
                (u (Fin.castLE (Nat.sub_le m 1) i) j -
                  p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
              ∑ j : Fin (n - 1),
                (v i (Fin.castLE (Nat.sub_le n 1) j) -
                  q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) := by
            rw [Finset.mul_sum, hsplitBC]
    _ =
      ∑ i : Fin (m - 1), (lam *
          (∑ j : Fin (n - 1),
            Real.sqrt
              ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
                (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) +
        (1 / 2 : ℝ) *
          ((∑ j : Fin (n - 1),
              (u (Fin.castLE (Nat.sub_le m 1) i) j -
                p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
            ∑ j : Fin (n - 1),
              (v i (Fin.castLE (Nat.sub_le n 1) j) -
                q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]

/-- Helper for Proposition 12.4: the rowwise interior isotropic expression is the exact double
sum of the textbook `ℓ²` block summands, still entirely in `ℝ`. -/
lemma interior_rowwise_real_to_blockwise_real_sum_eq
    (lam : ℝ) (p u : Hmn) (q v : Vmn) :
    (∑ i : Fin (m - 1), (lam *
          (∑ j : Fin (n - 1),
            Real.sqrt
              ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
                (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) +
        (1 / 2 : ℝ) *
          ((∑ j : Fin (n - 1),
              (u (Fin.castLE (Nat.sub_le m 1) i) j -
                p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
            ∑ j : Fin (n - 1),
              (v i (Fin.castLE (Nat.sub_le n 1) j) -
                q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)))) =
      ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
        (lam *
            Real.sqrt
              ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
                (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) +
          (1 / 2 : ℝ) *
            (((u (Fin.castLE (Nat.sub_le m 1) i) j -
                p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
              (((v i (Fin.castLE (Nat.sub_le n 1) j) -
                  q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) : ℝ))) := by
  -- Keep the interior regrouping in `ℝ`: distribute the two scalar coefficients rowwise and then
  -- collapse the horizontal/vertical square terms into the exact block summand shape.
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hsquares :
      ((∑ j : Fin (n - 1),
            (u (Fin.castLE (Nat.sub_le m 1) i) j -
              p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
          ∑ j : Fin (n - 1),
            (v i (Fin.castLE (Nat.sub_le n 1) j) -
              q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) =
        ∑ j : Fin (n - 1),
          (((u (Fin.castLE (Nat.sub_le m 1) i) j -
                p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
            ((v i (Fin.castLE (Nat.sub_le n 1) j) -
                q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) : ℝ) := by
    rw [← Finset.sum_add_distrib]
  rw [hsquares, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- Helper for Proposition 12.4: the interior isotropic contribution is exactly the finite sum of
two-dimensional `norm_penalty` proximal blocks. -/
lemma interior_norm_proximal_sum_eq
    (lam : ℝ) (p u : Hmn) (q v : Vmn) :
    ((lam *
          (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
            Real.sqrt
              ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
                (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) : ℝ) : EReal) +
        (((1 / 2 : ℝ) *
              ((∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
                    (u (Fin.castLE (Nat.sub_le m 1) i) j -
                      p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
                ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
                    (v i (Fin.castLE (Nat.sub_le n 1) j) -
                      q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) : ℝ) : EReal) =
      ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
        proximal_objective (norm_penalty lam)
          (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) i) j,
            q i (Fin.castLE (Nat.sub_le n 1) j)))
          (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) i) j,
            v i (Fin.castLE (Nat.sub_le n 1) j))) := by
  -- Route correction: finish the interior normalization in `ℝ` first, then coerce the resulting
  -- exact double sum to `EReal` once and rewrite each summand as a `norm_penalty` block.
  have hreal :
      lam *
          (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
            Real.sqrt
              ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
                (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) +
        (1 / 2 : ℝ) *
          ((∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
                (u (Fin.castLE (Nat.sub_le m 1) i) j -
                  p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
            ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
                (v i (Fin.castLE (Nat.sub_le n 1) j) -
                  q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) =
        ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          (lam *
              Real.sqrt
                ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
                  (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) +
            (1 / 2 : ℝ) *
              (((u (Fin.castLE (Nat.sub_le m 1) i) j -
                    p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
                ((v i (Fin.castLE (Nat.sub_le n 1) j) -
                    q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) : ℝ)) := by
    calc
      lam *
          (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
            Real.sqrt
              ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
                (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) +
        (1 / 2 : ℝ) *
          ((∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
                (u (Fin.castLE (Nat.sub_le m 1) i) j -
                  p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
            ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
                (v i (Fin.castLE (Nat.sub_le n 1) j) -
                  q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) =
          ∑ i : Fin (m - 1), (lam *
              (∑ j : Fin (n - 1),
                Real.sqrt
                  ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
                    (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) +
            (1 / 2 : ℝ) *
              ((∑ j : Fin (n - 1),
                    (u (Fin.castLE (Nat.sub_le m 1) i) j -
                      p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
                ∑ j : Fin (n - 1),
                  (v i (Fin.castLE (Nat.sub_le n 1) j) -
                    q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) := by
            simpa using interior_norm_proximal_sum_eq_real (lam := lam) (p := p) (u := u)
              (q := q) (v := v)
      _ =
          ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
            (lam *
                Real.sqrt
                  ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
                    (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) +
              (1 / 2 : ℝ) *
                (((u (Fin.castLE (Nat.sub_le m 1) i) j -
                      p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
                  ((v i (Fin.castLE (Nat.sub_le n 1) j) -
                      q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) : ℝ)) := by
            simpa using interior_rowwise_real_to_blockwise_real_sum_eq (lam := lam) (p := p)
              (u := u) (q := q) (v := v)
  let interiorNorm : ℝ :=
    lam *
      (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
        Real.sqrt
          ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
            (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)))
  let interiorSq : ℝ :=
    (1 / 2 : ℝ) *
      ((∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
            (u (Fin.castLE (Nat.sub_le m 1) i) j -
              p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
        ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
            (v i (Fin.castLE (Nat.sub_le n 1) j) -
              q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))
  let blockReal : Fin (m - 1) → Fin (n - 1) → ℝ := fun i j ↦
    lam *
        Real.sqrt
          ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
            (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) +
      (1 / 2 : ℝ) *
        (((u (Fin.castLE (Nat.sub_le m 1) i) j -
              p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
          ((v i (Fin.castLE (Nat.sub_le n 1) j) -
              q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) : ℝ)
  have hcombine :
      interiorNorm + interiorSq = ∑ i : Fin (m - 1), ∑ j : Fin (n - 1), blockReal i j := by
    simpa [interiorNorm, interiorSq, blockReal] using hreal
  calc
    ((lam *
          (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
            Real.sqrt
              ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
                (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) : ℝ) : EReal) +
        (((1 / 2 : ℝ) *
              ((∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
                    (u (Fin.castLE (Nat.sub_le m 1) i) j -
                      p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)) +
                ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
                    (v i (Fin.castLE (Nat.sub_le n 1) j) -
                      q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) : ℝ) : EReal) =
        ((interiorNorm : ℝ) : EReal) + ((interiorSq : ℝ) : EReal) := by
          simp [interiorNorm, interiorSq]
    _ = (((interiorNorm + interiorSq : ℝ) : ℝ) : EReal) := by
          rw [EReal.coe_add]
    _ =
        (((∑ i : Fin (m - 1), ∑ j : Fin (n - 1), blockReal i j : ℝ) : ℝ) : EReal) := by
          exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hcombine
    _ =
        ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          ((blockReal i j : ℝ) : EReal) := by
          simpa using
            (ereal_coe_double_sum_local (s := (Finset.univ : Finset (Fin (m - 1))))
              (t := (Finset.univ : Finset (Fin (n - 1))))
              (φ := blockReal))
    _ =
        ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          proximal_objective (norm_penalty lam)
            (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) i) j,
              q i (Fin.castLE (Nat.sub_le n 1) j)))
            (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) i) j,
              v i (Fin.castLE (Nat.sub_le n 1) j))) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          simpa [blockReal] using
            (isotropic_interior_block_proximal_objective_eq
              (lam := lam) (p := p) (u := u) (q := q) (v := v) i j).symm

/-- Helper for Proposition 12.4: the interior isotropic block sum can be treated as one finite
sum over pair indices. -/
lemma interior_norm_proximal_sum_eq_sum_product
    (lam : ℝ) (p u : Hmn) (q v : Vmn) :
    (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
      proximal_objective (norm_penalty lam)
        (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) i) j,
          q i (Fin.castLE (Nat.sub_le n 1) j)))
        (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) i) j,
          v i (Fin.castLE (Nat.sub_le n 1) j)))) =
      ∑ ij : Fin (m - 1) × Fin (n - 1),
        proximal_objective (norm_penalty lam)
          (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2,
            q ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2)))
          (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2,
            v ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2))) := by
  -- Flatten the nested interior sum to a single product index before isolating one active block.
  rw [← Finset.sum_product (s := (Finset.univ : Finset (Fin (m - 1))))
    (t := (Finset.univ : Finset (Fin (n - 1))))
    (f := fun ij : Fin (m - 1) × Fin (n - 1) ↦
      proximal_objective (norm_penalty lam)
        (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2,
          q ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2)))
        (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2,
          v ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2))))]
  simp [Finset.univ_product_univ]

/-- Helper for Proposition 12.4: the full interior isotropic pair-index sum is a finite
real-valued `EReal`. -/
lemma interior_pair_proximal_sum_eq_coe
    (lam : ℝ) (p u : Hmn) (q v : Vmn) :
    ∃ r : ℝ,
      (∑ ij : Fin (m - 1) × Fin (n - 1),
        proximal_objective (norm_penalty lam)
          (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2,
            q ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2)))
          (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2,
            v ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2)))) = (r : EReal) := by
  let r : ℝ :=
    ∑ ij : Fin (m - 1) × Fin (n - 1),
      (lam *
          Real.sqrt
            ((u (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2) ^ (2 : ℕ) +
              (v ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2)) ^ (2 : ℕ)) +
        (1 / 2 : ℝ) *
          (((u (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2 -
                p (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2) ^ (2 : ℕ)) +
            ((v ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2) -
                q ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2)) ^ (2 : ℕ)) : ℝ))
  refine ⟨r, ?_⟩
  -- Rewrite each interior block as a real coercion and push the coercion through the finite sum.
  calc
    (∑ ij : Fin (m - 1) × Fin (n - 1),
        proximal_objective (norm_penalty lam)
          (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2,
            q ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2)))
          (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2,
            v ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2)))) =
      ∑ ij : Fin (m - 1) × Fin (n - 1),
        (((lam *
              Real.sqrt
                ((u (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2) ^ (2 : ℕ) +
                  (v ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2)) ^ (2 : ℕ)) +
            (1 / 2 : ℝ) *
              (((u (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2 -
                    p (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2) ^ (2 : ℕ)) +
                ((v ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2) -
                    q ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2)) ^ (2 : ℕ)) : ℝ) : ℝ)) :
              EReal) := by
            refine Finset.sum_congr rfl ?_
            intro ij hij
            rw [isotropic_interior_block_proximal_objective_eq]
    _ = ((r : ℝ) : EReal) := by
          symm
          exact
            ereal_coe_sum_local (s := (Finset.univ : Finset (Fin (m - 1) × Fin (n - 1))))
              (φ := fun ij ↦
                lam *
                    Real.sqrt
                      ((u (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2) ^ (2 : ℕ) +
                        (v ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2)) ^ (2 : ℕ)) +
                  (1 / 2 : ℝ) *
                    (((u (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2 -
                          p (Fin.castLE (Nat.sub_le m 1) ij.1) ij.2) ^ (2 : ℕ)) +
                      ((v ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2) -
                          q ij.1 (Fin.castLE (Nat.sub_le n 1) ij.2)) ^ (2 : ℕ)) : ℝ))

/-- Helper for Proposition 12.4: the last-row isotropic contribution is exactly the guarded finite
sum of scalar absolute-value proximal blocks. -/
lemma horizontal_boundary_absolute_value_proximal_sum_eq
    (lam : ℝ) (p u : Hmn) :
    ((lam * (∑ i : Fin m, ∑ j : Fin (n - 1),
          if hrow : (i : ℕ) + 1 < m then (0 : ℝ) else |u i j|) : ℝ) : EReal) +
        (((1 / 2 : ℝ) * (∑ i : Fin m, ∑ j : Fin (n - 1),
              if hrow : (i : ℕ) + 1 < m then (0 : ℝ) else (u i j - p i j) ^ (2 : ℕ)) : ℝ) :
          EReal) =
      ∑ i : Fin m, ∑ j : Fin (n - 1),
        if hrow : (i : ℕ) + 1 < m then 0
        else proximal_objective (absolute_value_penalty lam) (p i j) (u i j) := by
  -- Keep the row guard attached to each scalar term until the final `EReal` coercion.
  have hreal :
      lam * (∑ i : Fin m, ∑ j : Fin (n - 1),
            if hrow : (i : ℕ) + 1 < m then (0 : ℝ) else |u i j|) +
          (1 / 2 : ℝ) * (∑ i : Fin m, ∑ j : Fin (n - 1),
            if hrow : (i : ℕ) + 1 < m then (0 : ℝ) else (u i j - p i j) ^ (2 : ℕ)) =
        ∑ i : Fin m, ∑ j : Fin (n - 1),
          if hrow : (i : ℕ) + 1 < m then 0
          else lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) := by
    -- Distribute the prefactors, then collapse the guarded row terms entrywise.
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    by_cases hrow : (i : ℕ) + 1 < m
    · simp [hrow]
    · simp [hrow]
  calc
    ((lam * (∑ i : Fin m, ∑ j : Fin (n - 1),
          if hrow : (i : ℕ) + 1 < m then (0 : ℝ) else |u i j|) : ℝ) : EReal) +
        (((1 / 2 : ℝ) * (∑ i : Fin m, ∑ j : Fin (n - 1),
              if hrow : (i : ℕ) + 1 < m then (0 : ℝ) else (u i j - p i j) ^ (2 : ℕ)) : ℝ) :
          EReal) =
      (((lam * (∑ i : Fin m, ∑ j : Fin (n - 1),
            if hrow : (i : ℕ) + 1 < m then (0 : ℝ) else |u i j|) +
          (1 / 2 : ℝ) * (∑ i : Fin m, ∑ j : Fin (n - 1),
            if hrow : (i : ℕ) + 1 < m then (0 : ℝ) else (u i j - p i j) ^ (2 : ℕ)) : ℝ) :
            EReal)) := by
          rw [EReal.coe_add]
    _ =
      (((∑ i : Fin m, ∑ j : Fin (n - 1),
          if hrow : (i : ℕ) + 1 < m then 0
          else lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ) : EReal)) := by
          exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hreal
    _ =
      ∑ i : Fin m, ∑ j : Fin (n - 1),
        (((if hrow : (i : ℕ) + 1 < m then 0
            else lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ)) : ℝ) : EReal) := by
          simpa using
            (ereal_coe_double_sum_local (s := (Finset.univ : Finset (Fin m)))
              (t := (Finset.univ : Finset (Fin (n - 1))))
              (φ := fun i j ↦
                if hrow : (i : ℕ) + 1 < m then (0 : ℝ)
                else lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ)))
    _ =
      ∑ i : Fin m, ∑ j : Fin (n - 1),
        if hrow : (i : ℕ) + 1 < m then 0
        else proximal_objective (absolute_value_penalty lam) (p i j) (u i j) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          by_cases hrow : (i : ℕ) + 1 < m
          · simpa [hrow]
          · simpa [hrow, proximal_objective_apply, absolute_value_penalty_apply, Real.norm_eq_abs,
              sq_abs, EReal.coe_add]

/-- Helper for Proposition 12.4: the last-column isotropic contribution is exactly the guarded
finite sum of scalar absolute-value proximal blocks. -/
lemma vertical_boundary_absolute_value_proximal_sum_eq
    (lam : ℝ) (q v : Vmn) :
    ((lam * (∑ i : Fin (m - 1), ∑ j : Fin n,
          if hcol : (j : ℕ) + 1 < n then (0 : ℝ) else |v i j|) : ℝ) : EReal) +
        (((1 / 2 : ℝ) * (∑ i : Fin (m - 1), ∑ j : Fin n,
              if hcol : (j : ℕ) + 1 < n then (0 : ℝ) else (v i j - q i j) ^ (2 : ℕ)) : ℝ) :
          EReal) =
      ∑ i : Fin (m - 1), ∑ j : Fin n,
        if hcol : (j : ℕ) + 1 < n then 0
        else proximal_objective (absolute_value_penalty lam) (q i j) (v i j) := by
  -- Keep the column guard attached to each scalar term until the final `EReal` coercion.
  have hreal :
      lam * (∑ i : Fin (m - 1), ∑ j : Fin n,
            if hcol : (j : ℕ) + 1 < n then (0 : ℝ) else |v i j|) +
          (1 / 2 : ℝ) * (∑ i : Fin (m - 1), ∑ j : Fin n,
            if hcol : (j : ℕ) + 1 < n then (0 : ℝ) else (v i j - q i j) ^ (2 : ℕ)) =
        ∑ i : Fin (m - 1), ∑ j : Fin n,
          if hcol : (j : ℕ) + 1 < n then 0
          else lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) := by
    -- Distribute the prefactors, then collapse the guarded column terms entrywise.
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    by_cases hcol : (j : ℕ) + 1 < n
    · simp [hcol]
    · simp [hcol]
  calc
    ((lam * (∑ i : Fin (m - 1), ∑ j : Fin n,
          if hcol : (j : ℕ) + 1 < n then (0 : ℝ) else |v i j|) : ℝ) : EReal) +
        (((1 / 2 : ℝ) * (∑ i : Fin (m - 1), ∑ j : Fin n,
              if hcol : (j : ℕ) + 1 < n then (0 : ℝ) else (v i j - q i j) ^ (2 : ℕ)) : ℝ) :
          EReal) =
      (((lam * (∑ i : Fin (m - 1), ∑ j : Fin n,
            if hcol : (j : ℕ) + 1 < n then (0 : ℝ) else |v i j|) +
          (1 / 2 : ℝ) * (∑ i : Fin (m - 1), ∑ j : Fin n,
            if hcol : (j : ℕ) + 1 < n then (0 : ℝ) else (v i j - q i j) ^ (2 : ℕ)) : ℝ) :
            EReal)) := by
          rw [EReal.coe_add]
    _ =
      (((∑ i : Fin (m - 1), ∑ j : Fin n,
          if hcol : (j : ℕ) + 1 < n then 0
          else lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ) : EReal)) := by
          exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hreal
    _ =
      ∑ i : Fin (m - 1), ∑ j : Fin n,
        (((if hcol : (j : ℕ) + 1 < n then 0
            else lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ)) : ℝ) : EReal) := by
          simpa using
            (ereal_coe_double_sum_local (s := (Finset.univ : Finset (Fin (m - 1))))
              (t := (Finset.univ : Finset (Fin n)))
              (φ := fun i j ↦
                if hcol : (j : ℕ) + 1 < n then (0 : ℝ)
                else lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ)))
    _ =
      ∑ i : Fin (m - 1), ∑ j : Fin n,
        if hcol : (j : ℕ) + 1 < n then 0
        else proximal_objective (absolute_value_penalty lam) (q i j) (v i j) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          by_cases hcol : (j : ℕ) + 1 < n
          · simpa [hcol]
          · simpa [hcol, proximal_objective_apply, absolute_value_penalty_apply, Real.norm_eq_abs,
              sq_abs, EReal.coe_add]

/-- Helper for Proposition 12.4: splitting the horizontal isotropic regularizer across the last
row isolates the interior `ℓ²` blocks from the guarded last-row absolute values. -/
lemma horizontal_isotropic_regularizer_split
    (u : Hmn) (v : Vmn) :
    (∑ i : Fin m, ∑ j : Fin (n - 1),
      if hi : (i : ℕ) + 1 < m then
        Real.sqrt
          ((u i j) ^ (2 : ℕ) +
            (v (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi)) (Fin.castLE (Nat.sub_le n 1) j)) ^
              (2 : ℕ))
      else
        |u i j|) =
      (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
        Real.sqrt
          ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
            (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) +
        ∑ i : Fin m, ∑ j : Fin (n - 1),
          if hrow : (i : ℕ) + 1 < m then (0 : ℝ) else |u i j| := by
  let g : Fin m → ℝ := fun i ↦
    ∑ j : Fin (n - 1),
      if hi : (i : ℕ) + 1 < m then
        Real.sqrt
          ((u i j) ^ (2 : ℕ) +
            (v (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi)) (Fin.castLE (Nat.sub_le n 1) j)) ^
              (2 : ℕ))
      else
        |u i j|
  -- Split only the outer row sum, then normalize the interior row cast before touching `EReal`.
  calc
    (∑ i : Fin m, ∑ j : Fin (n - 1),
        if hi : (i : ℕ) + 1 < m then
          Real.sqrt
            ((u i j) ^ (2 : ℕ) +
              (v (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi)) (Fin.castLE (Nat.sub_le n 1) j)) ^
                (2 : ℕ))
        else
          |u i j|) =
      ∑ i : Fin m, g i := by
        simp [g]
    _ =
        (∑ i : Fin (m - 1), g (Fin.castLE (Nat.sub_le m 1) i)) +
          ∑ i : Fin m, if hrow : (i : ℕ) + 1 < m then 0 else g i := by
        simpa [g] using (fin_sum_split_last (m := m) g)
    _ =
        (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          Real.sqrt
            ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
              (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) +
          ∑ i : Fin m, if hrow : (i : ℕ) + 1 < m then 0 else g i := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro i hi
        -- The embedded interior row satisfies the strict inequality, so the cast back to
        -- `Fin (m - 1)` disappears and the row contributes the Euclidean block.
        have hrow :
            (((Fin.castLE (Nat.sub_le m 1) i : Fin m) : ℕ) + 1 < m) :=
          castLE_row_succ_lt i
        simp only [g]
        simp_rw [dif_pos hrow]
        simp [castLE_row_castLT_eq]
    _ =
        (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          Real.sqrt
            ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
              (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))) +
          ∑ i : Fin m, ∑ j : Fin (n - 1),
            if hrow : (i : ℕ) + 1 < m then (0 : ℝ) else |u i j| := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hrow : (i : ℕ) + 1 < m
        · simp [g, hrow]
        · simp [g, hrow]

/-- Helper for Proposition 12.4: the isotropic TV proximal objective splits into interior
Euclidean blocks and guarded scalar boundary blocks. -/
lemma isotropic_proximal_objective_split
    (lam : ℝ) (p u : Hmn) (q v : Vmn) :
    proximal_objective
        (fun z : TVSpace ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
        (toLp 2 (p, q)) (toLp 2 (u, v)) =
      (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
        proximal_objective (norm_penalty lam)
          (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) i) j,
            q i (Fin.castLE (Nat.sub_le n 1) j)))
          (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) i) j,
            v i (Fin.castLE (Nat.sub_le n 1) j)))) +
        (∑ i : Fin m, ∑ j : Fin (n - 1),
          if hrow : (i : ℕ) + 1 < m then 0
          else proximal_objective (absolute_value_penalty lam) (p i j) (u i j)) +
        ∑ i : Fin (m - 1), ∑ j : Fin n,
          if hcol : (j : ℕ) + 1 < n then 0
          else proximal_objective (absolute_value_penalty lam) (q i j) (v i j) := by
  -- Route correction: isolate the row-split of the isotropic regularizer first, then regroup the
  -- interior and guarded boundary real sums before coercing each finished piece to `EReal`.
  let interiorReg : ℝ :=
    ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
      Real.sqrt
        ((u (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
          (v i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ))
  let horizontalBoundaryReg : ℝ :=
    ∑ i : Fin m, ∑ j : Fin (n - 1),
      if hrow : (i : ℕ) + 1 < m then (0 : ℝ) else |u i j|
  let verticalBoundaryReg : ℝ :=
    ∑ i : Fin (m - 1), ∑ j : Fin n,
      if hcol : (j : ℕ) + 1 < n then (0 : ℝ) else |v i j|
  let interiorHorizontalSq : ℝ :=
    ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
      (u (Fin.castLE (Nat.sub_le m 1) i) j - p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ)
  let horizontalBoundarySq : ℝ :=
    ∑ i : Fin m, ∑ j : Fin (n - 1),
      if hrow : (i : ℕ) + 1 < m then (0 : ℝ) else (u i j - p i j) ^ (2 : ℕ)
  let interiorVerticalSq : ℝ :=
    ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
      (v i (Fin.castLE (Nat.sub_le n 1) j) - q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)
  let verticalBoundarySq : ℝ :=
    ∑ i : Fin (m - 1), ∑ j : Fin n,
      if hcol : (j : ℕ) + 1 < n then (0 : ℝ) else (v i j - q i j) ^ (2 : ℕ)
  let interiorRaw : EReal :=
    ((lam * interiorReg : ℝ) : EReal) +
      (((1 / 2 : ℝ) * (interiorHorizontalSq + interiorVerticalSq) : ℝ) : EReal)
  let horizontalRaw : EReal :=
    ((lam * horizontalBoundaryReg : ℝ) : EReal) +
      (((1 / 2 : ℝ) * horizontalBoundarySq : ℝ) : EReal)
  let verticalRaw : EReal :=
    ((lam * verticalBoundaryReg : ℝ) : EReal) +
      (((1 / 2 : ℝ) * verticalBoundarySq : ℝ) : EReal)
  have hhorizontalSqSplit :
      (∑ i : Fin m, ∑ j : Fin (n - 1), (u i j - p i j) ^ (2 : ℕ)) =
        interiorHorizontalSq + horizontalBoundarySq := by
    let g : Fin m → ℝ := fun i ↦
      ∑ j : Fin (n - 1), (u i j - p i j) ^ (2 : ℕ)
    -- Split the horizontal squared-distance sum across interior rows and the guarded last row.
    calc
      (∑ i : Fin m, ∑ j : Fin (n - 1), (u i j - p i j) ^ (2 : ℕ)) =
          ∑ i : Fin m, g i := by
            simp [g]
      _ =
          (∑ i : Fin (m - 1), g (Fin.castLE (Nat.sub_le m 1) i)) +
            ∑ i : Fin m, if hrow : (i : ℕ) + 1 < m then 0 else g i := by
            simpa [g] using (fin_sum_split_last (m := m) g)
      _ = interiorHorizontalSq + ∑ i : Fin m, if hrow : (i : ℕ) + 1 < m then 0 else g i := by
            simp [g, interiorHorizontalSq]
      _ = interiorHorizontalSq + horizontalBoundarySq := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hrow : (i : ℕ) + 1 < m
            · simp [g, horizontalBoundarySq, hrow]
            · simp [g, horizontalBoundarySq, hrow]
  have hverticalSqSplit :
      (∑ i : Fin (m - 1), ∑ j : Fin n, (v i j - q i j) ^ (2 : ℕ)) =
        interiorVerticalSq + verticalBoundarySq := by
    -- Split each row's vertical squared-distance sum across interior columns and the last column.
    calc
      (∑ i : Fin (m - 1), ∑ j : Fin n, (v i j - q i j) ^ (2 : ℕ)) =
          ∑ i : Fin (m - 1),
            ((∑ j : Fin (n - 1), (v i (Fin.castLE (Nat.sub_le n 1) j) -
                q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ)) +
              ∑ j : Fin n, if hcol : (j : ℕ) + 1 < n then 0 else (v i j - q i j) ^ (2 : ℕ)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using
              (fin_sum_split_last (m := n) (g := fun j : Fin n ↦ (v i j - q i j) ^ (2 : ℕ)))
      _ = interiorVerticalSq + verticalBoundarySq := by
            simp [interiorVerticalSq, verticalBoundarySq, Finset.sum_add_distrib]
  have hreal_reassoc :
      lam * ((interiorReg + horizontalBoundaryReg) + verticalBoundaryReg) +
          (1 / 2 : ℝ) * ((interiorHorizontalSq + horizontalBoundarySq) +
            (interiorVerticalSq + verticalBoundarySq)) =
        (lam * interiorReg + (1 / 2 : ℝ) * (interiorHorizontalSq + interiorVerticalSq)) +
          ((lam * horizontalBoundaryReg + (1 / 2 : ℝ) * horizontalBoundarySq) +
            (lam * verticalBoundaryReg + (1 / 2 : ℝ) * verticalBoundarySq)) := by
    ring
  rw [proximal_objective_apply, two_dimensional_total_variation_isotropic_regularizer_apply,
    tvspace_sqdist_split, horizontal_frobenius_sqdist_eq_entrywise_sum,
    vertical_frobenius_sqdist_eq_entrywise_sum, horizontal_isotropic_regularizer_split,
    hhorizontalSqSplit, hverticalSqSplit]
  calc
    ((lam * ((interiorReg + horizontalBoundaryReg) + verticalBoundaryReg) : ℝ) : EReal) +
        (((1 / 2 : ℝ) *
              ((interiorHorizontalSq + horizontalBoundarySq) +
                (interiorVerticalSq + verticalBoundarySq)) : ℝ) : EReal) =
      interiorRaw + (horizontalRaw + verticalRaw) := by
        calc
          ((lam * ((interiorReg + horizontalBoundaryReg) + verticalBoundaryReg) : ℝ) : EReal) +
              (((1 / 2 : ℝ) *
                    ((interiorHorizontalSq + horizontalBoundarySq) +
                      (interiorVerticalSq + verticalBoundarySq)) : ℝ) : EReal) =
            (((lam * ((interiorReg + horizontalBoundaryReg) + verticalBoundaryReg) +
                  (1 / 2 : ℝ) * ((interiorHorizontalSq + horizontalBoundarySq) +
                    (interiorVerticalSq + verticalBoundarySq)) : ℝ) : EReal)) := by
              rw [EReal.coe_add]
          _ =
            ((((lam * interiorReg + (1 / 2 : ℝ) * (interiorHorizontalSq + interiorVerticalSq)) +
                  ((lam * horizontalBoundaryReg + (1 / 2 : ℝ) * horizontalBoundarySq) +
                    (lam * verticalBoundaryReg + (1 / 2 : ℝ) * verticalBoundarySq)) : ℝ) :
                  EReal)) := by
              exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hreal_reassoc
          _ = interiorRaw + (horizontalRaw + verticalRaw) := by
              simp [interiorRaw, horizontalRaw, verticalRaw, EReal.coe_add, add_assoc]
    _ =
        (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          proximal_objective (norm_penalty lam)
            (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) i) j,
              q i (Fin.castLE (Nat.sub_le n 1) j)))
            (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) i) j,
              v i (Fin.castLE (Nat.sub_le n 1) j)))) +
          (horizontalRaw + verticalRaw) := by
          exact
            congrArg
              (fun t : EReal ↦ t + (horizontalRaw + verticalRaw))
              (by
                simpa [interiorRaw, interiorReg, interiorHorizontalSq, interiorVerticalSq] using
                  (interior_norm_proximal_sum_eq (lam := lam) (p := p) (u := u) (q := q)
                    (v := v)))
    _ =
        (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          proximal_objective (norm_penalty lam)
            (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) i) j,
              q i (Fin.castLE (Nat.sub_le n 1) j)))
            (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) i) j,
              v i (Fin.castLE (Nat.sub_le n 1) j)))) +
          ((∑ i : Fin m, ∑ j : Fin (n - 1),
              if hrow : (i : ℕ) + 1 < m then 0
              else proximal_objective (absolute_value_penalty lam) (p i j) (u i j)) +
            verticalRaw) := by
          exact
            congrArg
              (fun t : EReal ↦
                (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
                  proximal_objective (norm_penalty lam)
                    (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) i) j,
                      q i (Fin.castLE (Nat.sub_le n 1) j)))
                    (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) i) j,
                      v i (Fin.castLE (Nat.sub_le n 1) j)))) +
                  (t + verticalRaw))
              (by
                simpa [horizontalRaw, horizontalBoundaryReg, horizontalBoundarySq] using
                  (horizontal_boundary_absolute_value_proximal_sum_eq (lam := lam) (p := p)
                    (u := u)))
    _ =
        (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          proximal_objective (norm_penalty lam)
            (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) i) j,
              q i (Fin.castLE (Nat.sub_le n 1) j)))
            (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) i) j,
              v i (Fin.castLE (Nat.sub_le n 1) j)))) +
          ((∑ i : Fin m, ∑ j : Fin (n - 1),
              if hrow : (i : ℕ) + 1 < m then 0
              else proximal_objective (absolute_value_penalty lam) (p i j) (u i j)) +
            ∑ i : Fin (m - 1), ∑ j : Fin n,
              if hcol : (j : ℕ) + 1 < n then 0
              else proximal_objective (absolute_value_penalty lam) (q i j) (v i j)) := by
          exact
            congrArg
              (fun t : EReal ↦
                (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
                  proximal_objective (norm_penalty lam)
                    (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) i) j,
                      q i (Fin.castLE (Nat.sub_le n 1) j)))
                    (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) i) j,
                      v i (Fin.castLE (Nat.sub_le n 1) j)))) +
                  ((∑ i : Fin m, ∑ j : Fin (n - 1),
                      if hrow : (i : ℕ) + 1 < m then 0
                      else proximal_objective (absolute_value_penalty lam) (p i j) (u i j)) +
                    t))
              (by
                simpa [verticalRaw, verticalBoundaryReg, verticalBoundarySq] using
                  (vertical_boundary_absolute_value_proximal_sum_eq (lam := lam) (q := q)
                    (v := v)))
    _ =
        (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          proximal_objective (norm_penalty lam)
            (toLp 2 (p (Fin.castLE (Nat.sub_le m 1) i) j,
              q i (Fin.castLE (Nat.sub_le n 1) j)))
            (toLp 2 (u (Fin.castLE (Nat.sub_le m 1) i) j,
              v i (Fin.castLE (Nat.sub_le n 1) j)))) +
          (∑ i : Fin m, ∑ j : Fin (n - 1),
            if hrow : (i : ℕ) + 1 < m then 0
            else proximal_objective (absolute_value_penalty lam) (p i j) (u i j)) +
          ∑ i : Fin (m - 1), ∑ j : Fin n,
            if hcol : (j : ℕ) + 1 < n then 0
            else proximal_objective (absolute_value_penalty lam) (q i j) (v i j) := by
          simp [add_assoc]


/-- Helper for Proposition 12.4: the horizontal anisotropic contribution is exactly the finite sum
of scalar absolute-value proximal objectives. -/
lemma horizontal_absolute_value_proximal_sum_eq
    (lam : ℝ) (p u : Hmn) :
    ((lam * (∑ i : Fin m, ∑ j : Fin (n - 1), |u i j|) : ℝ) : EReal) +
        (((1 / 2 : ℝ) * (∑ i : Fin m, ∑ j : Fin (n - 1), (u i j - p i j) ^ (2 : ℕ)) : ℝ) :
          EReal) =
      ∑ i : Fin m, ∑ j : Fin (n - 1),
        proximal_objective (absolute_value_penalty lam) (p i j) (u i j) := by
  -- Route correction: normalize the real double sums first, then push one coercion into `EReal`
  -- instead of asking `simp` to reassociate the whole extended-real expression at once.
  have hreal :
      lam * (∑ i : Fin m, ∑ j : Fin (n - 1), |u i j|) +
          (1 / 2 : ℝ) * (∑ i : Fin m, ∑ j : Fin (n - 1), (u i j - p i j) ^ (2 : ℕ)) =
        ∑ i : Fin m, ∑ j : Fin (n - 1),
          (lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ)) := by
    -- Distribute the two scalar prefactors over the nested finite sums before regrouping terms.
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← Finset.sum_add_distrib]
  calc
    ((lam * (∑ i : Fin m, ∑ j : Fin (n - 1), |u i j|) : ℝ) : EReal) +
        (((1 / 2 : ℝ) * (∑ i : Fin m, ∑ j : Fin (n - 1), (u i j - p i j) ^ (2 : ℕ)) : ℝ) :
          EReal) =
      (((lam * (∑ i : Fin m, ∑ j : Fin (n - 1), |u i j|) +
          (1 / 2 : ℝ) * (∑ i : Fin m, ∑ j : Fin (n - 1), (u i j - p i j) ^ (2 : ℕ)) : ℝ) :
            EReal)) := by
          rw [EReal.coe_add]
    _ = (((∑ i : Fin m, ∑ j : Fin (n - 1),
          (lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ)) : ℝ) : EReal)) := by
          exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hreal
    _ = ∑ i : Fin m, ∑ j : Fin (n - 1),
          (((lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) : EReal) := by
          simpa using
            (ereal_coe_double_sum_local (s := (Finset.univ : Finset (Fin m)))
              (t := (Finset.univ : Finset (Fin (n - 1))))
              (φ := fun i j ↦ lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ)))
    _ = ∑ i : Fin m, ∑ j : Fin (n - 1),
          proximal_objective (absolute_value_penalty lam) (p i j) (u i j) := by
          -- Each summand is exactly the scalar proximal objective from Example 6.8.
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [proximal_objective_apply, absolute_value_penalty_apply, Real.norm_eq_abs, sq_abs,
            EReal.coe_add]

/-- Helper for Proposition 12.4: the vertical anisotropic contribution is exactly the finite sum
of scalar absolute-value proximal objectives. -/
lemma vertical_absolute_value_proximal_sum_eq
    (lam : ℝ) (q v : Vmn) :
    ((lam * (∑ i : Fin (m - 1), ∑ j : Fin n, |v i j|) : ℝ) : EReal) +
        (((1 / 2 : ℝ) * (∑ i : Fin (m - 1), ∑ j : Fin n, (v i j - q i j) ^ (2 : ℕ)) : ℝ) :
          EReal) =
      ∑ i : Fin (m - 1), ∑ j : Fin n,
        proximal_objective (absolute_value_penalty lam) (q i j) (v i j) := by
  -- As in the horizontal case, keep the algebra in `ℝ` until the last coercion to `EReal`.
  have hreal :
      lam * (∑ i : Fin (m - 1), ∑ j : Fin n, |v i j|) +
          (1 / 2 : ℝ) * (∑ i : Fin (m - 1), ∑ j : Fin n, (v i j - q i j) ^ (2 : ℕ)) =
        ∑ i : Fin (m - 1), ∑ j : Fin n,
          (lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ)) := by
    -- Distribute the scalar prefactors over the two nested finite sums, then regroup entrywise.
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← Finset.sum_add_distrib]
  calc
    ((lam * (∑ i : Fin (m - 1), ∑ j : Fin n, |v i j|) : ℝ) : EReal) +
        (((1 / 2 : ℝ) * (∑ i : Fin (m - 1), ∑ j : Fin n, (v i j - q i j) ^ (2 : ℕ)) : ℝ) :
          EReal) =
      (((lam * (∑ i : Fin (m - 1), ∑ j : Fin n, |v i j|) +
          (1 / 2 : ℝ) * (∑ i : Fin (m - 1), ∑ j : Fin n, (v i j - q i j) ^ (2 : ℕ)) : ℝ) :
            EReal)) := by
          rw [EReal.coe_add]
    _ = (((∑ i : Fin (m - 1), ∑ j : Fin n,
          (lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ)) : ℝ) : EReal)) := by
          exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hreal
    _ = ∑ i : Fin (m - 1), ∑ j : Fin n,
          (((lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)) : EReal) := by
          simpa using
            (ereal_coe_double_sum_local (s := (Finset.univ : Finset (Fin (m - 1))))
              (t := (Finset.univ : Finset (Fin n)))
              (φ := fun i j ↦ lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ)))
    _ = ∑ i : Fin (m - 1), ∑ j : Fin n,
          proximal_objective (absolute_value_penalty lam) (q i j) (v i j) := by
          -- Each vertical summand is the same scalar soft-thresholding proximal objective.
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [proximal_objective_apply, absolute_value_penalty_apply, Real.norm_eq_abs, sq_abs,
            EReal.coe_add]

/-- Helper for Proposition 12.4: the anisotropic TV proximal objective splits into independent
scalar absolute-value proximal objectives over all horizontal and vertical entries. -/
lemma anisotropic_proximal_objective_split
    (lam : ℝ) (p u : Hmn) (q v : Vmn) :
    proximal_objective
        (fun z : TVSpace ↦ ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
        (toLp 2 (p, q)) (toLp 2 (u, v)) =
      (∑ i : Fin m, ∑ j : Fin (n - 1),
        proximal_objective (absolute_value_penalty lam) (p i j) (u i j)) +
      ∑ i : Fin (m - 1), ∑ j : Fin n,
        proximal_objective (absolute_value_penalty lam) (q i j) (v i j) := by
  -- Route correction: first split the global TV-space objective into horizontal and vertical
  -- real sums, then invoke the two scalar normalization lemmas instead of reassociating in
  -- one large `EReal` expression.
  rw [proximal_objective_apply, two_dimensional_total_variation_anisotropic_regularizer_apply,
    tvspace_sqdist_split, horizontal_frobenius_sqdist_eq_entrywise_sum,
    vertical_frobenius_sqdist_eq_entrywise_sum]
  calc
    ((lam *
          ((∑ i : Fin m, ∑ j : Fin (n - 1), |u i j|) +
            ∑ i : Fin (m - 1), ∑ j : Fin n, |v i j|) : ℝ) : EReal) +
        (((1 / 2 : ℝ) *
              ((∑ i : Fin m, ∑ j : Fin (n - 1), (u i j - p i j) ^ (2 : ℕ)) +
                ∑ i : Fin (m - 1), ∑ j : Fin n, (v i j - q i j) ^ (2 : ℕ)) : ℝ) : EReal) =
      (((lam * (∑ i : Fin m, ∑ j : Fin (n - 1), |u i j|) : ℝ) : EReal) +
          (((1 / 2 : ℝ) *
                (∑ i : Fin m, ∑ j : Fin (n - 1), (u i j - p i j) ^ (2 : ℕ)) : ℝ) : EReal)) +
        (((lam * (∑ i : Fin (m - 1), ∑ j : Fin n, |v i j|) : ℝ) : EReal) +
          (((1 / 2 : ℝ) *
                (∑ i : Fin (m - 1), ∑ j : Fin n, (v i j - q i j) ^ (2 : ℕ)) : ℝ) : EReal)) := by
          rw [mul_add, mul_add, EReal.coe_add, EReal.coe_add]
          let a : EReal :=
            ((lam * (∑ i : Fin m, ∑ j : Fin (n - 1), |u i j|) : ℝ) : EReal)
          let b : EReal :=
            ((lam * (∑ i : Fin (m - 1), ∑ j : Fin n, |v i j|) : ℝ) : EReal)
          let c : EReal :=
            ((((∑ i : Fin m, ∑ j : Fin (n - 1), (u i j - p i j) ^ (2 : ℕ)) : ℝ) *
                (1 / 2 : ℝ)) : EReal)
          let d : EReal :=
            ((((∑ i : Fin (m - 1), ∑ j : Fin n, (v i j - q i j) ^ (2 : ℕ)) : ℝ) *
                (1 / 2 : ℝ)) : EReal)
          have h_reassoc : a + b + (c + d) = a + c + (b + d) := by
            calc
              a + b + (c + d) = a + (b + (c + d)) := by rw [add_assoc]
              _ = a + (c + (b + d)) := by
                    congr 1
                    calc
                      b + (c + d) = (b + c) + d := by rw [← add_assoc]
                      _ = (c + b) + d := by rw [add_comm b c]
                      _ = c + (b + d) := by rw [add_assoc]
              _ = a + c + (b + d) := by rw [add_assoc]
          simpa [a, b, c, d, mul_comm, mul_left_comm, mul_assoc] using h_reassoc
    _ =
        (∑ i : Fin m, ∑ j : Fin (n - 1),
          proximal_objective (absolute_value_penalty lam) (p i j) (u i j)) +
        (((lam * (∑ i : Fin (m - 1), ∑ j : Fin n, |v i j|) : ℝ) : EReal) +
          (((1 / 2 : ℝ) *
                (∑ i : Fin (m - 1), ∑ j : Fin n, (v i j - q i j) ^ (2 : ℕ)) : ℝ) :
            EReal)) := by
          exact
            congrArg
              (fun t : EReal ↦
                t +
                  (((lam * (∑ i : Fin (m - 1), ∑ j : Fin n, |v i j|) : ℝ) : EReal) +
                    (((1 / 2 : ℝ) *
                          (∑ i : Fin (m - 1), ∑ j : Fin n, (v i j - q i j) ^ (2 : ℕ)) : ℝ) :
                      EReal)))
              (horizontal_absolute_value_proximal_sum_eq lam p u)
    _ =
        (∑ i : Fin m, ∑ j : Fin (n - 1),
          proximal_objective (absolute_value_penalty lam) (p i j) (u i j)) +
        ∑ i : Fin (m - 1), ∑ j : Fin n,
          proximal_objective (absolute_value_penalty lam) (q i j) (v i j) := by
          exact
            congrArg
              (fun t : EReal ↦
                (∑ i : Fin m, ∑ j : Fin (n - 1),
                  proximal_objective (absolute_value_penalty lam) (p i j) (u i j)) +
                  t)
              (vertical_absolute_value_proximal_sum_eq lam q v)

/-- Helper for Proposition 12.4: each scalar anisotropic proximal summand is a finite real-valued
extended-real expression. -/
lemma absolute_value_proximal_objective_eq_coe
    (lam a u : ℝ) :
    proximal_objective (absolute_value_penalty lam) a u =
      (((lam * |u| + (1 / 2 : ℝ) * (u - a) ^ (2 : ℕ) : ℝ)) : EReal) := by
  -- Unfold the scalar proximal objective and rewrite its norm term with the absolute value.
  simp [proximal_objective_apply, absolute_value_penalty_apply, Real.norm_eq_abs, sq_abs,
    EReal.coe_add]

/-- Helper for Proposition 12.4: every scalar anisotropic proximal block stays away from `⊥`. -/
lemma absolute_value_proximal_objective_ne_bot
    (lam a u : ℝ) :
    proximal_objective (absolute_value_penalty lam) a u ≠ ⊥ := by
  -- The scalar proximal objective is literally a real number coerced into `EReal`.
  rw [proximal_objective_apply, absolute_value_penalty_apply]
  exact EReal.add_ne_bot_iff.2 ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _⟩

/-- Helper for Proposition 12.4: every scalar anisotropic proximal block stays strictly below
`⊤`. -/
lemma absolute_value_proximal_objective_lt_top
    (lam a u : ℝ) :
    proximal_objective (absolute_value_penalty lam) a u < ⊤ := by
  -- The same coercion-to-`EReal` description shows the scalar block is finite.
  rw [proximal_objective_apply, absolute_value_penalty_apply]
  exact EReal.add_lt_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)

/-- Helper for Proposition 12.4: the horizontal anisotropic sum can be treated as one finite sum
over pair indices. -/
lemma horizontal_absolute_value_proximal_sum_eq_sum_product
    (lam : ℝ) (p u : Hmn) :
    (∑ i : Fin m, ∑ j : Fin (n - 1),
      proximal_objective (absolute_value_penalty lam) (p i j) (u i j)) =
      ∑ ij : Fin m × Fin (n - 1),
        proximal_objective (absolute_value_penalty lam) (p ij.1 ij.2) (u ij.1 ij.2) := by
  -- Collapse the nested matrix sum to a single finite sum indexed by coordinate pairs.
  rw [← Finset.sum_product (s := (Finset.univ : Finset (Fin m)))
    (t := (Finset.univ : Finset (Fin (n - 1))))
    (f := fun ij : Fin m × Fin (n - 1) ↦
      proximal_objective (absolute_value_penalty lam) (p ij.1 ij.2) (u ij.1 ij.2))]
  simp [Finset.univ_product_univ]

/-- Helper for Proposition 12.4: the vertical anisotropic sum can be treated as one finite sum
over pair indices. -/
lemma vertical_absolute_value_proximal_sum_eq_sum_product
    (lam : ℝ) (q v : Vmn) :
    (∑ i : Fin (m - 1), ∑ j : Fin n,
      proximal_objective (absolute_value_penalty lam) (q i j) (v i j)) =
      ∑ ij : Fin (m - 1) × Fin n,
        proximal_objective (absolute_value_penalty lam) (q ij.1 ij.2) (v ij.1 ij.2) := by
  -- Collapse the nested matrix sum to a single finite sum indexed by coordinate pairs.
  rw [← Finset.sum_product (s := (Finset.univ : Finset (Fin (m - 1))))
    (t := (Finset.univ : Finset (Fin n)))
    (f := fun ij : Fin (m - 1) × Fin n ↦
      proximal_objective (absolute_value_penalty lam) (q ij.1 ij.2) (v ij.1 ij.2))]
  simp [Finset.univ_product_univ]

/-- Helper for Proposition 12.4: the full horizontal pair-index sum of scalar anisotropic
proximal blocks is a finite real-valued `EReal`. -/
lemma horizontal_pair_proximal_sum_eq_coe
    (lam : ℝ) (p u : Hmn) :
    ∃ r : ℝ,
      (∑ ij : Fin m × Fin (n - 1),
        proximal_objective (absolute_value_penalty lam) (p ij.1 ij.2) (u ij.1 ij.2)) = (r : EReal) := by
  refine ⟨∑ ij : Fin m × Fin (n - 1),
      (lam * |u ij.1 ij.2| + (1 / 2 : ℝ) * (u ij.1 ij.2 - p ij.1 ij.2) ^ (2 : ℕ)), ?_⟩
  -- Rewrite each scalar block as a real coercion and push the coercion through the finite sum.
  calc
    (∑ ij : Fin m × Fin (n - 1),
        proximal_objective (absolute_value_penalty lam) (p ij.1 ij.2) (u ij.1 ij.2)) =
      ∑ ij : Fin m × Fin (n - 1),
        (((lam * |u ij.1 ij.2| + (1 / 2 : ℝ) * (u ij.1 ij.2 - p ij.1 ij.2) ^ (2 : ℕ) : ℝ)) :
          EReal) := by
            refine Finset.sum_congr rfl ?_
            intro ij hij
            rw [absolute_value_proximal_objective_eq_coe]
    _ =
      (((∑ ij : Fin m × Fin (n - 1),
          (lam * |u ij.1 ij.2| + (1 / 2 : ℝ) * (u ij.1 ij.2 - p ij.1 ij.2) ^ (2 : ℕ)) : ℝ)) :
            EReal) := by
          symm
          exact
            ereal_coe_sum_local (s := (Finset.univ : Finset (Fin m × Fin (n - 1))))
              (φ := fun ij ↦
                lam * |u ij.1 ij.2| + (1 / 2 : ℝ) * (u ij.1 ij.2 - p ij.1 ij.2) ^ (2 : ℕ))

/-- Helper for Proposition 12.4: the full vertical pair-index sum of scalar anisotropic proximal
blocks is a finite real-valued `EReal`. -/
lemma vertical_pair_proximal_sum_eq_coe
    (lam : ℝ) (q v : Vmn) :
    ∃ r : ℝ,
      (∑ ij : Fin (m - 1) × Fin n,
        proximal_objective (absolute_value_penalty lam) (q ij.1 ij.2) (v ij.1 ij.2)) = (r : EReal) := by
  refine ⟨∑ ij : Fin (m - 1) × Fin n,
      (lam * |v ij.1 ij.2| + (1 / 2 : ℝ) * (v ij.1 ij.2 - q ij.1 ij.2) ^ (2 : ℕ)), ?_⟩
  -- Rewrite each scalar block as a real coercion and push the coercion through the finite sum.
  calc
    (∑ ij : Fin (m - 1) × Fin n,
        proximal_objective (absolute_value_penalty lam) (q ij.1 ij.2) (v ij.1 ij.2)) =
      ∑ ij : Fin (m - 1) × Fin n,
        (((lam * |v ij.1 ij.2| + (1 / 2 : ℝ) * (v ij.1 ij.2 - q ij.1 ij.2) ^ (2 : ℕ) : ℝ)) :
          EReal) := by
            refine Finset.sum_congr rfl ?_
            intro ij hij
            rw [absolute_value_proximal_objective_eq_coe]
    _ =
      (((∑ ij : Fin (m - 1) × Fin n,
          (lam * |v ij.1 ij.2| + (1 / 2 : ℝ) * (v ij.1 ij.2 - q ij.1 ij.2) ^ (2 : ℕ)) : ℝ)) :
            EReal) := by
          symm
          exact
            ereal_coe_sum_local (s := (Finset.univ : Finset (Fin (m - 1) × Fin n)))
              (φ := fun ij ↦
                lam * |v ij.1 ij.2| + (1 / 2 : ℝ) * (v ij.1 ij.2 - q ij.1 ij.2) ^ (2 : ℕ))

/-- Helper for Proposition 12.4: after updating one horizontal entry, the horizontal pair-index
sum splits into the updated scalar block plus an unchanged finite remainder. -/
lemma horizontal_update_pair_sum_cancellation
    (lam : ℝ) (p u : Hmn) (ij : Fin m × Fin (n - 1)) (t : ℝ) :
    let u' : Hmn := Function.update u ij.1 (Function.update (u ij.1) ij.2 t)
    ∃ r : ℝ,
      (∑ k : Fin m × Fin (n - 1),
        proximal_objective (absolute_value_penalty lam) (p k.1 k.2) (u' k.1 k.2)) =
          proximal_objective (absolute_value_penalty lam) (p ij.1 ij.2) t + (r : EReal) ∧
      (∑ k : Fin m × Fin (n - 1),
        proximal_objective (absolute_value_penalty lam) (p k.1 k.2) (u k.1 k.2)) =
          proximal_objective (absolute_value_penalty lam) (p ij.1 ij.2) (u ij.1 ij.2) + (r : EReal) := by
  classical
  dsimp
  let s : Finset (Fin m × Fin (n - 1)) := Finset.univ.erase ij
  let r : ℝ :=
    ∑ k ∈ s, (lam * |u k.1 k.2| + (1 / 2 : ℝ) * (u k.1 k.2 - p k.1 k.2) ^ (2 : ℕ))
  refine ⟨r, ?_, ?_⟩
  have hrest_u :
      (∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (p k.1 k.2) (u k.1 k.2)) =
        (r : EReal) := by
    -- Package the inactive horizontal remainder as a real finite sum.
    calc
      (∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (p k.1 k.2) (u k.1 k.2)) =
          ∑ k ∈ s,
            (((lam * |u k.1 k.2| + (1 / 2 : ℝ) * (u k.1 k.2 - p k.1 k.2) ^ (2 : ℕ) : ℝ)) :
              EReal) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                rw [absolute_value_proximal_objective_eq_coe]
      _ =
          (((∑ k ∈ s,
              (lam * |u k.1 k.2| + (1 / 2 : ℝ) * (u k.1 k.2 - p k.1 k.2) ^ (2 : ℕ)) : ℝ)) :
                EReal) := by
              symm
              exact
                ereal_coe_sum_local (s := s)
                  (φ := fun k ↦
                    lam * |u k.1 k.2| + (1 / 2 : ℝ) * (u k.1 k.2 - p k.1 k.2) ^ (2 : ℕ))
      _ = (r : EReal) := by simp [r]
  have hrest_u' :
      (∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (p k.1 k.2)
        ((Function.update u ij.1 (Function.update (u ij.1) ij.2 t)) k.1 k.2)) =
        (r : EReal) := by
    -- Away from the updated entry, the horizontal matrix is unchanged.
    calc
      (∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (p k.1 k.2)
        ((Function.update u ij.1 (Function.update (u ij.1) ij.2 t)) k.1 k.2)) =
          ∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (p k.1 k.2) (u k.1 k.2) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hk_ne : k ≠ ij := (Finset.mem_erase.mp hk).1
            by_cases hrow : k.1 = ij.1
            · have hcol : k.2 ≠ ij.2 := by
                intro hcol
                apply hk_ne
                exact Prod.ext hrow hcol
              simp [Function.update, hrow, hcol]
            · simp [Function.update, hrow]
      _ = (r : EReal) := hrest_u
  · -- Split off the updated horizontal entry and reuse the common inactive remainder.
    calc
      (∑ k : Fin m × Fin (n - 1),
          proximal_objective (absolute_value_penalty lam) (p k.1 k.2)
            ((Function.update u ij.1 (Function.update (u ij.1) ij.2 t)) k.1 k.2)) =
        proximal_objective (absolute_value_penalty lam) (p ij.1 ij.2)
            ((Function.update u ij.1 (Function.update (u ij.1) ij.2 t)) ij.1 ij.2) +
          ∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (p k.1 k.2)
            ((Function.update u ij.1 (Function.update (u ij.1) ij.2 t)) k.1 k.2) := by
              symm
              exact Finset.add_sum_erase (Finset.univ : Finset (Fin m × Fin (n - 1)))
                (fun k ↦
                  proximal_objective (absolute_value_penalty lam) (p k.1 k.2)
                    ((Function.update u ij.1 (Function.update (u ij.1) ij.2 t)) k.1 k.2))
                (Finset.mem_univ ij)
      _ = proximal_objective (absolute_value_penalty lam) (p ij.1 ij.2) t +
          ∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (p k.1 k.2)
            ((Function.update u ij.1 (Function.update (u ij.1) ij.2 t)) k.1 k.2) := by
              simp [Function.update]
      _ = proximal_objective (absolute_value_penalty lam) (p ij.1 ij.2) t + (r : EReal) := by
            rw [hrest_u']
  · -- The same split at the original point keeps exactly the same inactive remainder.
    calc
      (∑ k : Fin m × Fin (n - 1),
          proximal_objective (absolute_value_penalty lam) (p k.1 k.2) (u k.1 k.2)) =
        proximal_objective (absolute_value_penalty lam) (p ij.1 ij.2) (u ij.1 ij.2) +
          ∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (p k.1 k.2) (u k.1 k.2) := by
              symm
              exact Finset.add_sum_erase (Finset.univ : Finset (Fin m × Fin (n - 1)))
                (fun k ↦ proximal_objective (absolute_value_penalty lam) (p k.1 k.2) (u k.1 k.2))
                (Finset.mem_univ ij)
      _ = proximal_objective (absolute_value_penalty lam) (p ij.1 ij.2) (u ij.1 ij.2) +
          (r : EReal) := by
            have hrest_u_second :
                (∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (p k.1 k.2) (u k.1 k.2)) =
                  (r : EReal) := by
              calc
                (∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (p k.1 k.2) (u k.1 k.2)) =
                    ∑ k ∈ s,
                      (((lam * |u k.1 k.2| + (1 / 2 : ℝ) * (u k.1 k.2 - p k.1 k.2) ^ (2 : ℕ) : ℝ)) :
                        EReal) := by
                          refine Finset.sum_congr rfl ?_
                          intro k hk
                          rw [absolute_value_proximal_objective_eq_coe]
                _ =
                    (((∑ k ∈ s,
                        (lam * |u k.1 k.2| + (1 / 2 : ℝ) * (u k.1 k.2 - p k.1 k.2) ^ (2 : ℕ)) : ℝ)) :
                          EReal) := by
                        symm
                        exact
                          ereal_coe_sum_local (s := s)
                            (φ := fun k ↦
                              lam * |u k.1 k.2| + (1 / 2 : ℝ) * (u k.1 k.2 - p k.1 k.2) ^ (2 : ℕ))
                _ = (r : EReal) := by simp [r]
            exact congrArg
              (fun s : EReal ↦
                proximal_objective (absolute_value_penalty lam) (p ij.1 ij.2) (u ij.1 ij.2) + s)
              hrest_u_second

/-- Helper for Proposition 12.4: after updating one vertical entry, the vertical pair-index sum
splits into the updated scalar block plus an unchanged finite remainder. -/
lemma vertical_update_pair_sum_cancellation
    (lam : ℝ) (q v : Vmn) (ij : Fin (m - 1) × Fin n) (t : ℝ) :
    let v' : Vmn := Function.update v ij.1 (Function.update (v ij.1) ij.2 t)
    ∃ r : ℝ,
      (∑ k : Fin (m - 1) × Fin n,
        proximal_objective (absolute_value_penalty lam) (q k.1 k.2) (v' k.1 k.2)) =
          proximal_objective (absolute_value_penalty lam) (q ij.1 ij.2) t + (r : EReal) ∧
      (∑ k : Fin (m - 1) × Fin n,
        proximal_objective (absolute_value_penalty lam) (q k.1 k.2) (v k.1 k.2)) =
          proximal_objective (absolute_value_penalty lam) (q ij.1 ij.2) (v ij.1 ij.2) + (r : EReal) := by
  classical
  dsimp
  let s : Finset (Fin (m - 1) × Fin n) := Finset.univ.erase ij
  let r : ℝ :=
    ∑ k ∈ s, (lam * |v k.1 k.2| + (1 / 2 : ℝ) * (v k.1 k.2 - q k.1 k.2) ^ (2 : ℕ))
  refine ⟨r, ?_, ?_⟩
  have hrest_v :
      (∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (q k.1 k.2) (v k.1 k.2)) =
        (r : EReal) := by
    -- Package the inactive vertical remainder as a real finite sum.
    calc
      (∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (q k.1 k.2) (v k.1 k.2)) =
          ∑ k ∈ s,
            (((lam * |v k.1 k.2| + (1 / 2 : ℝ) * (v k.1 k.2 - q k.1 k.2) ^ (2 : ℕ) : ℝ)) :
              EReal) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                rw [absolute_value_proximal_objective_eq_coe]
      _ =
          (((∑ k ∈ s,
              (lam * |v k.1 k.2| + (1 / 2 : ℝ) * (v k.1 k.2 - q k.1 k.2) ^ (2 : ℕ)) : ℝ)) :
                EReal) := by
              symm
              exact
                ereal_coe_sum_local (s := s)
                  (φ := fun k ↦
                    lam * |v k.1 k.2| + (1 / 2 : ℝ) * (v k.1 k.2 - q k.1 k.2) ^ (2 : ℕ))
      _ = (r : EReal) := by simp [r]
  have hrest_v' :
      (∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (q k.1 k.2)
        ((Function.update v ij.1 (Function.update (v ij.1) ij.2 t)) k.1 k.2)) =
        (r : EReal) := by
    -- Away from the updated entry, the vertical matrix is unchanged.
    calc
      (∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (q k.1 k.2)
        ((Function.update v ij.1 (Function.update (v ij.1) ij.2 t)) k.1 k.2)) =
          ∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (q k.1 k.2) (v k.1 k.2) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hk_ne : k ≠ ij := (Finset.mem_erase.mp hk).1
            by_cases hrow : k.1 = ij.1
            · have hcol : k.2 ≠ ij.2 := by
                intro hcol
                apply hk_ne
                exact Prod.ext hrow hcol
              simp [Function.update, hrow, hcol]
            · simp [Function.update, hrow]
      _ = (r : EReal) := hrest_v
  · -- Split off the updated vertical entry and reuse the common inactive remainder.
    calc
      (∑ k : Fin (m - 1) × Fin n,
          proximal_objective (absolute_value_penalty lam) (q k.1 k.2)
            ((Function.update v ij.1 (Function.update (v ij.1) ij.2 t)) k.1 k.2)) =
        proximal_objective (absolute_value_penalty lam) (q ij.1 ij.2)
            ((Function.update v ij.1 (Function.update (v ij.1) ij.2 t)) ij.1 ij.2) +
          ∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (q k.1 k.2)
            ((Function.update v ij.1 (Function.update (v ij.1) ij.2 t)) k.1 k.2) := by
              symm
              exact Finset.add_sum_erase (Finset.univ : Finset (Fin (m - 1) × Fin n))
                (fun k ↦
                  proximal_objective (absolute_value_penalty lam) (q k.1 k.2)
                    ((Function.update v ij.1 (Function.update (v ij.1) ij.2 t)) k.1 k.2))
                (Finset.mem_univ ij)
      _ = proximal_objective (absolute_value_penalty lam) (q ij.1 ij.2) t +
          ∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (q k.1 k.2)
            ((Function.update v ij.1 (Function.update (v ij.1) ij.2 t)) k.1 k.2) := by
              simp [Function.update]
      _ = proximal_objective (absolute_value_penalty lam) (q ij.1 ij.2) t + (r : EReal) := by
            rw [hrest_v']
  · -- The same split at the original point keeps exactly the same inactive remainder.
    calc
      (∑ k : Fin (m - 1) × Fin n,
          proximal_objective (absolute_value_penalty lam) (q k.1 k.2) (v k.1 k.2)) =
        proximal_objective (absolute_value_penalty lam) (q ij.1 ij.2) (v ij.1 ij.2) +
          ∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (q k.1 k.2) (v k.1 k.2) := by
              symm
              exact Finset.add_sum_erase (Finset.univ : Finset (Fin (m - 1) × Fin n))
                (fun k ↦ proximal_objective (absolute_value_penalty lam) (q k.1 k.2) (v k.1 k.2))
                (Finset.mem_univ ij)
      _ = proximal_objective (absolute_value_penalty lam) (q ij.1 ij.2) (v ij.1 ij.2) +
          (r : EReal) := by
            have hrest_v_second :
                (∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (q k.1 k.2) (v k.1 k.2)) =
                  (r : EReal) := by
              calc
                (∑ k ∈ s, proximal_objective (absolute_value_penalty lam) (q k.1 k.2) (v k.1 k.2)) =
                    ∑ k ∈ s,
                      (((lam * |v k.1 k.2| + (1 / 2 : ℝ) * (v k.1 k.2 - q k.1 k.2) ^ (2 : ℕ) : ℝ)) :
                        EReal) := by
                          refine Finset.sum_congr rfl ?_
                          intro k hk
                          rw [absolute_value_proximal_objective_eq_coe]
                _ =
                    (((∑ k ∈ s,
                        (lam * |v k.1 k.2| + (1 / 2 : ℝ) * (v k.1 k.2 - q k.1 k.2) ^ (2 : ℕ)) : ℝ)) :
                          EReal) := by
                        symm
                        exact
                          ereal_coe_sum_local (s := s)
                            (φ := fun k ↦
                              lam * |v k.1 k.2| + (1 / 2 : ℝ) * (v k.1 k.2 - q k.1 k.2) ^ (2 : ℕ))
                _ = (r : EReal) := by simp [r]
            exact congrArg
              (fun s : EReal ↦
                proximal_objective (absolute_value_penalty lam) (q ij.1 ij.2) (v ij.1 ij.2) + s)
              hrest_v_second

/-- Helper for Proposition 12.4: minimizing the anisotropic TV proximal objective is equivalent to
minimizing each scalar absolute-value proximal block. -/
lemma anisotropic_isMinOn_proximal_objective_iff_coordinatewise
    (lam : ℝ) (p u : Hmn) (q v : Vmn) :
    IsMinOn
        (proximal_objective
          (fun z : TVSpace ↦ ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
          (toLp 2 (p, q)))
        Set.univ (toLp 2 (u, v)) ↔
      (∀ i j, IsMinOn (proximal_objective (absolute_value_penalty lam) (p i j)) Set.univ
        (u i j)) ∧
      (∀ i j, IsMinOn (proximal_objective (absolute_value_penalty lam) (q i j)) Set.univ
        (v i j)) := by
  constructor
  · intro hmin
    constructor
    · intro i j
      rw [isMinOn_univ_iff] at hmin ⊢
      intro t
      let u' : Hmn := Function.update u i (Function.update (u i) j t)
      have huz := hmin (toLp 2 (u', v))
      -- Freeze the vertical block and update only one horizontal entry.
      rw [anisotropic_proximal_objective_split (lam := lam) (p := p) (u := u) (q := q) (v := v),
        anisotropic_proximal_objective_split (lam := lam) (p := p) (u := u') (q := q) (v := v),
        horizontal_absolute_value_proximal_sum_eq_sum_product,
        horizontal_absolute_value_proximal_sum_eq_sum_product,
        vertical_absolute_value_proximal_sum_eq_sum_product] at huz
      obtain ⟨rh, hu'_split, hu_split⟩ :=
        horizontal_update_pair_sum_cancellation (lam := lam) (p := p) (u := u) (ij := (i, j))
          (t := t)
      obtain ⟨rv, hv_split⟩ := vertical_pair_proximal_sum_eq_coe (lam := lam) (q := q) (v := v)
      rw [hu_split, hu'_split, hv_split] at huz
      have hcancel :
          proximal_objective (absolute_value_penalty lam) (p i j) (u i j) +
              (((rh + rv : ℝ) : EReal)) ≤
            proximal_objective (absolute_value_penalty lam) (p i j) t +
              (((rh + rv : ℝ) : EReal)) := by
        -- Reassociate the unchanged horizontal and vertical remainders into one finite constant.
        simpa [u', hu'_split, hu_split, hv_split, EReal.coe_add, add_assoc] using huz
      exact (EReal.addLECancellable_coe (rh + rv)).add_le_add_iff_right.mp hcancel
    · intro i j
      rw [isMinOn_univ_iff] at hmin ⊢
      intro t
      let v' : Vmn := Function.update v i (Function.update (v i) j t)
      have hvz := hmin (toLp 2 (u, v'))
      -- Freeze the horizontal block and update only one vertical entry.
      rw [anisotropic_proximal_objective_split (lam := lam) (p := p) (u := u) (q := q) (v := v),
        anisotropic_proximal_objective_split (lam := lam) (p := p) (u := u) (q := q) (v := v'),
        horizontal_absolute_value_proximal_sum_eq_sum_product,
        vertical_absolute_value_proximal_sum_eq_sum_product,
        vertical_absolute_value_proximal_sum_eq_sum_product] at hvz
      obtain ⟨rh, hu_split⟩ := horizontal_pair_proximal_sum_eq_coe (lam := lam) (p := p) (u := u)
      obtain ⟨rv, hv'_split, hv_split⟩ :=
        vertical_update_pair_sum_cancellation (lam := lam) (q := q) (v := v) (ij := (i, j))
          (t := t)
      rw [hu_split, hv_split, hv'_split] at hvz
      have hcancel_left :
          proximal_objective (absolute_value_penalty lam) (q i j) (v i j) + (rv : EReal) ≤
            proximal_objective (absolute_value_penalty lam) (q i j) t + (rv : EReal) := by
        -- First cancel the unchanged horizontal remainder on the left.
        exact
          (EReal.addLECancellable_coe rh).add_le_add_iff_left.mp
            (by simpa [add_assoc] using hvz)
      -- Then cancel the unchanged vertical remainder on the right.
      exact (EReal.addLECancellable_coe rv).add_le_add_iff_right.mp hcancel_left
  · rintro ⟨hu_min, hv_min⟩
    rw [isMinOn_univ_iff]
    intro z
    -- Once the global objective is split into scalar blocks, sum the coordinatewise inequalities.
    have hsplit_z :
        proximal_objective
            (fun z : TVSpace ↦ ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
            (toLp 2 (p, q)) z =
          (∑ i : Fin m, ∑ j : Fin (n - 1),
            proximal_objective (absolute_value_penalty lam) (p i j) (z.fst i j)) +
          ∑ i : Fin (m - 1), ∑ j : Fin n,
            proximal_objective (absolute_value_penalty lam) (q i j) (z.snd i j) := by
      simpa using
        (anisotropic_proximal_objective_split (lam := lam) (p := p) (u := z.fst) (q := q)
          (v := z.snd))
    rw [anisotropic_proximal_objective_split (lam := lam) (p := p) (u := u) (q := q) (v := v),
      hsplit_z]
    have hhorizontal :
        (∑ i : Fin m, ∑ j : Fin (n - 1),
          proximal_objective (absolute_value_penalty lam) (p i j) (u i j)) ≤
        ∑ i : Fin m, ∑ j : Fin (n - 1),
          proximal_objective (absolute_value_penalty lam) (p i j) (z.fst i j) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      refine Finset.sum_le_sum ?_
      intro j hj
      exact (isMinOn_univ_iff.mp (hu_min i j)) (z.fst i j)
    have hvertical :
        (∑ i : Fin (m - 1), ∑ j : Fin n,
          proximal_objective (absolute_value_penalty lam) (q i j) (v i j)) ≤
        ∑ i : Fin (m - 1), ∑ j : Fin n,
          proximal_objective (absolute_value_penalty lam) (q i j) (z.snd i j) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      refine Finset.sum_le_sum ?_
      intro j hj
      exact (isMinOn_univ_iff.mp (hv_min i j)) (z.snd i j)
    exact add_le_add hhorizontal hvertical

-- Proof sketch: combine the separable-product proximal theorem from Chapter 6 with Example 6.19
-- on the interior Euclidean norms and Example 6.8 on the boundary absolute-value terms, then
-- reassemble the unique minimizer into the explicit `L²` product point defined above.
/-- The proximal mapping of the scaled isotropic regularizer `λ g₁`, evaluated at the canonical
`L²` product point corresponding to `(p, q)`, is the singleton given by the textbook isotropic
shrinkage and boundary soft-thresholding formulas. -/
theorem prox_two_dimensional_total_variation_isotropic_regularizer_eq_singleton
    (lam : ℝ) (hlam : 0 ≤ lam) (p : Hmn) (q : Vmn) :
    prox[fun z : TVSpace ↦
      ↑(lam * two_dimensional_total_variation_isotropic_regularizer z)] (toLp 2 (p, q)) =
      {two_dimensional_total_variation_isotropic_prox_point lam p q} := by
  -- TODO: after `isotropic_interior_block_proximal_objective_eq`, rewrite the full isotropic
  -- objective as interior `norm_penalty` blocks plus boundary scalar `absolute_value_penalty`
  -- terms (`isotropic_proximal_objective_split`), then derive the blockwise `IsMinOn`
  -- characterization and reassemble the singleton with Example 6.19 and Example 6.8.
  sorry

-- Proof sketch: apply the separable-product proximal theorem from Chapter 6 and use Example 6.8
-- coordinatewise, since every term in `g_{ℓ¹}` is an absolute-value penalty.
/-- The proximal mapping of the scaled anisotropic regularizer `λ g_{ℓ¹}`, evaluated at the
canonical `L²` product point corresponding to `(p, q)`, is the singleton given by entrywise
soft-thresholding. -/
theorem prox_two_dimensional_total_variation_anisotropic_regularizer_eq_singleton
    (lam : ℝ) (hlam : 0 ≤ lam) (p : Hmn) (q : Vmn) :
    prox[fun z : TVSpace ↦
      ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z)] (toLp 2 (p, q)) =
      {two_dimensional_total_variation_anisotropic_prox_point lam p q} := by
  ext z
  constructor
  · intro hz
    rw [mem_proximal_mapping_iff] at hz
    rw [Set.mem_singleton_iff]
    have hz_coord :=
      (anisotropic_isMinOn_proximal_objective_iff_coordinatewise
        (lam := lam) (p := p) (u := z.fst) (q := q) (v := z.snd)).mp (by simpa using hz)
    rcases hz_coord with ⟨hp_min, hq_min⟩
    have hp_eq :
        z.fst = (two_dimensional_total_variation_anisotropic_prox_point lam p q).fst := by
      -- Each horizontal coordinate is the scalar soft-thresholding proximal point.
      ext i j
      have hp_mem : z.fst i j ∈ prox[absolute_value_penalty lam] (p i j) := by
        simpa [mem_proximal_mapping_iff] using hp_min i j
      rw [prox_absolute_value_penalty_eq_singleton_soft_thresholding lam hlam (p i j),
        Set.mem_singleton_iff] at hp_mem
      simpa using hp_mem
    have hq_eq :
        z.snd = (two_dimensional_total_variation_anisotropic_prox_point lam p q).snd := by
      -- Each vertical coordinate is the scalar soft-thresholding proximal point.
      ext i j
      have hq_mem : z.snd i j ∈ prox[absolute_value_penalty lam] (q i j) := by
        simpa [mem_proximal_mapping_iff] using hq_min i j
      rw [prox_absolute_value_penalty_eq_singleton_soft_thresholding lam hlam (q i j),
        Set.mem_singleton_iff] at hq_mem
      simpa using hq_mem
    simpa using congrArg (fun t : Hmn × Vmn ↦ toLp 2 t) (Prod.ext hp_eq hq_eq)
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [mem_proximal_mapping_iff]
    -- Reassemble the global minimizer from the coordinatewise scalar proximal memberships.
    refine
      (anisotropic_isMinOn_proximal_objective_iff_coordinatewise
        (lam := lam) (p := p)
        (u := (two_dimensional_total_variation_anisotropic_prox_point lam p q).fst)
        (q := q)
        (v := (two_dimensional_total_variation_anisotropic_prox_point lam p q).snd)).2 ?_
    constructor
    · intro i j
      have hp_mem : 𝒯[lam] (p i j) ∈ prox[absolute_value_penalty lam] (p i j) := by
        rw [prox_absolute_value_penalty_eq_singleton_soft_thresholding lam hlam (p i j)]
        simp
      simpa [mem_proximal_mapping_iff] using hp_mem
    · intro i j
      have hq_mem : 𝒯[lam] (q i j) ∈ prox[absolute_value_penalty lam] (q i j) := by
        rw [prox_absolute_value_penalty_eq_singleton_soft_thresholding lam hlam (q i j)]
        simp
      simpa [mem_proximal_mapping_iff] using hq_mem

end
