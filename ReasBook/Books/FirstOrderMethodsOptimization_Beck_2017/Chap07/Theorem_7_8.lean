import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_2
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_9

-- Declarations for this item will be appended below by the statement pipeline.

open Function Matrix InnerProductSpace
open scoped Matrix

section

variable {n : ℕ}

local notation "𝕊" => symmetricMatrices n
local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "symmetricEigenvalues" => symmetric_eigenvalue_function

/-- Helper for Theorem 7.8: a real diagonal matrix is symmetric, so it defines a point of
`𝕊^n`. -/
lemma diagonal_mem_symmetricMatrices_raw (x : Fin n → ℝ) :
    Matrix.diagonal x ∈ 𝕊 := by
  -- Diagonal matrices are fixed by transpose entrywise.
  rw [mem_symmetricMatrices_iff]
  simp

/-- Helper for Theorem 7.8: evaluating the spectral lift on a diagonal matrix recovers the vector
profile, because the diagonal entries and the ordered eigenvalues differ only by a permutation. -/
lemma symmetric_spectral_diagonal_pullback_eq_theorem78
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f) (x : Fin n → ℝ) :
    (f ∘ symmetricEigenvalues) ⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices_raw x⟩ = f x := by
  -- Route correction: work with the older ordered-eigenvalue owner from Theorem 7.2 so the proof
  -- can reuse its orthogonal-conjugation API without importing the conflicting Definition 7.23
  -- helper names.
  have hf_desc :
      ∀ z : Fin n → ℝ, f z = f z↓ :=
    ((isPermutationSymmetricFunction_iff_forall_eq_descendingRearrangement f).1 hf).2
  let σ : Equiv.Perm (Fin n) := Fin.revPerm.symm * (Tuple.sort x).symm
  have hσ : ∀ i, x i = x↓ (σ i) := by
    -- The chosen permutation unsorts the decreasing rearrangement back to `x`.
    intro i
    simp [σ, descendingRearrangement, Function.comp_def, Equiv.Perm.coe_mul]
  have hdiag :
      Matrix.diagonal x =
        ((permutationOrthogonalMatrix σ : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) *
          Matrix.diagonal (x↓) *
          (((permutationOrthogonalMatrix σ : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ) := by
    have hdiagx : Matrix.diagonal x = Matrix.diagonal (x↓ ∘ σ) := by
      -- Entrywise, `x` is the permutation pullback of its decreasing rearrangement.
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hσ]
      · simp [Matrix.diagonal, hij]
    calc
      Matrix.diagonal x = Matrix.diagonal (x↓ ∘ σ) := hdiagx
      _ = ((permutationOrthogonalMatrix σ : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) *
            Matrix.diagonal (x↓) *
            (((permutationOrthogonalMatrix σ : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ) :=
          diagonal_comp_perm_eq_orthogonal_conjugate σ (x↓)
  let X : 𝕊 := ⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices_raw x⟩
  let Y : 𝕊 := ⟨Matrix.diagonal (x↓), diagonal_mem_symmetricMatrices (x↓)⟩
  have hchar : ((X : Mₙ)).charpoly = ((Y : Mₙ)).charpoly := by
    -- Orthogonal conjugation preserves the characteristic polynomial, hence the ordered spectrum.
    dsimp [X, Y]
    calc
      Matrix.charpoly (Matrix.diagonal x) =
          Matrix.charpoly
            (((permutationOrthogonalMatrix σ : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) *
              Matrix.diagonal (x↓) *
              (((permutationOrthogonalMatrix σ : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ)) := by
            exact congrArg Matrix.charpoly hdiag
      _ = Matrix.charpoly (Matrix.diagonal (x↓)) := by
            exact orthogonal_conjugate_diagonal_charpoly (permutationOrthogonalMatrix σ) (x↓)
  have heq : symmetricEigenvalues X = symmetricEigenvalues Y := by
    -- The ordered zero-indexed Hermitian spectra are determined by the characteristic polynomial.
    ext i
    rw [symmetric_eigenvalue_function_apply, symmetric_eigenvalue_function_apply]
    have heig0 :
        X.property.isHermitian.eigenvalues₀ = Y.property.isHermitian.eigenvalues₀ := by
      simp_rw [← List.ofFn_inj,
        ← X.property.isHermitian.sort_roots_charpoly_eq_eigenvalues₀,
        ← Y.property.isHermitian.sort_roots_charpoly_eq_eigenvalues₀, hchar]
    simpa using congrFun heig0 (Fin.cast (Fintype.card_fin n).symm i)
  have hY :
      symmetricEigenvalues Y = x↓ := by
    -- The sorted diagonal matrix already carries the ordered eigenvalue vector on its diagonal.
    simpa [Y] using
      diagonal_symmetric_eigenvalue_function_eq_of_antitone
        (x↓) (antitone_descendingRearrangement x)
  calc
    (f ∘ symmetricEigenvalues) X = f (symmetricEigenvalues Y) := by
      simp [heq]
    _ = f (x↓) := by
      rw [hY]
    _ = f x := by
      exact (hf_desc x).symm

/-- Helper for Theorem 7.8: the diagonal embedding of `ℝ^n` into `𝕊^n` is continuous. -/
lemma continuous_diagonal_symmetricMatrices :
    Continuous
      (fun x : Fin n → ℝ ↦
        (⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices_raw x⟩ : 𝕊)) := by
  -- The matrix diagonal map is continuous coordinatewise, and the subtype condition is fixed.
  exact continuous_id.matrix_diagonal.subtype_mk _

/-- Helper for Theorem 7.8: convexity plus permutation symmetry makes `f` decrease under every
doubly stochastic averaging. -/
lemma convex_permutation_symmetric_le_of_doubly_stochastic
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f)
    (hfconv : is_convex_function f) {x : Fin n → ℝ} (hx : x ∈ effective_domain f)
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : P ∈ doublyStochastic ℝ (Fin n)) :
    f (P *ᵥ x) ≤ f x := by
  obtain ⟨w, hw_nonneg, hw_sum, hwP⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
  have hconv_toReal : ConvexOn ℝ (effective_domain f) (fun z ↦ (f z).toReal) :=
    convexOn_toReal_of_is_convex_function hfconv (fun z hz ↦ hf.ne_bot z)
  have hperm_eq :
      ∀ σ : Equiv.Perm (Fin n), f ((σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) = f x := by
    intro σ
    -- Permutation symmetry identifies each permutation orbit point with the original vector.
    exact hf.map_smul (permutationOrthogonalMatrix σ) (Set.mem_range_self σ) x
  have hperm_mem :
      ∀ σ : Equiv.Perm (Fin n),
        ((σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) ∈ effective_domain f := by
    intro σ
    rw [mem_effective_domain, hperm_eq σ]
    simpa [mem_effective_domain] using hx
  have hmulVec_decomp :
      (∑ σ, (w σ • (σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ))) *ᵥ x =
        ∑ σ, w σ • ((σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) := by
    rw [sum_mulVec]
    refine Finset.sum_congr rfl ?_
    intro σ hσ
    rw [smul_mulVec]
  have hPx_mem : P *ᵥ x ∈ effective_domain f := by
    have hconv_dom : Convex ℝ (effective_domain f) :=
      effective_domain_convex_of_is_convex_function hfconv
    -- A doubly stochastic matrix is a convex combination of permutation matrices.
    rw [← hwP, hmulVec_decomp]
    exact hconv_dom.sum_mem (fun σ _ ↦ hw_nonneg σ) (by simpa using hw_sum)
      (fun σ _ ↦ hperm_mem σ)
  have h_toReal : (f (P *ᵥ x)).toReal ≤ (f x).toReal := by
    rw [← hwP, hmulVec_decomp]
    calc
      (f (∑ σ, w σ • ((σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ) *ᵥ x))).toReal
          ≤ ∑ σ, w σ • (f ((σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ) *ᵥ x)).toReal := by
            -- Jensen applies on the convex effective domain to the Birkhoff expansion.
            exact hconv_toReal.map_sum_le (fun σ _ ↦ hw_nonneg σ) (by simpa using hw_sum)
              (fun σ _ ↦ hperm_mem σ)
      _ = ∑ σ, w σ • (f x).toReal := by
            refine Finset.sum_congr rfl ?_
            intro σ hσ
            rw [hperm_eq σ]
      _ = (∑ σ, w σ) * (f x).toReal := by
            simp [smul_eq_mul, Finset.sum_mul]
      _ = (f x).toReal := by
            rw [hw_sum, one_mul]
  have hx_top : f x ≠ ⊤ := by
    exact ne_of_lt (by simpa [mem_effective_domain] using hx)
  have hPx_top : f (P *ᵥ x) ≠ ⊤ := by
    exact ne_of_lt (by simpa [mem_effective_domain] using hPx_mem)
  have hx_bot : f x ≠ ⊥ := hf.ne_bot x
  have hPx_bot : f (P *ᵥ x) ≠ ⊥ := hf.ne_bot (P *ᵥ x)
  -- Convert the real-valued Jensen inequality back to the original `EReal` statement.
  rw [← EReal.coe_toReal hPx_top hPx_bot, ← EReal.coe_toReal hx_top hx_bot]
  exact_mod_cast h_toReal

/-- Helper for Theorem 7.8: the diagonal of an orthogonal conjugate of a symmetric matrix is a
doubly stochastic image of its ordered eigenvalue vector. -/
lemma diag_orthogonal_conjugate_eq_doubly_stochastic_mul_symmetric_eigenvalues
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (X : 𝕊) :
    ∃ P : Mₙ, P ∈ doublyStochastic ℝ (Fin n) ∧
      Matrix.diag ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) = P *ᵥ symmetricEigenvalues X := by
  obtain ⟨V, hX⟩ := exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function X
  let Q : Matrix.orthogonalGroup (Fin n) ℝ := star U * V
  let P : Mₙ := fun i j : Fin n ↦ (Q i j)^2
  have hP : P ∈ doublyStochastic ℝ (Fin n) := by
    -- The squared entries of the relative orthogonal change of basis form a doubly stochastic
    -- matrix.
    simpa [P] using orthogonal_entrywise_sq_mem_doubly_stochastic Q
  have hQ :
      ((Q : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) = (U : Mₙ)ᵀ * (V : Mₙ) := by
    -- Over `ℝ`, the group inverse is the transpose matrix.
    change star (U : Mₙ) * (V : Mₙ) = _
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  refine ⟨P, hP, ?_⟩
  ext i
  have hconj :
      ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) =
        (Q : Mₙ) * Matrix.diagonal (symmetricEigenvalues X) * ((Q : Mₙ)ᵀ) := by
    -- Diagonalize `X`, then rewrite the relative basis change as `Q = Uᵀ V`.
    calc
      ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) =
          ((U : Mₙ)ᵀ) *
            ((V : Mₙ) * Matrix.diagonal (symmetricEigenvalues X) * (V : Mₙ)ᵀ) *
            (U : Mₙ) := by
              rw [hX]
      _ = ((U : Mₙ)ᵀ * (V : Mₙ)) * Matrix.diagonal (symmetricEigenvalues X) *
            ((V : Mₙ)ᵀ * (U : Mₙ)) := by
              simp [mul_assoc]
      _ = (Q : Mₙ) * Matrix.diagonal (symmetricEigenvalues X) * ((Q : Mₙ)ᵀ) := by
              simp [hQ, mul_assoc, Matrix.transpose_mul]
  -- Read off the diagonal through the squared-entry formula from Theorem 7.2.
  calc
    Matrix.diag ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) i =
        (((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) i i) := by
          rfl
    _ = (((Q : Mₙ) * Matrix.diagonal (symmetricEigenvalues X) * ((Q : Mₙ)ᵀ)) i i) := by
          rw [hconj]
    _ = ∑ j, (Q i j)^2 * symmetricEigenvalues X j := by
          rw [diagonal_conj_entry (symmetricEigenvalues X) Q i]
    _ = ∑ j, P i j * symmetricEigenvalues X j := by
          simp [P]
    _ = (P *ᵥ symmetricEigenvalues X) i := by
          simp [Matrix.mulVec, dotProduct]

/-- Helper for Theorem 7.8: after diagonalizing the midpoint matrix, its ordered eigenvalue vector
is the convex combination of the two conjugated diagonals in that eigenbasis. -/
lemma symmetric_eigenvalue_segment_eq_conjugate_diagonal_combo
    (X Y : 𝕊) (t : ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (hZ :
      (((t • X + (1 - t) • Y : 𝕊) : Mₙ)) =
        (U : Mₙ) * Matrix.diagonal (symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊)) *
          (U : Mₙ)ᵀ) :
    symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊) =
      t • Matrix.diag ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) +
        (1 - t) • Matrix.diag ((U : Mₙ)ᵀ * (Y : Mₙ) * (U : Mₙ)) := by
  have hUtU : ((U : Mₙ)ᵀ * (U : Mₙ)) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (U : Mₙ)) (R := ℝ)).1 U.2
  have hUUt : ((U : Mₙ) * (U : Mₙ)ᵀ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff (A := (U : Mₙ)) (R := ℝ)).1 U.2
  have hdiag :
      Matrix.diag
          ((U : Mₙ)ᵀ * (((t • X + (1 - t) • Y : 𝕊) : Mₙ)) * (U : Mₙ)) =
        symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊) := by
    -- Conjugating by the eigenbasis collapses the midpoint matrix to its diagonal spectrum.
    have hconj :
        ((U : Mₙ)ᵀ * (((t • X + (1 - t) • Y : 𝕊) : Mₙ)) * (U : Mₙ)) =
          Matrix.diagonal (symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊)) := by
      let D : Mₙ := Matrix.diagonal (symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊))
      calc
        ((U : Mₙ)ᵀ * (((t • X + (1 - t) • Y : 𝕊) : Mₙ)) * (U : Mₙ)) =
            ((U : Mₙ)ᵀ) *
              ((U : Mₙ) * D * (U : Mₙ)ᵀ) *
              (U : Mₙ) := by
                rw [hZ]
        _ = (((U : Mₙ)ᵀ * (U : Mₙ)) * D) * ((U : Mₙ)ᵀ * (U : Mₙ)) := by
                simp [mul_assoc]
        _ = D := by
                rw [hUtU, Matrix.mul_one]
                simp
        _ = Matrix.diagonal (symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊)) := by
                rfl
    simpa using congrArg Matrix.diag hconj
  -- Expand the midpoint matrix linearly before reading off its diagonal.
  calc
    symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊) =
        Matrix.diag ((U : Mₙ)ᵀ * (((t • X + (1 - t) • Y : 𝕊) : Mₙ)) * (U : Mₙ)) := by
          symm
          exact hdiag
    _ = Matrix.diag
          (t • ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) +
            (1 - t) • ((U : Mₙ)ᵀ * (Y : Mₙ) * (U : Mₙ))) := by
          simp [mul_add, add_mul, mul_assoc]
    _ = t • Matrix.diag ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ)) +
          (1 - t) • Matrix.diag ((U : Mₙ)ᵀ * (Y : Mₙ) * (U : Mₙ)) := by
          ext i
          simp [Matrix.diag, Pi.add_apply, Pi.smul_apply]

/-- Helper for Theorem 7.8: the Jensen inequality for the spectral lift follows by diagonalizing
the midpoint matrix and comparing the two resulting diagonals to the ordered spectra via doubly
stochastic averaging. -/
lemma spectral_segment_jensen_step
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f)
    (hfconv : is_convex_function f) (X Y : 𝕊)
    (hx : X ∈ effective_domain (f ∘ symmetricEigenvalues))
    (hy : Y ∈ effective_domain (f ∘ symmetricEigenvalues))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    f (symmetricEigenvalues (t • X + (1 - t) • Y : 𝕊)) ≤
      (t : EReal) * f (symmetricEigenvalues X) +
        (((1 - t : ℝ) : EReal)) * f (symmetricEigenvalues Y) := by
  let Z : 𝕊 := t • X + (1 - t) • Y
  obtain ⟨U, hZ⟩ := exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function Z
  let a : Fin n → ℝ := Matrix.diag ((U : Mₙ)ᵀ * (X : Mₙ) * (U : Mₙ))
  let b : Fin n → ℝ := Matrix.diag ((U : Mₙ)ᵀ * (Y : Mₙ) * (U : Mₙ))
  obtain ⟨PX, hPX_ds, hPX⟩ :=
    diag_orthogonal_conjugate_eq_doubly_stochastic_mul_symmetric_eigenvalues U X
  obtain ⟨PY, hPY_ds, hPY⟩ :=
    diag_orthogonal_conjugate_eq_doubly_stochastic_mul_symmetric_eigenvalues U Y
  have hspec :
      symmetricEigenvalues Z = t • a + (1 - t) • b := by
    -- Route correction: work in the eigenbasis of the midpoint matrix `Z`, then split the
    -- diagonal of `Uᵀ Z U` into the two conjugated diagonals coming from `X` and `Y`.
    simpa [Z, a, b] using
      symmetric_eigenvalue_segment_eq_conjugate_diagonal_combo X Y t U hZ
  have hx_vec : symmetricEigenvalues X ∈ effective_domain f := by
    simpa [mem_effective_domain, Function.comp] using hx
  have hy_vec : symmetricEigenvalues Y ∈ effective_domain f := by
    simpa [mem_effective_domain, Function.comp] using hy
  have ha_le : f a ≤ f (symmetricEigenvalues X) := by
    -- Doubly stochastic averaging can only decrease a convex permutation-symmetric profile.
    rw [show a = PX *ᵥ symmetricEigenvalues X by simpa [a] using hPX]
    exact convex_permutation_symmetric_le_of_doubly_stochastic f hf hfconv hx_vec hPX_ds
  have hb_le : f b ≤ f (symmetricEigenvalues Y) := by
    rw [show b = PY *ᵥ symmetricEigenvalues Y by simpa [b] using hPY]
    exact convex_permutation_symmetric_le_of_doubly_stochastic f hf hfconv hy_vec hPY_ds
  have ha_eff : a ∈ effective_domain f := by
    -- The doubly stochastic bound transfers finiteness from `λ(X)` to the conjugated diagonal.
    exact lt_of_le_of_lt ha_le (by simpa [mem_effective_domain] using hx_vec)
  have hb_eff : b ∈ effective_domain f := by
    exact lt_of_le_of_lt hb_le (by simpa [mem_effective_domain] using hy_vec)
  have hseg :
      f (t • a + (1 - t) • b) ≤
        (t : EReal) * f a + (((1 - t : ℝ) : EReal)) * f b :=
    (is_convex_function_iff_segment_ineq (f := f)).1 hfconv a ha_eff b hb_eff ht
  have ht_nonneg : 0 ≤ (t : EReal) := by
    exact_mod_cast ht.1
  have hone_sub_nonneg : 0 ≤ (((1 - t : ℝ) : EReal)) := by
    exact_mod_cast sub_nonneg.2 ht.2
  -- Apply Jensen to the two conjugated diagonals, then compare each diagonal back to the
  -- corresponding ordered eigenvalue vector.
  calc
    f (symmetricEigenvalues Z) = f (t • a + (1 - t) • b) := by rw [hspec]
    _ ≤ (t : EReal) * f a + (((1 - t : ℝ) : EReal)) * f b := hseg
    _ ≤ (t : EReal) * f (symmetricEigenvalues X) +
          (((1 - t : ℝ) : EReal)) * f (symmetricEigenvalues Y) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left ha_le ht_nonneg)
              (mul_le_mul_of_nonneg_left hb_le hone_sub_nonneg)

/-- Helper for Theorem 7.8: pulling the conjugate back along `dotProductEquiv` preserves
permutation symmetry. -/
lemma dotProduct_conjugate_profile_is_permutation_symmetric_theorem78
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f)
    (hfconv : is_convex_function f) :
    IsPermutationSymmetricFunction
      (fun x : Fin n → ℝ ↦ conjugate_function f (dotProductEquiv ℝ (Fin n) x)) := by
  let hproper : IsProperExtendedRealFunction f := hf.toIsProperExtendedRealFunction
  let hconj := isProperExtendedRealFunction_conjugate_function f hproper hfconv
  refine
    { toIsProperExtendedRealFunction := ?_
      map_smul := ?_ }
  · -- Properness transports across the linear equivalence `dotProductEquiv`.
    refine ⟨?_, ?_⟩
    · intro x
      exact hconj.ne_bot (dotProductEquiv ℝ (Fin n) x)
    · rcases hconj.effective_domain_nonempty with ⟨y, hy⟩
      refine ⟨(dotProductEquiv ℝ (Fin n)).symm y, ?_⟩
      have hdual :
          dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm y) = y :=
        (dotProductEquiv ℝ (Fin n)).apply_symm_apply y
      simpa [hdual] using hy
  · intro A hA y
    -- Theorem 7.9 gives the orthogonal invariance of the vector-side conjugate.
    exact conjugate_function_eq_conjugate_function_orthogonal_mulVec Λperm[n] f hf A hA y

/-- Helper for Theorem 7.8: taking the `dotProductEquiv`-pullback conjugate twice recovers the
Chapter 4 biconjugate. -/
lemma dotProduct_conjugate_profile_biconjugate_eq_theorem78
    (f : (Fin n → ℝ) → EReal) :
    (fun x : Fin n → ℝ ↦
      conjugate_function
        (fun z : Fin n → ℝ ↦ conjugate_function f (dotProductEquiv ℝ (Fin n) z))
        (dotProductEquiv ℝ (Fin n) x)) =
      biconjugate_function f := by
  funext x
  -- Compare the two defining suprema by transporting witnesses through `dotProductEquiv`.
  rw [conjugate_function_apply, biconjugate_function_apply]
  congr 1
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨dotProductEquiv ℝ (Fin n) z, ?_⟩
    simp [dotProduct_comm]
  · rintro ⟨y, rfl⟩
    refine ⟨(dotProductEquiv ℝ (Fin n)).symm y, ?_⟩
    have hdual :
        dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm y) = y :=
      (dotProductEquiv ℝ (Fin n)).apply_symm_apply y
    have hpair' :
        (dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm y)) x = y x := by
      exact congrArg (fun ψ : Module.Dual ℝ (Fin n → ℝ) => ψ x) hdual
    have hpair : dotProduct x ((dotProductEquiv ℝ (Fin n)).symm y) = y x := by
      simpa [dotProductEquiv, dotProduct_comm] using hpair'
    simp [hdual, hpair]

/-- Helper for Theorem 7.8: if the vector profile is closed and convex, then its spectral lift is
closed and convex. This is the textbook conjugate-biconjugate route, proved in the owner's
`symmetric_eigenvalue_function` notation so it can consume Theorem 7.2 directly. -/
lemma symmetric_spectral_closed_convex_forward
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    LowerSemicontinuous (f ∘ symmetricEigenvalues) ∧
      is_convex_function (f ∘ symmetricEigenvalues) := by
  let fconj : (Fin n → ℝ) → EReal :=
    fun x ↦ conjugate_function f (dotProductEquiv ℝ (Fin n) x)
  have hfconj_symm : IsPermutationSymmetricFunction fconj :=
    dotProduct_conjugate_profile_is_permutation_symmetric_theorem78 f hf hf_convex
  have hmatrix_conj :
      (fun Y : 𝕊 ↦ conjugate_function (f ∘ symmetricEigenvalues) ↑(toDualMap ℝ 𝕊 Y)) =
        fconj ∘ symmetricEigenvalues := by
    -- The first spectral conjugate formula identifies the matrix conjugate with the vector one.
    simpa [fconj, Function.comp] using spectral_conjugate_formula f hf
  have hmatrix_conj_conj :
      (fun Y : 𝕊 ↦ conjugate_function (fconj ∘ symmetricEigenvalues) ↑(toDualMap ℝ 𝕊 Y)) =
        (fun x : Fin n → ℝ ↦ conjugate_function fconj (dotProductEquiv ℝ (Fin n) x)) ∘
          symmetricEigenvalues := by
    -- Apply the same spectral formula once more to the conjugate profile.
    simpa [Function.comp] using spectral_conjugate_formula fconj hfconj_symm
  have hself : biconjugate_function f = f :=
    biconjugate_function_eq_self_of_closed_convex f hf_closed hf_convex
  have hmatrix_self :
      (fun Y : 𝕊 ↦ conjugate_function (fconj ∘ symmetricEigenvalues) ↑(toDualMap ℝ 𝕊 Y)) =
        f ∘ symmetricEigenvalues := by
    -- The second conjugation turns the vector profile into its Chapter 4 biconjugate.
    calc
      (fun Y : 𝕊 ↦ conjugate_function (fconj ∘ symmetricEigenvalues) ↑(toDualMap ℝ 𝕊 Y)) =
          (fun x : Fin n → ℝ ↦ conjugate_function fconj (dotProductEquiv ℝ (Fin n) x)) ∘
            symmetricEigenvalues := hmatrix_conj_conj
      _ = biconjugate_function f ∘ symmetricEigenvalues := by
            rw [dotProduct_conjugate_profile_biconjugate_eq_theorem78 f]
      _ = f ∘ symmetricEigenvalues := by
            rw [hself]
  let G : 𝕊 → EReal :=
    fun Y ↦ conjugate_function (f ∘ symmetricEigenvalues) ↑(toDualMap ℝ 𝕊 Y)
  have hdouble : G∗ = f ∘ symmetricEigenvalues := by
    -- Rewrite the primal conjugate of `G` through the stabilized matrix-side biconjugate route.
    funext Y
    calc
      (G∗) Y = conjugate_function G ↑(toDualMap ℝ 𝕊 Y) := by
        rw [conjugate_function_primal_apply]
      _ = f (symmetricEigenvalues Y) := by
        exact congrFun
          (show (fun Y : 𝕊 ↦ conjugate_function G ↑(toDualMap ℝ 𝕊 Y)) =
              f ∘ symmetricEigenvalues by
            calc
              (fun Y : 𝕊 ↦ conjugate_function G ↑(toDualMap ℝ 𝕊 Y)) =
                  (fun Y : 𝕊 ↦
                    conjugate_function (fconj ∘ symmetricEigenvalues) ↑(toDualMap ℝ 𝕊 Y)) := by
                      simp [G, hmatrix_conj]
              _ = f ∘ symmetricEigenvalues := hmatrix_self) Y
  have hclosedconv := conjugate_function_closed_and_convex G
  -- Theorem 4.1 gives closedness and convexity of the double conjugate, which now equals `F`.
  rw [hdouble] at hclosedconv
  exact hclosedconv

-- Proof sketch: combine the spectral conjugate formula with the biconjugate characterization of
-- closed convex functions to identify the biconjugate of `f ∘ symmetricEigenvalues` with
-- `f** ∘ symmetricEigenvalues`; then use diagonal matrices and permutation symmetry to transfer
-- lower semicontinuity back and forth between the spectral lift and `f`.
/-- Theorem 7.8 (1): for a permutation-symmetric extended-real-valued function on `ℝ^n`, the
spectral lift `f ∘ λ` on `𝕊^n` is lower semicontinuous if and only if `f` is lower
semicontinuous. Here `λ` denotes `symmetricEigenvalues`. -/
theorem symmetric_spectral_function_lowerSemicontinuous_iff
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f) :
    LowerSemicontinuous (f ∘ symmetricEigenvalues) ↔ LowerSemicontinuous f := by
  constructor
  · intro hF
    let d : (Fin n → ℝ) → 𝕊 :=
      fun x ↦ ⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices_raw x⟩
    have hd : Continuous d := by
      -- The reverse implication is the continuous pullback along the diagonal embedding.
      simpa [d] using continuous_diagonal_symmetricMatrices (n := n)
    have hcomp : LowerSemicontinuous ((f ∘ symmetricEigenvalues) ∘ d) :=
      hF.comp hd
    have hdiagpull : ((f ∘ symmetricEigenvalues) ∘ d) = f := by
      -- The diagonal pullback realizes the vector profile exactly.
      ext x
      simpa [Function.comp, d] using symmetric_spectral_diagonal_pullback_eq_theorem78 f hf x
    rw [hdiagpull] at hcomp
    exact hcomp
  · intro hf_closed
    -- TODO: the closed-and-convex conjugate skeleton is now proved by
    -- `symmetric_spectral_closed_convex_forward`, but the separate lower-semicontinuity statement
    -- still needs a continuity theorem for `symmetric_eigenvalue_function : 𝕊^n → ℝ^n`.
    sorry

-- Proof sketch: use the same spectral conjugate/biconjugate identity together with the epigraph
-- characterization of convexity, and transfer the resulting equivalence along diagonal matrices
-- using permutation symmetry of `f`.
/-- Theorem 7.8 (2): for a permutation-symmetric extended-real-valued function on `ℝ^n`, the
spectral lift `f ∘ λ` on `𝕊^n` is convex if and only if `f` is convex. Here convexity is
expressed by `is_convex_function` and `λ` denotes `symmetricEigenvalues`. -/
theorem symmetric_spectral_function_is_convex_function_iff
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f) :
    is_convex_function (f ∘ symmetricEigenvalues) ↔ is_convex_function f := by
  constructor
  · intro hF
    rw [is_convex_function_iff_segment_ineq] at hF ⊢
    intro x hx y hy t ht
    let X : 𝕊 := ⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices_raw x⟩
    let Y : 𝕊 := ⟨Matrix.diagonal y, diagonal_mem_symmetricMatrices_raw y⟩
    have hXeq : (f ∘ symmetricEigenvalues) X = f x := by
      -- The diagonal embedding turns the matrix inequality into the vector one.
      simpa [X] using symmetric_spectral_diagonal_pullback_eq_theorem78 f hf x
    have hYeq : (f ∘ symmetricEigenvalues) Y = f y := by
      simpa [Y] using symmetric_spectral_diagonal_pullback_eq_theorem78 f hf y
    have hx_top : f x < ⊤ := by
      simpa [mem_effective_domain] using hx
    have hy_top : f y < ⊤ := by
      simpa [mem_effective_domain] using hy
    have hX : X ∈ effective_domain (f ∘ symmetricEigenvalues) := by
      rw [mem_effective_domain, hXeq]
      exact hx_top
    have hY : Y ∈ effective_domain (f ∘ symmetricEigenvalues) := by
      rw [mem_effective_domain, hYeq]
      exact hy_top
    have hseg := hF X hX Y hY ht
    have hdiagcombo :
        t • X + (1 - t) • Y =
          (⟨Matrix.diagonal (t • x + (1 - t) • y),
            diagonal_mem_symmetricMatrices_raw (t • x + (1 - t) • y)⟩ : 𝕊) := by
      -- Diagonal matrices are closed under convex combinations, coordinatewise.
      ext i j
      simp [X, Y, Matrix.diagonal_apply, Pi.add_apply, Pi.smul_apply]
      split_ifs <;> simp [*]
    have hcomboeq :
        (f ∘ symmetricEigenvalues)
            (⟨Matrix.diagonal (t • x + (1 - t) • y),
              diagonal_mem_symmetricMatrices_raw (t • x + (1 - t) • y)⟩ : 𝕊) =
          f (t • x + (1 - t) • y) := by
      -- The same diagonal pullback applies to the convex combination.
      simpa using
        symmetric_spectral_diagonal_pullback_eq_theorem78 f hf (t • x + (1 - t) • y)
    rw [hdiagcombo, hcomboeq, hXeq, hYeq] at hseg
    exact hseg
  · intro hf_convex
    rw [is_convex_function_iff_segment_ineq]
    intro X hx Y hy t ht
    -- Use the midpoint-eigenbasis Jensen step proved above for the spectral lift.
    simpa [Function.comp] using spectral_segment_jensen_step f hf hf_convex X Y hx hy ht

end
