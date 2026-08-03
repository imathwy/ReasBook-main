import Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

open scoped Matrix LovaszSchrijverNotation

section Exercise1010

variable {m p : ℕ}

/-- The polyhedron `P = {x ∈ ℝ_+^(2 + p) | A x ≥ b}` from Exercise 10.10. -/
def mixed_zero_one_polyhedron
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ) : Set (Fin (p + 2) → ℝ) :=
  {x | b ≤ A *ᵥ x ∧ 0 ≤ x}

/-- Membership in `mixed_zero_one_polyhedron A b` is exactly the conjunction of the inequalities
`A x ≥ b` and coordinatewise nonnegativity. -/
theorem mem_mixed_zero_one_polyhedron_iff
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ} :
    x ∈ mixed_zero_one_polyhedron A b ↔ b ≤ A *ᵥ x ∧ 0 ≤ x :=
  Iff.rfl

/-- The mixed `0,1` linear set `S = {x ∈ {0,1}^2 × ℝ_+^p | A x ≥ b}` from Exercise 10.10. -/
def mixed_zero_one_linear_set
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ) : Set (Fin (p + 2) → ℝ) :=
  {x |
    x ∈ mixed_zero_one_polyhedron A b ∧
      (x 0 = 0 ∨ x 0 = 1) ∧
        (x 1 = 0 ∨ x 1 = 1)}

/-- Membership in `mixed_zero_one_linear_set A b` means membership in the polyhedron together with
binary first and second coordinates. -/
theorem mem_mixed_zero_one_linear_set_iff
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ} :
    x ∈ mixed_zero_one_linear_set A b ↔
      x ∈ mixed_zero_one_polyhedron A b ∧
        (x 0 = 0 ∨ x 0 = 1) ∧
          (x 1 = 0 ∨ x 1 = 1) :=
  Iff.rfl

/-- The mixed `0,1` Lovasz-Schrijver lift-matrix conditions from Exercise 10.10: the first two
coordinates are treated as binary, while the remaining `p` coordinates stay continuous. The
homogenized-cone owner is reused from Section 10.3. -/
def IsMixedZeroOneLovaszSchrijverMatrix
    (P : Set (Fin (p + 2) → ℝ))
    (Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ) : Prop :=
  Yᵀ = Y ∧
    (Y *ᵥ lifted_basis 0) ∈ homogenized_cone P ∧
      (Y *ᵥ lifted_basis 1) ∈ homogenized_cone P ∧
        (Y *ᵥ lifted_basis 2) ∈ homogenized_cone P ∧
          (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) ∈ homogenized_cone P ∧
            (Y *ᵥ (lifted_basis 0 - lifted_basis 2)) ∈ homogenized_cone P ∧
              Y 1 1 = Y 1 0 ∧
                Y 2 2 = Y 2 0

/-- Unfolding characterization of `IsMixedZeroOneLovaszSchrijverMatrix`. -/
theorem isMixedZeroOneLovaszSchrijverMatrix_iff
    {P : Set (Fin (p + 2) → ℝ)}
    {Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ} :
    IsMixedZeroOneLovaszSchrijverMatrix P Y ↔
      Yᵀ = Y ∧
        (Y *ᵥ lifted_basis 0) ∈ homogenized_cone P ∧
          (Y *ᵥ lifted_basis 1) ∈ homogenized_cone P ∧
            (Y *ᵥ lifted_basis 2) ∈ homogenized_cone P ∧
              (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) ∈ homogenized_cone P ∧
                (Y *ᵥ (lifted_basis 0 - lifted_basis 2)) ∈ homogenized_cone P ∧
                  Y 1 1 = Y 1 0 ∧
                    Y 2 2 = Y 2 0 :=
  Iff.rfl

namespace IsLovaszSchrijverMatrix

/-- The full `0/1` Lovasz-Schrijver matrix constraints imply the mixed `0,1` constraints when only
the first two coordinates are singled out as binary. -/
theorem toMixedZeroOne
    {P : Set (Fin (p + 2) → ℝ)}
    {Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ}
    (hY : IsLovaszSchrijverMatrix P Y) :
    IsMixedZeroOneLovaszSchrijverMatrix P Y := by
  rcases hY with ⟨h_symm, hcol0, hcols, hdiag⟩
  refine ⟨h_symm, hcol0, (hcols 0).1, (hcols 1).1, (hcols 0).2, (hcols 1).2, hdiag 0, hdiag 1⟩

end IsLovaszSchrijverMatrix

/-- The mixed `0,1` one-step linear Lovasz-Schrijver operator from Exercise 10.10. -/
def mixed_zero_one_lovasz_schrijver_N
    (P : Set (Fin (p + 2) → ℝ)) : Set (Fin (p + 2) → ℝ) :=
  {x | ∃ Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ,
      IsMixedZeroOneLovaszSchrijverMatrix P Y ∧
        Y *ᵥ lifted_basis 0 = homogenized_point x}

/-- Membership in `mixed_zero_one_lovasz_schrijver_N P` means admitting a mixed `0,1`
Lovasz-Schrijver lift matrix with first column `(1, x)`. -/
theorem mem_mixed_zero_one_lovasz_schrijver_N_iff
    {P : Set (Fin (p + 2) → ℝ)}
    {x : Fin (p + 2) → ℝ} :
    x ∈ mixed_zero_one_lovasz_schrijver_N P ↔
      ∃ Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ,
        IsMixedZeroOneLovaszSchrijverMatrix P Y ∧
          Y *ᵥ lifted_basis 0 = homogenized_point x :=
  Iff.rfl

/-- The mixed `0,1` one-step semidefinite Lovasz-Schrijver operator from Exercise 10.10. -/
def mixed_zero_one_lovasz_schrijver_N_plus
    (P : Set (Fin (p + 2) → ℝ)) : Set (Fin (p + 2) → ℝ) :=
  {x | ∃ Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ,
      IsMixedZeroOneLovaszSchrijverMatrix P Y ∧
        Y.PosSemidef ∧
        Y *ᵥ lifted_basis 0 = homogenized_point x}

/-- Membership in `mixed_zero_one_lovasz_schrijver_N_plus P` means admitting a positive
semidefinite mixed `0,1` Lovasz-Schrijver lift matrix with first column `(1, x)`. -/
theorem mem_mixed_zero_one_lovasz_schrijver_N_plus_iff
    {P : Set (Fin (p + 2) → ℝ)}
    {x : Fin (p + 2) → ℝ} :
    x ∈ mixed_zero_one_lovasz_schrijver_N_plus P ↔
      ∃ Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ,
        IsMixedZeroOneLovaszSchrijverMatrix P Y ∧
          Y.PosSemidef ∧
          Y *ᵥ lifted_basis 0 = homogenized_point x :=
  Iff.rfl

/-- Dropping positive semidefiniteness sends the mixed `0,1` semidefinite lift to the mixed
`0,1` linear lift. -/
theorem mixed_zero_one_lovasz_schrijver_N_plus_subset_N
    (P : Set (Fin (p + 2) → ℝ)) :
    mixed_zero_one_lovasz_schrijver_N_plus P ⊆
      mixed_zero_one_lovasz_schrijver_N P := by
  intro x hx
  rw [mem_mixed_zero_one_lovasz_schrijver_N_plus_iff] at hx
  rcases hx with ⟨Y, hY, -, hcol⟩
  exact (mem_mixed_zero_one_lovasz_schrijver_N_iff).2 ⟨Y, hY, hcol⟩

/-- The chapter-wide all-binary Lovasz-Schrijver lift maps into the mixed `0,1` lift when only
the first two coordinates are remembered as binary. -/
theorem lovasz_schrijver_N_subset_mixed_zero_one_lovasz_schrijver_N
    (P : Set (Fin (p + 2) → ℝ)) :
    N(P) ⊆ mixed_zero_one_lovasz_schrijver_N P := by
  intro x hx
  rw [mem_lovasz_schrijver_N_iff] at hx
  rcases hx with ⟨Y, hY, hcol⟩
  exact (mem_mixed_zero_one_lovasz_schrijver_N_iff).2 ⟨Y, hY.toMixedZeroOne, hcol⟩

/-- The chapter-wide all-binary semidefinite Lovasz-Schrijver lift maps into the mixed `0,1`
semidefinite lift when only the first two coordinates are remembered as binary. -/
theorem lovasz_schrijver_N_plus_subset_mixed_zero_one_lovasz_schrijver_N_plus
    (P : Set (Fin (p + 2) → ℝ)) :
    N₊(P) ⊆ mixed_zero_one_lovasz_schrijver_N_plus P := by
  intro x hx
  rw [mem_lovasz_schrijver_N_plus_iff] at hx
  rcases hx with ⟨Y, hY, hpsd, hcol⟩
  exact (mem_mixed_zero_one_lovasz_schrijver_N_plus_iff).2
    ⟨Y, hY.toMixedZeroOne, hpsd, hcol⟩

/-- Helper for Exercise 10.10: `mixed_zero_one_polyhedron A b` is convex because both the matrix
system `b ≤ A *ᵥ x` and the coordinatewise nonnegativity constraints are preserved by convex
combinations. -/
lemma convex_mixedZeroOnePolyhedron
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ) :
    Convex ℝ (mixed_zero_one_polyhedron A b) := by
  intro x hx y hy a c ha hc hac
  rw [mem_mixed_zero_one_polyhedron_iff] at hx hy ⊢
  refine ⟨?_, ?_⟩
  · -- Combine the row inequalities linearly and use `a + c = 1`.
    intro i
    have hx_i : b i ≤ (A *ᵥ x) i := hx.1 i
    have hy_i : b i ≤ (A *ᵥ y) i := hy.1 i
    calc
      b i = a * b i + c * b i := by rw [← add_mul, hac, one_mul]
      _ ≤ a * (A *ᵥ x) i + c * (A *ᵥ y) i := by
        exact add_le_add (mul_le_mul_of_nonneg_left hx_i ha) (mul_le_mul_of_nonneg_left hy_i hc)
      _ = (A *ᵥ (a • x + c • y)) i := by
        rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
        calc
          a * ∑ j, A i j * x j + c * ∑ j, A i j * y j
              = ∑ j, (a * (A i j * x j) + c * (A i j * y j)) := by
                  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          _ = ∑ j, A i j * (a • x + c • y) j := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                simp [Pi.smul_apply]
                ring
  · -- Coordinatewise nonnegativity is preserved termwise.
    intro j
    exact add_nonneg (mul_nonneg ha (hx.2 j)) (mul_nonneg hc (hy.2 j))

/-- Helper for Exercise 10.10: enlarging the base set enlarges its homogenized cone. -/
lemma homogenizedCone_mono
    {P Q : Set (Fin (p + 2) → ℝ)}
    (hPQ : P ⊆ Q) :
    homogenized_cone P ⊆ homogenized_cone Q := by
  intro y hy
  rw [mem_homogenized_cone_iff] at hy ⊢
  rcases hy with ⟨t, ht, x, hx, rfl⟩
  exact ⟨t, ht, x, convexHull_mono hPQ hx, rfl⟩

/-- Helper for Exercise 10.10: the mixed linear Lovász-Schrijver relaxation is monotone in the
underlying set. -/
lemma mixedZeroOneLovaszSchrijverN_mono :
    Monotone (fun P : Set (Fin (p + 2) → ℝ) ↦ mixed_zero_one_lovasz_schrijver_N P) := by
  intro P Q hPQ x hx
  rw [mem_mixed_zero_one_lovasz_schrijver_N_iff] at hx ⊢
  rcases hx with ⟨Y, hY, hcol⟩
  rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨h_symm, h0, h1, h2, hdiff1, hdiff2, hdiag1, hdiag2⟩
  refine ⟨Y, ?_, hcol⟩
  exact (isMixedZeroOneLovaszSchrijverMatrix_iff).2
    ⟨h_symm, homogenizedCone_mono hPQ h0, homogenizedCone_mono hPQ h1,
      homogenizedCone_mono hPQ h2, homogenizedCone_mono hPQ hdiff1,
      homogenizedCone_mono hPQ hdiff2, hdiag1, hdiag2⟩

/-- Helper for Exercise 10.10: a homogenized cone point with positive first coordinate can be
dehomogenized back to a point of the original convex set. -/
lemma normalizeMemOfMemHomogenizedCone
    {P : Set (Fin (p + 2) → ℝ)}
    (hP_convex : Convex ℝ P)
    {y : Fin (p + 3) → ℝ}
    (hy : y ∈ homogenized_cone P)
    (hy0_pos : 0 < y 0) :
    ∃ x : Fin (p + 2) → ℝ, x ∈ P ∧ y = y 0 • homogenized_point x := by
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨t, ht, x, hxHull, rfl⟩
  have hxP : x ∈ P := by
    have hxHull' : x ∈ convexHull ℝ P := hxHull
    rwa [convexHull_eq_self.2 hP_convex] at hxHull'
  refine ⟨x, hxP, ?_⟩
  -- The cone scalar is exactly the first coordinate of the homogenized vector.
  simp [homogenized_point]

/-- Helper for Exercise 10.10: every point of a homogenized cone has nonnegative top coordinate,
because the cone scalar is exactly that top coordinate. -/
lemma top_nonneg_of_memHomogenizedCone
    {P : Set (Fin (p + 2) → ℝ)}
    {y : Fin (p + 3) → ℝ}
    (hy : y ∈ homogenized_cone P) :
    0 ≤ y 0 := by
  -- Unpack the cone witness and read off the top coordinate of `t • homogenized_point x`.
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨t, ht, x, hx, rfl⟩
  simpa [homogenized_point] using ht

/-- Helper for Exercise 10.10: a homogenized cone point with zero top coordinate is the zero
vector. -/
lemma eq_zero_of_memHomogenizedCone_of_top_zero
    {P : Set (Fin (p + 2) → ℝ)}
    {y : Fin (p + 3) → ℝ}
    (hy : y ∈ homogenized_cone P)
    (hy0 : y 0 = 0) :
    y = 0 := by
  -- Unpack the cone witness and read the cone scalar off the top coordinate.
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨t, ht, x, hx, rfl⟩
  have ht_zero : t = 0 := by
    simpa [homogenized_point] using hy0
  ext j
  simp [ht_zero]

/-- Helper for Exercise 10.10: the mixed witness already forces the first two distinguished
coordinates into the unit interval. -/
lemma firstTwoUnitBounds_of_mem_mixedZeroOneLovaszSchrijverN
    {Q : Set (Fin (p + 2) → ℝ)}
    {x : Fin (p + 2) → ℝ}
    (hx : x ∈ mixed_zero_one_lovasz_schrijver_N Q) :
    0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 := by
  -- Read the top coordinates of the first/second lifted columns and their complements.
  rw [mem_mixed_zero_one_lovasz_schrijver_N_iff] at hx
  rcases hx with ⟨Y, hY, hcol0⟩
  rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨hYsymm, -, hcone1, hcone2, hconeDiff1, hconeDiff2, -, -⟩
  have hY10 : Y 1 0 = x 0 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 1
  have hY20 : Y 2 0 = x 1 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 2
  have hY01_eq : Y 1 0 = Y 0 1 := by
    simpa [Matrix.transpose_apply] using congr_fun (congr_fun hYsymm 0) 1
  have hY02_eq : Y 2 0 = Y 0 2 := by
    simpa [Matrix.transpose_apply] using congr_fun (congr_fun hYsymm 0) 2
  have hY01 : Y 0 1 = x 0 := by
    calc
      Y 0 1 = Y 1 0 := hY01_eq.symm
      _ = x 0 := hY10
  have hY02 : Y 0 2 = x 1 := by
    calc
      Y 0 2 = Y 2 0 := hY02_eq.symm
      _ = x 1 := hY20
  have hY00 : Y 0 0 = 1 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 0
  have hx0_nonneg : 0 ≤ x 0 := by
    simpa [mulVec_lifted_basis, hY01] using top_nonneg_of_memHomogenizedCone hcone1
  have hx0_le_one : x 0 ≤ 1 := by
    have hdiff1_nonneg : 0 ≤ (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) 0 :=
      top_nonneg_of_memHomogenizedCone hconeDiff1
    simpa [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY01] using hdiff1_nonneg
  have hx1_nonneg : 0 ≤ x 1 := by
    simpa [mulVec_lifted_basis, hY02] using top_nonneg_of_memHomogenizedCone hcone2
  have hx1_le_one : x 1 ≤ 1 := by
    have hdiff2_nonneg : 0 ≤ (Y *ᵥ (lifted_basis 0 - lifted_basis 2)) 0 :=
      top_nonneg_of_memHomogenizedCone hconeDiff2
    simpa [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY02] using hdiff2_nonneg
  exact ⟨hx0_nonneg, hx0_le_one, hx1_nonneg, hx1_le_one⟩

/-- Helper for Exercise 10.10: the mixed `0,1` semidefinite Lovasz-Schrijver relaxation is convex.
-/
lemma convex_mixedZeroOneLovaszSchrijverNPlus
    (P : Set (Fin (p + 2) → ℝ)) :
    Convex ℝ (mixed_zero_one_lovasz_schrijver_N_plus P) := by
  intro x hx y hy a b ha hb hab
  rw [mem_mixed_zero_one_lovasz_schrijver_N_plus_iff] at hx hy ⊢
  rcases hx with ⟨Yx, hYx, hYx_psd, hcolx⟩
  rcases hy with ⟨Yy, hYy, hYy_psd, hcoly⟩
  rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hYx hYy
  rcases hYx with ⟨hYx_symm, hYx0, hYx1, hYx2, hYxDiff1, hYxDiff2, hYxDiag1, hYxDiag2⟩
  rcases hYy with ⟨hYy_symm, hYy0, hYy1, hYy2, hYyDiff1, hYyDiff2, hYyDiag1, hYyDiag2⟩
  refine ⟨a • Yx + b • Yy, ?_, ?_, ?_⟩
  · -- Symmetry, cone membership, and the two binary diagonal identities are preserved termwise.
    rw [isMixedZeroOneLovaszSchrijverMatrix_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        (a • Yx + b • Yy)ᵀ = a • Yxᵀ + b • Yyᵀ := by simp
        _ = a • Yx + b • Yy := by rw [hYx_symm, hYy_symm]
    · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
      exact homogenizedCone_add_mem P
        (homogenizedCone_nonneg_smul_mem P hYx0 ha)
        (homogenizedCone_nonneg_smul_mem P hYy0 hb)
    · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
      exact homogenizedCone_add_mem P
        (homogenizedCone_nonneg_smul_mem P hYx1 ha)
        (homogenizedCone_nonneg_smul_mem P hYy1 hb)
    · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
      exact homogenizedCone_add_mem P
        (homogenizedCone_nonneg_smul_mem P hYx2 ha)
        (homogenizedCone_nonneg_smul_mem P hYy2 hb)
    · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
      exact homogenizedCone_add_mem P
        (homogenizedCone_nonneg_smul_mem P hYxDiff1 ha)
        (homogenizedCone_nonneg_smul_mem P hYyDiff1 hb)
    · rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
      exact homogenizedCone_add_mem P
        (homogenizedCone_nonneg_smul_mem P hYxDiff2 ha)
        (homogenizedCone_nonneg_smul_mem P hYyDiff2 hb)
    · simp [hYxDiag1, hYyDiag1]
    · simp [hYxDiag2, hYyDiag2]
  · -- Positive semidefiniteness is stable under nonnegative scaling and addition.
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hYx_psd ha)
      (Matrix.PosSemidef.smul hYy_psd hb)
  · -- The first column becomes the homogenized lift of the convex combination.
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hcolx, hcoly]
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [homogenized_point, hab]
    · intro j
      simp [homogenized_point]

/-- Helper for Exercise 10.10: every mixed binary feasible point has the standard rank-one witness
in the mixed `N₊` relaxation. -/
lemma mem_mixedZeroOneLovaszSchrijverNPlus_of_mem_mixedZeroOneLinearSet
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ}
    (hx : x ∈ mixed_zero_one_linear_set A b) :
    x ∈ mixed_zero_one_lovasz_schrijver_N_plus (mixed_zero_one_polyhedron A b) := by
  rw [mem_mixed_zero_one_linear_set_iff] at hx
  rcases hx with ⟨hxP, hx01, hx11⟩
  let u : Fin (p + 3) → ℝ := homogenized_point x
  let Y : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ := Matrix.vecMulVec u u
  have hxHull : x ∈ convexHull ℝ (mixed_zero_one_polyhedron A b) := by
    exact subset_convexHull ℝ (mixed_zero_one_polyhedron A b) hxP
  have hcol0 : Y *ᵥ lifted_basis 0 = u := by
    -- The first column of the rank-one witness is the homogenized lift itself.
    ext j
    rw [mulVec_lifted_basis]
    simp [Y, u, Matrix.vecMulVec, homogenized_point]
  have hsymm : Yᵀ = Y := by
    -- A rank-one matrix `u uᵀ` is symmetric over `ℝ`.
    ext i j
    simp [Y, Matrix.vecMulVec, mul_comm]
  have hpsd : Y.PosSemidef := by
    -- Positive semidefiniteness is the standard `vecMulVec` fact.
    simpa [Y, u] using Matrix.posSemidef_vecMulVec_self_star u
  rw [mem_mixed_zero_one_lovasz_schrijver_N_plus_iff]
  refine ⟨Y, ?_, hpsd, ?_⟩
  · -- The mixed matrix constraints only use the first two binary coordinates.
    rw [isMixedZeroOneLovaszSchrijverMatrix_iff]
    refine ⟨hsymm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcol0]
      simpa [u] using homogenized_point_mem_homogenized_cone
        (mixed_zero_one_polyhedron A b) hxHull
    · have hx0_nonneg : 0 ≤ x 0 := hxP.2 0
      have hcol1 : Y *ᵥ lifted_basis 1 = x 0 • u := by
        rw [mulVec_lifted_basis]
        ext j
        simp [Y, u, Matrix.vecMulVec, homogenized_point, mul_comm]
      rw [hcol1]
      exact homogenizedCone_nonneg_smul_mem (mixed_zero_one_polyhedron A b)
        (homogenized_point_mem_homogenized_cone (mixed_zero_one_polyhedron A b) hxHull)
        hx0_nonneg
    · have hx1_nonneg : 0 ≤ x 1 := hxP.2 1
      have hu2 : u 2 = x 1 := by
        change (Fin.cons (α := fun _ : Fin (p + 3) => ℝ) 1 x) (Fin.succ (1 : Fin (p + 2))) = x 1
        rw [Fin.cons_succ]
      have hcol2 : Y *ᵥ lifted_basis 2 = x 1 • u := by
        rw [mulVec_lifted_basis]
        ext j
        rw [show Y j 2 = u j * u 2 by simp [Y, Matrix.vecMulVec], hu2]
        simp [Pi.smul_apply, mul_comm]
      rw [hcol2]
      exact homogenizedCone_nonneg_smul_mem (mixed_zero_one_polyhedron A b)
        (homogenized_point_mem_homogenized_cone (mixed_zero_one_polyhedron A b) hxHull)
        hx1_nonneg
    · have hone_sub_nonneg : 0 ≤ 1 - x 0 := by
        rcases hx01 with hx0 | hx0 <;> linarith
      have hx0_sq : x 0 * x 0 = x 0 := by
        rcases hx01 with hx0 | hx0 <;> simp [hx0]
      have hcol1 : Y *ᵥ lifted_basis 1 = x 0 • u := by
        rw [mulVec_lifted_basis]
        ext j
        simp [Y, u, Matrix.vecMulVec, homogenized_point, mul_comm]
      have hcolDiff1 :
          Y *ᵥ (lifted_basis 0 - lifted_basis 1) = (1 - x 0) • u := by
        rw [Matrix.mulVec_sub, hcol0, hcol1]
        ext j
        simp [one_sub_mul]
      rw [hcolDiff1]
      exact homogenizedCone_nonneg_smul_mem (mixed_zero_one_polyhedron A b)
        (homogenized_point_mem_homogenized_cone (mixed_zero_one_polyhedron A b) hxHull)
        hone_sub_nonneg
    · have hone_sub_nonneg : 0 ≤ 1 - x 1 := by
        rcases hx11 with hx1 | hx1 <;> linarith
      have hx1_sq : x 1 * x 1 = x 1 := by
        rcases hx11 with hx1 | hx1 <;> simp [hx1]
      have hu2 : u 2 = x 1 := by
        change (Fin.cons (α := fun _ : Fin (p + 3) => ℝ) 1 x) (Fin.succ (1 : Fin (p + 2))) = x 1
        rw [Fin.cons_succ]
      have hcol2 : Y *ᵥ lifted_basis 2 = x 1 • u := by
        rw [mulVec_lifted_basis]
        ext j
        rw [show Y j 2 = u j * u 2 by simp [Y, Matrix.vecMulVec], hu2]
        simp [Pi.smul_apply, mul_comm]
      have hcolDiff2 :
          Y *ᵥ (lifted_basis 0 - lifted_basis 2) = (1 - x 1) • u := by
        rw [Matrix.mulVec_sub, hcol0, hcol2]
        ext j
        simp [one_sub_mul]
      rw [hcolDiff2]
      exact homogenizedCone_nonneg_smul_mem (mixed_zero_one_polyhedron A b)
        (homogenized_point_mem_homogenized_cone (mixed_zero_one_polyhedron A b) hxHull)
        hone_sub_nonneg
    · have hx0_sq : x 0 * x 0 = x 0 := by
        rcases hx01 with hx0 | hx0 <;> simp [hx0]
      simpa [Y, u, Matrix.vecMulVec, homogenized_point] using hx0_sq
    · have hx1_sq : x 1 * x 1 = x 1 := by
        rcases hx11 with hx1 | hx1 <;> simp [hx1]
      have hu0 : u 0 = 1 := by
        change (Fin.cons (α := fun _ : Fin (p + 3) => ℝ) 1 x) 0 = 1
        rw [Fin.cons_zero]
      have hu2 : u 2 = x 1 := by
        change (Fin.cons (α := fun _ : Fin (p + 3) => ℝ) 1 x) (Fin.succ (1 : Fin (p + 2))) = x 1
        rw [Fin.cons_succ]
      calc
        Y 2 2 = u 2 * u 2 := by simp [Y, Matrix.vecMulVec]
        _ = x 1 * x 1 := by rfl
        _ = x 1 := hx1_sq
        _ = x 1 * 1 := by ring
        _ = u 2 * u 0 := by simp [hu0, hu2]
        _ = Y 2 0 := by simp [Y, Matrix.vecMulVec]
  · simpa [u] using hcol0

/-- Helper for Exercise 10.10: the convex hull of the mixed `0,1` feasible set lies in the mixed
`N₊` relaxation. -/
lemma convexHull_mixedZeroOneLinearSet_subset_mixedZeroOneLovaszSchrijverNPlus
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ) :
    convexHull ℝ (mixed_zero_one_linear_set A b) ⊆
      mixed_zero_one_lovasz_schrijver_N_plus (mixed_zero_one_polyhedron A b) := by
  -- Every mixed binary feasible point already has a PSD rank-one witness, and `N₊` is convex.
  refine convexHull_min ?_
    (convex_mixedZeroOneLovaszSchrijverNPlus (mixed_zero_one_polyhedron A b))
  intro x hx
  exact mem_mixedZeroOneLovaszSchrijverNPlus_of_mem_mixedZeroOneLinearSet hx

/-- Helper for Exercise 10.10: every mixed `N` point already belongs to the underlying polyhedron
because the first lifted column is a homogenized cone point over a convex owner. -/
lemma mem_mixedZeroOnePolyhedron_of_mem_mixedZeroOneLovaszSchrijverN
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ}
    (hx : x ∈ mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b)) :
    x ∈ mixed_zero_one_polyhedron A b := by
  -- Read the first lifted column as `homogenized_point x` and collapse the convex hull.
  rw [mem_mixed_zero_one_lovasz_schrijver_N_iff] at hx
  rcases hx with ⟨Y, hY, hcol0⟩
  rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨-, hcone0, -, -, -, -, -, -⟩
  have hcone0' : homogenized_point x ∈ homogenized_cone (mixed_zero_one_polyhedron A b) := by
    simpa [hcol0] using hcone0
  have hxHull : x ∈ convexHull ℝ (mixed_zero_one_polyhedron A b) := by
    exact mem_convexHull_of_homogenized_point_mem_homogenized_cone
      (mixed_zero_one_polyhedron A b) hcone0'
  rwa [convexHull_eq_self.2 (convex_mixedZeroOnePolyhedron A b)] at hxHull

/-- Helper for Exercise 10.10: a mixed `N` point satisfies the polyhedron inequalities and the
source box bounds on the two binary coordinates. -/
lemma firstTwoBounds_of_mem_mixedZeroOneLovaszSchrijverN
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ}
    (hbox : ∀ {x : Fin (p + 2) → ℝ}, x ∈ mixed_zero_one_polyhedron A b → x 0 ≤ 1 ∧ x 1 ≤ 1)
    (hx : x ∈ mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b)) :
    0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 := by
  -- Combine polyhedron membership from the first lifted column with the external box hypothesis.
  have hxP : x ∈ mixed_zero_one_polyhedron A b :=
    mem_mixedZeroOnePolyhedron_of_mem_mixedZeroOneLovaszSchrijverN hx
  have hxBox : x 0 ≤ 1 ∧ x 1 ≤ 1 := hbox hxP
  rw [mem_mixed_zero_one_polyhedron_iff] at hxP
  exact ⟨hxP.2 0, hxBox.1, hxP.2 1, hxBox.2⟩

/-- Helper for Exercise 10.10: if the first binary coordinate is strictly between `0` and `1`,
the mixed witness splits `x` into normalized points on the first-coordinate faces `x 0 = 1` and
`x 0 = 0`. -/
lemma splitOnFirstBinaryCoordinateOfInterior
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ}
    (hx : x ∈ mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b))
    (hx0_pos : 0 < x 0)
    (hx0_lt : x 0 < 1) :
    ∃ xOne xZero : Fin (p + 2) → ℝ,
      xOne ∈ mixed_zero_one_polyhedron A b ∧
        xOne 0 = 1 ∧
          xZero ∈ mixed_zero_one_polyhedron A b ∧
            xZero 0 = 0 ∧
              x = x 0 • xOne + (1 - x 0) • xZero := by
  -- Unpack the mixed witness and isolate the first-coordinate column and complementary column.
  rw [mem_mixed_zero_one_lovasz_schrijver_N_iff] at hx
  rcases hx with ⟨Y, hY, hcol0⟩
  rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨hYsymm, -, hcone1, -, hconeDiff1, -, hdiag1, -⟩
  have hY10 : Y 1 0 = x 0 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 1
  have hY01_eq : Y 1 0 = Y 0 1 := by
    simpa [Matrix.transpose_apply] using congr_fun (congr_fun hYsymm 0) 1
  have hY01 : Y 0 1 = x 0 := by
    calc
      Y 0 1 = Y 1 0 := hY01_eq.symm
      _ = x 0 := hY10
  have hY00 : Y 0 0 = 1 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 0
  have hcol1_pos : 0 < (Y *ᵥ lifted_basis 1) 0 := by
    simpa [mulVec_lifted_basis, hY01] using hx0_pos
  obtain ⟨xOne, hxOneP, hcol1_eq⟩ :=
    normalizeMemOfMemHomogenizedCone (convex_mixedZeroOnePolyhedron A b) hcone1 hcol1_pos
  have hcol1_top : (Y *ᵥ lifted_basis 1) 0 = x 0 := by
    calc
      (Y *ᵥ lifted_basis 1) 0 = Y 0 1 := by simp [mulVec_lifted_basis]
      _ = x 0 := hY01
  have hcol1_eq' : Y *ᵥ lifted_basis 1 = x 0 • homogenized_point xOne := by
    simpa [hcol1_top] using hcol1_eq
  have hxOne0 : xOne 0 = 1 := by
    -- The first binary diagonal identity forces the normalized upper-face point onto `x 0 = 1`.
    have hcoord : x 0 = x 0 * xOne 0 := by
      calc
        x 0 = (Y *ᵥ lifted_basis 1) 1 := by
          simp [mulVec_lifted_basis, hdiag1, hY10]
        _ = (x 0 • homogenized_point xOne) 1 := by rw [hcol1_eq']
        _ = x 0 * xOne 0 := by simp [homogenized_point]
    nlinarith
  have hdiff1_pos : 0 < (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) 0 := by
    -- The complementary lifted column has height `1 - x 0`, which is positive in the interior.
    have hcoord :
        (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) 0 = 1 - x 0 := by
      simp [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY01]
    rw [hcoord]
    linarith
  obtain ⟨xZero, hxZeroP, hdiff1_eq⟩ :=
    normalizeMemOfMemHomogenizedCone
      (convex_mixedZeroOnePolyhedron A b) hconeDiff1 hdiff1_pos
  have hdiff1_top : (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) 0 = 1 - x 0 := by
    simp [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY01]
  have hdiff1_eq' :
      Y *ᵥ (lifted_basis 0 - lifted_basis 1) = (1 - x 0) • homogenized_point xZero := by
    simpa [hdiff1_top] using hdiff1_eq
  have hxZero0 : xZero 0 = 0 := by
    -- The complementary first-face column has vanishing first binary coordinate after normalization.
    have hcoord :
        (1 - x 0) * xZero 0 = 0 := by
      calc
        (1 - x 0) * xZero 0 = ((1 - x 0) • homogenized_point xZero) 1 := by
          simp [homogenized_point]
        _ = (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) 1 := by rw [hdiff1_eq']
        _ = Y 1 0 - Y 1 1 := by
          simp [Matrix.mulVec_sub, mulVec_lifted_basis]
        _ = 0 := by rw [hdiag1, sub_self]
    nlinarith
  refine ⟨xOne, xZero, hxOneP, hxOne0, hxZeroP, hxZero0, ?_⟩
  -- Reassemble the original point from the two normalized face columns.
  have hhom :
      homogenized_point x =
        x 0 • homogenized_point xOne + (1 - x 0) • homogenized_point xZero := by
    calc
      homogenized_point x = Y *ᵥ lifted_basis 0 := hcol0.symm
      _ = Y *ᵥ lifted_basis 1 + Y *ᵥ (lifted_basis 0 - lifted_basis 1) := by
        rw [Matrix.mulVec_sub]
        ext j
        simp [Pi.add_apply, sub_eq_add_neg]
      _ = x 0 • homogenized_point xOne + (1 - x 0) • homogenized_point xZero := by
        rw [hcol1_eq', hdiff1_eq']
  have htail :
      x = x 0 • xOne + (1 - x 0) • xZero := by
    have := congrArg (fun y : Fin (p + 3) → ℝ => fun j : Fin (p + 2) ↦ y j.succ) hhom
    simpa [homogenized_point] using this
  exact htail

/-- Helper for Exercise 10.10: once the first distinguished coordinate is already binary, the
mixed witness only needs a second-coordinate split to land in the mixed binary convex hull. -/
lemma binaryFirstCoordinate_mem_convexHull_mixedZeroOneLinearSet
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ}
    (hbox : ∀ {x : Fin (p + 2) → ℝ}, x ∈ mixed_zero_one_polyhedron A b → x 0 ≤ 1 ∧ x 1 ≤ 1)
    (hx : x ∈ mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b))
    (hx0_binary : x 0 = 0 ∨ x 0 = 1) :
    x ∈ convexHull ℝ (mixed_zero_one_linear_set A b) := by
  have hx_bounds := firstTwoBounds_of_mem_mixedZeroOneLovaszSchrijverN hbox hx
  rcases hx_bounds with ⟨hx0_nonneg, hx0_le_one, hx1_nonneg, hx1_le_one⟩
  by_cases hx1_zero : x 1 = 0
  · -- If the second coordinate is already `0`, the point is itself mixed binary feasible.
    have hxP : x ∈ mixed_zero_one_polyhedron A b :=
      mem_mixedZeroOnePolyhedron_of_mem_mixedZeroOneLovaszSchrijverN hx
    exact subset_convexHull ℝ (mixed_zero_one_linear_set A b) <|
      (mem_mixed_zero_one_linear_set_iff).2 ⟨hxP, hx0_binary, Or.inl hx1_zero⟩
  by_cases hx1_one : x 1 = 1
  · -- If the second coordinate is already `1`, the point is itself mixed binary feasible.
    have hxP : x ∈ mixed_zero_one_polyhedron A b :=
      mem_mixedZeroOnePolyhedron_of_mem_mixedZeroOneLovaszSchrijverN hx
    exact subset_convexHull ℝ (mixed_zero_one_linear_set A b) <|
      (mem_mixed_zero_one_linear_set_iff).2 ⟨hxP, hx0_binary, Or.inr hx1_one⟩
  · -- Otherwise normalize the second lifted column and its complement into the two binary faces.
    have hx1_pos : 0 < x 1 := by
      exact lt_of_le_of_ne hx1_nonneg (Ne.symm hx1_zero)
    have hx1_lt : x 1 < 1 := by
      exact lt_of_le_of_ne hx1_le_one hx1_one
    rw [mem_mixed_zero_one_lovasz_schrijver_N_iff] at hx
    rcases hx with ⟨Y, hY, hcol0⟩
    rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hY
    rcases hY with ⟨hYsymm, -, hcone1, hcone2, hconeDiff1, hconeDiff2, hdiag1, hdiag2⟩
    have hY10 : Y 1 0 = x 0 := by
      simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 1
    have hY20 : Y 2 0 = x 1 := by
      simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 2
    have hY01_eq : Y 1 0 = Y 0 1 := by
      simpa [Matrix.transpose_apply] using congr_fun (congr_fun hYsymm 0) 1
    have hY01 : Y 0 1 = x 0 := by
      calc
        Y 0 1 = Y 1 0 := hY01_eq.symm
        _ = x 0 := hY10
    have hY00 : Y 0 0 = 1 := by
      simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 0
    have hY02_eq : Y 2 0 = Y 0 2 := by
      simpa [Matrix.transpose_apply] using congr_fun (congr_fun hYsymm 0) 2
    have hY02 : Y 0 2 = x 1 := by
      calc
        Y 0 2 = Y 2 0 := hY02_eq.symm
        _ = x 1 := hY20
    have hcol2_top : (Y *ᵥ lifted_basis 2) 0 = x 1 := by
      calc
        (Y *ᵥ lifted_basis 2) 0 = Y 0 2 := by simp [mulVec_lifted_basis]
        _ = x 1 := hY02
    obtain ⟨xOne, hxOneP, hcol2_eq⟩ :=
      normalizeMemOfMemHomogenizedCone
        (convex_mixedZeroOnePolyhedron A b) hcone2 (by simpa [hcol2_top] using hx1_pos)
    have hcol2_eq' : Y *ᵥ lifted_basis 2 = x 1 • homogenized_point xOne := by
      simpa [hcol2_top] using hcol2_eq
    have hdiff2_top : (Y *ᵥ (lifted_basis 0 - lifted_basis 2)) 0 = 1 - x 1 := by
      simp [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY02]
    obtain ⟨xZero, hxZeroP, hdiff2_eq⟩ :=
      normalizeMemOfMemHomogenizedCone
        (convex_mixedZeroOnePolyhedron A b) hconeDiff2
        (by simpa [hdiff2_top] using sub_pos.mpr hx1_lt)
    have hdiff2_eq' :
        Y *ᵥ (lifted_basis 0 - lifted_basis 2) = (1 - x 1) • homogenized_point xZero := by
      simpa [hdiff2_top] using hdiff2_eq
    have hY12_mul : Y 1 2 = x 0 * x 1 := by
      rcases hx0_binary with hx0 | hx0
      · -- If `x 0 = 0`, the first lifted column has zero height and vanishes.
        have hcol1_zero : Y *ᵥ lifted_basis 1 = 0 := by
          apply eq_zero_of_memHomogenizedCone_of_top_zero hcone1
          simp [mulVec_lifted_basis, hY01, hx0]
        have hY21_zero : Y 2 1 = 0 := by
          simpa [mulVec_lifted_basis] using congr_fun hcol1_zero 2
        have hY12_zero : Y 1 2 = 0 := by
          calc
            Y 1 2 = Y 2 1 := by
              simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hYsymm 1) 2).symm
            _ = 0 := hY21_zero
        simp [hx0, hY12_zero]
      · -- If `x 0 = 1`, the complementary first-face column has zero height and vanishes.
        have hdiff1_zero : Y *ᵥ (lifted_basis 0 - lifted_basis 1) = 0 := by
          apply eq_zero_of_memHomogenizedCone_of_top_zero hconeDiff1
          simp [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY01, hx0]
        have hY21_eq : Y 2 1 = x 1 := by
          have hcoord : (Y *ᵥ (lifted_basis 0 - lifted_basis 1)) 2 = 0 := by
            simpa using congr_fun hdiff1_zero 2
          have : x 1 - Y 2 1 = 0 := by
            simpa [Matrix.mulVec_sub, mulVec_lifted_basis, hY20] using hcoord
          linarith
        have hY12_eq : Y 1 2 = x 1 := by
          calc
            Y 1 2 = Y 2 1 := by
              simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hYsymm 1) 2).symm
            _ = x 1 := hY21_eq
        nlinarith
    have hxOne0_eq : xOne 0 = x 0 := by
      have hcoord :
          x 1 * xOne 0 = x 0 * x 1 := by
        calc
          x 1 * xOne 0 = (x 1 • homogenized_point xOne) 1 := by
            simp [homogenized_point]
          _ = (Y *ᵥ lifted_basis 2) 1 := by rw [← hcol2_eq']
          _ = Y 1 2 := by simp [mulVec_lifted_basis]
          _ = x 0 * x 1 := hY12_mul
      nlinarith
    have hxOne1 : xOne 1 = 1 := by
      have hcoord :
          x 1 = x 1 * homogenized_point xOne 2 := by
        calc
          x 1 = (Y *ᵥ lifted_basis 2) 2 := by
            simp [mulVec_lifted_basis, hdiag2, hY20]
          _ = (x 1 • homogenized_point xOne) 2 := by rw [hcol2_eq']
          _ = x 1 * homogenized_point xOne 2 := by simp
      have hhom2 : homogenized_point xOne 2 = xOne 1 := by
        rfl
      rw [hhom2] at hcoord
      nlinarith
    have hxZero0_eq : xZero 0 = x 0 := by
      have hcoord :
          (1 - x 1) * xZero 0 = x 0 * (1 - x 1) := by
        calc
          (1 - x 1) * xZero 0 = ((1 - x 1) • homogenized_point xZero) 1 := by
            simp [homogenized_point]
          _ = (Y *ᵥ (lifted_basis 0 - lifted_basis 2)) 1 := by rw [← hdiff2_eq']
          _ = Y 1 0 - Y 1 2 := by
            simp [Matrix.mulVec_sub, mulVec_lifted_basis]
          _ = x 0 - x 0 * x 1 := by rw [hY10, hY12_mul]
          _ = x 0 * (1 - x 1) := by ring
      nlinarith
    have hxZero1 : xZero 1 = 0 := by
      have hcoord :
          (1 - x 1) * xZero 1 = 0 := by
        calc
          (1 - x 1) * xZero 1 = (1 - x 1) * homogenized_point xZero 2 := by
            rw [show homogenized_point xZero 2 = xZero 1 by rfl]
          _ = ((1 - x 1) • homogenized_point xZero) 2 := by simp
          _ = (Y *ᵥ (lifted_basis 0 - lifted_basis 2)) 2 := by rw [← hdiff2_eq']
          _ = Y 2 0 - Y 2 2 := by
            simp [Matrix.mulVec_sub, mulVec_lifted_basis]
          _ = 0 := by rw [hdiag2, sub_self]
      nlinarith
    have hxOne_mem : xOne ∈ mixed_zero_one_linear_set A b := by
      refine (mem_mixed_zero_one_linear_set_iff).2 ?_
      refine ⟨hxOneP, ?_, ?_⟩
      · rcases hx0_binary with hx0 | hx0
        · left
          simpa [hx0] using hxOne0_eq
        · right
          simpa [hx0] using hxOne0_eq
      · exact Or.inr hxOne1
    have hxZero_mem : xZero ∈ mixed_zero_one_linear_set A b := by
      refine (mem_mixed_zero_one_linear_set_iff).2 ?_
      refine ⟨hxZeroP, ?_, ?_⟩
      · rcases hx0_binary with hx0 | hx0
        · left
          simpa [hx0] using hxZero0_eq
        · right
          simpa [hx0] using hxZero0_eq
      · exact Or.inl hxZero1
    have hhom :
        homogenized_point x =
          x 1 • homogenized_point xOne + (1 - x 1) • homogenized_point xZero := by
      calc
        homogenized_point x = Y *ᵥ lifted_basis 0 := hcol0.symm
        _ = Y *ᵥ lifted_basis 2 + Y *ᵥ (lifted_basis 0 - lifted_basis 2) := by
          rw [Matrix.mulVec_sub]
          ext j
          simp [Pi.add_apply, sub_eq_add_neg]
        _ = x 1 • homogenized_point xOne + (1 - x 1) • homogenized_point xZero := by
          rw [hcol2_eq', hdiff2_eq']
    have hx_lineMap : AffineMap.lineMap xZero xOne (x 1) = x := by
      ext j
      have hcoord := congr_fun hhom j.succ
      simpa [AffineMap.lineMap_apply_module, homogenized_point, add_comm, add_left_comm, add_assoc]
        using hcoord.symm
    have hx_segment : x ∈ segment ℝ xZero xOne := by
      rw [← hx_lineMap]
      exact lineMap_mem_segment ℝ xZero xOne ⟨hx1_nonneg, hx1_le_one⟩
    exact (segment_subset_convexHull hxZero_mem hxOne_mem) hx_segment

/-- Helper for Exercise 10.10: for a convex owner, every mixed `N` point already lies in that
owner because the first lifted column is a homogenized cone point over the owner's convex hull. -/
lemma mem_of_mem_mixedZeroOneLovaszSchrijverN
    {Q : Set (Fin (p + 2) → ℝ)}
    (hQ_convex : Convex ℝ Q)
    {x : Fin (p + 2) → ℝ}
    (hx : x ∈ mixed_zero_one_lovasz_schrijver_N Q) :
    x ∈ Q := by
  -- Read the first lifted column as `homogenized_point x` and collapse the owner's convex hull.
  rw [mem_mixed_zero_one_lovasz_schrijver_N_iff] at hx
  rcases hx with ⟨Y, hY, hcol0⟩
  rw [isMixedZeroOneLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨-, hcone0, -, -, -, -, -, -⟩
  have hcone0' : homogenized_point x ∈ homogenized_cone Q := by
    simpa [hcol0] using hcone0
  have hxHull : x ∈ convexHull ℝ Q := by
    exact mem_convexHull_of_homogenized_point_mem_homogenized_cone Q hcone0'
  rwa [convexHull_eq_self.2 hQ_convex] at hxHull

/-- Helper for Exercise 10.10: intersecting the polyhedron with a fixed first-coordinate face
preserves convexity. -/
lemma convex_mixedZeroOnePolyhedron_firstCoordinateFace
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ)
    (c : ℝ) :
    Convex ℝ {u : Fin (p + 2) → ℝ | u ∈ mixed_zero_one_polyhedron A b ∧ u 0 = c} := by
  intro x hx y hy a d ha hd had
  refine ⟨convex_mixedZeroOnePolyhedron A b hx.1 hy.1 ha hd had, ?_⟩
  -- The fixed first-coordinate equation is preserved because the coefficients sum to `1`.
  calc
    (a • x + d • y) 0 = a * x 0 + d * y 0 := by simp [Pi.smul_apply]
    _ = a * c + d * c := by rw [hx.2, hy.2]
    _ = (a + d) * c := by ring
    _ = c := by rw [had, one_mul]

/-- Helper for Exercise 10.10: a mixed `N` point on the upper first-coordinate face can be viewed
in the ambient owner and then closed by the already proved one-binary hull lemma. -/
lemma upperFirstFace_mem_convexHull_mixedZeroOneLinearSet
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ)
    (hbox : ∀ {x : Fin (p + 2) → ℝ}, x ∈ mixed_zero_one_polyhedron A b → x 0 ≤ 1 ∧ x 1 ≤ 1)
    {x : Fin (p + 2) → ℝ}
    (hx :
      x ∈ mixed_zero_one_lovasz_schrijver_N
        {u : Fin (p + 2) → ℝ | u ∈ mixed_zero_one_polyhedron A b ∧ u 0 = 1}) :
    x ∈ convexHull ℝ (mixed_zero_one_linear_set A b) := by
  have hxAmbient : x ∈ mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b) :=
    mixedZeroOneLovaszSchrijverN_mono (by intro u hu; exact hu.1) hx
  have hxFace :
      x ∈ {u : Fin (p + 2) → ℝ | u ∈ mixed_zero_one_polyhedron A b ∧ u 0 = 1} :=
    mem_of_mem_mixedZeroOneLovaszSchrijverN
      (convex_mixedZeroOnePolyhedron_firstCoordinateFace A b 1) hx
  -- Transport the face witness to the ambient owner, then use the solved one-binary closure step.
  exact binaryFirstCoordinate_mem_convexHull_mixedZeroOneLinearSet hbox hxAmbient (Or.inr hxFace.2)

/-- Helper for Exercise 10.10: the same ambient transport closes the lower first-coordinate face. -/
lemma lowerFirstFace_mem_convexHull_mixedZeroOneLinearSet
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ)
    (hbox : ∀ {x : Fin (p + 2) → ℝ}, x ∈ mixed_zero_one_polyhedron A b → x 0 ≤ 1 ∧ x 1 ≤ 1)
    {x : Fin (p + 2) → ℝ}
    (hx :
      x ∈ mixed_zero_one_lovasz_schrijver_N
        {u : Fin (p + 2) → ℝ | u ∈ mixed_zero_one_polyhedron A b ∧ u 0 = 0}) :
    x ∈ convexHull ℝ (mixed_zero_one_linear_set A b) := by
  have hxAmbient : x ∈ mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b) :=
    mixedZeroOneLovaszSchrijverN_mono (by intro u hu; exact hu.1) hx
  have hxFace :
      x ∈ {u : Fin (p + 2) → ℝ | u ∈ mixed_zero_one_polyhedron A b ∧ u 0 = 0} :=
    mem_of_mem_mixedZeroOneLovaszSchrijverN
      (convex_mixedZeroOnePolyhedron_firstCoordinateFace A b 0) hx
  -- The lower face has first binary coordinate `0`, so the same one-binary closure applies.
  exact binaryFirstCoordinate_mem_convexHull_mixedZeroOneLinearSet hbox hxAmbient (Or.inl hxFace.2)

/-- Helper for Exercise 10.10: the interior first-coordinate branch should be packaged as a split
into two face-local mixed-`N` witnesses, one on `x 0 = 1` and one on `x 0 = 0`. -/
lemma conditionOnFirstBinaryCoordinate
    {A : Matrix (Fin m) (Fin (p + 2)) ℝ}
    {b : Fin m → ℝ}
    {x : Fin (p + 2) → ℝ}
    (hx : x ∈ mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b))
    (hx0_pos : 0 < x 0)
    (hx0_lt : x 0 < 1) :
    ∃ xOne xZero : Fin (p + 2) → ℝ,
      xOne ∈ mixed_zero_one_lovasz_schrijver_N
          {u : Fin (p + 2) → ℝ | u ∈ mixed_zero_one_polyhedron A b ∧ u 0 = 1} ∧
        xOne 0 = 1 ∧
          xZero ∈ mixed_zero_one_lovasz_schrijver_N
            {u : Fin (p + 2) → ℝ | u ∈ mixed_zero_one_polyhedron A b ∧ u 0 = 0} ∧
            xZero 0 = 0 ∧
              x = x 0 • xOne + (1 - x 0) • xZero := by
  -- Route correction: `splitOnFirstBinaryCoordinateOfInterior` already gives the right points.
  -- The remaining gap is exactly the face-local mixed-`N` ownership of those two normalized
  -- branch points, not their geometry or convex-combination identity.
  -- TODO: condition the original mixed witness on the first binary column so the same `xOne` and
  -- `xZero` become mixed-`N` points of the upper and lower first-coordinate faces.
  sorry

/-- Helper for Exercise 10.10: the remaining hard step is to convert a mixed `N` witness into a
convex combination of mixed binary feasible points. -/
lemma mixedZeroOneLovaszSchrijverN_subset_convexHull_mixedZeroOneLinearSet
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ)
    (hbox : ∀ {x : Fin (p + 2) → ℝ}, x ∈ mixed_zero_one_polyhedron A b → x 0 ≤ 1 ∧ x 1 ≤ 1) :
    mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b) ⊆
      convexHull ℝ (mixed_zero_one_linear_set A b) := by
  intro x hx
  have hx_bounds := firstTwoBounds_of_mem_mixedZeroOneLovaszSchrijverN hbox hx
  rcases hx_bounds with ⟨hx0_nonneg, hx0_le_one, -, -⟩
  by_cases hx0_zero : x 0 = 0
  · -- The lower first-face branch is exactly the already solved one-binary case.
    exact binaryFirstCoordinate_mem_convexHull_mixedZeroOneLinearSet hbox hx (Or.inl hx0_zero)
  by_cases hx0_one : x 0 = 1
  · -- The upper first-face branch is also the one-binary case.
    exact binaryFirstCoordinate_mem_convexHull_mixedZeroOneLinearSet hbox hx (Or.inr hx0_one)
  · have hx0_pos : 0 < x 0 := by
      exact lt_of_le_of_ne hx0_nonneg (Ne.symm hx0_zero)
    have hx0_lt : x 0 < 1 := by
      exact lt_of_le_of_ne hx0_le_one hx0_one
    obtain ⟨xOne, xZero, hxOne, hxOne0, hxZero, hxZero0, hsplit⟩ :=
      conditionOnFirstBinaryCoordinate hx hx0_pos hx0_lt
    have hxOneHull :
        xOne ∈ convexHull ℝ (mixed_zero_one_linear_set A b) :=
      upperFirstFace_mem_convexHull_mixedZeroOneLinearSet A b hbox hxOne
    have hxZeroHull :
        xZero ∈ convexHull ℝ (mixed_zero_one_linear_set A b) :=
      lowerFirstFace_mem_convexHull_mixedZeroOneLinearSet A b hbox hxZero
    have hcomb :
        x 0 • xOne + (1 - x 0) • xZero ∈
          convexHull ℝ (mixed_zero_one_linear_set A b) := by
      -- Reassemble the two face points using the interior coefficients `x 0` and `1 - x 0`.
      refine (convex_convexHull ℝ (mixed_zero_one_linear_set A b))
        hxOneHull hxZeroHull hx0_nonneg ?_ ?_
      · linarith
      · ring
    -- The packaged conditioning lemma already identifies `x` with that convex combination.
    simpa [hsplit] using hcomb

/-- Exercise 10.10. Let `P = {x ∈ ℝ_+^(2 + p) | A x ≥ b}` and
`S = {x ∈ {0,1}^2 × ℝ_+^p | A x ≥ b}`. Assuming the first two coordinates of `P` are bounded
above by `1`, the mixed `0,1` semidefinite and linear one-step Lovasz-Schrijver operators
coincide. -/
theorem exercise_10_10_lovasz_schrijver_N_plus_eq_N
    (A : Matrix (Fin m) (Fin (p + 2)) ℝ)
    (b : Fin m → ℝ)
    (hbox : ∀ {x : Fin (p + 2) → ℝ}, x ∈ mixed_zero_one_polyhedron A b → x 0 ≤ 1 ∧ x 1 ≤ 1) :
    mixed_zero_one_lovasz_schrijver_N_plus (mixed_zero_one_polyhedron A b) =
      mixed_zero_one_lovasz_schrijver_N (mixed_zero_one_polyhedron A b) := by
  refine Set.Subset.antisymm
    (mixed_zero_one_lovasz_schrijver_N_plus_subset_N (mixed_zero_one_polyhedron A b)) ?_
  intro x hx
  -- Route correction: prove `N ⊆ N₊` through the mixed binary convex hull, not by forcing the
  -- original witness itself to be positive semidefinite.
  exact convexHull_mixedZeroOneLinearSet_subset_mixedZeroOneLovaszSchrijverNPlus A b <|
    mixedZeroOneLovaszSchrijverN_subset_convexHull_mixedZeroOneLinearSet A b hbox hx

end Exercise1010
