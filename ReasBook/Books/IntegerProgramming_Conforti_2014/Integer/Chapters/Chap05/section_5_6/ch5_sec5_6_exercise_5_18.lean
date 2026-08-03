import Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_definition_3_14_extra_1
import Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1
import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_27
import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_remark_5_1

open scoped Matrix
open scoped IntegerVectorNotation

section Exercise518

variable {m n : ℕ}

/-- `is_largest_abs_square_subdeterminant A Δ` means that `Δ` is the maximum absolute value of the
determinants of the square submatrices of `A`. -/
def is_largest_abs_square_subdeterminant
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ) : Prop :=
  (∀ ⦃k : ℕ⦄ (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n),
      |(A.submatrix rows cols).det| ≤ Δ) ∧
    ∃ (k : ℕ) (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n),
      Δ = |(A.submatrix rows cols).det|

/-- Unfolding `is_largest_abs_square_subdeterminant A Δ` gives the stated upper-bound and
attainment conditions on the square subdeterminants of `A`. -/
theorem is_largest_abs_square_subdeterminant_iff
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ) :
    is_largest_abs_square_subdeterminant A Δ ↔
      (∀ ⦃k : ℕ⦄ (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n),
        |(A.submatrix rows cols).det| ≤ Δ) ∧
        ∃ (k : ℕ) (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n),
          Δ = |(A.submatrix rows cols).det| :=
  Iff.rfl

/-- Every square subdeterminant of `A` has absolute value at most `Δ` when
`is_largest_abs_square_subdeterminant A Δ` holds. -/
theorem abs_square_subdet_le_of_is_largest_abs_square_subdeterminant
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ)
    {k : ℕ}
    (rows : Fin k ↪ Fin m)
    (cols : Fin k ↪ Fin n) :
    |(A.submatrix rows cols).det| ≤ Δ :=
  hΔ.1 rows cols

/-- If `Δ` is the largest absolute square subdeterminant of `A`, then some square subdeterminant
of `A` attains the value `Δ`. -/
theorem exists_square_subdeterminant_eq_of_is_largest_abs_square_subdeterminant
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ) :
    ∃ (k : ℕ) (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n),
      Δ = |(A.submatrix rows cols).det| :=
  hΔ.2

/-- A finite family `rays` represents the extreme rays of `C` when each listed vector generates an
extreme ray of `C`, different indices represent different rays, and every extreme ray of `C` is
same-ray equivalent to one of the listed vectors. -/
def IsExtremeRayRepresentativeFamily
    (C : Set (Fin n → ℝ))
    {q : ℕ}
    (rays : Fin q → Fin n → ℝ) : Prop :=
  (∀ t : Fin q, IsExtremeRayOfCone C (rays t)) ∧
  Pairwise (fun s t ↦ ¬ SameRay ℝ (rays s) (rays t)) ∧
    ∀ r : Fin n → ℝ, IsExtremeRayOfCone C r → ∃ t : Fin q, SameRay ℝ r (rays t)

/-- Unfolding `IsExtremeRayRepresentativeFamily C rays` gives the source-facing extreme-ray,
pairwise-distinct-ray, and spanning conditions. -/
theorem isExtremeRayRepresentativeFamily_iff
    (C : Set (Fin n → ℝ))
    {q : ℕ}
    (rays : Fin q → Fin n → ℝ) :
    IsExtremeRayRepresentativeFamily C rays ↔
      (∀ t : Fin q, IsExtremeRayOfCone C (rays t)) ∧
        Pairwise (fun s t ↦ ¬ SameRay ℝ (rays s) (rays t)) ∧
          ∀ r : Fin n → ℝ, IsExtremeRayOfCone C r → ∃ t : Fin q, SameRay ℝ r (rays t) :=
  Iff.rfl

theorem IsExtremeRayRepresentativeFamily.isExtremeRay
    {C : Set (Fin n → ℝ)}
    {q : ℕ}
    {rays : Fin q → Fin n → ℝ}
    (hrays : IsExtremeRayRepresentativeFamily C rays)
    (t : Fin q) :
    IsExtremeRayOfCone C (rays t) :=
  hrays.1 t

theorem IsExtremeRayRepresentativeFamily.not_sameRay
    {C : Set (Fin n → ℝ)}
    {q : ℕ}
    {rays : Fin q → Fin n → ℝ}
    (hrays : IsExtremeRayRepresentativeFamily C rays)
    {s t : Fin q}
    (hst : s ≠ t) :
    ¬ SameRay ℝ (rays s) (rays t) :=
  hrays.2.1 hst

theorem IsExtremeRayRepresentativeFamily.exists_sameRay
    {C : Set (Fin n → ℝ)}
    {q : ℕ}
    {rays : Fin q → Fin n → ℝ}
    (hrays : IsExtremeRayRepresentativeFamily C rays)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfCone C r) :
    ∃ t : Fin q, SameRay ℝ r (rays t) :=
  hrays.2.2 r hr

/-- Helper for Exercise 5.18: every generator lies in the pointed-cone hull of its singleton. -/
lemma self_mem_singletonRayHull
    (r : Fin n → ℝ) :
    r ∈ (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  -- The singleton source set already contains the generator.
  exact PointedCone.subset_hull (by simp : r ∈ ({r} : Set (Fin n → ℝ)))

/-- Helper for Exercise 5.18: an extreme-ray generator belongs to the ambient cone it spans in. -/
lemma extremeRay_mem_of_isExtremeRayOfCone
    {C : Set (Fin n → ℝ)}
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfCone C r) :
    r ∈ C := by
  -- Unpack the extreme-ray predicate and evaluate the extreme-subset axiom at the generator.
  have hr_edge :
      IsEdgeOf C (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
    (isExtremeRayOfCone_iff).1 hr
  exact hr_edge.isExtreme.1 (self_mem_singletonRayHull r)

/-- Helper for Exercise 5.18: if `Δ` is the largest absolute square subdeterminant of `A`, then
`Δ` is nonnegative. -/
lemma largestAbsSquareSubdeterminant_nonneg
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ) :
    0 ≤ Δ := by
  -- Use the attained subdeterminant description and the nonnegativity of absolute values.
  rcases exists_square_subdeterminant_eq_of_is_largest_abs_square_subdeterminant A Δ hΔ with
    ⟨k, rows, cols, hdet⟩
  rw [hdet]
  exact abs_nonneg _

/-- Helper for Exercise 5.18: the real coercion of an integer vector belongs to `ℤ^n`. -/
lemma intCastVector_mem_integerVectors
    (z : Fin n → ℤ) :
    (fun i ↦ (z i : ℝ)) ∈ ℤ^n := by
  -- The coercion map itself is the witnessing integer vector.
  exact ⟨z, rfl⟩

/-- Helper for Exercise 5.18: a nonzero integer vector remains nonzero after coercion to `ℝ`. -/
lemma intCastVector_ne_zero
    {z : Fin n → ℤ}
    (hz : z ≠ 0) :
    (fun i ↦ (z i : ℝ)) ≠ 0 := by
  -- Coordinatewise coercion reflects zero because `Int.cast` into `ℝ` is injective.
  intro hcast
  apply hz
  ext i
  have hi : (z i : ℝ) = (0 : ℝ) := by
    simpa using congrFun hcast i
  exact_mod_cast hi

/-- Helper for Exercise 5.18: a nonzero point of the nonnegative kernel cone has a positive
coordinate. -/
lemma exists_positive_coordinate_of_mem_nonnegative_kernel_cone
    (A : Matrix (Fin m) (Fin n) ℤ)
    {x : Fin n → ℝ}
    (hx : x ∈ standard_equality_form (A.map (Int.castRingHom ℝ)) 0)
    (hx_ne : x ≠ 0) :
    ∃ j : Fin n, 0 < x j := by
  -- Only the coordinatewise nonnegativity part is needed to upgrade a nonzero coordinate to
  -- a positive one.
  have hx_nonneg : 0 ≤ x := (mem_standard_equality_form_iff.mp hx).2
  by_contra hpos
  apply hx_ne
  ext j
  by_cases hj : x j = 0
  · exact hj
  · have hzero_ne : (0 : ℝ) ≠ x j := by
      intro h0
      exact hj h0.symm
    have hxj_pos : 0 < x j := lt_of_le_of_ne (hx_nonneg j) hzero_ne
    exact False.elim (hpos ⟨j, hxj_pos⟩)

/-- Helper for Exercise 5.18: every extreme ray of the nonnegative kernel cone has a positive
coordinate. -/
lemma exists_positive_coordinate_of_extremeRay_nonnegative_kernel_cone
    (A : Matrix (Fin m) (Fin n) ℤ)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfCone (standard_equality_form (A.map (Int.castRingHom ℝ)) 0) r) :
    ∃ j : Fin n, 0 < r j := by
  -- First place the extreme generator in the cone, then apply the previous nonzero-vector lemma.
  have hr_mem :
      r ∈ standard_equality_form (A.map (Int.castRingHom ℝ)) 0 :=
    extremeRay_mem_of_isExtremeRayOfCone hr
  have hr_ne : r ≠ 0 := extremeRay_ne_zero hr
  exact exists_positive_coordinate_of_mem_nonnegative_kernel_cone A hr_mem hr_ne

/-- Helper for Exercise 5.18: for a nonnegative integer vector, the integer coordinate gcd is `1`
whenever the gcd of the coordinate absolute values is `1`. -/
lemma intGcd_eq_one_of_nonnegative_primitive
    {z : Fin n → ℤ}
    (hz_nonneg : ∀ i : Fin n, 0 ≤ z i)
    (hz_primitive : Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (z i)) = 1) :
    Finset.univ.gcd (fun i : Fin n ↦ z i) = 1 := by
  -- Rewrite the integer gcd through the nonnegative-coordinate normal form `z i = |z i|`.
  calc
    Finset.univ.gcd (fun i : Fin n ↦ z i)
      = Finset.univ.gcd (fun i : Fin n ↦ ((z i).natAbs : ℤ)) := by
          refine Finset.gcd_congr rfl ?_
          intro i hi
          rw [← Int.eq_natAbs_of_nonneg (hz_nonneg i)]
    _ = ((Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (z i)) : ℕ) : ℤ) := by
          exact coordinate_gcd_int_cast_eq_nat_gcd_natAbs z
    _ = 1 := by
          norm_num [hz_primitive]

/-- Helper for Exercise 5.18: primitive nonnegative integer generators on the same ray are equal.
This is the uniqueness step used to turn the finite primitive box into a representative family. -/
lemma eq_of_sameRay_of_nonnegative_primitiveGenerators
    {z w : Fin n → ℤ}
    (hz_ne : z ≠ 0)
    (hw_ne : w ≠ 0)
    (hz_nonneg : ∀ i : Fin n, 0 ≤ z i)
    (hw_nonneg : ∀ i : Fin n, 0 ≤ w i)
    (hz_primitive : Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (z i)) = 1)
    (hw_primitive : Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (w i)) = 1)
    (hsame : SameRay ℝ (fun i ↦ (z i : ℝ)) (fun i ↦ (w i : ℝ))) :
    z = w := by
  -- Convert the primitive natAbs hypotheses to integer gcd statements usable by Bézout.
  have hz_gcd_int : Finset.univ.gcd (fun i : Fin n ↦ z i) = 1 :=
    intGcd_eq_one_of_nonnegative_primitive hz_nonneg hz_primitive
  have hw_gcd_int : Finset.univ.gcd (fun i : Fin n ↦ w i) = 1 :=
    intGcd_eq_one_of_nonnegative_primitive hw_nonneg hw_primitive
  have hz_cast_ne : (fun i ↦ (z i : ℝ)) ≠ 0 := intCastVector_ne_zero hz_ne
  have hw_cast_ne : (fun i ↦ (w i : ℝ)) ≠ 0 := intCastVector_ne_zero hw_ne
  obtain ⟨α, hα_pos, hα⟩ := hsame.exists_pos_left hz_cast_ne hw_cast_ne
  have hα_coord : ∀ i : Fin n, α * (z i : ℝ) = (w i : ℝ) := by
    -- Evaluate the same-ray scaling identity coordinatewise.
    intro i
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun hα i
  obtain ⟨c, hc⟩ := Finset.gcd_eq_sum_mul Finset.univ (fun i : Fin n ↦ z i)
  have hc_real : (1 : ℝ) =
      Finset.sum Finset.univ (fun i : Fin n ↦ (z i : ℝ) * (c i : ℝ)) := by
    -- Cast the Bézout identity from `ℤ` to `ℝ`.
    have hc_int : (1 : ℤ) = Finset.sum Finset.univ (fun i : Fin n ↦ z i * c i) := by
      simpa [hz_gcd_int] using hc
    exact_mod_cast hc_int
  let k : ℤ := Finset.sum Finset.univ (fun i : Fin n ↦ w i * c i)
  have hk_cast : (k : ℝ) = α := by
    -- Re-express `α` through the Bézout relation, showing that the same-ray scalar is integral.
    calc
      (k : ℝ) = Finset.sum Finset.univ (fun i : Fin n ↦ (w i : ℝ) * (c i : ℝ)) := by
        simp [k]
      _ = Finset.sum Finset.univ (fun i : Fin n ↦ (α * (z i : ℝ)) * (c i : ℝ)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hα_coord i]
      _ = α * Finset.sum Finset.univ (fun i : Fin n ↦ (z i : ℝ) * (c i : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      _ = α * 1 := by
        rw [hc_real]
      _ = α := by
        ring
  have hk_pos_real : (0 : ℝ) < (k : ℝ) := by
    simpa [hk_cast] using hα_pos
  have hk_pos : 0 < k := by
    exact_mod_cast hk_pos_real
  have hk_mul_coord : ∀ i : Fin n, k * z i = w i := by
    -- Replace the real same-ray scalar with its integral value on each coordinate.
    intro i
    have hi_real : (k : ℝ) * (z i : ℝ) = (w i : ℝ) := by
      simpa [hk_cast] using hα_coord i
    exact_mod_cast hi_real
  have hk_dvd_w : k ∣ Finset.univ.gcd (fun i : Fin n ↦ w i) := by
    -- Every coordinate of `w` is a multiple of `k`, so the gcd is also a multiple of `k`.
    refine Finset.dvd_gcd ?_
    intro i hi
    exact ⟨z i, (hk_mul_coord i).symm⟩
  have hk_dvd_one : k ∣ (1 : ℤ) := by
    simpa [hw_gcd_int] using hk_dvd_w
  have hk_eq_one : k = 1 := by
    exact Int.eq_one_of_dvd_one hk_pos.le hk_dvd_one
  -- Substituting the forced scalar `k = 1` identifies the two primitive generators.
  ext i
  calc
    z i = 1 * z i := by ring
    _ = k * z i := by rw [hk_eq_one]
    _ = w i := hk_mul_coord i

/-- Helper for Exercise 5.18: stack the equalities `A x = 0` and the nonnegativity constraints
`x ≥ 0` into one polyhedral inequality matrix. -/
def nonnegativeKernelConstraintMatrix
    (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin ((m + m) + n)) (Fin n) ℤ :=
  let equalities : Matrix (Fin (m + m)) (Fin n) ℤ :=
    (Matrix.fromRows A (-A)).reindex finSumFinEquiv (Equiv.refl _)
  (Matrix.fromRows equalities (-(1 : Matrix (Fin n) (Fin n) ℤ))).reindex
    finSumFinEquiv (Equiv.refl _)

/-- Helper for Exercise 5.18: membership in the stacked inequality owner is exactly membership in
the nonnegative kernel cone `standard_equality_form (A.map _) 0`. -/
lemma mem_nonnegativeKernelConstraintPolyhedron_iff
    (A : Matrix (Fin m) (Fin n) ℤ)
    {x : Fin n → ℝ} :
    x ∈ polyhedron_le_set
          ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
          (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ)) ↔
      x ∈ standard_equality_form (A.map (Int.castRingHom ℝ)) 0 := by
  rw [mem_polyhedron_le_set_iff, mem_standard_equality_form_iff]
  constructor
  · intro hx
    constructor
    · ext i
      -- The paired `A` and `-A` rows force every equality row to vanish.
      have hi_le :
          (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x)
              (Fin.castAdd n (Fin.castAdd m i)) ≤ 0 := hx (Fin.castAdd n (Fin.castAdd m i))
      have hi_neg_le :
          (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x)
              (Fin.castAdd n (Fin.natAdd m i)) ≤ 0 := hx (Fin.castAdd n (Fin.natAdd m i))
      have hAi_le : ((A.map (Int.castRingHom ℝ)) *ᵥ x) i ≤ 0 := by
        simpa [nonnegativeKernelConstraintMatrix, Matrix.mulVec, dotProduct] using hi_le
      have hAi_ge : 0 ≤ ((A.map (Int.castRingHom ℝ)) *ᵥ x) i := by
        have hneg : -((A.map (Int.castRingHom ℝ)) *ᵥ x) i ≤ 0 := by
          simpa [nonnegativeKernelConstraintMatrix, Matrix.mulVec, dotProduct] using hi_neg_le
        linarith
      exact le_antisymm hAi_le hAi_ge
    · intro j
      -- The `-I` block is equivalent to coordinatewise nonnegativity.
      have hj_le :
          (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ x)
              (Fin.natAdd (m + m) j) ≤ 0 := hx (Fin.natAdd (m + m) j)
      have hnegx : -x j ≤ 0 := by
        simpa [nonnegativeKernelConstraintMatrix, Matrix.mulVec, dotProduct] using hj_le
      linarith
  · rintro ⟨hx_eq, hx_nonneg⟩ i
    -- Split the stacked system into an `A` row, a `-A` row, or a `-I` row.
    cases houter : finSumFinEquiv.symm i with
    | inl r =>
        cases hinner : finSumFinEquiv.symm r with
        | inl iA =>
            simpa [nonnegativeKernelConstraintMatrix, houter, hinner,
              Matrix.mulVec, dotProduct, hx_eq]
        | inr iNegA =>
            simpa [nonnegativeKernelConstraintMatrix, houter, hinner,
              Matrix.mulVec, dotProduct, hx_eq]
    | inr j =>
        have hnegx : -x j ≤ 0 := by
          linarith [hx_nonneg j]
        simpa [nonnegativeKernelConstraintMatrix, houter, Matrix.mulVec, dotProduct] using hnegx

/-- Helper for Exercise 5.18: the nonnegative kernel cone is exactly the stacked polyhedron
defined by `nonnegativeKernelConstraintMatrix A`. -/
lemma standard_equality_form_eq_nonnegativeKernelConstraintPolyhedron
    (A : Matrix (Fin m) (Fin n) ℤ) :
    standard_equality_form (A.map (Int.castRingHom ℝ)) 0 =
      polyhedron_le_set
        ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
        (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ)) := by
  ext x
  simpa [eq_comm] using (mem_nonnegativeKernelConstraintPolyhedron_iff A (x := x))

/-- Helper for Exercise 5.18: the nonnegative kernel cone is pointed because a lineality
direction would have to be both coordinatewise nonnegative and coordinatewise nonpositive. -/
lemma nonnegativeKernelConstraintPolyhedron_pointed
    (A : Matrix (Fin m) (Fin n) ℤ) :
    is_pointed
      (polyhedron_le_set
        ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
        (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))) := by
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro d hd
  have hzero_mem :
      (0 : Fin n → ℝ) ∈
        polyhedron_le_set
          ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
          (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ)) := by
    simpa [standard_equality_form_eq_nonnegativeKernelConstraintPolyhedron A,
      mem_standard_equality_form_iff]
  have hd_mem :
      d ∈ polyhedron_le_set
        ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
        (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ)) := by
    simpa using (mem_linealitySpace_iff.mp hd) hzero_mem (1 : ℝ)
  have hnegd_mem :
      -d ∈ polyhedron_le_set
        ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
        (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ)) := by
    simpa using (mem_linealitySpace_iff.mp hd) hzero_mem (-1 : ℝ)
  have hd_nonneg :
      0 ≤ d := (mem_standard_equality_form_iff.mp
        ((standard_equality_form_eq_nonnegativeKernelConstraintPolyhedron A).symm ▸ hd_mem)).2
  have hnegd_nonneg :
      0 ≤ -d := (mem_standard_equality_form_iff.mp
        ((standard_equality_form_eq_nonnegativeKernelConstraintPolyhedron A).symm ▸ hnegd_mem)).2
  ext j
  linarith [hd_nonneg j, hnegd_nonneg j]

/-- Helper for Exercise 5.18: the stacked polyhedral owner has itself as recession cone because
its right-hand side is zero. -/
lemma recessionCone_eq_nonnegativeKernelConstraintPolyhedron
    (A : Matrix (Fin m) (Fin n) ℤ) :
    recessionCone
        (polyhedron_le_set
          ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
          (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))) =
      polyhedron_le_set
        ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
        (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ)) := by
  have hnonempty :
      (polyhedron_le_set
          ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
          (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [standard_equality_form_eq_nonnegativeKernelConstraintPolyhedron A,
      mem_standard_equality_form_iff]
  rw [recessionCone_polyhedron_eq_matrix_polyhedral_cone
      (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)))
      (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))
      hnonempty]
  ext x
  rw [mem_matrix_polyhedral_cone, mem_polyhedron_le_set_iff]

/-- Helper for Exercise 5.18: every extreme ray of the nonnegative kernel cone determines
`n - 1` active linearly independent rows of the stacked inequality owner. -/
lemma exists_active_linearlyIndependent_rows_of_extremeRay_nonnegative_kernel_cone
    (A : Matrix (Fin m) (Fin n) ℤ)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfCone (standard_equality_form (A.map (Int.castRingHom ℝ)) 0) r) :
    ∃ I : Fin (n - 1) ↪ Fin ((m + m) + n),
      (∀ i : Fin (n - 1),
        (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ r) (I i) = 0) ∧
        LinearIndependent ℝ
          (fun i : Fin (n - 1) ↦
            ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) (I i)) := by
  let P : Set (Fin n → ℝ) :=
    polyhedron_le_set
      ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ))
      (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))
  have hnonempty : P.Nonempty := by
    refine ⟨0, ?_⟩
    simpa [P, standard_equality_form_eq_nonnegativeKernelConstraintPolyhedron A,
      mem_standard_equality_form_iff]
  have hpointed : is_pointed P := by
    simpa [P] using nonnegativeKernelConstraintPolyhedron_pointed A
  have hr_poly : IsExtremeRayOfPolyhedron P r := by
    -- Rewrite the cone owner through the zero-right-hand-side polyhedral presentation.
    rw [isExtremeRayOfPolyhedron_iff]
    simpa [P, recessionCone_eq_nonnegativeKernelConstraintPolyhedron A,
      standard_equality_form_eq_nonnegativeKernelConstraintPolyhedron A] using hr
  -- Exercise 3.27 already extracts the active independent rows once the owner is in polyhedral form.
  simpa [P] using
    extreme_recession_ray_exists_active_linearlyIndependent_rows
      (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)))
      (fun _ : Fin ((m + m) + n) ↦ (0 : ℝ))
      hnonempty hpointed hr_poly

/-- Helper for Exercise 5.18: any vector on the line spanned by `r` can be oriented onto the ray
generated by `r` after possibly flipping its sign. -/
lemma sameRay_or_sameRay_neg_of_mem_span_singleton
    {r s : Fin n → ℝ}
    (hs_span : s ∈ Submodule.span ℝ ({r} : Set (Fin n → ℝ))) :
    SameRay ℝ r s ∨ SameRay ℝ r (-s) := by
  rcases Submodule.mem_span_singleton.mp hs_span with ⟨μ, rfl⟩
  -- The line witness is already a scalar multiple of `r`; only the sign of the scalar matters.
  by_cases hμ : 0 ≤ μ
  · -- A nonnegative scalar leaves the vector on the same ray.
    exact Or.inl (SameRay.sameRay_nonneg_smul_right r hμ)
  · have hnegμ : 0 ≤ -μ := by linarith
    -- A negative scalar becomes nonnegative after flipping the resulting vector.
    exact Or.inr (by simpa [neg_smul] using (SameRay.sameRay_nonneg_smul_right r hnegμ))

/-- Helper for Exercise 5.18: once an integer vector is on the same real ray as a point of the
nonnegative kernel cone, every integer coordinate is nonnegative. -/
lemma intCastVector_nonneg_of_sameRay_mem_nonnegative_kernel_cone
    (A : Matrix (Fin m) (Fin n) ℤ)
    {r : Fin n → ℝ}
    (hr_mem : r ∈ standard_equality_form (A.map (Int.castRingHom ℝ)) 0)
    (hr_ne : r ≠ 0)
    {z : Fin n → ℤ}
    (hsame : SameRay ℝ r (fun i ↦ (z i : ℝ))) :
    ∀ i : Fin n, 0 ≤ z i := by
  have hr_nonneg : 0 ≤ r := (mem_standard_equality_form_iff.mp hr_mem).2
  obtain ⟨μ, hμ_nonneg, hz_eq⟩ := hsame.exists_nonneg_left hr_ne
  intro i
  have hz_cast_nonneg : 0 ≤ (z i : ℝ) := by
    -- The same-ray scaling writes the casted integer vector as a nonnegative multiple of `r`.
    calc
      0 ≤ μ * r i := mul_nonneg hμ_nonneg (hr_nonneg i)
      _ = ((fun j ↦ (z j : ℝ)) i) := by
            simpa [Pi.smul_apply, smul_eq_mul] using congrFun hz_eq i
  exact_mod_cast hz_cast_nonneg

/-- Helper for Exercise 5.18: an integer kernel witness for the selected stacked rows lies on the
line spanned by the extreme-ray generator. -/
lemma intKernelWitness_mem_span_singleton_of_selected_rows
    (A : Matrix (Fin m) (Fin n) ℤ)
    {r : Fin n → ℝ}
    (hr_ne : r ≠ 0)
    (I : Fin (n - 1) ↪ Fin ((m + m) + n))
    (hI_active : ∀ i : Fin (n - 1),
      (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ
      (fun i : Fin (n - 1) ↦ ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) (I i)))
    {z : Fin n → ℤ}
    (hz_zero : ((nonnegativeKernelConstraintMatrix A).submatrix I id) *ᵥ z = 0) :
    (fun i ↦ (z i : ℝ)) ∈ Submodule.span ℝ ({r} : Set (Fin n → ℝ)) := by
  -- Cast the selected-row integer kernel relation to `ℝ`, then invoke the existing line lemma.
  refine mem_span_singleton_of_selected_rows_zero
    (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)))
    hr_ne I hI_active hI_linearIndependent ?_
  intro i
  have hi_int : (((nonnegativeKernelConstraintMatrix A).submatrix I id) *ᵥ z) i = 0 := by
    simpa using congrFun hz_zero i
  have hi_real :
      ((((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ
          (fun j ↦ (z j : ℝ))) (I i)) = 0 := by
    exact_mod_cast hi_int
  exact hi_real

/-- Helper for Exercise 5.18: orient a bounded integral line witness onto the nonnegative ray of
the extreme-ray generator. -/
lemma existsBoundedSameRayGenerator_of_intKernelWitness
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ)
    {r : Fin n → ℝ}
    (hr_mem : r ∈ standard_equality_form (A.map (Int.castRingHom ℝ)) 0)
    (hr_ne : r ≠ 0)
    (I : Fin (n - 1) ↪ Fin ((m + m) + n))
    (hI_active : ∀ i : Fin (n - 1),
      (((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) *ᵥ r) (I i) = 0)
    (hI_linearIndependent : LinearIndependent ℝ
      (fun i : Fin (n - 1) ↦ ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) (I i)))
    {z : Fin n → ℤ}
    (hz_ne : z ≠ 0)
    (hz_zero : ((nonnegativeKernelConstraintMatrix A).submatrix I id) *ᵥ z = 0)
    (hz_abs : ∀ i : Fin n, |z i| ≤ Δ) :
    ∃ z' : Fin n → ℤ,
      SameRay ℝ r (fun i ↦ (z' i : ℝ)) ∧
        z' ≠ 0 ∧
        ∀ i : Fin n, 0 ≤ z' i ∧ z' i ≤ Δ := by
  have hs_span :
      (fun i ↦ (z i : ℝ)) ∈ Submodule.span ℝ ({r} : Set (Fin n → ℝ)) :=
    intKernelWitness_mem_span_singleton_of_selected_rows
      A hr_ne I hI_active hI_linearIndependent hz_zero
  rcases sameRay_or_sameRay_neg_of_mem_span_singleton hs_span with hsame | hsame
  · -- When the line witness already points along the ray, use nonnegativity plus `|z i| ≤ Δ`.
    have hz_nonneg :
        ∀ i : Fin n, 0 ≤ z i :=
      intCastVector_nonneg_of_sameRay_mem_nonnegative_kernel_cone A hr_mem hr_ne hsame
    refine ⟨z, hsame, hz_ne, ?_⟩
    intro i
    have hz_abs_i : |z i| ≤ Δ := hz_abs i
    rw [abs_of_nonneg (hz_nonneg i)] at hz_abs_i
    exact ⟨hz_nonneg i, hz_abs_i⟩
  · -- Otherwise flip the sign: the absolute-value bound is unchanged and the ray orientation fixes.
    let z' : Fin n → ℤ := fun i ↦ -z i
    have hsame' : SameRay ℝ r (fun i ↦ (z' i : ℝ)) := by
      simpa [z', Pi.neg_apply] using hsame
    have hz'_ne : z' ≠ 0 := by
      intro hz'_zero
      apply hz_ne
      ext i
      have hi : z' i = 0 := by simpa using congrFun hz'_zero i
      exact neg_eq_zero.mp (by simpa [z'] using hi)
    have hz'_nonneg :
        ∀ i : Fin n, 0 ≤ z' i :=
      intCastVector_nonneg_of_sameRay_mem_nonnegative_kernel_cone A hr_mem hr_ne hsame'
    refine ⟨z', hsame', hz'_ne, ?_⟩
    intro i
    have hz'_abs_i : |z' i| ≤ Δ := by
      simpa [z'] using hz_abs i
    rw [abs_of_nonneg (hz'_nonneg i)] at hz'_abs_i
    exact ⟨hz'_nonneg i, hz'_abs_i⟩

/-- Helper for Exercise 5.18: selected active rows of the stacked constraint matrix admit a
nonzero bounded integer kernel witness. -/
lemma existsBoundedIntegralKernelWitness_of_selectedActiveRows
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ)
    (I : Fin (n - 1) ↪ Fin ((m + m) + n))
    (hI_linearIndependent : LinearIndependent ℝ
      (fun i : Fin (n - 1) ↦ ((nonnegativeKernelConstraintMatrix A).map (Int.castRingHom ℝ)) (I i))) :
    ∃ z : Fin n → ℤ,
      z ≠ 0 ∧
        ((nonnegativeKernelConstraintMatrix A).submatrix I id) *ᵥ z = 0 ∧
        ∀ i : Fin n, |z i| ≤ Δ := by
  -- Route correction: the unresolved frontier is now only the rectangular Cramer bridge on the
  -- selected active-row matrix `((nonnegativeKernelConstraintMatrix A).submatrix I id)`.
  -- TODO: choose a full-row-rank column basis of the selected `(n - 1) × n` matrix, build the
  -- deleted-minor/Cramer kernel vector, and bound its coordinates by `Δ` via maximal minors of
  -- the selected stacked matrix.
  let _ := hΔ
  let _ := hI_linearIndependent
  sorry

/-- Helper for Exercise 5.18: every extreme ray of the nonnegative kernel cone admits a primitive
integral generator whose coordinates lie in `[0, Δ]`. -/
lemma existsIntegralBoundedSameRayGenerator_of_extremeRay
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfCone (standard_equality_form (A.map (Int.castRingHom ℝ)) 0) r) :
    ∃ z : Fin n → ℤ,
      SameRay ℝ r (fun i ↦ (z i : ℝ)) ∧
        z ≠ 0 ∧
        ∀ i : Fin n, 0 ≤ z i ∧ z i ≤ Δ := by
  have hr_mem :
      r ∈ standard_equality_form (A.map (Int.castRingHom ℝ)) 0 :=
    extremeRay_mem_of_isExtremeRayOfCone hr
  have hr_ne : r ≠ 0 := extremeRay_ne_zero hr
  obtain ⟨I, hI_active, hI_linearIndependent⟩ :=
    exists_active_linearlyIndependent_rows_of_extremeRay_nonnegative_kernel_cone A hr
  obtain ⟨z, hz_ne, hz_zero, hz_abs⟩ :=
    existsBoundedIntegralKernelWitness_of_selectedActiveRows
      A Δ hΔ I hI_linearIndependent
  -- Route correction: once the bounded integer kernel witness is available, only orientation onto
  -- the extreme ray and the conversion from `|z i| ≤ Δ` to `[0, Δ]` remain.
  exact
    existsBoundedSameRayGenerator_of_intKernelWitness
      A Δ hΔ hr_mem hr_ne I hI_active hI_linearIndependent hz_ne hz_zero hz_abs

/-- Helper for Exercise 5.18: every extreme ray of the nonnegative kernel cone admits a primitive
integral generator whose coordinates lie in `[0, Δ]`. -/
lemma existsPrimitiveBoundedIntegralSameRayGenerator_of_extremeRay
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ)
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfCone (standard_equality_form (A.map (Int.castRingHom ℝ)) 0) r) :
    ∃ z : Fin n → ℤ,
      SameRay ℝ r (fun i ↦ (z i : ℝ)) ∧
        z ≠ 0 ∧
        (∀ i : Fin n, 0 ≤ z i ∧ z i ≤ Δ) ∧
        Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (z i)) = 1 := by
  obtain ⟨z, hsame, hz_ne, hz_bounds⟩ :=
    existsIntegralBoundedSameRayGenerator_of_extremeRay A Δ hΔ hr
  set gN : ℕ := Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (z i)) with hgN
  let zPrimitive : Fin n → ℤ := fun i ↦ z i / gN
  have hg_pos : 0 < gN := by
    -- The coordinate gcd of a nonzero integer vector is positive.
    simpa [hgN] using coordinate_gcd_pos z hz_ne
  have hz_dvd : ∀ i : Fin n, (gN : ℤ) ∣ z i := by
    -- Each coordinate is divisible by the coordinate gcd.
    intro i
    rw [Int.natCast_dvd]
    simpa [hgN] using
      (Finset.gcd_dvd (b := i) (f := fun j : Fin n ↦ Int.natAbs (z j)) (by simp))
  have hz_sameRay_primitive :
      SameRay ℝ (fun i ↦ (z i : ℝ)) (fun i ↦ (zPrimitive i : ℝ)) := by
    -- Dividing by the positive coordinate gcd keeps the vector on the same real ray.
    have hcast_eq :
        (fun i ↦ (z i : ℝ)) = (gN : ℝ) • (fun i ↦ (zPrimitive i : ℝ)) := by
      ext i
      calc
        (z i : ℝ) = (((gN : ℤ) * zPrimitive i : ℤ) : ℝ) := by
          simpa [zPrimitive] using congrArg (fun t : ℤ ↦ (t : ℝ)) (Int.mul_ediv_cancel' (hz_dvd i)).symm
        _ = (gN : ℝ) * (zPrimitive i : ℝ) := by
          rw [Int.cast_mul]
        _ = ((gN : ℝ) • (fun j ↦ (zPrimitive j : ℝ))) i := by
          simp [Pi.smul_apply, smul_eq_mul]
    rw [hcast_eq]
    exact SameRay.sameRay_pos_smul_left (fun i ↦ (zPrimitive i : ℝ)) (by exact_mod_cast hg_pos)
  have hsamePrimitive : SameRay ℝ r (fun i ↦ (zPrimitive i : ℝ)) := by
    -- Compose the geometric same-ray witness with the positive gcd rescaling.
    exact SameRay.trans hsame hz_sameRay_primitive
      (fun hz_zero ↦ False.elim ((intCastVector_ne_zero hz_ne) hz_zero))
  have hzPrimitive_ne : zPrimitive ≠ 0 := by
    -- A positive rescaling of a nonzero vector cannot become zero after dividing by the gcd.
    intro hzPrimitive_zero
    apply hz_ne
    ext i
    calc
      z i = (gN : ℤ) * zPrimitive i := by
        simpa [zPrimitive] using (Int.mul_ediv_cancel' (hz_dvd i)).symm
      _ = 0 := by simp [hzPrimitive_zero]
  have hzPrimitive_bounds : ∀ i : Fin n, 0 ≤ zPrimitive i ∧ zPrimitive i ≤ Δ := by
    intro i
    have hzi_nonneg : 0 ≤ z i := (hz_bounds i).1
    have hzi_le : z i ≤ Δ := (hz_bounds i).2
    have hzPrimitive_nonneg : 0 ≤ zPrimitive i := by
      -- Integer division by a positive gcd preserves nonnegativity.
      exact Int.ediv_nonneg hzi_nonneg (by exact_mod_cast (Nat.zero_le gN))
    have hg_one_le : (1 : ℤ) ≤ gN := by
      exact_mod_cast (Nat.succ_le_of_lt hg_pos)
    have hzPrimitive_le_z : zPrimitive i ≤ z i := by
      -- Since `gN ≥ 1`, the normalized coordinate is bounded by the original coordinate.
      calc
        zPrimitive i ≤ (gN : ℤ) * zPrimitive i := by
          simpa using mul_le_mul_of_nonneg_right hg_one_le hzPrimitive_nonneg
        _ = z i := by
          simpa [zPrimitive] using (Int.mul_ediv_cancel' (hz_dvd i))
    exact ⟨hzPrimitive_nonneg, hzPrimitive_le_z.trans hzi_le⟩
  have hzPrimitive_gcd :
      Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (zPrimitive i)) = 1 := by
    -- Remark 5.1 provides primitiveness after dividing by the coordinate gcd.
    simpa [zPrimitive, hgN] using normalized_split_vector_gcd_eq_one z hz_ne
  exact ⟨zPrimitive, hsamePrimitive, hzPrimitive_ne, hzPrimitive_bounds, hzPrimitive_gcd⟩

/-- Exercise 5.18. Let `C = {x ∈ ℝ^n | A x = 0, x ≥ 0}` where `A` is an integral matrix. Let `Δ`
be the largest among the absolute values of the determinants of the square submatrices of `A`.
Then the extreme rays of `C` admit a finite representative family of integral vectors whose
coordinates all lie in `[-Δ, Δ]`. -/
theorem exists_integral_bounded_extreme_ray_representative_family_of_nonnegative_kernel_cone
    (A : Matrix (Fin m) (Fin n) ℤ)
    (Δ : ℤ)
    (hΔ : is_largest_abs_square_subdeterminant A Δ) :
    ∃ q : ℕ,
      ∃ rays : Fin q → Fin n → ℝ,
        IsExtremeRayRepresentativeFamily
            (standard_equality_form (A.map (Int.castRingHom ℝ)) 0) rays ∧
          (∀ t : Fin q, rays t ∈ ℤ^n) ∧
          ∀ t : Fin q, ∀ j : Fin n, (-(Δ : ℝ)) ≤ rays t j ∧ rays t j ≤ (Δ : ℝ) := by
  classical
  let C : Set (Fin n → ℝ) := standard_equality_form (A.map (Int.castRingHom ℝ)) 0
  let box : Set (Fin n → ℤ) := {z | ∀ i : Fin n, z i ∈ Set.Icc 0 Δ}
  let primitiveExtremeBox : Set (Fin n → ℤ) :=
    {z |
      z ≠ 0 ∧
        (∀ i : Fin n, 0 ≤ z i ∧ z i ≤ Δ) ∧
        Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (z i)) = 1 ∧
        IsExtremeRayOfCone C (fun i ↦ (z i : ℝ))}
  have hΔ_nonneg : 0 ≤ Δ := largestAbsSquareSubdeterminant_nonneg A Δ hΔ
  have hboxFinite : box.Finite := by
    -- The bounded integer coordinate box is finite.
    simpa [box, Set.pi] using
      (Set.Finite.pi' (t := fun i : Fin n ↦ Set.Icc (0 : ℤ) Δ)
        fun i ↦ Set.finite_Icc (0 : ℤ) Δ)
  have hprimitiveExtremeBoxFinite : primitiveExtremeBox.Finite := by
    -- Filtering the box by primitive and extreme-ray conditions preserves finiteness.
    refine hboxFinite.subset ?_
    intro z hz
    exact hz.2.1
  obtain ⟨q, zs, hzs_inj, hzs_range⟩ := hprimitiveExtremeBoxFinite.fin_param
  let rays : Fin q → Fin n → ℝ := fun t i ↦ (zs t i : ℝ)
  refine ⟨q, rays, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro t
      -- Each enumerated vector was filtered to be an extreme-ray generator.
      have ht_mem : zs t ∈ primitiveExtremeBox := by
        rw [← hzs_range]
        exact ⟨t, rfl⟩
      exact ht_mem.2.2.2
    · intro s t hst
      intro hsame
      -- Same-ray primitive nonnegative generators must coincide, contradicting injectivity.
      have hs_mem : zs s ∈ primitiveExtremeBox := by
        rw [← hzs_range]
        exact ⟨s, rfl⟩
      have ht_mem : zs t ∈ primitiveExtremeBox := by
        rw [← hzs_range]
        exact ⟨t, rfl⟩
      have hEq :
          zs s = zs t :=
        eq_of_sameRay_of_nonnegative_primitiveGenerators
          hs_mem.1
          ht_mem.1
          (fun i ↦ (hs_mem.2.1 i).1)
          (fun i ↦ (ht_mem.2.1 i).1)
          hs_mem.2.2.1
          ht_mem.2.2.1
          hsame
      exact hst (hzs_inj hEq)
    · intro r hr
      -- Coverage comes from the bounded primitive same-ray generator lemma.
      obtain ⟨z, hsame, hz_ne, hz_bounds, hz_primitive⟩ :=
        existsPrimitiveBoundedIntegralSameRayGenerator_of_extremeRay A Δ hΔ hr
      have hz_extreme : IsExtremeRayOfCone C (fun i ↦ (z i : ℝ)) := by
        -- Replacing an extreme generator by a nonzero vector on the same ray preserves the ray.
        exact isExtremeRayOfCone_of_sameRay hr hsame (intCastVector_ne_zero hz_ne)
      have hz_mem : z ∈ primitiveExtremeBox :=
        ⟨hz_ne, hz_bounds, hz_primitive, hz_extreme⟩
      rw [← hzs_range] at hz_mem
      rcases hz_mem with ⟨t, rfl⟩
      exact ⟨t, hsame⟩
  · intro t
    -- The enumerated rays are integer vectors by construction.
    exact intCastVector_mem_integerVectors (zs t)
  · intro t j
    -- Nonnegativity and `Δ ≥ 0` convert the `[0, Δ]` bounds into `[-Δ, Δ]`.
    have ht_mem : zs t ∈ primitiveExtremeBox := by
      rw [← hzs_range]
      exact ⟨t, rfl⟩
    constructor
    · have hzj_nonneg_real : (0 : ℝ) ≤ rays t j := by
        exact_mod_cast (ht_mem.2.1 j).1
      have hΔ_nonneg_real : (0 : ℝ) ≤ (Δ : ℝ) := by
        exact_mod_cast hΔ_nonneg
      linarith
    · exact_mod_cast (ht_mem.2.1 j).2

end Exercise518
