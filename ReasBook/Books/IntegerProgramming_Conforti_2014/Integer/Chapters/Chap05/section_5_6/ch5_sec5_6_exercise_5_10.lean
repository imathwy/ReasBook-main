import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import Integer.Chapters.Chap04.section_4_8.ch4_sec4_8_remark_4_32
import Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_38
import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import Integer.Chapters.Chap05.section_5_2.ch5_sec5_2_definition_5_2_extra_1

open scoped BigOperators IntegerVectorNotation

-- Semantic recall note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available in this runner, so the exercise below reuses the existing Chapter 4 mixed-space
-- owners `MixedRealPoint`, `mixed_integer_points`, and `ℤ^n`, together with the canonical
-- Section 3.18 facet owner `IsFacetOf` for the mixed-space conclusion.

section Exercise510

variable {n p : ℕ}

/-- The index set `J⁻ = {j | g_j < 0}` from Exercise 5.10. -/
noncomputable def exercise_5_10_negative_index_set (g : Fin p → ℝ) : Finset (Fin p) :=
  Finset.univ.filter fun j : Fin p ↦ g j < 0

/-- Membership in `exercise_5_10_negative_index_set g` is exactly the inequality `g j < 0`. -/
theorem mem_exercise_5_10_negative_index_set_iff
    (g : Fin p → ℝ) (j : Fin p) :
    j ∈ exercise_5_10_negative_index_set g ↔ g j < 0 := by
  simp [exercise_5_10_negative_index_set]

/-- The mixed-integer set
`S = {(x, y) ∈ ℤ^n × ℝ_+^p | ∑ a_j x_j + ∑ g_j y_j ≤ b}`
from Exercise 5.10, embedded in `ℝ^n × ℝ^p`. -/
def exercise_5_10_mixed_integer_set
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Set (MixedRealPoint n p) :=
  mixed_integer_points
    {xy |
      (∀ j : Fin p, 0 ≤ xy.2 j) ∧
        mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b}

/-- Membership in `exercise_5_10_mixed_integer_set a g b` expands to integer-valued first
coordinates, nonnegative continuous coordinates, and the defining linear inequality. -/
theorem mem_exercise_5_10_mixed_integer_set_iff
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    xy ∈ exercise_5_10_mixed_integer_set a g b ↔
      xy.1 ∈ ℤ^n ∧
        (∀ j : Fin p, 0 ≤ xy.2 j) ∧
          mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b := by
  rw [exercise_5_10_mixed_integer_set, mem_mixed_integer_points_iff, mem_mixed_integer_lattice_iff]
  simp [and_left_comm, and_comm]

/-- The left-hand side of the inequality in Exercise 5.10:
`∑ ⌊a_j⌋ x_j + (1 / (1 - f)) * ∑_{j ∈ J⁻} g_j y_j`.
Since `a_j ∈ ℤ`, the coefficient term is written directly as `a_j`. -/
noncomputable def exercise_5_10_cut_value
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) : ℝ :=
  (∑ j, (a j : ℝ) * xy.1 j) +
    (1 / (1 - Int.fract b)) *
      Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j)

/-- Expanding `exercise_5_10_cut_value` recovers the source inequality from Exercise 5.10. -/
theorem exercise_5_10_cut_value_eq
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    exercise_5_10_cut_value a g b xy =
      (∑ j, (a j : ℝ) * xy.1 j) +
        (1 / (1 - Int.fract b)) *
          Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j) :=
  rfl

/-- The equality face of `conv(S)` cut out by the Exercise 5.10 inequality. -/
def exercise_5_10_cut_face
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Set (MixedRealPoint n p) :=
  {xy |
    xy ∈ convexHull ℝ (exercise_5_10_mixed_integer_set a g b) ∧
      exercise_5_10_cut_value a g b xy = (Int.floor b : ℝ)}

/-- Membership in `exercise_5_10_cut_face a g b` means lying in `conv(S)` and saturating the
Exercise 5.10 cut inequality. -/
theorem mem_exercise_5_10_cut_face_iff
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    xy ∈ exercise_5_10_cut_face a g b ↔
      xy ∈ convexHull ℝ (exercise_5_10_mixed_integer_set a g b) ∧
        exercise_5_10_cut_value a g b xy = (Int.floor b : ℝ) :=
  Iff.rfl

/-- Helper for Exercise 5.10: the negative continuous contribution is nonpositive on the mixed
integer set because every selected coefficient is negative while every continuous coordinate is
nonnegative. -/
lemma negativeContribution_nonpos
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p)
    (hxy : xy ∈ exercise_5_10_mixed_integer_set a g b) :
    Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j) ≤ 0 := by
  rcases (mem_exercise_5_10_mixed_integer_set_iff a g b xy).1 hxy with ⟨_, hy_nonneg, _⟩
  -- Each selected term has a negative coefficient and a nonnegative variable value.
  refine Finset.sum_nonpos ?_
  intro j hj
  have hj_neg : g j < 0 := (mem_exercise_5_10_negative_index_set_iff g j).1 hj
  exact mul_nonpos_of_nonpos_of_nonneg hj_neg.le (hy_nonneg j)

/-- Helper for Exercise 5.10: removing the nonnegative `g_j y_j` terms can only decrease the
continuous part of the original row inequality. -/
lemma negativeContribution_le_totalContribution
    (g : Fin p → ℝ)
    (xy : MixedRealPoint n p)
    (hy_nonneg : ∀ j : Fin p, 0 ≤ xy.2 j) :
    Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j) ≤
      ∑ j, g j * xy.2 j := by
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ)
      (p := fun j : Fin p ↦ g j < 0)
      (f := fun j : Fin p ↦ g j * xy.2 j)
  let nonnegativeIndexSet : Finset (Fin p) :=
    Finset.univ.filter fun j : Fin p ↦ ¬ g j < 0
  have hrest_nonneg :
      0 ≤ Finset.sum nonnegativeIndexSet (fun j ↦ g j * xy.2 j) := by
    -- The complementary summands come from coefficients `g_j ≥ 0`.
    refine Finset.sum_nonneg ?_
    intro j hj
    have hj_nonneg : 0 ≤ g j := by
      exact le_of_not_gt (Finset.mem_filter.1 hj).2
    exact mul_nonneg hj_nonneg (hy_nonneg j)
  -- Splitting the full sum into the negative and nonnegative blocks isolates the desired bound.
  have hsplit' :
      ∑ j, g j * xy.2 j =
        Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j) +
          Finset.sum nonnegativeIndexSet (fun j ↦ g j * xy.2 j) := by
    simpa [exercise_5_10_negative_index_set, nonnegativeIndexSet] using hsplit.symm
  linarith [hsplit', hrest_nonneg]

/-- Helper for Exercise 5.10: once the integer part of the row and the negative slack are
isolated, floor arithmetic turns the original row bound into the mixed cut bound. -/
lemma cutBound_of_integerRowAndNegativeSlack
    (b : ℝ)
    (z : ℤ)
    {s : ℝ}
    (hs_nonpos : s ≤ 0)
    (hsum : (z : ℝ) + s ≤ b) :
    (z : ℝ) + s / (1 - Int.fract b) ≤ (Int.floor b : ℝ) := by
  have hfract_nonneg : 0 ≤ Int.fract b := Int.fract_nonneg b
  have hden_pos : 0 < 1 - Int.fract b := by
    linarith [Int.fract_lt_one b]
  by_cases hzle : z ≤ Int.floor b
  · -- If the integer row is already at most `⌊b⌋`, the negative slack term only helps.
    have hsdiv_nonpos : s / (1 - Int.fract b) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hs_nonpos hden_pos.le
    have hz_real : (z : ℝ) ≤ (Int.floor b : ℝ) := by
      exact_mod_cast hzle
    linarith
  · -- Otherwise the original row bound forces enough negative slack to offset the excess integer part.
    have hzgt : Int.floor b < z := lt_of_not_ge hzle
    have hzge_real : ((Int.floor b : ℤ) : ℝ) + 1 ≤ (z : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hzgt)
    have hs_upper : s ≤ Int.fract b - ((z : ℝ) - (Int.floor b : ℝ)) := by
      linarith [hsum, Int.floor_add_fract b]
    have hs_scaled :
        s ≤ -((z : ℝ) - (Int.floor b : ℝ)) * (1 - Int.fract b) := by
      nlinarith
        [hs_upper, hfract_nonneg,
          show (0 : ℝ) ≤ (z : ℝ) - (Int.floor b : ℝ) - 1 by linarith]
    have hsdiv :
        s / (1 - Int.fract b) ≤ -((z : ℝ) - (Int.floor b : ℝ)) := by
      exact (div_le_iff₀ hden_pos).2
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using hs_scaled)
    linarith

/-- Exercise 5.10 (1). Let
`S = {(x, y) ∈ ℤ^n × ℝ_+^p | ∑ a_j x_j + ∑ g_j y_j ≤ b}` where
`a₁, …, aₙ ∈ ℤ`, `g₁, …, g_p ∈ ℝ`, `f = b - ⌊b⌋`, and `J⁻ = {j | g_j < 0}`. Then
`∑ ⌊a_j⌋ x_j + (1 / (1 - f)) * ∑_{j ∈ J⁻} g_j y_j ≤ ⌊b⌋`
is valid for `S`. The source side condition `b ∉ ℤ` is redundant for validity, so it is omitted
from the Lean statement. -/
theorem exercise_5_10_valid_cut
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p)
    (hxy : xy ∈ exercise_5_10_mixed_integer_set a g b) :
    exercise_5_10_cut_value a g b xy ≤ (Int.floor b : ℝ) := by
  rcases (mem_exercise_5_10_mixed_integer_set_iff a g b xy).1 hxy with
    ⟨hx_int, hy_nonneg, hrow_bound⟩
  rcases (mem_integerVectors_iff).1 hx_int with ⟨xInt, hx_cast⟩
  let z : ℤ := ∑ j, a j * xInt j
  let s : ℝ := Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j)
  have hz_row : (z : ℝ) = ∑ j, (a j : ℝ) * xy.1 j := by
    -- The integer block of `xy` is the real coercion of an integer vector.
    calc
      (z : ℝ) = ((∑ j, a j * xInt j : ℤ) : ℝ) := by rfl
      _ = ∑ j, ((a j * xInt j : ℤ) : ℝ) := by simp
      _ = ∑ j, (a j : ℝ) * xy.1 j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [hx_cast, Int.cast_mul]
  have hs_nonpos : s ≤ 0 := by
    simpa [s] using negativeContribution_nonpos a g b xy hxy
  have hs_le_total : s ≤ ∑ j, g j * xy.2 j := by
    simpa [s] using negativeContribution_le_totalContribution g xy hy_nonneg
  have hrow_bound' : (∑ j, (a j : ℝ) * xy.1 j) + ∑ j, g j * xy.2 j ≤ b := by
    simpa [mixed_linear_objective, dotProduct] using hrow_bound
  have hreduced_row : (z : ℝ) + s ≤ b := by
    linarith [hrow_bound', hs_le_total, hz_row]
  -- The final step is the scalar floor lemma on the integer row value and the negative slack.
  have hcut :
      (z : ℝ) + s / (1 - Int.fract b) ≤ (Int.floor b : ℝ) :=
    cutBound_of_integerRowAndNegativeSlack b z hs_nonpos hreduced_row
  simpa [exercise_5_10_cut_value, z, s, hz_row, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using hcut

/-- Helper for Exercise 5.10: the cut face is nonempty because the primitive integer row `a`
admits a lattice point at level `⌊b⌋`, and setting all continuous coordinates to `0` saturates
the cut. -/
lemma exercise_5_10_cut_face_nonempty
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1) :
    (exercise_5_10_cut_face a g b).Nonempty := by
  have ha_nonzero : a ≠ 0 := by
    intro ha_zero
    have hgcd_zero :
        Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 0 := by
      apply Finset.gcd_eq_zero_iff.mpr
      intro j hj
      simp [ha_zero]
    rw [hgcd_zero] at ha_relatively_prime
    exact Nat.zero_ne_one ha_relatively_prime
  let splitRow : Split Finset.univ :=
    { π := a
      π0 := Int.floor b
      nonzero := ha_nonzero
      zero_on_continuous := by
        intro j hj
        simpa using hj }
  have hprimitive : splitRow.IsPrimitive := by
    simpa [Split.IsPrimitive, splitRow] using ha_relatively_prime
  obtain ⟨xInt, hxInt⟩ :=
    exists_integral_solution_on_split_hyperplane_of_relatively_prime_coefficients
      Finset.univ splitRow hprimitive
  let xy : MixedRealPoint n p := (Int.cast ∘ xInt, fun _ : Fin p ↦ 0)
  have hrow_eq : ∑ j, (a j : ℝ) * xy.1 j = (Int.floor b : ℝ) := by
    -- The chosen integer point lies on the hyperplane `a · x = ⌊b⌋`.
    calc
      ∑ j, (a j : ℝ) * xy.1 j = ∑ j, ((a j * xInt j : ℤ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [xy, Int.cast_mul]
      _ = ((∑ j, a j * xInt j : ℤ) : ℝ) := by simp
      _ = (Int.floor b : ℝ) := by
            have hxIntReal :
                ((∑ j, splitRow.π j * xInt j : ℤ) : ℝ) = (splitRow.π0 : ℝ) := by
              exact_mod_cast hxInt
            simpa [splitRow] using hxIntReal
  have hrow_eq' : ∑ j, (a j : ℝ) * (xInt j : ℝ) = (Int.floor b : ℝ) := by
    simpa [xy] using hrow_eq
  have hxy_mem : xy ∈ exercise_5_10_mixed_integer_set a g b := by
    rw [mem_exercise_5_10_mixed_integer_set_iff]
    refine ⟨(mem_integerVectors_iff).2 ⟨xInt, rfl⟩, ?_, ?_⟩
    · intro j
      simp [xy]
    · -- With `y = 0`, the original row inequality reduces to `a · x = ⌊b⌋ ≤ b`.
      calc
        mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy
            = ∑ j, (a j : ℝ) * xy.1 j := by
                simp [mixed_linear_objective, dotProduct, xy]
        _ = (Int.floor b : ℝ) := hrow_eq
        _ ≤ b := Int.floor_le b
  refine ⟨xy, ?_⟩
  rw [mem_exercise_5_10_cut_face_iff]
  refine ⟨subset_convexHull ℝ _ hxy_mem, ?_⟩
  -- The same witness saturates the mixed cut because its continuous block is zero.
  simp [exercise_5_10_cut_value, xy, div_eq_mul_inv, hrow_eq']

/-- Helper for Exercise 5.10: the cut inequality can be viewed on the flattened ambient space
`Fin (n + p) → ℝ` by keeping the integer coefficients on the `x`-block and attaching the scaled
negative continuous coefficients on the `y`-block. -/
noncomputable def exercise_5_10_flat_cut_vector
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Fin (n + p) → ℝ :=
  Fin.append
    (fun i : Fin n ↦ (a i : ℝ))
    (fun j : Fin p ↦ if g j < 0 then g j / (1 - Int.fract b) else 0)

/-- Helper for Exercise 5.10: evaluating the flattened cut vector on `Fin.appendEquiv n p xy`
recovers `exercise_5_10_cut_value a g b xy`. -/
lemma exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy =
      exercise_5_10_cut_value a g b xy := by
  -- Split the flattened dot product into the integer and continuous blocks.
  have hcont :
      (∑ j : Fin p,
          (if g j < 0 then g j / (1 - Int.fract b) else 0) * xy.2 j) =
        (1 / (1 - Int.fract b)) *
          Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j) := by
    calc
      (∑ j : Fin p, (if g j < 0 then g j / (1 - Int.fract b) else 0) * xy.2 j)
          = Finset.sum (exercise_5_10_negative_index_set g)
              (fun j ↦ (g j / (1 - Int.fract b)) * xy.2 j) := by
              simpa [exercise_5_10_negative_index_set] using
                (Finset.sum_filter
                  (s := Finset.univ)
                  (p := fun j : Fin p ↦ g j < 0)
                  (f := fun j ↦ (g j / (1 - Int.fract b)) * xy.2 j)).symm
      _ = Finset.sum (exercise_5_10_negative_index_set g)
            (fun j ↦ (1 / (1 - Int.fract b)) * (g j * xy.2 j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = (1 / (1 - Int.fract b)) *
            Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j) := by
              rw [Finset.mul_sum]
  -- After normalizing the continuous block, the flattened and mixed-space formulas coincide.
  have hdot :
      exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy =
        ∑ i, (a i : ℝ) * xy.1 i +
          ∑ j : Fin p, (if g j < 0 then g j / (1 - Int.fract b) else 0) * xy.2 j := by
    simp [exercise_5_10_flat_cut_vector, dotProduct, Fin.appendEquiv, Fin.append, Fin.sum_univ_add]
  rw [hdot, exercise_5_10_cut_value, hcont]

/-- Helper for Exercise 5.10: flattening commutes with the convex hull of the mixed-integer set. -/
lemma appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b) =
      convexHull ℝ (Fin.appendEquiv n p '' exercise_5_10_mixed_integer_set a g b) := by
  let eL : MixedRealPoint n p ≃ₗ[ℝ] (Fin (n + p) → ℝ) :=
    (Fin.appendEquiv (α := ℝ) n p).toLinearEquiv appendEquivIsLinearMap
  -- The flattening map is linear, so it carries convex hulls to convex hulls.
  simpa [eL] using
    (LinearMap.image_convexHull eL.toLinearMap (exercise_5_10_mixed_integer_set a g b))

/-- Helper for Exercise 5.10: after flattening, the cut face is the equality face cut out by the
flattened cut vector on the flattened mixed hull. -/
lemma appendEquiv_image_exercise_5_10_cut_face_eq_face_set
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Fin.appendEquiv n p '' exercise_5_10_cut_face a g b =
      face_set
        (Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b))
        (exercise_5_10_flat_cut_vector a g b)
        (Int.floor b : ℝ) := by
  ext u
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    rw [mem_exercise_5_10_cut_face_iff] at hxy
    -- The image point stays in the flattened hull and satisfies the equality case of the cut.
    refine (mem_face_set_iff).2 ?_
    refine ⟨⟨xy, hxy.1, rfl⟩, ?_⟩
    simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hxy.2
  · intro hu
    rw [mem_face_set_iff] at hu
    rcases hu.1 with ⟨xy, hxyHull, rfl⟩
    -- Pull the equality slice back through the flattening equivalence.
    refine ⟨xy, ?_, rfl⟩
    rw [mem_exercise_5_10_cut_face_iff]
    refine ⟨hxyHull, ?_⟩
    simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hu.2

/-- Helper for Exercise 5.10: the cut face is an exposed face of the mixed hull because the cut
inequality is valid on every generator of the convex hull and is attained on the nonempty face. -/
lemma exercise_5_10_cut_face_isExposed
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    IsExposed ℝ
      (convexHull ℝ (exercise_5_10_mixed_integer_set a g b))
      (exercise_5_10_cut_face a g b) := by
  let eL : MixedRealPoint n p ≃ₗ[ℝ] (Fin (n + p) → ℝ) :=
    (Fin.appendEquiv (α := ℝ) n p).toLinearEquiv appendEquivIsLinearMap
  let e : MixedRealPoint n p ≃L[ℝ] (Fin (n + p) → ℝ) :=
    eL.toContinuousLinearEquiv
  have he_symm_apply (u : Fin (n + p) → ℝ) :
      e.symm u = (Fin.appendEquiv n p).symm u := by
    rfl
  have hgen_valid :
      Fin.appendEquiv n p '' exercise_5_10_mixed_integer_set a g b ⊆
        {u : Fin (n + p) → ℝ |
          exercise_5_10_flat_cut_vector a g b ⬝ᵥ u ≤ (Int.floor b : ℝ)} := by
    intro u hu
    rcases hu with ⟨xy, hxy, rfl⟩
    -- Validity on generators becomes validity of the flattened inequality after reindexing.
    simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using
      exercise_5_10_valid_cut a g b xy hxy
  have hcut_halfspace_convex :
      Convex ℝ {u : Fin (n + p) → ℝ |
        exercise_5_10_flat_cut_vector a g b ⬝ᵥ u ≤ (Int.floor b : ℝ)} := by
    let L : (Fin (n + p) → ℝ) →ₗ[ℝ] ℝ :=
      (dotProductStrongDual (exercise_5_10_flat_cut_vector a g b)).toLinearMap
    have hset :
        {u : Fin (n + p) → ℝ |
          exercise_5_10_flat_cut_vector a g b ⬝ᵥ u ≤ (Int.floor b : ℝ)} =
          L ⁻¹' Set.Iic (Int.floor b : ℝ) := by
      ext u
      simp [L, dotProductStrongDual_apply]
    -- The cut halfspace is a linear preimage of the convex interval `(-∞, ⌊b⌋]`.
    rw [hset]
    exact (convex_Iic (Int.floor b : ℝ)).linear_preimage L
  have hflat_valid :
      is_valid_inequality
        (Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b))
        (exercise_5_10_flat_cut_vector a g b)
        (Int.floor b : ℝ) := by
    have himage_subset :
        Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b) ⊆
          {u : Fin (n + p) → ℝ |
            exercise_5_10_flat_cut_vector a g b ⬝ᵥ u ≤ (Int.floor b : ℝ)} := by
      calc
        Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b)
            = convexHull ℝ (Fin.appendEquiv n p '' exercise_5_10_mixed_integer_set a g b) := by
                exact appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set a g b
        _ ⊆ {u : Fin (n + p) → ℝ |
              exercise_5_10_flat_cut_vector a g b ⬝ᵥ u ≤ (Int.floor b : ℝ)} := by
              exact convexHull_min hgen_valid hcut_halfspace_convex
    intro u hu
    exact himage_subset hu
  have hflat_exposed :
      IsExposed ℝ
        (Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b))
        (Fin.appendEquiv n p '' exercise_5_10_cut_face a g b) := by
    rw [appendEquiv_image_exercise_5_10_cut_face_eq_face_set]
    exact isExposed_face_set_of_valid_inequality hflat_valid
  have hback :
      IsExposed ℝ
        (e.symm '' (Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b)))
        (e.symm '' (Fin.appendEquiv n p '' exercise_5_10_cut_face a g b)) := by
    exact isExposed_image_continuousLinearEquiv e.symm hflat_exposed
  have hsymm_hull :
      e.symm '' (Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b)) =
        convexHull ℝ (exercise_5_10_mixed_integer_set a g b) := by
    ext xy
    constructor
    · rintro ⟨u, hu, hxy⟩
      rcases hu with ⟨z, hz, rfl⟩
      have hzxy : z = xy := by
        simpa [he_symm_apply] using hxy
      exact hzxy ▸ hz
    · intro hxy
      refine ⟨Fin.appendEquiv n p xy, ⟨xy, hxy, rfl⟩, ?_⟩
      simpa [he_symm_apply] using
        (Fin.appendEquiv n p).symm_apply_apply (Fin.appendEquiv n p xy)
  have hsymm_face :
      e.symm '' (Fin.appendEquiv n p '' exercise_5_10_cut_face a g b) =
        exercise_5_10_cut_face a g b := by
    ext xy
    constructor
    · rintro ⟨u, hu, hxy⟩
      rcases hu with ⟨z, hz, rfl⟩
      have hzxy : z = xy := by
        simpa [he_symm_apply] using hxy
      exact hzxy ▸ hz
    · intro hxy
      refine ⟨Fin.appendEquiv n p xy, ⟨xy, hxy, rfl⟩, ?_⟩
      simpa [he_symm_apply] using
        (Fin.appendEquiv n p).symm_apply_apply (Fin.appendEquiv n p xy)
  -- Transport the exposed face back through the flattening equivalence.
  rw [hsymm_hull, hsymm_face] at hback
  exact hback

/-- Helper for Exercise 5.10: the cut is strict at a feasible mixed-integer point on the lower
integer level `a · x = ⌊b⌋ - 1`, so the cut face is a proper subset of the mixed hull. -/
lemma exercise_5_10_exists_strict_cut_point
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (hb_nonint : ¬ ∃ z : ℤ, b = (z : ℝ)) :
    ∃ xy : MixedRealPoint n p,
      xy ∈ convexHull ℝ (exercise_5_10_mixed_integer_set a g b) ∧
        exercise_5_10_cut_value a g b xy < (Int.floor b : ℝ) := by
  have ha_nonzero : a ≠ 0 := by
    intro ha_zero
    have hgcd_zero :
        Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 0 := by
      apply Finset.gcd_eq_zero_iff.mpr
      intro j hj
      simp [ha_zero]
    rw [hgcd_zero] at ha_relatively_prime
    exact Nat.zero_ne_one ha_relatively_prime
  let splitRow : Split Finset.univ :=
    { π := a
      π0 := Int.floor b - 1
      nonzero := ha_nonzero
      zero_on_continuous := by
        intro j hj
        simpa using hj }
  have hprimitive : splitRow.IsPrimitive := by
    simpa [Split.IsPrimitive, splitRow] using ha_relatively_prime
  obtain ⟨xInt, hxInt⟩ :=
    exists_integral_solution_on_split_hyperplane_of_relatively_prime_coefficients
      Finset.univ splitRow hprimitive
  let xy : MixedRealPoint n p := (Int.cast ∘ xInt, fun _ : Fin p ↦ 0)
  have hrow_eq : ∑ j, (a j : ℝ) * xy.1 j = ((Int.floor b : ℝ) - 1) := by
    -- The primitive witness is chosen on the lower integer level `⌊b⌋ - 1`.
    calc
      ∑ j, (a j : ℝ) * xy.1 j = ∑ j, ((a j * xInt j : ℤ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [xy, Int.cast_mul]
      _ = ((∑ j, a j * xInt j : ℤ) : ℝ) := by simp
      _ = ((Int.floor b - 1 : ℤ) : ℝ) := by
            have hxIntReal :
                ((∑ j, splitRow.π j * xInt j : ℤ) : ℝ) = (splitRow.π0 : ℝ) := by
              exact_mod_cast hxInt
            simpa [splitRow] using hxIntReal
      _ = (Int.floor b : ℝ) - 1 := by norm_num
  have hrow_eq' : ∑ j, (a j : ℝ) * (xInt j : ℝ) = (Int.floor b : ℝ) - 1 := by
    simpa [xy] using hrow_eq
  have hfract_pos : 0 < Int.fract b := by
    have hfloor_ne : b ≠ (Int.floor b : ℝ) := by
      intro hb_floor
      exact hb_nonint ⟨Int.floor b, hb_floor⟩
    exact (Int.fract_pos).2 hfloor_ne
  have hbelow_b : (Int.floor b : ℝ) - 1 ≤ b := by
    linarith [Int.floor_add_fract b, hfract_pos]
  have hxy_mem : xy ∈ exercise_5_10_mixed_integer_set a g b := by
    rw [mem_exercise_5_10_mixed_integer_set_iff]
    refine ⟨(mem_integerVectors_iff).2 ⟨xInt, rfl⟩, ?_, ?_⟩
    · intro j
      simp [xy]
    · -- With `y = 0`, the original row is exactly `a · x = ⌊b⌋ - 1 ≤ b`.
      calc
        mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy
            = ∑ j, (a j : ℝ) * xy.1 j := by
                simp [mixed_linear_objective, dotProduct, xy]
        _ = (Int.floor b : ℝ) - 1 := hrow_eq
        _ ≤ b := hbelow_b
  refine ⟨xy, subset_convexHull ℝ _ hxy_mem, ?_⟩
  -- The same lower-level witness makes the cut strict by exactly one unit.
  calc
    exercise_5_10_cut_value a g b xy = (Int.floor b : ℝ) - 1 := by
      simp [exercise_5_10_cut_value, xy, div_eq_mul_inv, hrow_eq']
    _ < (Int.floor b : ℝ) := by linarith

/-- Helper for Exercise 5.10: the integer block matrix of the one-row relaxation keeps the
original row in position `0` and has zero integer coefficients on the nonnegativity rows. -/
noncomputable def exercise_5_10_relaxationMatrixInt
    (a : Fin n → ℤ) : Matrix (Fin (p + 1)) (Fin n) ℝ :=
  fun i ↦ Fin.cases (fun j : Fin n ↦ (a j : ℝ)) (fun _j _k ↦ 0) i

/-- Helper for Exercise 5.10: the continuous block matrix of the one-row relaxation keeps the
original coefficient row in position `0` and uses the rows `-y_j ≤ 0` for nonnegativity. -/
noncomputable def exercise_5_10_relaxationMatrixCont
    (g : Fin p → ℝ) : Matrix (Fin (p + 1)) (Fin p) ℝ :=
  fun i ↦ Fin.cases g (fun j : Fin p ↦ -Pi.single j (1 : ℝ)) i

/-- Helper for Exercise 5.10: the right-hand side of the one-row relaxation is `b` on the
original row and `0` on the nonnegativity rows. -/
noncomputable def exercise_5_10_relaxationRhs
    (b : ℝ) : Fin (p + 1) → ℝ :=
  Fin.cases b (fun _j ↦ 0)

/-- Helper for Exercise 5.10: the basic multiplier `(1, g)` reproduces the split row `a` and
annihilates the continuous block of the one-row relaxation. -/
noncomputable def exercise_5_10_relaxationMultiplier
    (g : Fin p → ℝ) : Fin (p + 1) → ℝ :=
  Fin.cases 1 g

/-- Helper for Exercise 5.10: the real mixed polyhedron built from the explicit one-row
relaxation data is exactly the source-facing relaxation `y ≥ 0` and
`mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b`. -/
lemma mem_exercise_5_10_relaxation_polyhedron_iff
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    xy ∈ real_mixed_polyhedron
        (exercise_5_10_relaxationMatrixInt (p := p) a)
        (exercise_5_10_relaxationMatrixCont g)
        (exercise_5_10_relaxationRhs (p := p) b) ↔
      (∀ j : Fin p, 0 ≤ xy.2 j) ∧
        mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b := by
  rw [mem_real_mixed_polyhedron_iff]
  constructor
  · intro hxy
    refine ⟨?_, ?_⟩
    · intro j
      have hj := hxy j.succ
      -- The nonnegativity rows are exactly the inequalities `-y_j ≤ 0`.
      have hj' : 0 ≤ ∑ x : Fin p, (if x = j then (1 : ℝ) else 0) * xy.2 x := by
        simpa [exercise_5_10_relaxationMatrixInt, exercise_5_10_relaxationMatrixCont,
          exercise_5_10_relaxationRhs, mixed_linear_objective, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, Pi.single_apply] using hj
      simpa [dotProduct] using hj'
    · have h0 := hxy 0
      -- Row `0` is the original mixed inequality.
      simpa [exercise_5_10_relaxationMatrixInt, exercise_5_10_relaxationMatrixCont,
        exercise_5_10_relaxationRhs, mixed_linear_objective, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] using h0
  · rintro ⟨hy_nonneg, hrow⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · -- Row `0` restates the original mixed inequality.
      simpa [exercise_5_10_relaxationMatrixInt, exercise_5_10_relaxationMatrixCont,
        exercise_5_10_relaxationRhs, mixed_linear_objective, dotProduct] using hrow
    · intro j
      -- Each successor row is the nonnegativity constraint `-y_j ≤ 0`.
      have hj' : 0 ≤ ∑ x : Fin p, (if x = j then (1 : ℝ) else 0) * xy.2 x := by
        simpa [dotProduct] using hy_nonneg j
      simpa [exercise_5_10_relaxationMatrixInt, exercise_5_10_relaxationMatrixCont,
        exercise_5_10_relaxationRhs, mixed_linear_objective, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, Pi.single_apply] using hj'

/-- Helper for Exercise 5.10: the multiplier `(1, g)` reproduces the integer split row `a` on
the explicit relaxation matrix. -/
lemma exercise_5_10_relaxationMultiplier_vecMul_matrixInt
    (a : Fin n → ℤ)
    (g : Fin p → ℝ) :
    Matrix.vecMul (exercise_5_10_relaxationMultiplier g)
        (exercise_5_10_relaxationMatrixInt (p := p) a) =
      fun j : Fin n ↦ (a j : ℝ) := by
  ext j
  -- Only the original row contributes to the integer block.
  simp [Matrix.vecMul, exercise_5_10_relaxationMultiplier,
    exercise_5_10_relaxationMatrixInt, dotProduct, Fin.sum_univ_succ]

/-- Helper for Exercise 5.10: the same multiplier annihilates the continuous block of the
explicit relaxation matrix. -/
lemma exercise_5_10_relaxationMultiplier_vecMul_matrixCont
    (g : Fin p → ℝ) :
    Matrix.vecMul (exercise_5_10_relaxationMultiplier g)
        (exercise_5_10_relaxationMatrixCont (p := p) g) = 0 := by
  ext j
  -- The original row contributes `g_j`, which is cancelled by the `j`th nonnegativity row.
  have hsum_single :
      ∑ x : Fin p, g x * (if x = j then (1 : ℝ) else 0) = g j := by
    simp
  calc
    Matrix.vecMul (exercise_5_10_relaxationMultiplier g)
        (exercise_5_10_relaxationMatrixCont (p := p) g) j
        = g j - ∑ x : Fin p, g x * (if x = j then (1 : ℝ) else 0) := by
            simp [Matrix.vecMul, exercise_5_10_relaxationMultiplier,
              exercise_5_10_relaxationMatrixCont, dotProduct, Fin.sum_univ_succ,
              Pi.single_apply]
    _ = g j - g j := by rw [hsum_single]
    _ = 0 := by ring

/-- Helper for Exercise 5.10: adjoining one nonnegative slack variable turns the original
mixed-integer inequality into an equality system without changing the `(x, y)` projection. -/
def exercise_5_10_augmentedSet
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Set (MixedRealPoint n p × ℝ) :=
  {xys |
    xys.1.1 ∈ ℤ^n ∧
      (∀ j : Fin p, 0 ≤ xys.1.2 j) ∧
        0 ≤ xys.2 ∧
          mixed_linear_objective (fun i ↦ (a i : ℝ)) g xys.1 + xys.2 = b}

/-- Membership in `exercise_5_10_augmentedSet a g b` means that the integer block is integral,
the original continuous block and the new slack are nonnegative, and the lifted row is exact. -/
theorem mem_exercise_5_10_augmentedSet_iff
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xys : MixedRealPoint n p × ℝ) :
    xys ∈ exercise_5_10_augmentedSet a g b ↔
      xys.1.1 ∈ ℤ^n ∧
        (∀ j : Fin p, 0 ≤ xys.1.2 j) ∧
          0 ≤ xys.2 ∧
            mixed_linear_objective (fun i ↦ (a i : ℝ)) g xys.1 + xys.2 = b :=
  Iff.rfl

/-- Helper for Exercise 5.10: forgetting the slack coordinate identifies the lifted equality
system with the original mixed-integer set. -/
lemma exercise_5_10_augmentedProjection_eq_mixed_integer_set
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Prod.fst '' exercise_5_10_augmentedSet a g b =
      exercise_5_10_mixed_integer_set a g b := by
  ext xy
  constructor
  · rintro ⟨xys, hxys, rfl⟩
    rcases (mem_exercise_5_10_augmentedSet_iff a g b xys).1 hxys with
      ⟨hx_int, hy_nonneg, _hs_nonneg, hrow_eq⟩
    rw [mem_exercise_5_10_mixed_integer_set_iff]
    refine ⟨hx_int, hy_nonneg, ?_⟩
    -- Dropping the nonnegative slack recovers the original row inequality.
    linarith
  · intro hxy
    rcases (mem_exercise_5_10_mixed_integer_set_iff a g b xy).1 hxy with
      ⟨hx_int, hy_nonneg, hrow_le⟩
    refine ⟨(xy, b - mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy), ?_, rfl⟩
    refine (mem_exercise_5_10_augmentedSet_iff a g b _).2 ?_
    constructor
    · exact hx_int
    constructor
    · exact hy_nonneg
    constructor
    · -- The slack is exactly the residual of the original feasible inequality.
      linarith
    · -- By construction the lifted row holds at equality.
      ring

/-- Helper for Exercise 5.10: linear projection commutes with the convex hull of the augmented
slack model, so the lifted owner projects back to `conv(S)`. -/
lemma exercise_5_10_augmentedProjection_image_convexHull
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Prod.fst '' convexHull ℝ (exercise_5_10_augmentedSet a g b) =
      convexHull ℝ (exercise_5_10_mixed_integer_set a g b) := by
  let proj : (MixedRealPoint n p × ℝ) →ₗ[ℝ] MixedRealPoint n p :=
    LinearMap.fst ℝ (MixedRealPoint n p) ℝ
  have hproj_image :
      proj '' exercise_5_10_augmentedSet a g b =
        Prod.fst '' exercise_5_10_augmentedSet a g b := by
    rfl
  -- Push the convex hull through the linear projection, then simplify the projected owner.
  calc
    Prod.fst '' convexHull ℝ (exercise_5_10_augmentedSet a g b)
        = proj '' convexHull ℝ (exercise_5_10_augmentedSet a g b) := by
            rfl
    _ = convexHull ℝ (proj '' exercise_5_10_augmentedSet a g b) := by
          simpa [proj] using LinearMap.image_convexHull proj (exercise_5_10_augmentedSet a g b)
    _ = convexHull ℝ (exercise_5_10_mixed_integer_set a g b) := by
          rw [hproj_image, exercise_5_10_augmentedProjection_eq_mixed_integer_set]

/-- Helper for Exercise 5.10: the lifted equality owner has the same cut face after forgetting
the slack coordinate, so the facet question can be moved to the augmented model. -/
def exercise_5_10_augmentedCutFace
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Set (MixedRealPoint n p × ℝ) :=
  {xys |
    xys ∈ convexHull ℝ (exercise_5_10_augmentedSet a g b) ∧
      exercise_5_10_cut_value a g b xys.1 = (Int.floor b : ℝ)}

/-- Forgetting the slack variable sends the lifted cut-equality face exactly to the source-facing
cut face `exercise_5_10_cut_face a g b`. -/
lemma exercise_5_10_augmentedProjection_eq_cut_face
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Prod.fst '' exercise_5_10_augmentedCutFace a g b =
      exercise_5_10_cut_face a g b := by
  ext xy
  constructor
  · rintro ⟨xys, hxys, rfl⟩
    rw [mem_exercise_5_10_cut_face_iff]
    refine ⟨?_, hxys.2⟩
    -- Projecting a lifted hull point lands in the original convex hull.
    rw [← exercise_5_10_augmentedProjection_image_convexHull]
    exact ⟨xys, hxys.1, rfl⟩
  · intro hxy
    rw [mem_exercise_5_10_cut_face_iff] at hxy
    rw [← exercise_5_10_augmentedProjection_image_convexHull] at hxy
    rcases hxy.1 with ⟨xys, hxys_hull, hproj⟩
    refine ⟨xys, ⟨hxys_hull, ?_⟩, hproj⟩
    -- The cut equation only depends on `(x, y)`, so it transfers across the projection equality.
    simpa [hproj] using hxy.2

/-- Helper for Exercise 5.10: the flat polyhedron used for the facet argument keeps row `0` as the
original relaxation inequality, row `1` as the cut inequality, and rows `2 + j` as the
nonnegativity inequalities `-y_j ≤ 0`. -/
noncomputable def exercise_5_10_facetMatrix
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Matrix (Fin (p + 2)) (Fin (n + p)) ℝ :=
  fun i ↦
    Fin.cases
      (Fin.append (fun j : Fin n ↦ (a j : ℝ)) g)
      (fun i' ↦
        Fin.cases
          (exercise_5_10_flat_cut_vector a g b)
          (fun j : Fin p ↦ Fin.append (fun _ : Fin n ↦ (0 : ℝ)) (-Pi.single j (1 : ℝ)))
          i')
      i

/-- Helper for Exercise 5.10: the flat right-hand side uses `b` on the original row,
`⌊b⌋` on the cut row, and `0` on the nonnegativity rows. -/
noncomputable def exercise_5_10_facetRhs
    (p : ℕ)
    (b : ℝ) : Fin (p + 2) → ℝ :=
  Fin.cases b (fun i' ↦ Fin.cases (Int.floor b : ℝ) (fun _ : Fin p ↦ 0) i')

/-- Helper for Exercise 5.10: each successor row after the cut row is the nonnegativity
constraint `-y_j ≤ 0` on a flattened mixed-space point. -/
lemma exercise_5_10_facetMatrix_nonneg_row_eval
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p)
    (j : Fin p) :
    Matrix.mulVec (exercise_5_10_facetMatrix a g b) (Fin.appendEquiv n p xy) (Fin.succ (Fin.succ j))
      = -xy.2 j := by
  -- Only the `j`th nonnegativity row contributes on this successor coordinate.
  simp [exercise_5_10_facetMatrix, Matrix.mulVec, dotProduct, Fin.appendEquiv, Fin.append,
    Fin.sum_univ_add, Pi.single_apply]

/-- Helper for Exercise 5.10: membership in the explicit flat polyhedron is exactly the source
relaxation `y ≥ 0`, the original row inequality, and the Exercise 5.10 cut inequality. -/
lemma mem_exercise_5_10_facetPolyhedron_iff
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    Fin.appendEquiv n p xy ∈
        polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b) ↔
      (∀ j : Fin p, 0 ≤ xy.2 j) ∧
        mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b ∧
          exercise_5_10_cut_value a g b xy ≤ (Int.floor b : ℝ) := by
  rw [mem_polyhedron_le_set_iff]
  constructor
  · intro hxy
    refine ⟨?_, ?_, ?_⟩
    · intro j
      have hj := hxy (Fin.succ (Fin.succ j))
      have hj' : -xy.2 j ≤ 0 := by
        simpa [exercise_5_10_facetRhs, exercise_5_10_facetMatrix_nonneg_row_eval] using hj
      linarith
    · have h0 := hxy 0
      simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, mixed_linear_objective,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_add] using h0
    · have h1 := hxy 1
      have hcut :
          exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy ≤ (Int.floor b : ℝ) := by
        simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ] using h1
      simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hcut
  · rintro ⟨hy_nonneg, hrow, hcut⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · -- Row `0` is the original one-row relaxation inequality.
      simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, mixed_linear_objective,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_add] using hrow
    · intro i'
      refine Fin.cases ?_ ?_ i'
      · -- Row `1` is the flat cut inequality.
        have hcut' :
            exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy ≤ (Int.floor b : ℝ) := by
          simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hcut
        simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ] using hcut'
      · intro j
        -- Each successor row after the cut is exactly `-y_j ≤ 0`.
        have hj' : -xy.2 j ≤ 0 := by
          linarith [hy_nonneg j]
        simpa [exercise_5_10_facetRhs, exercise_5_10_facetMatrix_nonneg_row_eval] using hj'

/-- Helper for Exercise 5.10: the explicit flat facet owner is convex because it is a finite
system of linear inequalities. -/
lemma exercise_5_10_facetPolyhedron_convex
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Convex ℝ
      (polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b)) := by
  intro u hu v hv α β hα hβ hαβ
  intro i
  have hui :
      Matrix.mulVec (exercise_5_10_facetMatrix a g b) u i ≤ exercise_5_10_facetRhs p b i := hu i
  have hvi :
      Matrix.mulVec (exercise_5_10_facetMatrix a g b) v i ≤ exercise_5_10_facetRhs p b i := hv i
  calc
    Matrix.mulVec (exercise_5_10_facetMatrix a g b) (α • u + β • v) i
        = α * Matrix.mulVec (exercise_5_10_facetMatrix a g b) u i +
            β * Matrix.mulVec (exercise_5_10_facetMatrix a g b) v i := by
              calc
                ∑ j, exercise_5_10_facetMatrix a g b i j * (α * u j + β * v j)
                    = ∑ j, (α * (exercise_5_10_facetMatrix a g b i j * u j) +
                        β * (exercise_5_10_facetMatrix a g b i j * v j)) := by
                          refine Finset.sum_congr rfl ?_
                          intro j hj
                          ring
                _ = (∑ j, α * (exercise_5_10_facetMatrix a g b i j * u j)) +
                      ∑ j, β * (exercise_5_10_facetMatrix a g b i j * v j) := by
                        rw [Finset.sum_add_distrib]
                _ = α * Matrix.mulVec (exercise_5_10_facetMatrix a g b) u i +
                      β * Matrix.mulVec (exercise_5_10_facetMatrix a g b) v i := by
                        simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ ≤ α * exercise_5_10_facetRhs p b i + β * exercise_5_10_facetRhs p b i := by
          exact add_le_add (mul_le_mul_of_nonneg_left hui hα) (mul_le_mul_of_nonneg_left hvi hβ)
    _ = exercise_5_10_facetRhs p b i := by
          rw [← add_mul, hαβ, one_mul]

/-- Helper for Exercise 5.10: flattening sends `conv(S)` into the explicit facet owner `P'`
because the generators satisfy the relaxation rows and the cut is valid on `S`. -/
lemma appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set_subset_facetPolyhedron
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b) ⊆
      polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b) := by
  have hgen :
      Fin.appendEquiv n p '' exercise_5_10_mixed_integer_set a g b ⊆
        polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b) := by
    intro u hu
    rcases hu with ⟨xy, hxy, rfl⟩
    rcases (mem_exercise_5_10_mixed_integer_set_iff a g b xy).1 hxy with
      ⟨_, hy_nonneg, hrow⟩
    refine (mem_exercise_5_10_facetPolyhedron_iff a g b xy).2 ?_
    exact ⟨hy_nonneg, hrow, exercise_5_10_valid_cut a g b xy hxy⟩
  calc
    Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b)
        = convexHull ℝ (Fin.appendEquiv n p '' exercise_5_10_mixed_integer_set a g b) := by
            exact appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set a g b
    _ ⊆ polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b) := by
          exact convexHull_min hgen (exercise_5_10_facetPolyhedron_convex a g b)

/-- Helper for Exercise 5.10: every point of the source cut face maps into the singleton active
face of row `1` on the explicit flat owner `P'`. -/
lemma appendEquiv_image_exercise_5_10_cut_face_subset_activeConstraintFace
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Fin.appendEquiv n p '' exercise_5_10_cut_face a g b ⊆
      active_constraint_face
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b)
        ({1} : Set (Fin (p + 2))) := by
  intro u hu
  rcases hu with ⟨xy, hxy, rfl⟩
  rw [mem_exercise_5_10_cut_face_iff] at hxy
  have hxP :
      Fin.appendEquiv n p xy ∈
        polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b) := by
    exact appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set_subset_facetPolyhedron
      a g b ⟨xy, hxy.1, rfl⟩
  refine (mem_active_constraint_face_iff).2 ?_
  constructor
  · intro i hi
    have hi1 : i = 1 := by simpa using hi
    have hcut :
        exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy = (Int.floor b : ℝ) := by
      simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hxy.2
    simpa [hi1, exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using hcut
  · intro i hi
    exact hxP i

/-- Helper for Exercise 5.10: the strict-cut point already built inside `conv(S)` witnesses that
the cut row is not an implicit equality of the explicit flat owner `P'`. -/
lemma exercise_5_10_cutRow_irredundant
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (hb_nonint : ¬ ∃ z : ℤ, b = (z : ℝ)) :
    is_irredundant_row
      (exercise_5_10_facetMatrix a g b)
      (exercise_5_10_facetRhs p b)
      1 := by
  have ha_nonzero : a ≠ 0 := by
    intro ha_zero
    have hgcd_zero :
        Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 0 := by
      apply Finset.gcd_eq_zero_iff.mpr
      intro j hj
      simp [ha_zero]
    rw [hgcd_zero] at ha_relatively_prime
    exact Nat.zero_ne_one ha_relatively_prime
  have hfract_pos : 0 < Int.fract b := by
    have hfloor_ne : b ≠ (Int.floor b : ℝ) := by
      intro hb_floor
      exact hb_nonint ⟨Int.floor b, hb_floor⟩
    exact (Int.fract_pos).2 hfloor_ne
  let splitFloor : Split Finset.univ :=
    { π := a
      π0 := Int.floor b
      nonzero := ha_nonzero
      zero_on_continuous := by
        intro j hj
        simpa using hj }
  have hprimitiveFloor : splitFloor.IsPrimitive := by
    simpa [Split.IsPrimitive, splitFloor] using ha_relatively_prime
  obtain ⟨xFloor, hxFloor⟩ :=
    exists_integral_solution_on_split_hyperplane_of_relatively_prime_coefficients
      Finset.univ splitFloor hprimitiveFloor
  let splitDir : Split Finset.univ :=
    { π := a
      π0 := 1
      nonzero := ha_nonzero
      zero_on_continuous := by
        intro j hj
        simpa using hj }
  have hprimitiveDir : splitDir.IsPrimitive := by
    simpa [Split.IsPrimitive, splitDir] using ha_relatively_prime
  obtain ⟨d, hd⟩ :=
    exists_integral_solution_on_split_hyperplane_of_relatively_prime_coefficients
      Finset.univ splitDir hprimitiveDir
  let xWitness : Fin n → ℝ := fun j ↦ (xFloor j : ℝ) + Int.fract b * (d j : ℝ)
  let xy : MixedRealPoint n p := (xWitness, fun _ : Fin p ↦ 0)
  have hxFloor_row : ∑ j, (a j : ℝ) * (xFloor j : ℝ) = (Int.floor b : ℝ) := by
    -- The first lattice witness lies on the integer hyperplane `a · x = floor b`.
    have hxFloor_real :
        ((∑ j, splitFloor.π j * xFloor j : ℤ) : ℝ) = (splitFloor.π0 : ℝ) := by
      exact_mod_cast hxFloor
    simpa [splitFloor, Int.cast_mul] using hxFloor_real
  have hd_row : ∑ j, (a j : ℝ) * (d j : ℝ) = (1 : ℝ) := by
    -- The primitive direction changes the integer row value by exactly one.
    have hd_real :
        ((∑ j, splitDir.π j * d j : ℤ) : ℝ) = (splitDir.π0 : ℝ) := by
      exact_mod_cast hd
    simpa [splitDir, Int.cast_mul] using hd_real
  have hxWitness_row :
      ∑ j, (a j : ℝ) * xWitness j = b := by
    -- Expanding `xFloor + fract(b) • d` gives `floor b + fract b = b`.
    calc
      ∑ j, (a j : ℝ) * xWitness j
          = ∑ j, ((a j : ℝ) * (xFloor j : ℝ) + Int.fract b * ((a j : ℝ) * (d j : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = ∑ j, (a j : ℝ) * (xFloor j : ℝ) +
            Int.fract b * ∑ j, (a j : ℝ) * (d j : ℝ) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (Int.floor b : ℝ) + Int.fract b * (1 : ℝ) := by rw [hxFloor_row, hd_row]
      _ = b := by simpa using (Int.floor_add_fract b)
  refine ⟨Fin.appendEquiv n p xy, ?_, ?_⟩
  · intro i hi
    revert hi
    -- All rows except the cut row are satisfied by the explicit witness.
    refine Fin.cases ?_ ?_ i
    · intro _hi
      have hrow0 :
        mixed_linear_objective (fun j ↦ (a j : ℝ)) g xy = b := by
        simpa [mixed_linear_objective, dotProduct, xy, xWitness] using hxWitness_row
      simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
        mixed_linear_objective, Fin.sum_univ_succ, Fin.sum_univ_add, xy, xWitness]
        using hrow0.le
    · intro i' hi
      by_cases hi0 : i' = 0
      · subst hi0
        exact (hi rfl).elim
      · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi0
        simpa [exercise_5_10_facetRhs, exercise_5_10_facetMatrix_nonneg_row_eval, xy]
  · -- The cut row is violated strictly because the same witness attains value `b > floor b`.
    have hcut_eq : exercise_5_10_cut_value a g b xy = b := by
      simpa [exercise_5_10_cut_value, mixed_linear_objective, dotProduct, xy, xWitness]
        using hxWitness_row
    have hcut_gt : (Int.floor b : ℝ) < exercise_5_10_cut_value a g b xy := by
      rw [hcut_eq]
      linarith [Int.floor_add_fract b, hfract_pos]
    have hrow1 :
        (Int.floor b : ℝ) <
          Matrix.mulVec (exercise_5_10_facetMatrix a g b) (Fin.appendEquiv n p xy) 1 := by
      have hflat :
          (Int.floor b : ℝ) <
            exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy := by
        simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hcut_gt
      simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] using hflat
    simpa using hrow1

/-- Helper for Exercise 5.10: the strict-cut point already built inside `conv(S)` witnesses that
the cut row is not an implicit equality of the explicit flat owner `P'`. -/
lemma exercise_5_10_cutRow_not_implicit
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (hb_nonint : ¬ ∃ z : ℤ, b = (z : ℝ)) :
    ¬ is_implicit_equality
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b)
        1 := by
  rcases exercise_5_10_exists_strict_cut_point a g b ha_relatively_prime hb_nonint with
    ⟨xy, hxy_hull, hxy_strict⟩
  intro himplicit
  have hxP :
      Fin.appendEquiv n p xy ∈
        polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b) := by
    exact appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set_subset_facetPolyhedron
      a g b ⟨xy, hxy_hull, rfl⟩
  have hrow_eq :
      Matrix.mulVec (exercise_5_10_facetMatrix a g b) (Fin.appendEquiv n p xy) 1 =
        exercise_5_10_facetRhs p b 1 := himplicit hxP
  have hcut_eq : exercise_5_10_cut_value a g b xy = (Int.floor b : ℝ) := by
    have hflat :
        exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy = (Int.floor b : ℝ) := by
      simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] using hrow_eq
    simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hflat
  exact (ne_of_lt hxy_strict) hcut_eq

/-- Exercise 5.10 (2). Under the same hypotheses, the inequality from Exercise 5.10 (1) defines
a facet of `conv(S)`. The relative-primality assumption already excludes the zero row. -/
theorem exercise_5_10_cut_defines_facet
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (hb_nonint : ¬ ∃ z : ℤ, b = (z : ℝ)) :
    IsFacetOf
      (convexHull ℝ (exercise_5_10_mixed_integer_set a g b))
      (exercise_5_10_cut_face a g b) := by
  have hface_nonempty :
      (exercise_5_10_cut_face a g b).Nonempty :=
    exercise_5_10_cut_face_nonempty a g b ha_relatively_prime
  have hface_exposed :
      IsExposed ℝ
        (convexHull ℝ (exercise_5_10_mixed_integer_set a g b))
        (exercise_5_10_cut_face a g b) :=
    exercise_5_10_cut_face_isExposed a g b
  have hstrict_cut :
      ∃ xy : MixedRealPoint n p,
        xy ∈ convexHull ℝ (exercise_5_10_mixed_integer_set a g b) ∧
          exercise_5_10_cut_value a g b xy < (Int.floor b : ℝ) :=
    exercise_5_10_exists_strict_cut_point a g b ha_relatively_prime hb_nonint
  have hcut_row_irredundant :
      is_irredundant_row
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b)
        1 :=
    exercise_5_10_cutRow_irredundant a g b ha_relatively_prime hb_nonint
  -- Route correction: instead of asking again for a full hull equality, the proof now works with
  -- the explicit flat owner `P'` from `exercise_5_10_facetMatrix`. The verified prefix already
  -- shows `conv(S) ⊆ P'`, sends the cut face into the singleton active face of row `1`, and
  -- shows row `1` is genuinely non-implicit and irredundant via explicit witnesses.
  -- TODO: prove the reverse face inclusion `active_constraint_face P' {1} ⊆ image(cut_face)` by
  -- decomposing a row-`1` equality point into lower/upper split pieces using the primitive
  -- direction `a · d = 1` and the one-row rounded hull theorem on the `x`-block. Then show that
  -- the image face has the same affine span as the singleton active face, apply the singleton-row
  -- codimension theorem to `P'` using `hcut_row_irredundant`, and then
  -- transfer the codimension-one equation back to `conv(S)` using the existing strict-cut point.
  sorry

end Exercise510
