import Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_exercise_2_26

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

-- Semantic search tool `lean_leansearch` was unavailable in this environment; the statement below
-- was matched against the Chapter 4 `is_zero_one_vector` owner together with local `convexHull`
-- and `Fin`-indexed precedents.

/-- The support of a `0,1`-vertex of the hypercube: the coordinates where the vertex is equal to
`1`. -/
def hypercube_vertex_support {n : ℕ} (v : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ v j = 1

/-- Two hypercube vertices are adjacent when they differ in exactly one coordinate. -/
def hypercube_adjacent {n : ℕ} (u v : Fin n → ℝ) : Prop :=
  is_zero_one_vector u ∧ is_zero_one_vector v ∧
    (Finset.univ.filter fun j ↦ u j ≠ v j).card = 1

/-- The inequality associated with deleting the hypercube vertex `v`, written in terms of the
support of `v`. -/
def deleted_vertex_inequality {n : ℕ} (v x : Fin n → ℝ) : Prop :=
  Finset.sum (hypercube_vertex_support v) x -
      Finset.sum (Finset.univ \ hypercube_vertex_support v) x ≤
    ((hypercube_vertex_support v).card : ℝ) - 1

/-- Helper for Exercise 4.2: the deleted-vertex inequality is defined by a linear functional on
`ℝ^n`. -/
def deleted_vertex_linear {n : ℕ} (v : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  (∑ j ∈ hypercube_vertex_support v,
      (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ)) -
    ∑ j ∈ (Finset.univ \ hypercube_vertex_support v),
      (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ)

/-- Helper for Exercise 4.2: a hypercube vertex lies in the unit cube. -/
lemma hypercube_vertex_mem_unit_hypercube {n : ℕ} {v : Fin n → ℝ}
    (hv : is_zero_one_vector v) :
    v ∈ Set.Icc (0 : Fin n → ℝ) 1 := by
  -- A `0/1` vector satisfies the unit-cube bounds coordinatewise.
  constructor
  · intro i
    rcases hv i with h0 | h1
    · simpa [Pi.zero_apply, h0]
    · simpa [Pi.zero_apply, h1]
  · intro i
    rcases hv i with h0 | h1
    · simpa [Pi.one_apply, h0]
    · simpa [Pi.one_apply, h1]

/-- Helper for Exercise 4.2: the deleted-vertex region is the preimage of a half-line under the
associated linear functional. -/
lemma deleted_vertex_region_eq_preimage {n : ℕ} (v : Fin n → ℝ) :
    {x | deleted_vertex_inequality v x} =
      deleted_vertex_linear v ⁻¹'
        Set.Iic (((hypercube_vertex_support v).card : ℝ) - 1) := by
  -- Unfold the linear map and compare both descriptions pointwise.
  ext x
  simp [deleted_vertex_inequality, deleted_vertex_linear]

/-- Helper for Exercise 4.2: the region cut out by one deleted-vertex inequality is convex. -/
lemma deleted_vertex_region_convex {n : ℕ} (v : Fin n → ℝ) :
    Convex ℝ {x : Fin n → ℝ | deleted_vertex_inequality v x} := by
  -- Each deleted-vertex region is the preimage of a convex half-line under a linear map.
  rw [deleted_vertex_region_eq_preimage]
  simpa using (convex_Iic (((hypercube_vertex_support v).card : ℝ) - 1)).linear_preimage
    (deleted_vertex_linear v)

/-- Helper for Exercise 4.2: on the unit cube, the deleted-vertex inequality is exactly the
statement that the `ℓ¹` distance from `x` to `v` is at least `1`. -/
lemma deleted_vertex_inequality_iff_one_le_l1_distance {n : ℕ} {v x : Fin n → ℝ}
    (hv : is_zero_one_vector v) (hx : x ∈ Set.Icc (0 : Fin n → ℝ) 1) :
    deleted_vertex_inequality v x ↔ 1 ≤ ∑ j : Fin n, |x j - v j| := by
  -- Rewrite the `ℓ¹` distance by separating the coordinates where `v` is `1` from those where
  -- `v` is `0`.
  have hsupport :
      (hypercube_vertex_support v).sum (fun j ↦ |x j - v j|) =
        ((hypercube_vertex_support v).card : ℝ) -
          ((hypercube_vertex_support v).sum x) := by
    calc
      (hypercube_vertex_support v).sum (fun j ↦ |x j - v j|)
          = (hypercube_vertex_support v).sum (fun j ↦ (1 - x j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hvj : v j = 1 := (Finset.mem_filter.mp hj).2
              have hxj : x j ≤ 1 := hx.2 j
              have habs : |x j - 1| = 1 - x j := by
                have habs' : |x j - 1| = -(x j - 1) := abs_of_nonpos (sub_nonpos.mpr hxj)
                linarith
              simpa [hvj] using habs
      _ = ((hypercube_vertex_support v).sum fun _ ↦ (1 : ℝ)) -
            ((hypercube_vertex_support v).sum x) := by
            rw [Finset.sum_sub_distrib]
      _ = ((hypercube_vertex_support v).card : ℝ) -
            ((hypercube_vertex_support v).sum x) := by
            simp
  have hcomplement :
      (Finset.univ \ hypercube_vertex_support v).sum (fun j ↦ |x j - v j|) =
        (Finset.univ \ hypercube_vertex_support v).sum x := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj_not_mem : j ∉ hypercube_vertex_support v := (Finset.mem_sdiff.mp hj).2
    have hvj : v j = 0 := by
      rcases hv j with h0 | h1
      · exact h0
      · exfalso
        exact hj_not_mem (by simpa [hypercube_vertex_support, h1])
    have hxj : 0 ≤ x j := hx.1 j
    rw [hvj, sub_zero]
    exact abs_of_nonneg hxj
  have hl1 :
      Finset.univ.sum (fun j : Fin n ↦ |x j - v j|) =
        ((hypercube_vertex_support v).card : ℝ) -
          ((hypercube_vertex_support v).sum x) +
            ((Finset.univ \ hypercube_vertex_support v).sum x) := by
    calc
      Finset.univ.sum (fun j : Fin n ↦ |x j - v j|)
          = (hypercube_vertex_support v).sum (fun j ↦ |x j - v j|) +
              (Finset.univ \ hypercube_vertex_support v).sum (fun j ↦ |x j - v j|) := by
                simpa [hypercube_vertex_support, Finset.sdiff_eq_filter] using
                  (Finset.sum_filter_add_sum_filter_not
                    (s := Finset.univ)
                    (f := fun j : Fin n ↦ |x j - v j|)
                    (p := fun j ↦ v j = 1)).symm
      _ = ((hypercube_vertex_support v).card : ℝ) -
            ((hypercube_vertex_support v).sum x) +
              ((Finset.univ \ hypercube_vertex_support v).sum fun j ↦ |x j - v j|) := by
            rw [hsupport]
      _ = ((hypercube_vertex_support v).card : ℝ) -
            ((hypercube_vertex_support v).sum x) +
              ((Finset.univ \ hypercube_vertex_support v).sum x) := by
            rw [hcomplement]
  -- The deleted inequality is exactly the rearranged lower bound `1 ≤ ‖x - v‖₁`.
  constructor
  · intro hineq
    unfold deleted_vertex_inequality at hineq
    rw [hl1]
    linarith
  · intro hlower
    unfold deleted_vertex_inequality
    rw [hl1] at hlower
    linarith

/-- Helper for Exercise 4.2: distinct hypercube vertices differ in at least one coordinate, so
their `ℓ¹` distance is at least `1`. -/
lemma one_le_l1_distance_of_ne_hypercube_vertices {n : ℕ} {v w : Fin n → ℝ}
    (hv : is_zero_one_vector v) (hw : is_zero_one_vector w) (hvw : w ≠ v) :
    1 ≤ ∑ j : Fin n, |w j - v j| := by
  classical
  -- Pick a coordinate where the two binary vectors differ.
  have hcoord : ∃ i : Fin n, w i ≠ v i := by
    by_contra hcoord
    apply hvw
    ext i
    by_contra hneq
    exact hcoord ⟨i, hneq⟩
  rcases hcoord with ⟨i, hi⟩
  have hi_abs : |w i - v i| = 1 := by
    rcases hw i with hwi0 | hwi1 <;> rcases hv i with hvi0 | hvi1
    · exfalso
      exact hi (by simpa [hwi0, hvi0])
    · simp [hwi0, hvi1]
    · simp [hwi1, hvi0]
    · exfalso
      exact hi (by simpa [hwi1, hvi1])
  have hi_le_sum : |w i - v i| ≤ Finset.univ.sum (fun j : Fin n ↦ |w j - v j|) := by
    simpa using
      (Finset.single_le_sum
        (fun j _ ↦ abs_nonneg (w j - v j))
        (by simp : i ∈ Finset.univ) :
          |w i - v i| ≤ Finset.univ.sum (fun j : Fin n ↦ |w j - v j|))
  -- Compare the full sum with the nonzero coordinate contribution.
  have hi_one : (1 : ℝ) ≤ |w i - v i| := by
    simpa [hi_abs]
  exact hi_one.trans hi_le_sum

/-- Helper for Exercise 4.2: on hypercube vertices, the deleted-vertex inequality excludes exactly
the deleted vertex itself. -/
lemma deleted_vertex_inequality_iff_ne_on_hypercube_vertices {n : ℕ} {v w : Fin n → ℝ}
    (hv : is_zero_one_vector v) (hw : is_zero_one_vector w) :
    deleted_vertex_inequality v w ↔ w ≠ v := by
  -- Specialize the `ℓ¹` reformulation to binary points.
  have hw_cube : w ∈ Set.Icc (0 : Fin n → ℝ) 1 := hypercube_vertex_mem_unit_hypercube hw
  rw [deleted_vertex_inequality_iff_one_le_l1_distance hv hw_cube]
  constructor
  · intro hineq hEq
    have : (1 : ℝ) ≤ 0 := by
      simpa [hEq] using hineq
    linarith
  · intro hne
    exact one_le_l1_distance_of_ne_hypercube_vertices hv hw hne

/-- Helper for Exercise 4.2: the deleted-vertex system is convex because it is the unit cube
intersected with deleted-vertex halfspaces. -/
lemma deleted_vertex_system_convex {n : ℕ} {V : Finset (Fin n → ℝ)} :
    Convex ℝ {x : Fin n → ℝ | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
      ∀ v ∈ V, deleted_vertex_inequality v x} := by
  -- Rewrite the feasible region as an intersection indexed by the deleted vertices.
  have hrewrite :
      {x : Fin n → ℝ | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
          ∀ v ∈ V, deleted_vertex_inequality v x} =
        Set.Icc (0 : Fin n → ℝ) 1 ∩
          ⋂ v : ↥V, {x : Fin n → ℝ | deleted_vertex_inequality (v : Fin n → ℝ) x} := by
    ext x
    simp
  rw [hrewrite]
  exact (convex_Icc (0 : Fin n → ℝ) 1).inter <|
    convex_iInter fun v ↦ deleted_vertex_region_convex (v : Fin n → ℝ)

/-- Helper for Exercise 4.2: an undeleted hypercube vertex satisfies every deleted-vertex
inequality, hence lies in the deleted-vertex system. -/
lemma undeleted_hypercube_vertex_mem_deleted_vertex_system
    {n : ℕ} {V : Finset (Fin n → ℝ)}
    (hV_vertices : ∀ ⦃v : Fin n → ℝ⦄, v ∈ V → is_zero_one_vector v)
    {w : Fin n → ℝ} (hw : is_zero_one_vector w) (hw_not_mem : w ∉ V) :
    w ∈ {x : Fin n → ℝ | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
      ∀ v ∈ V, deleted_vertex_inequality v x} := by
  -- The box constraints come from binaryness, and each deleted inequality reduces to `w ≠ v`.
  have hw_cube : w ∈ Set.Icc (0 : Fin n → ℝ) 1 := hypercube_vertex_mem_unit_hypercube hw
  have hw_deleted : ∀ v ∈ V, deleted_vertex_inequality v w := by
    intro v hv
    exact (deleted_vertex_inequality_iff_ne_on_hypercube_vertices (hV_vertices hv) hw).2
      (fun hEq ↦ hw_not_mem (hEq ▸ hv))
  exact ⟨hw_cube, hw_deleted⟩

/-- Helper for Exercise 4.2: the convex hull of the undeleted hypercube vertices is contained in
the deleted-vertex system. -/
lemma convexHull_hypercube_vertices_diff_subset_deleted_vertex_system
    {n : ℕ} {V : Finset (Fin n → ℝ)}
    (hV_vertices : ∀ ⦃v : Fin n → ℝ⦄, v ∈ V → is_zero_one_vector v) :
    convexHull ℝ ({v : Fin n → ℝ | is_zero_one_vector v} \ (V : Set (Fin n → ℝ))) ⊆
      {x : Fin n → ℝ | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
        ∀ v ∈ V, deleted_vertex_inequality v x} := by
  -- It is enough to check the generating undeleted vertices and use convexity of the target set.
  refine convexHull_min ?_ deleted_vertex_system_convex
  intro w hw
  exact undeleted_hypercube_vertex_mem_deleted_vertex_system hV_vertices hw.1 hw.2

/-- Helper for Exercise 4.2: if a deleted-vertex inequality is active at a fractional feasible
point, then the deleted vertex agrees with that point on every integral coordinate. -/
lemma active_deleted_vertex_eq_on_integral_coordinates
    {n : ℕ} {v x : Fin n → ℝ}
    (hv : is_zero_one_vector v)
    (hx : x ∈ Set.Icc (0 : Fin n → ℝ) 1)
    (hactive : ∑ j : Fin n, |x j - v j| = 1)
    (hfrac : ¬ is_zero_one_vector x) :
    ∀ i : Fin n, (x i = 0 ∨ x i = 1) → v i = x i := by
  classical
  -- Pick a genuinely fractional coordinate of `x`; it contributes positive `ℓ¹` distance to any
  -- binary vertex, so an integral mismatch would force the active sum strictly above `1`.
  have hfrac_coord : ∃ k : Fin n, x k ≠ 0 ∧ x k ≠ 1 := by
    by_contra hno
    apply hfrac
    intro i
    by_contra hxi
    have hxi' : x i ≠ 0 ∧ x i ≠ 1 := by
      simpa [not_or] using hxi
    exact hno ⟨i, hxi'⟩
  rcases hfrac_coord with ⟨k, hk0, hk1⟩
  intro i hxi
  by_contra hvi
  have hki : k ≠ i := by
    intro hEq
    subst hEq
    rcases hxi with hxi0 | hxi1
    · exact hk0 hxi0
    · exact hk1 hxi1
  have hk_pos : 0 < |x k - v k| := by
    rcases hv k with hvk0 | hvk1
    · rw [hvk0, sub_zero]
      exact abs_pos.mpr hk0
    · have : x k - 1 ≠ 0 := sub_ne_zero.mpr hk1
      simpa [hvk1] using abs_pos.mpr this
  have hi_abs : |x i - v i| = 1 := by
    rcases hxi with hxi0 | hxi1 <;> rcases hv i with hvi0 | hvi1
    · exfalso
      exact hvi (by simpa [hxi0, hvi0])
    · simp [hxi0, hvi1]
    · simp [hxi1, hvi0]
    · exfalso
      exact hvi (by simpa [hxi1, hvi1])
  have hk_le :
      |x k - v k| ≤ (Finset.univ.erase i).sum (fun j : Fin n ↦ |x j - v j|) := by
    exact Finset.single_le_sum
      (fun j _ ↦ abs_nonneg (x j - v j))
      (by simpa [hki] using (show k ∈ Finset.univ.erase i by simp [hki]))
  have hsum_gt :
      1 < ∑ j : Fin n, |x j - v j| := by
    calc
      1 = |x i - v i| := hi_abs.symm
      _ < |x i - v i| + (Finset.univ.erase i).sum (fun j : Fin n ↦ |x j - v j|) := by
        have : 0 < (Finset.univ.erase i).sum (fun j : Fin n ↦ |x j - v j|) :=
          lt_of_lt_of_le hk_pos hk_le
        linarith
      _ = ∑ j : Fin n, |x j - v j| := by
        symm
        simpa [add_comm] using Finset.sum_erase_add
          (s := Finset.univ)
          (a := i)
          (f := fun j : Fin n ↦ |x j - v j|)
          (by simp)
  rw [hactive] at hsum_gt
  linarith

/-- Helper for Exercise 4.2: a feasible point with all but possibly one coordinate integral already
lies in the convex hull of the undeleted hypercube vertices. -/
lemma mem_convexHull_of_all_but_one_integral_coordinate
    {n : ℕ} {V : Finset (Fin n → ℝ)}
    (hV_vertices : ∀ ⦃v : Fin n → ℝ⦄, v ∈ V → is_zero_one_vector v)
    {x : Fin n → ℝ}
    (hx : x ∈ {y : Fin n → ℝ | y ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
      ∀ v ∈ V, deleted_vertex_inequality v y})
    (i : Fin n)
    (hintegral : ∀ j : Fin n, j ≠ i → x j = 0 ∨ x j = 1) :
    x ∈ convexHull ℝ ({v : Fin n → ℝ | is_zero_one_vector v} \ (V : Set (Fin n → ℝ))) := by
  classical
  let S : Set (Fin n → ℝ) := {v : Fin n → ℝ | is_zero_one_vector v} \ (V : Set (Fin n → ℝ))
  let x0 : Fin n → ℝ := fun j ↦ if j = i then 0 else x j
  let x1 : Fin n → ℝ := fun j ↦ if j = i then 1 else x j
  have hx0_zero_one : is_zero_one_vector x0 := by
    -- The rounded-down endpoint keeps every other coordinate at its already integral value.
    intro j
    by_cases hji : j = i
    · simp [x0, hji]
    · simpa [x0, hji] using hintegral j hji
  have hx1_zero_one : is_zero_one_vector x1 := by
    -- The rounded-up endpoint is handled identically.
    intro j
    by_cases hji : j = i
    · simp [x1, hji]
    · simpa [x1, hji] using hintegral j hji
  have hx_binary_of_coord (hxi : x i = 0 ∨ x i = 1) : is_zero_one_vector x := by
    -- Once the `i`-th coordinate is also integral, the whole point is binary.
    intro j
    by_cases hji : j = i
    · simpa [hji] using hxi
    · exact hintegral j hji
  have hx_not_mem_of_binary (hx_binary : is_zero_one_vector x) : x ∉ V := by
    -- A feasible binary point cannot be one of the deleted vertices, because it satisfies its own
    -- deleted inequality.
    intro hxV
    have hineq : deleted_vertex_inequality x x := hx.2 x hxV
    exact
      (deleted_vertex_inequality_iff_ne_on_hypercube_vertices hx_binary hx_binary).1 hineq rfl
  have hx0_sum :
      ∑ j : Fin n, |x j - x0 j| = x i := by
    -- The rounded-down endpoint differs from `x` only in coordinate `i`.
    rw [Finset.sum_eq_single i]
    · have hxi_nonneg : 0 ≤ x i := hx.1.1 i
      simp [x0, hxi_nonneg]
    · intro j _ hji
      simp [x0, hji]
    · intro hi
      exact (hi (by simp)).elim
  have hx1_sum :
      ∑ j : Fin n, |x j - x1 j| = 1 - x i := by
    -- The rounded-up endpoint also differs only in coordinate `i`.
    rw [Finset.sum_eq_single i]
    · have hxi_le : x i ≤ 1 := hx.1.2 i
      have habs : |x i - 1| = 1 - x i := by
        have habs' : |x i - 1| = -(x i - 1) := abs_of_nonpos (sub_nonpos.mpr hxi_le)
        linarith
      simp [x1, habs]
    · intro j _ hji
      simp [x1, hji]
    · intro hi
      exact (hi (by simp)).elim
  by_cases hxi0 : x i = 0
  · -- If `x i = 0`, then `x` itself is the rounded-down undeleted vertex.
    have hx_binary : is_zero_one_vector x := hx_binary_of_coord (Or.inl hxi0)
    have hx_not_mem : x ∉ V := hx_not_mem_of_binary hx_binary
    have hx_eq_x0 : x = x0 := by
      ext j
      by_cases hji : j = i
      · simp [x0, hji, hxi0]
      · simp [x0, hji]
    have hx_mem_S : x ∈ S := ⟨hx_binary, hx_not_mem⟩
    rw [hx_eq_x0]
    simpa [hx_eq_x0] using subset_convexHull ℝ S hx_mem_S
  by_cases hxi1 : x i = 1
  · -- If `x i = 1`, then `x` is the rounded-up undeleted vertex.
    have hx_binary : is_zero_one_vector x := hx_binary_of_coord (Or.inr hxi1)
    have hx_not_mem : x ∉ V := hx_not_mem_of_binary hx_binary
    have hx_eq_x1 : x = x1 := by
      ext j
      by_cases hji : j = i
      · simp [x1, hji, hxi1]
      · simp [x1, hji]
    have hx_mem_S : x ∈ S := ⟨hx_binary, hx_not_mem⟩
    rw [hx_eq_x1]
    simpa [hx_eq_x1] using subset_convexHull ℝ S hx_mem_S
  have hxi_pos : 0 < x i := by
    have hxi_nonneg : 0 ≤ x i := hx.1.1 i
    exact lt_of_le_of_ne hxi_nonneg (Ne.symm hxi0)
  have hxi_lt_one : x i < 1 := by
    have hxi_le : x i ≤ 1 := hx.1.2 i
    exact lt_of_le_of_ne hxi_le hxi1
  have hx0_not_mem : x0 ∉ V := by
    -- A deleted rounded-down endpoint would sit at `ℓ¹`-distance `x i < 1` from `x`.
    intro hx0V
    have hineq : deleted_vertex_inequality x0 x := hx.2 x0 hx0V
    have hone : 1 ≤ ∑ j : Fin n, |x j - x0 j| :=
      (deleted_vertex_inequality_iff_one_le_l1_distance (hV_vertices hx0V) hx.1).1 hineq
    rw [hx0_sum] at hone
    linarith
  have hx1_not_mem : x1 ∉ V := by
    -- The same argument excludes the rounded-up endpoint.
    intro hx1V
    have hineq : deleted_vertex_inequality x1 x := hx.2 x1 hx1V
    have hone : 1 ≤ ∑ j : Fin n, |x j - x1 j| :=
      (deleted_vertex_inequality_iff_one_le_l1_distance (hV_vertices hx1V) hx.1).1 hineq
    rw [hx1_sum] at hone
    linarith
  have hx_mem_segment : x ∈ segment ℝ x0 x1 := by
    -- Express `x` as the convex combination of the two rounded endpoints with weights
    -- `1 - x i` and `x i`.
    refine ⟨1 - x i, x i, sub_nonneg.mpr hx.1.2 i, hx.1.1 i, by linarith, ?_⟩
    ext j
    by_cases hji : j = i
    · subst hji
      simp [x0, x1]
    · simp [x0, x1, hji]
      ring
  have hx0_mem_S : x0 ∈ S := ⟨hx0_zero_one, hx0_not_mem⟩
  have hx1_mem_S : x1 ∈ S := ⟨hx1_zero_one, hx1_not_mem⟩
  exact (segment_subset_convexHull hx0_mem_S hx1_mem_S) hx_mem_segment

/-- Helper for Exercise 4.2: the `0/1` vertices of the `n`-hypercube form a finite set. -/
lemma finite_zero_one_vectors (n : ℕ) :
    ({v : Fin n → ℝ | is_zero_one_vector v} : Set (Fin n → ℝ)).Finite := by
  let vertexOfSupport : Finset (Fin n) → Fin n → ℝ := fun T i ↦ if i ∈ T then 1 else 0
  have hsubset :
      {v : Fin n → ℝ | is_zero_one_vector v} ⊆ Set.range vertexOfSupport := by
    intro v hv
    refine ⟨hypercube_vertex_support v, ?_⟩
    ext i
    by_cases hvi1 : v i = 1
    · have himem : i ∈ hypercube_vertex_support v := by
        simp [hypercube_vertex_support, hvi1]
      simp [vertexOfSupport, himem, hvi1]
    · have hvi0 : v i = 0 := by
        rcases hv i with h0 | h1
        · exact h0
        · exact (hvi1 h1).elim
      have hnot_mem : i ∉ hypercube_vertex_support v := by
        simp [hypercube_vertex_support, hvi0]
      simp [vertexOfSupport, hnot_mem, hvi0]
  exact (Set.finite_range vertexOfSupport).subset hsubset

/-- Helper for Exercise 4.2: once `x` is not binary, the negation of the one-fractional-coordinate
case yields two distinct fractional coordinates. -/
lemma exists_two_fractional_coordinates_of_not_small
    {n : ℕ} {x : Fin n → ℝ}
    (hx_nonbinary : ¬ is_zero_one_vector x)
    (hsmall : ¬ ∃ i : Fin n, ∀ j : Fin n, j ≠ i → x j = 0 ∨ x j = 1) :
    ∃ p q : Fin n, p ≠ q ∧ ¬ (x p = 0 ∨ x p = 1) ∧ ¬ (x q = 0 ∨ x q = 1) := by
  -- Start from one fractional coordinate and use `¬ hsmall` to find a second one away from it.
  have hp : ∃ p : Fin n, ¬ (x p = 0 ∨ x p = 1) := by
    by_contra hno
    apply hx_nonbinary
    intro i
    by_contra hi
    exact hno ⟨i, hi⟩
  rcases hp with ⟨p, hpfrac⟩
  have hq : ∃ q : Fin n, q ≠ p ∧ ¬ (x q = 0 ∨ x q = 1) := by
    by_contra hno
    apply hsmall
    refine ⟨p, ?_⟩
    intro j hj
    by_contra hjfrac
    exact hno ⟨j, hj, hjfrac⟩
  rcases hq with ⟨q, hqp, hqfrac⟩
  exact ⟨p, q, hqp.symm, hpfrac, hqfrac⟩

/-- Helper for Exercise 4.2: the genuinely higher-dimensional feasible branch should be excluded by
an active-face perturbation, so points in that branch are not extreme. -/
lemma many_fractional_deleted_vertex_system_point_not_extreme
    {n : ℕ} {V : Finset (Fin n → ℝ)}
    (hV_vertices : ∀ ⦃v : Fin n → ℝ⦄, v ∈ V → is_zero_one_vector v)
    (hV_nonadjacent : ((V : Set (Fin n → ℝ)).Pairwise fun u v ↦ ¬ hypercube_adjacent u v))
    {x : Fin n → ℝ}
    (hx : x ∈ {y : Fin n → ℝ | y ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
      ∀ v ∈ V, deleted_vertex_inequality v y})
    (hx_nonbinary : ¬ is_zero_one_vector x)
    (hsmall : ¬ ∃ i : Fin n, ∀ j : Fin n, j ≠ i → x j = 0 ∨ x j = 1) :
    x ∉ ({y : Fin n → ℝ | y ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
      ∀ v ∈ V, deleted_vertex_inequality v y}).extremePoints ℝ := by
  -- Route correction: the higher-dimensional branch must be handled by the source-faithful
  -- active-face perturbation argument, not by another one-coordinate edge decomposition.
  -- The extra hypothesis `hx_nonbinary` is necessary: for `n = 0`, the negation of `hsmall` holds
  -- vacuously even though the unique feasible point is binary and therefore extreme.
  -- TODO: build a nonzero direction on the fractional face that annihilates every active
  -- deleted-vertex linear form, then perturb `x` to two distinct feasible points around it.
  sorry

/-- Exercise 4.2. If `V` is a finite family of pairwise nonadjacent vertices of the `n`-hypercube,
then the convex hull of the remaining hypercube vertices is exactly the subset of `[0,1]^n`
cut out by the support inequalities associated with the deleted vertices. -/
theorem convexHull_hypercube_vertices_diff_eq_deleted_vertex_inequalities
    {n : ℕ} {V : Finset (Fin n → ℝ)}
    (hV_vertices : ∀ ⦃v : Fin n → ℝ⦄, v ∈ V → is_zero_one_vector v)
    (hV_nonadjacent : ((V : Set (Fin n → ℝ)).Pairwise fun u v ↦ ¬ hypercube_adjacent u v)) :
    convexHull ℝ ({v : Fin n → ℝ | is_zero_one_vector v} \ (V : Set (Fin n → ℝ))) =
      {x | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧ ∀ v ∈ V, deleted_vertex_inequality v x} := by
  classical
  let S : Set (Fin n → ℝ) := {v : Fin n → ℝ | is_zero_one_vector v} \ (V : Set (Fin n → ℝ))
  let P : Set (Fin n → ℝ) := {x : Fin n → ℝ | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
    ∀ v ∈ V, deleted_vertex_inequality v x}
  have hSP : convexHull ℝ S ⊆ P := by
    -- The easy inclusion is validity of every deleted inequality on every undeleted vertex,
    -- followed by convexity of the deleted-vertex system.
    simpa [S, P] using convexHull_hypercube_vertices_diff_subset_deleted_vertex_system hV_vertices
  have hPconvex : Convex ℝ P := by
    -- The deleted-vertex system is an intersection of the unit cube with finitely many
    -- deleted-vertex halfspaces.
    simpa [P] using (deleted_vertex_system_convex : Convex ℝ P)
  have hPclosed : IsClosed P := by
    -- Rewrite the feasible region as the unit cube intersected with closed halfspaces.
    have hrewrite :
        P = Set.Icc (0 : Fin n → ℝ) 1 ∩
          ⋂ v : ↥V, {x : Fin n → ℝ | deleted_vertex_inequality (v : Fin n → ℝ) x} := by
      ext x
      simp [P]
    rw [hrewrite]
    refine isClosed_Icc.inter ?_
    exact isClosed_iInter fun v ↦ by
      rw [deleted_vertex_region_eq_preimage]
      exact (isClosed_Iic).preimage
        (deleted_vertex_linear (v : Fin n → ℝ)).continuous_of_finiteDimensional
  have hPsubset_cube : P ⊆ Set.Icc (0 : Fin n → ℝ) 1 := by
    -- Membership in the deleted-vertex system includes the box constraints by definition.
    intro x hx
    have hx' : x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
        ∀ v ∈ V, deleted_vertex_inequality v x := by
      simpa [P] using hx
    exact hx'.1
  have hPcompact : IsCompact P := by
    -- The feasible region is a closed subset of the compact unit cube.
    exact IsCompact.of_isClosed_subset isCompact_Icc hPclosed hPsubset_cube
  have hPextreme_subset : P.extremePoints ℝ ⊆ S := by
    intro x hxext
    have hxP : x ∈ P := extremePoints_subset hxext
    by_cases hx_binary : is_zero_one_vector x
    · -- A feasible binary point is an undeleted hypercube vertex, hence already belongs to `S`.
      refine ⟨hx_binary, ?_⟩
      intro hxV
      have hineq : deleted_vertex_inequality x x := by
        simpa [P] using (hxP.2 x hxV)
      exact
        (deleted_vertex_inequality_iff_ne_on_hypercube_vertices hx_binary hx_binary).1 hineq rfl
    · by_cases hsmall : ∃ i : Fin n, ∀ j : Fin n, j ≠ i → x j = 0 ∨ x j = 1
      · -- The one-fractional-coordinate branch already places `x` in the convex hull of undeleted
        -- hypercube vertices, so extremality forces `x` to be one of those vertices.
        rcases hsmall with ⟨i, hi⟩
        have hxHull : x ∈ convexHull ℝ S := by
          simpa [S, P] using
            mem_convexHull_of_all_but_one_integral_coordinate hV_vertices
              (by simpa [P] using hxP) i hi
        have hxextHull : x ∈ (convexHull ℝ S).extremePoints ℝ :=
          inter_extremePoints_subset_extremePoints_of_subset hSP ⟨hxHull, hxext⟩
        exact extremePoints_convexHull_subset hxextHull
      · -- Route correction: after removing the binary case, only the genuinely higher-dimensional
        -- fractional branch remains, and that branch should be excluded by perturbation.
        exact False.elim <|
          many_fractional_deleted_vertex_system_point_not_extreme hV_vertices hV_nonadjacent
            (by simpa [P] using hxP) hx_binary hsmall hxext
  have hSfinite : S.Finite := by
    -- The undeleted vertices form a subset of the finite `0/1` cube.
    refine (finite_zero_one_vectors n).subset ?_
    intro x hx
    simpa [S] using hx.1
  refine Set.Subset.antisymm hSP ?_
  intro x hx
  have hclosure : closure (convexHull ℝ (P.extremePoints ℝ)) = P :=
    closure_convexHull_extremePoints hPcompact hPconvex
  have hxClosure : x ∈ closure (convexHull ℝ (P.extremePoints ℝ)) := by
    -- Krein-Milman reduces the feasible region to the closure of the convex hull of its extreme
    -- points.
    simpa [hclosure] using hx
  have hxClosureS : x ∈ closure (convexHull ℝ S) := by
    -- Every extreme point already lies in `S`, so the same holds for their convex hull.
    exact (closure_mono (convexHull_mono hPextreme_subset)) hxClosure
  -- The undeleted vertex set is finite, so its convex hull is closed and the closure can be
  -- removed.
  simpa [(hSfinite.isClosed_convexHull ℝ).closure_eq] using hxClosureS
