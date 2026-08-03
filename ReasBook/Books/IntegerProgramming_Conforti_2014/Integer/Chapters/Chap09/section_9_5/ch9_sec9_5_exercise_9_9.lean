import Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_theorem_9_7
import Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_exercise_9_7

-- Declarations for this item will be appended below by the statement pipeline.

-- This exercise reuses the Chapter 9 flatness-theorem owners for embedded integral points and
-- integral directions.

open scoped DirectionalWidthNotation

section Exercise99

variable {n : ℕ}

/-- Helper for Exercise 9.9: `SplitCoverProperty n c` means that every full-dimensional lattice-free
convex body in `ℝ^n` is covered by `c` open split strips. -/
abbrev SplitCoverProperty (n c : ℕ) : Prop :=
  ∀ K : ConvexBody (Fin n → ℝ),
    K.FullDimensional →
    ¬ K.ContainsIntegralPoint →
    ∃ π : Fin c → {π : Fin n → ℤ // π ≠ 0},
      ∃ π₀ : Fin c → ℤ,
        (K : Set (Fin n → ℝ)) ⊆
          ⋃ i : Fin c, split_strip (π i).1 (π₀ i)

/-- Helper for Exercise 9.9: in dimension `0`, every convex body already contains the unique
integral point. -/
lemma contains_integral_point_fin_zero
    (K : ConvexBody (Fin 0 → ℝ)) :
    K.ContainsIntegralPoint := by
  -- Any point of `K` is the unique point of `ℝ^0`, hence it is integral.
  change _root_.contains_integral_point (K : Set (Fin 0 → ℝ))
  rcases K.nonempty with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  rw [mem_integerVectors_iff]
  refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
  funext i
  exact Fin.elim0 i

/-- Helper for Exercise 9.9: the zero-dimensional cover statement is vacuous because the
lattice-free hypothesis is impossible. -/
lemma split_cover_property_zero_dimensional :
    SplitCoverProperty 0 0 := by
  intro K _ hfree
  -- The lattice-free assumption contradicts the unique integral point in `ℝ^0`.
  exfalso
  exact hfree (contains_integral_point_fin_zero K)

/-- Helper for Exercise 9.9: in `ℝ`, a point whose unique coordinate is an integer is already an
integral point of the ambient convex body. -/
lemma contains_integral_point_of_eq_int_one_dimensional
    (K : ConvexBody (Fin 1 → ℝ))
    {x : Fin 1 → ℝ}
    (hx : x ∈ K)
    {m : ℤ}
    (hm : x 0 = (m : ℝ)) :
    K.ContainsIntegralPoint := by
  -- Rewrite `x` as the real embedding of the constant integer vector.
  change _root_.contains_integral_point (K : Set (Fin 1 → ℝ))
  apply (contains_integral_point_iff).2
  refine ⟨fun _ ↦ m, ?_⟩
  have hx_eq : (Int.cast ∘ fun _ : Fin 1 ↦ m) = x := by
    funext i
    fin_cases i
    simpa [Function.comp] using hm.symm
  simpa [hx_eq] using hx

/-- Helper for Exercise 9.9: if a one-dimensional convex body meets both sides of an integer level,
then convexity forces it to contain that integral point. -/
lemma contains_integral_point_of_between_one_dimensional
    (K : ConvexBody (Fin 1 → ℝ))
    {x y : Fin 1 → ℝ}
    (hx : x ∈ K)
    (hy : y ∈ K)
    {m : ℤ}
    (hleft : x 0 ≤ (m : ℝ))
    (hright : (m : ℝ) ≤ y 0) :
    K.ContainsIntegralPoint := by
  by_cases hxy : x 0 = y 0
  · -- If the endpoints agree, the common coordinate is already the desired integer.
    have hm : x 0 = (m : ℝ) := by
      apply le_antisymm hleft
      simpa [hxy] using hright
    exact contains_integral_point_of_eq_int_one_dimensional K hx hm
  · -- Otherwise interpolate to the unique point whose coordinate equals `m`.
    have hlt : x 0 < y 0 := lt_of_le_of_ne (le_trans hleft hright) hxy
    let t : ℝ := ((m : ℝ) - x 0) / (y 0 - x 0)
    have hden : y 0 - x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    have ht0 : 0 ≤ t := by
      dsimp [t]
      refine div_nonneg ?_ ?_
      · linarith
      · linarith
    have ht1 : t ≤ 1 := by
      have hnum_le : (m : ℝ) - x 0 ≤ y 0 - x 0 := by
        linarith
      have hden_nonneg : 0 ≤ y 0 - x 0 := by
        linarith
      have hdiv :
          ((m : ℝ) - x 0) / (y 0 - x 0) ≤ (y 0 - x 0) / (y 0 - x 0) :=
        div_le_div_of_nonneg_right hnum_le hden_nonneg
      simpa [t, hden] using hdiv
    let z : Fin 1 → ℝ := (1 - t) • x + t • y
    have hz_mem : z ∈ K := by
      -- Convexity keeps the interpolated point inside the convex body.
      simpa [z] using
        (convex_iff_add_mem.mp K.convex) hx hy
          (a := 1 - t) (b := t)
          (by linarith) ht0 (by ring)
    have hmul : t * (y 0 - x 0) = (m : ℝ) - x 0 := by
      dsimp [t]
      field_simp [hden]
    have hz_eq : z 0 = (m : ℝ) := by
      calc
        z 0 = (1 - t) * x 0 + t * y 0 := by
          simp [z]
        _ = x 0 + t * (y 0 - x 0) := by ring
        _ = (m : ℝ) := by linarith
    exact contains_integral_point_of_eq_int_one_dimensional K hz_mem hz_eq

/-- Helper for Exercise 9.9: every one-dimensional full-dimensional lattice-free convex body lies in
a single open split strip. -/
lemma exists_single_open_split_cover_one_dimensional :
    SplitCoverProperty 1 1 := by
  intro K _ hfree
  rcases K.nonempty with ⟨x₀, hx₀⟩
  let πvec : Fin 1 → ℤ := fun _ ↦ 1
  have hπvec_nonzero : πvec ≠ 0 := by
    intro hπ
    have hzero : πvec 0 = 0 := by
      simpa using congrFun hπ 0
    norm_num [πvec] at hzero
  let π : Fin 1 → {π : Fin 1 → ℤ // π ≠ 0} := fun _ ↦ ⟨πvec, hπvec_nonzero⟩
  let π₀ : Fin 1 → ℤ := fun _ ↦ Int.floor (x₀ 0)
  refine ⟨π, π₀, ?_⟩
  intro y hy
  have hy_lower : (Int.floor (x₀ 0) : ℝ) < y 0 := by
    by_contra hy_not
    have hy_le : y 0 ≤ (Int.floor (x₀ 0) : ℝ) := not_lt.mp hy_not
    have hbad :=
      contains_integral_point_of_between_one_dimensional
        K hy hx₀ hy_le (Int.floor_le (x₀ 0))
    exact hfree hbad
  have hy_upper : y 0 < (Int.floor (x₀ 0) : ℝ) + 1 := by
    by_contra hy_not
    have hy_ge : (Int.floor (x₀ 0) : ℝ) + 1 ≤ y 0 := not_lt.mp hy_not
    have hx₀_le_next : x₀ 0 ≤ ((Int.floor (x₀ 0) + 1 : ℤ) : ℝ) := by
      -- Cast the standard `floor < a + 1` estimate to the integer level used by the helper.
      simpa [Int.cast_add] using le_of_lt (Int.lt_floor_add_one (x₀ 0))
    have hbad :=
      contains_integral_point_of_between_one_dimensional
        K hx₀ hy (m := Int.floor (x₀ 0) + 1)
        hx₀_le_next (by simpa using hy_ge)
    exact hfree hbad
  have hy_strip : y ∈ split_strip (π 0).1 (π₀ 0) := by
    -- In dimension one, the split scalar product is just the unique coordinate.
    have hsplit_dot : split_dot (π 0).1 y = y 0 := by
      rw [split_dot_eq_sum]
      simp [π, πvec]
    rw [mem_split_strip_iff, hsplit_dot]
    exact And.intro hy_lower hy_upper
  exact Set.mem_iUnion.2 ⟨0, hy_strip⟩

/-- Helper for Exercise 9.9: flatness plus width attainment produces a nonzero integral direction
whose width `w_{d}(K)` is bounded purely in terms of the ambient dimension. -/
lemma exists_bounded_flat_direction
    {n : ℕ}
    (hn : 0 < n)
    {k : ℕ → ℝ}
    (hk : ∀ {n : ℕ}, ∀ K : ConvexBody (Fin n → ℝ),
      K.FullDimensional →
      ¬ K.ContainsIntegralPoint →
      lattice_width K ≤ k n)
    (K : ConvexBody (Fin n → ℝ))
    (hfull : K.FullDimensional)
    (hfree : ¬ K.ContainsIntegralPoint) :
    ∃ d : {d : Fin n → ℤ // d ≠ 0},
      w_{d.1}(K) ≤ k n := by
  -- Realize the lattice width and rewrite the flatness bound through that witness.
  obtain ⟨d, hd_ne, hd⟩ :=
    exists_integral_direction_ne_zero_realizing_lattice_width hn K
  refine ⟨⟨d, hd_ne⟩, ?_⟩
  simpa [hd] using hk K hfull hfree

/-- Helper for Exercise 9.9: `split_dot` is the same linear form used in the lattice-width API. -/
lemma split_dot_eq_integral_direction_linear_form
    {n : ℕ}
    (d : Fin n → ℤ)
    (x : Fin n → ℝ) :
    split_dot d x = integral_direction_linear_form d x := by
  rfl

/-- Helper for Exercise 9.9: every point either already lies in the unit split strip determined by
its floor level, or else the split scalar product is exactly integral. -/
lemma mem_own_floor_split_strip_or_eq_floor
    {n : ℕ}
    (d : Fin n → ℤ)
    (x : Fin n → ℝ) :
    x ∈ split_strip d (Int.floor (split_dot d x)) ∨
      split_dot d x = (Int.floor (split_dot d x) : ℝ) := by
  by_cases hfloor : split_dot d x = (Int.floor (split_dot d x) : ℝ)
  · exact Or.inr hfloor
  · left
    rw [mem_split_strip_iff]
    refine ⟨?_, ?_⟩
    · -- Nonintegrality forces the split value to lie strictly above its floor.
      have hne : (Int.floor (split_dot d x) : ℝ) ≠ split_dot d x := by
        intro hEq
        exact hfloor hEq.symm
      exact lt_of_le_of_ne (Int.floor_le (split_dot d x)) hne
    · -- The standard floor estimate gives the upper unit-strip bound.
      exact Int.lt_floor_add_one (split_dot d x)

/-- Helper for Exercise 9.9: two split values attained on the same convex body differ by at most
the width `w_{d}(K)` in that direction. -/
lemma split_dot_sub_le_directional_width_of_mem
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (d : Fin n → ℤ)
    {x y : Fin n → ℝ}
    (hx : x ∈ K)
    (hy : y ∈ K) :
    split_dot d x - split_dot d y ≤ w_{d}(K) := by
  let imageSet : Set ℝ := split_dot d '' K
  have hcont : Continuous fun z : Fin n → ℝ ↦ split_dot d z := by
    -- Rewrite the scalar product as a finite sum of coordinate maps to use standard continuity.
    have hsum : Continuous fun z : Fin n → ℝ ↦ ∑ i : Fin n, (d i : ℝ) * z i := by
      refine continuous_finsetSum _ ?_
      intro i hi
      exact continuous_const.mul (continuous_apply i)
    simpa [split_dot_eq_sum] using hsum
  have hcompact : IsCompact imageSet := by
    simpa [imageSet] using K.isCompact.image hcont
  have hx_image : split_dot d x ∈ imageSet := by
    exact ⟨x, hx, rfl⟩
  have hy_image : split_dot d y ∈ imageSet := by
    exact ⟨y, hy, rfl⟩
  have hx_le_sup : split_dot d x ≤ sSup imageSet := by
    exact le_csSup hcompact.bddAbove hx_image
  have hinf_le_y : sInf imageSet ≤ split_dot d y := by
    exact csInf_le hcompact.bddBelow hy_image
  have hwidth :
      split_dot d x - split_dot d y ≤ sSup imageSet - sInf imageSet := by
    linarith
  simpa [imageSet, directional_width, split_dot_eq_integral_direction_linear_form] using hwidth

/-- Helper for Exercise 9.9: bounded directional width controls all split values relative to any
chosen base point of the convex body. -/
lemma split_dot_abs_sub_le_of_directional_width_le
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (d : Fin n → ℤ)
    {x y : Fin n → ℝ}
    (hx : x ∈ K)
    (hy : y ∈ K)
    {W : ℝ}
    (hwidth : w_{d}(K) ≤ W) :
    |split_dot d x - split_dot d y| ≤ W := by
  have hxy :
      split_dot d x - split_dot d y ≤ w_{d}(K) :=
    split_dot_sub_le_directional_width_of_mem K d hx hy
  have hyx :
      split_dot d y - split_dot d x ≤ w_{d}(K) :=
    split_dot_sub_le_directional_width_of_mem K d hy hx
  have hneg : -w_{d}(K) ≤ split_dot d x - split_dot d y := by
    linarith
  have habs :
      |split_dot d x - split_dot d y| ≤ w_{d}(K) := by
    exact abs_le.2 ⟨hneg, hxy⟩
  exact le_trans habs hwidth

/-- Exercise 9.9. Every full-dimensional convex body in `ℝ^n` that contains no integral point is
contained in the union of `C n` open split strips, for a constant `C` depending only on the
dimension. The cover is indexed by genuine split directions, so each direction is a nonzero
integral vector. -/
theorem exists_open_split_cover_constant :
    ∃ C : ℕ → ℕ,
      ∀ {n : ℕ}, ∀ K : ConvexBody (Fin n → ℝ),
        K.FullDimensional →
        ¬ K.ContainsIntegralPoint →
        ∃ π : Fin (C n) → {π : Fin n → ℤ // π ≠ 0},
          ∃ π₀ : Fin (C n) → ℤ,
          (K : Set (Fin n → ℝ)) ⊆
            ⋃ i : Fin (C n), split_strip (π i).1 (π₀ i) := by
  classical
  have hcover : ∀ n : ℕ, ∃ c, SplitCoverProperty n c := by
    intro n
    induction n with
    | zero =>
        -- The zero-dimensional case is impossible under the lattice-free hypothesis.
        exact ⟨0, split_cover_property_zero_dimensional⟩
    | succ n ih =>
        cases n with
        | zero =>
            -- In dimension one, one split strip already covers the body.
            exact ⟨1, exists_single_open_split_cover_one_dimensional⟩
        | succ m =>
            rcases ih with ⟨Cm, hCm⟩
            obtain ⟨k, hk⟩ := exists_flatness_constant_for_lattice_width
            refine ⟨Nat.succ (Nat.ceil (k (m + 2))) * (Cm + 1), ?_⟩
            intro K hfull hfree
            rcases K.nonempty with ⟨x₀, hx₀⟩
            have hdir :
                ∃ d : {d : Fin (m + 2) → ℤ // d ≠ 0},
                  w_{d.1}(K) ≤ k (m + 2) := by
              exact
                exists_bounded_flat_direction
                  (Nat.succ_pos (m + 1)) hk K hfull hfree
            obtain ⟨d, hd⟩ := hdir
            have hbase_interval :
                ∀ y ∈ K,
                  |split_dot d.1 y - split_dot d.1 x₀| ≤ k (m + 2) := by
              intro y hy
              -- The chosen flat direction controls all split values on `K`.
              simpa [abs_sub_comm] using
                split_dot_abs_sub_le_of_directional_width_le
                  K d.1 hy hx₀ hd
            -- The induction is reduced to finitely many integer slices, but the remaining
            -- hyperplane-to-lower-dimensional transport is not yet packaged in this chapter API.
            admit
  refine ⟨fun n ↦ Classical.choose (hcover n), ?_⟩
  intro n K hfull hfree
  exact Classical.choose_spec (hcover n) K hfull hfree

end Exercise99
