import Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_theorem_5_22

open scoped CoordinateLiftProjectNotation

-- Primary domain: Chapter 5 lift-and-project closures on prefix coordinates in `ℝ^n`.
-- Core/canonical owners reused here: `is_polyhedron`, `coordinate_lift_project_hull`, and
-- `lift_project_closure`.
-- This file stays source-facing: it keeps the `k`-step closure and the `k`-subset binary-point
-- sets from Exercise 5.25, while expressing the one-step prefix closure through the canonical
-- Chapter 5 lift-project owner.

section Exercise525

variable {n p : ℕ}

/-- The one-step lift-and-project closure of `P` along the first `p` coordinates. -/
def prefix_lift_project_closure
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  lift_project_closure P (Finset.univ.image (Fin.castLEEmb hp))

/-- Membership in `prefix_lift_project_closure hp P` means membership in every coordinate
lift-and-project hull attached to the first `p` coordinates. -/
theorem mem_prefix_lift_project_closure_iff
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (x : Fin n → ℝ) :
    x ∈ prefix_lift_project_closure hp P ↔
      ∀ j : Fin p, x ∈ (P)_{Fin.castLE hp j} := by
  simp [prefix_lift_project_closure, mem_lift_project_closure_iff]

/-- The points of `P` whose coordinates indexed by `J` are binary. -/
def binary_prefix_points_on_subset
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (J : Finset (Fin p)) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ | x ∈ P ∧ ∀ j ∈ J, x (Fin.castLE hp j) = 0 ∨ x (Fin.castLE hp j) = 1}

/-- Membership in `binary_prefix_points_on_subset hp P J` means belonging to `P` and having
binary coordinates on the prefix index set `J`. -/
theorem mem_binary_prefix_points_on_subset_iff
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (J : Finset (Fin p))
    (x : Fin n → ℝ) :
    x ∈ binary_prefix_points_on_subset hp P J ↔
      x ∈ P ∧ ∀ j ∈ J, x (Fin.castLE hp j) = 0 ∨ x (Fin.castLE hp j) = 1 :=
  Iff.rfl

/-- For the full prefix index set `Fin p`, the subset-based binary-point owner agrees with the
Chapter 5 full-prefix owner `zero_one_points`. -/
theorem binary_prefix_points_on_subset_univ_eq_zero_one_points
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ)) :
    binary_prefix_points_on_subset hp P (Finset.univ : Finset (Fin p)) = zero_one_points hp P := by
  ext x
  simp [binary_prefix_points_on_subset, zero_one_points, prefix_binary_points]

/-- For the full prefix index set `Fin p`, the subset-based binary-point owner agrees with the
underlying `prefix_binary_points` owner from Theorem 5.22. -/
theorem binary_prefix_points_on_subset_univ_eq_prefix_binary_points
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ)) :
    binary_prefix_points_on_subset hp P (Finset.univ : Finset (Fin p)) =
      prefix_binary_points hp P (Nat.le_refl p) := by
  simpa [zero_one_points] using binary_prefix_points_on_subset_univ_eq_zero_one_points hp P

/-- The `k`th lift-and-project closure is obtained by iterating the one-step closure operator
along the first `p` coordinates. -/
def kth_lift_project_closure
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (k : ℕ) : Set (Fin n → ℝ) :=
  Nat.iterate (prefix_lift_project_closure hp) k P

/-- The zeroth lift-and-project closure is the original set `P`. -/
theorem kth_lift_project_closure_zero
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ)) :
    kth_lift_project_closure hp P 0 = P :=
  rfl

/-- The successor lift-and-project closure is the one-step closure of the previous iterate. -/
theorem kth_lift_project_closure_succ
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (k : ℕ) :
    kth_lift_project_closure hp P (k + 1) =
      prefix_lift_project_closure hp (kth_lift_project_closure hp P k) := by
  simpa [kth_lift_project_closure] using
    Function.iterate_succ_apply' (prefix_lift_project_closure hp) k P

/-- Helper for Exercise 5.25: enlarging the binary index set only shrinks the admissible-point
family. -/
private lemma binaryPrefixPointsOnSubset_mono
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {K L : Finset (Fin p)}
    (hKL : K ⊆ L) :
    binary_prefix_points_on_subset hp P L ⊆
      binary_prefix_points_on_subset hp P K := by
  intro x hx
  rcases hx with ⟨hxP, hxBinary⟩
  -- Restrict the binary conditions from the larger index set `L` back to `K`.
  refine ⟨hxP, ?_⟩
  intro j hjK
  exact hxBinary j (hKL hjK)

/-- Helper for Exercise 5.25: `coordinate_lift_project_hull` is monotone in its set argument. -/
private lemma coordinateLiftProjectHull_mono
    {A B : Set (Fin n → ℝ)}
    (hAB : A ⊆ B)
    (j : Fin n) :
    coordinate_lift_project_hull A j ⊆ coordinate_lift_project_hull B j := by
  -- Push the subset relation through the defining convex hull.
  rw [coordinate_lift_project_hull_def, coordinate_lift_project_hull_def]
  exact convexHull_mono <| by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl ⟨hAB hx.1, hx.2⟩
    · exact Or.inr ⟨hAB hx.1, hx.2⟩

/-- Helper for Exercise 5.25: enlarging the binary index set makes the corresponding convex hull
smaller. -/
private lemma binaryPrefixHull_mono
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {K L : Finset (Fin p)}
    (hKL : K ⊆ L) :
    convexHull ℝ (binary_prefix_points_on_subset hp P L) ⊆
      convexHull ℝ (binary_prefix_points_on_subset hp P K) := by
  -- First shrink the generating family, then use monotonicity of `convexHull`.
  exact convexHull_mono <| binaryPrefixPointsOnSubset_mono hp P hKL

/-- Helper for Exercise 5.25: if every generator in `A` already has coordinate `j` in `[0,1]`,
then the `j`-coordinate lift-project hull of `convexHull ℝ A` is generated exactly by the
`j = 0` and `j = 1` slices of `A`. -/
private lemma coordinateLiftProjectHull_convexHull_eq_ofCoordinateBounds
    (A : Set (Fin n → ℝ))
    (j : Fin n)
    (hA_bounds : ∀ x ∈ A, 0 ≤ x j ∧ x j ≤ 1) :
    coordinate_lift_project_hull (convexHull ℝ A) j =
      convexHull ℝ
        ((A ∩ {x : Fin n → ℝ | x j = 0}) ∪
          (A ∩ {x : Fin n → ℝ | x j = 1})) := by
  let πj : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) j
  have hpreimageZero :
      (-πj) ⁻¹' ({0} : Set ℝ) = {x : Fin n → ℝ | x j = 0} := by
    ext x
    simp [πj]
  have hpreimageOne :
      πj ⁻¹' ({1} : Set ℝ) = {x : Fin n → ℝ | x j = 1} := by
    ext x
    simp [πj]
  -- Route correction: normalize the two hyperplane slices of `convexHull ℝ A` first, then
  -- collapse the resulting nested convex hulls.
  have hsliceZero :
      convexHull ℝ A ∩ {x : Fin n → ℝ | x j = 0} =
        convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 0}) := by
    have hA_nonpos : A ⊆ (-πj) ⁻¹' Set.Iic (0 : ℝ) := by
      intro x hx
      have hxj_nonneg := (hA_bounds x hx).1
      simpa [πj, LinearMap.proj_apply] using neg_nonpos.mpr hxj_nonneg
    calc
      convexHull ℝ A ∩ {x : Fin n → ℝ | x j = 0}
          = convexHull ℝ A ∩ (-πj) ⁻¹' ({0} : Set ℝ) := by
              rw [hpreimageZero]
      _ = convexHull ℝ (A ∩ (-πj) ⁻¹' ({0} : Set ℝ)) :=
            convexHull_inter_hyperplane_eq A (-πj) (0 : ℝ) hA_nonpos
      _ = convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 0}) := by
            rw [hpreimageZero]
  have hsliceOne :
      convexHull ℝ A ∩ {x : Fin n → ℝ | x j = 1} =
        convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 1}) := by
    have hA_le_one : A ⊆ πj ⁻¹' Set.Iic (1 : ℝ) := by
      intro x hx
      exact (hA_bounds x hx).2
    calc
      convexHull ℝ A ∩ {x : Fin n → ℝ | x j = 1}
          = convexHull ℝ A ∩ πj ⁻¹' ({1} : Set ℝ) := by
              rw [hpreimageOne]
      _ = convexHull ℝ (A ∩ πj ⁻¹' ({1} : Set ℝ)) :=
            convexHull_inter_hyperplane_eq A πj (1 : ℝ) hA_le_one
      _ = convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 1}) := by
            rw [hpreimageOne]
  calc
    coordinate_lift_project_hull (convexHull ℝ A) j
        = convexHull ℝ
            (((convexHull ℝ A) ∩ {x : Fin n → ℝ | x j = 0}) ∪
              ((convexHull ℝ A) ∩ {x : Fin n → ℝ | x j = 1})) := by
            rw [coordinate_lift_project_hull_def]
    _ = convexHull ℝ
          (convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 0}) ∪
            ((convexHull ℝ A) ∩ {x : Fin n → ℝ | x j = 1})) := by
          rw [hsliceZero]
    _ = convexHull ℝ
          (convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 0}) ∪
            convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 1})) := by
          rw [hsliceOne]
    _ = convexHull ℝ
          ((A ∩ {x : Fin n → ℝ | x j = 0}) ∪
            convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 1})) := by
          rw [convexHull_convexHull_union_left]
    _ = convexHull ℝ
          ((A ∩ {x : Fin n → ℝ | x j = 0}) ∪
            (A ∩ {x : Fin n → ℝ | x j = 1})) := by
          rw [convexHull_convexHull_union_right]

/-- Helper for Exercise 5.25: if `i ∈ L`, then the hull generated by points that are already
binary on `L` is fixed by the `i`-coordinate lift-project operator. -/
private lemma binaryPrefixHull_fixedByCoordinateHull
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {L : Finset (Fin p)}
    {i : Fin p}
    (hi : i ∈ L) :
    coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P L))
        (Fin.castLE hp i) =
      convexHull ℝ (binary_prefix_points_on_subset hp P L) := by
  -- Route correction: use the owner-level slice characterization instead of reproving the fixed
  -- point statement directly from the convex-hull definition.
  calc
    coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P L))
        (Fin.castLE hp i)
        = convexHull ℝ
            (((binary_prefix_points_on_subset hp P L) ∩
                {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) ∪
              ((binary_prefix_points_on_subset hp P L) ∩
                {x : Fin n → ℝ | x (Fin.castLE hp i) = 1})) := by
            refine coordinateLiftProjectHull_convexHull_eq_ofCoordinateBounds
              (binary_prefix_points_on_subset hp P L) (Fin.castLE hp i) ?_
            intro x hx
            have hxi :
                x (Fin.castLE hp i) = 0 ∨ x (Fin.castLE hp i) = 1 := by
              exact (mem_binary_prefix_points_on_subset_iff hp P L x).mp hx |>.2 i hi
            rcases hxi with hxi | hxi <;> constructor <;> linarith
    _ = convexHull ℝ (binary_prefix_points_on_subset hp P L) := by
          refine congrArg (convexHull ℝ) ?_
          ext x
          constructor
          · intro hx
            rcases hx with ⟨hxL, hxi⟩ | ⟨hxL, hxi⟩
            · exact hxL
            · exact hxL
          · intro hxL
            have hxi :
                x (Fin.castLE hp i) = 0 ∨ x (Fin.castLE hp i) = 1 := by
              exact (mem_binary_prefix_points_on_subset_iff hp P L x).mp hxL |>.2 i hi
            rcases hxi with hxi | hxi
            · exact Or.inl ⟨hxL, hxi⟩
            · exact Or.inr ⟨hxL, hxi⟩

/-- Helper for Exercise 5.25: every point in a coordinate lift-project hull has the split
coordinate in the interval `[0, 1]`. -/
private lemma coordinateLiftProjectHull_subset_coordinateStrip
    (A : Set (Fin n → ℝ))
    (j : Fin n) :
    coordinate_lift_project_hull A j ⊆
      {x : Fin n → ℝ | 0 ≤ x j ∧ x j ≤ 1} := by
  rw [coordinate_lift_project_hull_def]
  refine convexHull_min ?_ ?_
  · intro x hx
    rcases hx with hx | hx
    · constructor <;> linarith [hx.2.symm]
    · constructor <;> linarith [hx.2.symm]
  · -- The strip `0 ≤ x j ≤ 1` is convex because it is an intersection of two affine halfspaces.
    let πj : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) j
    have hLower : Convex ℝ (πj ⁻¹' Set.Ici (0 : ℝ)) :=
      (convex_Ici (0 : ℝ)).linear_preimage πj
    have hUpper : Convex ℝ (πj ⁻¹' Set.Iic (1 : ℝ)) :=
      (convex_Iic (1 : ℝ)).linear_preimage πj
    simpa [πj, LinearMap.proj_apply, Set.preimage, Set.setOf_and] using hLower.inter hUpper

/-- Helper for Exercise 5.25: if `i ∈ L`, then every point of the corresponding binary-prefix
hull has `i`th coordinate in `[0, 1]`. -/
private lemma binaryPrefixHull_coordinateBounds
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {L : Finset (Fin p)}
    {i : Fin p}
    (hi : i ∈ L) :
    convexHull ℝ (binary_prefix_points_on_subset hp P L) ⊆
      {x : Fin n → ℝ | 0 ≤ x (Fin.castLE hp i) ∧ x (Fin.castLE hp i) ≤ 1} := by
  intro x hx
  -- Rewrite through the fixed-point characterization so the generic strip lemma applies.
  have hxHull :
      x ∈ coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P L))
        (Fin.castLE hp i) := by
    simpa [binaryPrefixHull_fixedByCoordinateHull hp P hi] using hx
  exact coordinateLiftProjectHull_subset_coordinateStrip _ _ hxHull

/-- Helper for Exercise 5.25: there is exactly one `0`-subset, namely `∅`, so the right-hand
side at `k = 0` is just `P`. -/
private lemma iInter_convexHull_binary_on_zero_subsets
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P) :
    (⋂ J : {J : Finset (Fin p) // J.card = 0},
      convexHull ℝ (binary_prefix_points_on_subset hp P J.1)) = P := by
  have hP_convex : Convex ℝ P := convex_of_is_polyhedron hP_polyhedron
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iInter] at hx
    have hxEmpty :
        x ∈ convexHull ℝ (binary_prefix_points_on_subset hp P (∅ : Finset (Fin p))) := by
      simpa using hx ⟨∅, by simp⟩
    have hEmpty :
        binary_prefix_points_on_subset hp P (∅ : Finset (Fin p)) = P := by
      ext y
      simp [binary_prefix_points_on_subset]
    rw [hEmpty] at hxEmpty
    exact (Convex.convexHull_eq hP_convex) ▸ hxEmpty
  · intro hx
    simp only [Set.mem_iInter]
    rintro ⟨J, hJcard⟩
    -- Every `0`-subset is definitionally `∅`, so each factor is `convexHull ℝ P = P`.
    have hJ : J = ∅ := Finset.card_eq_zero.mp hJcard
    subst J
    simpa [binary_prefix_points_on_subset] using
      show x ∈ convexHull ℝ P from (Convex.convexHull_eq hP_convex).symm ▸ hx

/-- Helper for Exercise 5.25: every `k`-subset extends to a `(k + 1)`-subset whenever
`k + 1 ≤ p`. -/
private lemma existsSuperset_card_succ
    {k : ℕ}
    (K : Finset (Fin p))
    (hK : K.card = k)
    (hk : k + 1 ≤ p) :
    ∃ L : Finset (Fin p), K ⊆ L ∧ L.card = k + 1 := by
  classical
  have hKlt : K.card < (Finset.univ : Finset (Fin p)).card := by
    simpa [hK, Fintype.card_fin] using hk
  obtain ⟨i, -, hiK⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card
      (s := K) (t := (Finset.univ : Finset (Fin p))) hKlt
  refine ⟨insert i K, ?_, ?_⟩
  · intro j hjK
    exact Finset.mem_insert_of_mem hjK
  · simp [hK, hiK]

/-- Helper for Exercise 5.25: a `k`-subset extends to a `(k + 1)`-subset containing a prescribed
index `i` whenever `k + 1 ≤ p`. -/
private lemma existsSuperset_card_succ_mem
    {k : ℕ}
    (i : Fin p)
    (K : Finset (Fin p))
    (hK : K.card = k)
    (hk : k + 1 ≤ p) :
    ∃ L : Finset (Fin p), K ⊆ L ∧ i ∈ L ∧ L.card = k + 1 := by
  classical
  by_cases hiK : i ∈ K
  · obtain ⟨L, hKL, hLcard⟩ := existsSuperset_card_succ K hK hk
    exact ⟨L, hKL, hKL hiK, hLcard⟩
  · refine ⟨insert i K, ?_, by simp, ?_⟩
    · intro j hjK
      exact Finset.mem_insert_of_mem hjK
    · simp [hK, hiK]

/-- Helper for Exercise 5.25: the intersection family on the right-hand side descends with `k`.
-/
private lemma iInter_convexHull_binary_on_succ_subsets_subset
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (hk : k + 1 ≤ p) :
    (⋂ J : {J : Finset (Fin p) // J.card = k + 1},
      convexHull ℝ (binary_prefix_points_on_subset hp P J.1)) ⊆
    ⋂ J : {J : Finset (Fin p) // J.card = k},
      convexHull ℝ (binary_prefix_points_on_subset hp P J.1) := by
  intro x hx
  simp only [Set.mem_iInter] at hx ⊢
  intro J
  obtain ⟨L, hJL, hLcard⟩ := existsSuperset_card_succ J.1 J.2 hk
  -- Compare the `(k + 1)`-subset factor indexed by `L` with the `k`-subset factor indexed by `J`.
  exact (binaryPrefixHull_mono hp P hJL) (hx ⟨L, hLcard⟩)

/-- Helper for Exercise 5.25: the binary-point family on a singleton index set is exactly the
union of the corresponding `0`- and `1`-coordinate slices of `P`. -/
private lemma binaryPrefixPointsOnSingleton_eq_coordinateSlices
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (i : Fin p) :
    binary_prefix_points_on_subset hp P ({i} : Finset (Fin p)) =
      ((P ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) ∪
        (P ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1})) := by
  ext x
  constructor
  · intro hx
    rcases (mem_binary_prefix_points_on_subset_iff hp P {i} x).mp hx with ⟨hxP, hxBinary⟩
    have hxi : x (Fin.castLE hp i) = 0 ∨ x (Fin.castLE hp i) = 1 := by
      exact hxBinary i (by simp)
    rcases hxi with hxi | hxi
    · exact Or.inl ⟨hxP, hxi⟩
    · exact Or.inr ⟨hxP, hxi⟩
  · intro hx
    refine (mem_binary_prefix_points_on_subset_iff hp P {i} x).2 ?_
    rcases hx with ⟨hxP, hxi⟩ | ⟨hxP, hxi⟩
    · refine ⟨hxP, ?_⟩
      intro j hj
      have hj' : j = i := by simpa using hj
      subst j
      exact Or.inl hxi
    · refine ⟨hxP, ?_⟩
      intro j hj
      have hj' : j = i := by simpa using hj
      subst j
      exact Or.inr hxi

/-- Helper for Exercise 5.25: adding one binary coordinate splits the point family into its
`0`- and `1`-slices along that coordinate. -/
private lemma binaryPrefixPointsOnSubset_insert_eq_union_coordinateSlices
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (i : Fin p)
    (K : Finset (Fin p))
    (_hiK : i ∉ K) :
    binary_prefix_points_on_subset hp P (insert i K) =
      ((binary_prefix_points_on_subset hp P K) ∩
          {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) ∪
        ((binary_prefix_points_on_subset hp P K) ∩
          {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
  ext x
  constructor
  · intro hx
    rcases (mem_binary_prefix_points_on_subset_iff hp P (insert i K) x).mp hx with
      ⟨hxP, hxBinary⟩
    have hxK : x ∈ binary_prefix_points_on_subset hp P K := by
      -- Forget the new coordinate and keep the old binary conditions on `K`.
      refine (mem_binary_prefix_points_on_subset_iff hp P K x).2 ?_
      refine ⟨hxP, ?_⟩
      intro j hjK
      exact hxBinary j (Finset.mem_insert_of_mem hjK)
    have hxi : x (Fin.castLE hp i) = 0 ∨ x (Fin.castLE hp i) = 1 := by
      exact hxBinary i (by simp)
    rcases hxi with hxi | hxi
    · exact Or.inl ⟨hxK, hxi⟩
    · exact Or.inr ⟨hxK, hxi⟩
  · intro hx
    rcases hx with ⟨hxK, hxi0⟩ | ⟨hxK, hxi1⟩
    · rcases (mem_binary_prefix_points_on_subset_iff hp P K x).mp hxK with ⟨hxP, hxBinaryK⟩
      -- Reassemble the binary conditions on `insert i K` using the `x_i = 0` branch.
      refine (mem_binary_prefix_points_on_subset_iff hp P (insert i K) x).2 ?_
      refine ⟨hxP, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjK
      · exact Or.inl (by simpa using hxi0)
      · exact hxBinaryK j hjK
    · rcases (mem_binary_prefix_points_on_subset_iff hp P K x).mp hxK with ⟨hxP, hxBinaryK⟩
      -- The `x_i = 1` branch is identical except for the final binary witness at `i`.
      refine (mem_binary_prefix_points_on_subset_iff hp P (insert i K) x).2 ?_
      refine ⟨hxP, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjK
      · exact Or.inr (by simpa using hxi1)
      · exact hxBinaryK j hjK

/-- Helper for Exercise 5.25: on the `x_i = 0` hyperplane, adding `i` to the binary index set is
redundant already at the point-family level. -/
private lemma binaryPrefixPointsOnSubset_insert_inter_coordinateZero_eq
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (i : Fin p)
    (K : Finset (Fin p))
    (_hiK : i ∉ K) :
    binary_prefix_points_on_subset hp P (insert i K) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} =
      binary_prefix_points_on_subset hp P K ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} := by
  ext x
  constructor
  · rintro ⟨hxInsert, hxi⟩
    rcases (mem_binary_prefix_points_on_subset_iff hp P (insert i K) x).mp hxInsert with
      ⟨hxP, hxBinary⟩
    refine ⟨(mem_binary_prefix_points_on_subset_iff hp P K x).2 ?_, hxi⟩
    refine ⟨hxP, ?_⟩
    intro j hjK
    exact hxBinary j (Finset.mem_insert_of_mem hjK)
  · rintro ⟨hxK, hxi⟩
    rcases (mem_binary_prefix_points_on_subset_iff hp P K x).mp hxK with ⟨hxP, hxBinaryK⟩
    refine ⟨(mem_binary_prefix_points_on_subset_iff hp P (insert i K) x).2 ?_, hxi⟩
    refine ⟨hxP, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjK
    · exact Or.inl (by simpa using hxi)
    · exact hxBinaryK j hjK

/-- Helper for Exercise 5.25: on the `x_i = 1` hyperplane, adding `i` to the binary index set is
redundant already at the point-family level. -/
private lemma binaryPrefixPointsOnSubset_insert_inter_coordinateOne_eq
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (i : Fin p)
    (K : Finset (Fin p))
    (_hiK : i ∉ K) :
    binary_prefix_points_on_subset hp P (insert i K) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} =
      binary_prefix_points_on_subset hp P K ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} := by
  ext x
  constructor
  · rintro ⟨hxInsert, hxi⟩
    rcases (mem_binary_prefix_points_on_subset_iff hp P (insert i K) x).mp hxInsert with
      ⟨hxP, hxBinary⟩
    refine ⟨(mem_binary_prefix_points_on_subset_iff hp P K x).2 ?_, hxi⟩
    refine ⟨hxP, ?_⟩
    intro j hjK
    exact hxBinary j (Finset.mem_insert_of_mem hjK)
  · rintro ⟨hxK, hxi⟩
    rcases (mem_binary_prefix_points_on_subset_iff hp P K x).mp hxK with ⟨hxP, hxBinaryK⟩
    refine ⟨(mem_binary_prefix_points_on_subset_iff hp P (insert i K) x).2 ?_, hxi⟩
    refine ⟨hxP, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjK
    · exact Or.inr (by simpa using hxi)
    · exact hxBinaryK j hjK

/-- Helper for Exercise 5.25: intersecting the `(k + 1)`-subset hulls that contain a fixed
coordinate `i` is contained in the global `k`-subset intersection. -/
private lemma restrictedBinaryPrefixHull_subset_predecessorFamily
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (hk : k + 1 ≤ p)
    (i : Fin p) :
    (⋂ L : {L : Finset (Fin p) // L.card = k + 1 ∧ i ∈ L},
      convexHull ℝ (binary_prefix_points_on_subset hp P L.1)) ⊆
    ⋂ J : {J : Finset (Fin p) // J.card = k},
      convexHull ℝ (binary_prefix_points_on_subset hp P J.1) := by
  intro x hx
  simp only [Set.mem_iInter] at hx ⊢
  intro J
  obtain ⟨L, hJL, hiL, hLcard⟩ := existsSuperset_card_succ_mem i J.1 J.2 hk
  -- Extend the target `k`-subset to a `(k + 1)`-subset containing `i`, then use monotonicity.
  exact (binaryPrefixHull_mono hp P hJL) (hx ⟨L, by exact ⟨hLcard, hiL⟩⟩)

/-- Helper for Exercise 5.25: slicing an `L`-binary hull on the hyperplane `x_i = 0` keeps
exactly the generators that already satisfy `x_i = 0`. -/
private lemma binaryPrefixHull_inter_coordinateZero
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {L : Finset (Fin p)}
    {i : Fin p}
    (hi : i ∈ L) :
    convexHull ℝ (binary_prefix_points_on_subset hp P L) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} =
      convexHull ℝ
        (binary_prefix_points_on_subset hp P L ∩
          {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) := by
  let πi : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (Fin.castLE hp i)
  have hpreimageZero :
      (-πi) ⁻¹' ({0} : Set ℝ) = {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} := by
    ext x
    simp [πi]
  have hA_nonpos :
      binary_prefix_points_on_subset hp P L ⊆ (-πi) ⁻¹' Set.Iic (0 : ℝ) := by
    intro x hx
    have hxi :
        x (Fin.castLE hp i) = 0 ∨ x (Fin.castLE hp i) = 1 :=
      (mem_binary_prefix_points_on_subset_iff hp P L x).mp hx |>.2 i hi
    have hxi_nonneg : 0 ≤ x (Fin.castLE hp i) := by
      rcases hxi with hxi | hxi <;> linarith
    simpa [πi, LinearMap.proj_apply] using neg_nonpos.mpr hxi_nonneg
  -- Route correction: use the boundary-slice theorem at the owner level instead of unfolding
  -- the whole predecessor-family intersection.
  calc
    convexHull ℝ (binary_prefix_points_on_subset hp P L) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}
        = convexHull ℝ (binary_prefix_points_on_subset hp P L) ∩ (-πi) ⁻¹' ({0} : Set ℝ) := by
            rw [hpreimageZero]
    _ = convexHull ℝ
          (binary_prefix_points_on_subset hp P L ∩ (-πi) ⁻¹' ({0} : Set ℝ)) :=
          convexHull_inter_hyperplane_eq
            (binary_prefix_points_on_subset hp P L) (-πi) (0 : ℝ) hA_nonpos
    _ = convexHull ℝ
          (binary_prefix_points_on_subset hp P L ∩
            {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) := by
          rw [hpreimageZero]

/-- Helper for Exercise 5.25: slicing an `L`-binary hull on the hyperplane `x_i = 1` keeps
exactly the generators that already satisfy `x_i = 1`. -/
private lemma binaryPrefixHull_inter_coordinateOne
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {L : Finset (Fin p)}
    {i : Fin p}
    (hi : i ∈ L) :
    convexHull ℝ (binary_prefix_points_on_subset hp P L) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} =
      convexHull ℝ
        (binary_prefix_points_on_subset hp P L ∩
          {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
  let πi : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (Fin.castLE hp i)
  have hpreimageOne :
      πi ⁻¹' ({1} : Set ℝ) = {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} := by
    ext x
    simp [πi]
  have hA_le_one :
      binary_prefix_points_on_subset hp P L ⊆ πi ⁻¹' Set.Iic (1 : ℝ) := by
    intro x hx
    have hxi :
        x (Fin.castLE hp i) = 0 ∨ x (Fin.castLE hp i) = 1 :=
      (mem_binary_prefix_points_on_subset_iff hp P L x).mp hx |>.2 i hi
    rcases hxi with hxi | hxi <;> simpa [πi, LinearMap.proj_apply, hxi]
  -- The upper boundary slice is handled by the same owner theorem at level `1`.
  calc
    convexHull ℝ (binary_prefix_points_on_subset hp P L) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}
        = convexHull ℝ (binary_prefix_points_on_subset hp P L) ∩ πi ⁻¹' ({1} : Set ℝ) := by
            rw [hpreimageOne]
    _ = convexHull ℝ
          (binary_prefix_points_on_subset hp P L ∩ πi ⁻¹' ({1} : Set ℝ)) :=
          convexHull_inter_hyperplane_eq
            (binary_prefix_points_on_subset hp P L) πi (1 : ℝ) hA_le_one
    _ = convexHull ℝ
          (binary_prefix_points_on_subset hp P L ∩
            {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
          rw [hpreimageOne]

/-- Helper for Exercise 5.25: the full `(k + 1)`-subset intersection is contained in each
coordinate-restricted `(k + 1)`-subset family. -/
private lemma succBinaryPrefixHull_subset_restrictedFamily
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (i : Fin p) :
    (⋂ L : {L : Finset (Fin p) // L.card = k + 1},
      convexHull ℝ (binary_prefix_points_on_subset hp P L.1)) ⊆
    ⋂ L : {L : Finset (Fin p) // L.card = k + 1 ∧ i ∈ L},
      convexHull ℝ (binary_prefix_points_on_subset hp P L.1) := by
  intro x hx
  simp only [Set.mem_iInter] at hx ⊢
  intro L
  exact hx ⟨L.1, L.2.1⟩

/-- Helper for Exercise 5.25: the predecessor-family coordinate hulls on a fixed `(k + 1)`-subset
recover the hull that is binary on the whole subset. -/
private lemma binaryPrefixHull_subset_predecessorFamilyIntersection
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (L : Finset (Fin p))
    (_hL : L.card = k + 1) :
    convexHull ℝ (binary_prefix_points_on_subset hp P L) ⊆
      (⋂ j : {j : Fin p // j ∈ L},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase j.1)))
          (Fin.castLE hp j.1)) := by
  intro x hx
  -- Each predecessor factor already contains the full `L`-binary hull by monotonicity.
  simp only [Set.mem_iInter]
  intro j
  have hHullMono :
      convexHull ℝ (binary_prefix_points_on_subset hp P L) ⊆
        convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase j.1)) :=
    binaryPrefixHull_mono hp P (Finset.erase_subset j.1 L)
  have hxFixed :
      x ∈ coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P L))
        (Fin.castLE hp j.1) := by
    -- The `j`th coordinate is already binary on the full `L`-family.
    simpa [binaryPrefixHull_fixedByCoordinateHull hp P j.2] using hx
  exact coordinateLiftProjectHull_mono hHullMono (Fin.castLE hp j.1) hxFixed

/-- Helper for Exercise 5.25: the restricted `(k + 1)`-subset family is stable under taking the
contracting direction of the `i`-coordinate lift-project hull. -/
private lemma coordinateHull_restrictedBinaryPrefixHull_subset
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (i : Fin p) :
    coordinate_lift_project_hull
        (⋂ L : {L : Finset (Fin p) // L.card = k + 1 ∧ i ∈ L},
          convexHull ℝ (binary_prefix_points_on_subset hp P L.1))
        (Fin.castLE hp i) ⊆
      ⋂ L : {L : Finset (Fin p) // L.card = k + 1 ∧ i ∈ L},
        convexHull ℝ (binary_prefix_points_on_subset hp P L.1) := by
  intro x hx
  -- Compare the restricted family with each factor and use factorwise coordinate stability.
  simp only [Set.mem_iInter]
  intro L
  have hFamilySubset :
      (⋂ M : {M : Finset (Fin p) // M.card = k + 1 ∧ i ∈ M},
        convexHull ℝ (binary_prefix_points_on_subset hp P M.1)) ⊆
      convexHull ℝ (binary_prefix_points_on_subset hp P L.1) := by
    intro y hy
    have hyAll :
        ∀ M : {M : Finset (Fin p) // M.card = k + 1 ∧ i ∈ M},
          y ∈ convexHull ℝ (binary_prefix_points_on_subset hp P M.1) := by
      simpa only [Set.mem_iInter] using hy
    exact hyAll L
  have hxFactor :
      x ∈ coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P L.1))
        (Fin.castLE hp i) :=
    coordinateLiftProjectHull_mono hFamilySubset (Fin.castLE hp i) hx
  simpa [binaryPrefixHull_fixedByCoordinateHull hp P L.2.2] using hxFactor

/-- Helper for Exercise 5.25: after adding `i` to the binary index set, the `0`-slice of the
resulting convex hull is the same slice already seen before adding `i`. -/
private lemma binaryPrefixHull_insert_inter_coordinateZero
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (i : Fin p)
    (K : Finset (Fin p))
    (hiK : i ∉ K) :
    convexHull ℝ (binary_prefix_points_on_subset hp P (insert i K)) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} =
      convexHull ℝ
        (binary_prefix_points_on_subset hp P K ∩
          {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) := by
  -- First identify the `0`-slice through the owner boundary-slice lemma, then rewrite the
  -- underlying point family using the insert normalization.
  calc
    convexHull ℝ (binary_prefix_points_on_subset hp P (insert i K)) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}
        = convexHull ℝ
            (binary_prefix_points_on_subset hp P (insert i K) ∩
              {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) := by
            simpa using
              (binaryPrefixHull_inter_coordinateZero hp P
                (L := insert i K) (i := i) (by simp))
    _ = convexHull ℝ
          (binary_prefix_points_on_subset hp P K ∩
            {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) := by
          rw [binaryPrefixPointsOnSubset_insert_inter_coordinateZero_eq hp P i K hiK]

/-- Helper for Exercise 5.25: after adding `i` to the binary index set, the `1`-slice of the
resulting convex hull is the same slice already seen before adding `i`. -/
private lemma binaryPrefixHull_insert_inter_coordinateOne
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (i : Fin p)
    (K : Finset (Fin p))
    (hiK : i ∉ K) :
    convexHull ℝ (binary_prefix_points_on_subset hp P (insert i K)) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} =
      convexHull ℝ
        (binary_prefix_points_on_subset hp P K ∩
          {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
  -- The `1`-slice follows from the same owner-level slice theorem and point-family rewrite.
  calc
    convexHull ℝ (binary_prefix_points_on_subset hp P (insert i K)) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}
        = convexHull ℝ
            (binary_prefix_points_on_subset hp P (insert i K) ∩
              {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
            simpa using
              (binaryPrefixHull_inter_coordinateOne hp P
                (L := insert i K) (i := i) (by simp))
    _ = convexHull ℝ
          (binary_prefix_points_on_subset hp P K ∩
            {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
          rw [binaryPrefixPointsOnSubset_insert_inter_coordinateOne_eq hp P i K hiK]

/-- Helper for Exercise 5.25: adding `i` to the binary index set gives a hull that already lies in
the `i`-coordinate lift-project hull of the old binary-prefix hull. -/
private lemma binaryPrefixHull_insert_subset_coordinateLiftProjectHull
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (i : Fin p)
    (K : Finset (Fin p))
    (hiK : i ∉ K) :
    convexHull ℝ (binary_prefix_points_on_subset hp P (insert i K)) ⊆
      coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P K))
        (Fin.castLE hp i) := by
  -- Route correction: this is the honest one-step inclusion available from the insert-slice
  -- description of the generators; equality would require an additional boundary theorem that
  -- is not present here.
  rw [binaryPrefixPointsOnSubset_insert_eq_union_coordinateSlices hp P i K hiK]
  rw [coordinate_lift_project_hull_def]
  refine convexHull_mono ?_
  intro x hx
  rcases hx with ⟨hxK, hxi0⟩ | ⟨hxK, hxi1⟩
  · exact Or.inl ⟨subset_convexHull ℝ _ hxK, by simpa using hxi0⟩
  · exact Or.inr ⟨subset_convexHull ℝ _ hxK, by simpa using hxi1⟩

/-- Helper for Exercise 5.25: the predecessor-family coordinate hulls on a fixed `(k + 1)`-subset
recover the hull that is binary on the whole subset. -/
private lemma binaryPrefixHull_predecessorFamilyStep
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (L : Finset (Fin p))
    (hL : L.card = k + 1) :
    (⋂ j : {j : Fin p // j ∈ L},
      coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase j.1)))
        (Fin.castLE hp j.1)) =
    convexHull ℝ (binary_prefix_points_on_subset hp P L) := by
  refine Set.Subset.antisymm ?_ ?_
  · -- TODO: close the reverse inclusion by splitting the `j = i` and `j ≠ i` roles. The base
    -- predecessor factor supplies the two `x_i = 0/1` branch sets, and a non-base predecessor
    -- factor must certify each branch already lies in `convexHull ℝ (binary_prefix_points_on_subset hp P L)`.
    sorry
  · -- The easy direction is factorwise monotonicity from the full `L`-binary hull.
    exact binaryPrefixHull_subset_predecessorFamilyIntersection hp P (k := k) L hL

/-- Helper for Exercise 5.25: if the two boundary slices of `A` along coordinate `i` already lie
in a convex target `B`, then the whole `i`-coordinate lift-project hull of `A` lies in `B`. -/
private lemma coordinateLiftProjectHull_subset_ofBoundarySubsets
    {A B : Set (Fin n → ℝ)}
    (i : Fin n)
    (hZero : A ∩ {x : Fin n → ℝ | x i = 0} ⊆ B)
    (hOne : A ∩ {x : Fin n → ℝ | x i = 1} ⊆ B)
    (hB_convex : Convex ℝ B) :
    coordinate_lift_project_hull A i ⊆ B := by
  -- Unfold the coordinate hull once and send each boundary branch into the convex target.
  rw [coordinate_lift_project_hull_def]
  refine convexHull_min ?_ hB_convex
  intro x hx
  rcases hx with hx | hx
  · exact hZero hx
  · exact hOne hx

/-- Helper for Exercise 5.25: slicing a coordinate lift-project hull on its own `0`-boundary
recovers the convex hull of the original `0`-slice. -/
private lemma coordinateLiftProjectHull_inter_coordinateZero
    (A : Set (Fin n → ℝ))
    (i : Fin n) :
    coordinate_lift_project_hull A i ∩ {x : Fin n → ℝ | x i = 0} =
      convexHull ℝ (A ∩ {x : Fin n → ℝ | x i = 0}) := by
  let πi : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) i
  let U : Set (Fin n → ℝ) :=
    (A ∩ {x : Fin n → ℝ | x i = 0}) ∪ (A ∩ {x : Fin n → ℝ | x i = 1})
  have hpreimageZero :
      (-πi) ⁻¹' ({0} : Set ℝ) = {x : Fin n → ℝ | x i = 0} := by
    ext x
    simp [πi]
  have hU_nonpos : U ⊆ (-πi) ⁻¹' Set.Iic (0 : ℝ) := by
    intro x hx
    rcases hx with hx | hx
    · have hxi0 : x i = 0 := by simpa using hx.2
      have hxi_nonneg : 0 ≤ x i := by simpa [hxi0]
      simpa [πi, LinearMap.proj_apply] using neg_nonpos.mpr hxi_nonneg
    · have hxi1 : x i = 1 := by simpa using hx.2
      have hxi_nonneg : 0 ≤ x i := by simpa [hxi1]
      simpa [πi, LinearMap.proj_apply] using neg_nonpos.mpr hxi_nonneg
  -- Reduce the slice to a hyperplane section of the generating boundary union.
  calc
    coordinate_lift_project_hull A i ∩ {x : Fin n → ℝ | x i = 0}
        = convexHull ℝ U ∩ {x : Fin n → ℝ | x i = 0} := by
            rw [coordinate_lift_project_hull_def]
    _ = convexHull ℝ U ∩ (-πi) ⁻¹' ({0} : Set ℝ) := by
          rw [hpreimageZero]
    _ = convexHull ℝ (U ∩ (-πi) ⁻¹' ({0} : Set ℝ)) :=
          convexHull_inter_hyperplane_eq U (-πi) (0 : ℝ) hU_nonpos
    _ = convexHull ℝ (U ∩ {x : Fin n → ℝ | x i = 0}) := by
          rw [hpreimageZero]
    _ = convexHull ℝ (A ∩ {x : Fin n → ℝ | x i = 0}) := by
          refine congrArg (convexHull ℝ) ?_
          ext x
          constructor
          · rintro ⟨hxU, hxi0⟩
            rcases hxU with hx | hx
            · exact ⟨hx.1, hx.2⟩
            · exfalso
              have hx1 : x i = 1 := by simpa using hx.2
              have hx0 : x i = 0 := by simpa using hxi0
              have : (1 : ℝ) = 0 := by rw [← hx1, hx0]
              norm_num at this
          · intro hx
            exact ⟨Or.inl hx, hx.2⟩

/-- Helper for Exercise 5.25: slicing a coordinate lift-project hull on its own `1`-boundary
recovers the convex hull of the original `1`-slice. -/
private lemma coordinateLiftProjectHull_inter_coordinateOne
    (A : Set (Fin n → ℝ))
    (i : Fin n) :
    coordinate_lift_project_hull A i ∩ {x : Fin n → ℝ | x i = 1} =
      convexHull ℝ (A ∩ {x : Fin n → ℝ | x i = 1}) := by
  let πi : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) i
  let U : Set (Fin n → ℝ) :=
    (A ∩ {x : Fin n → ℝ | x i = 0}) ∪ (A ∩ {x : Fin n → ℝ | x i = 1})
  have hpreimageOne :
      πi ⁻¹' ({1} : Set ℝ) = {x : Fin n → ℝ | x i = 1} := by
    ext x
    simp [πi]
  have hU_le_one : U ⊆ πi ⁻¹' Set.Iic (1 : ℝ) := by
    intro x hx
    rcases hx with hx | hx
    · have hxi0 : x i = 0 := by simpa using hx.2
      have hxi_le_one : x i ≤ 1 := by simpa [hxi0]
      simpa [πi, LinearMap.proj_apply] using hxi_le_one
    · have hxi1 : x i = 1 := by simpa using hx.2
      have hxi_le_one : x i ≤ 1 := by simpa [hxi1]
      simpa [πi, LinearMap.proj_apply] using hxi_le_one
  -- The upper boundary slice is handled by the same hyperplane-section theorem at level `1`.
  calc
    coordinate_lift_project_hull A i ∩ {x : Fin n → ℝ | x i = 1}
        = convexHull ℝ U ∩ {x : Fin n → ℝ | x i = 1} := by
            rw [coordinate_lift_project_hull_def]
    _ = convexHull ℝ U ∩ πi ⁻¹' ({1} : Set ℝ) := by
          rw [hpreimageOne]
    _ = convexHull ℝ (U ∩ πi ⁻¹' ({1} : Set ℝ)) :=
          convexHull_inter_hyperplane_eq U πi (1 : ℝ) hU_le_one
    _ = convexHull ℝ (U ∩ {x : Fin n → ℝ | x i = 1}) := by
          rw [hpreimageOne]
    _ = convexHull ℝ (A ∩ {x : Fin n → ℝ | x i = 1}) := by
          refine congrArg (convexHull ℝ) ?_
          ext x
          constructor
          · rintro ⟨hxU, hxi1⟩
            rcases hxU with hx | hx
            · exfalso
              have hx0 : x i = 0 := by simpa using hx.2
              have hx1 : x i = 1 := by simpa using hxi1
              have : (0 : ℝ) = 1 := by rw [← hx0, hx1]
              norm_num at this
            · exact ⟨hx.1, hx.2⟩
          · intro hx
            exact ⟨Or.inr hx, hx.2⟩

/-- Helper for Exercise 5.25: the restricted `(k + 1)`-subset family lies in every
`i`-coordinate hull attached to a `k`-subset factor. -/
private lemma restrictedBinaryPrefixHull_subset_iInterCoordinateHulls
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (hk : k + 1 ≤ p)
    (i : Fin p) :
    (⋂ L : {L : Finset (Fin p) // L.card = k + 1 ∧ i ∈ L},
      convexHull ℝ (binary_prefix_points_on_subset hp P L.1)) ⊆
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i) := by
  intro x hx
  have hxRk :
      x ∈ ⋂ J : {J : Finset (Fin p) // J.card = k},
        convexHull ℝ (binary_prefix_points_on_subset hp P J.1) :=
    restrictedBinaryPrefixHull_subset_predecessorFamily hp P hk i hx
  -- Route correction: reduce the restricted family to factorwise `i`-coordinate hull membership
  -- before facing the remaining global commuting step.
  simp only [Set.mem_iInter] at hx hxRk ⊢
  intro J
  by_cases hiJ : i ∈ J.1
  · have hxJ :
        x ∈ convexHull ℝ (binary_prefix_points_on_subset hp P J.1) :=
      hxRk J
    simpa [binaryPrefixHull_fixedByCoordinateHull hp P (L := J.1) (i := i) hiJ] using hxJ
  · have hxInsert :
        x ∈ convexHull ℝ (binary_prefix_points_on_subset hp P (insert i J.1)) :=
      hx ⟨insert i J.1, by simp [J.2, hiJ]⟩
    exact binaryPrefixHull_insert_subset_coordinateLiftProjectHull hp P i J.1 hiJ hxInsert

/-- Helper for Exercise 5.25: for a fixed coordinate `i`, the restricted `(k + 1)`-subset family
already lies in the `i`-coordinate lift-project hull of the global `k`-subset family. -/
private lemma iInterKSubsetCoordinateHulls_coordinateSlices
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (i : Fin p) :
    let Rk :=
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        convexHull ℝ (binary_prefix_points_on_subset hp P J.1)
    let Tk :=
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i)
    (Tk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} ⊆
        Rk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) ∧
      (Tk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} ⊆
        Rk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
  dsimp
  constructor
  · intro x hx
    rcases hx with ⟨hxTk, hxi0⟩
    refine ⟨?_, hxi0⟩
    -- On the `x_i = 0` boundary, each factorwise coordinate hull collapses back to its source hull.
    simp only [Set.mem_iInter] at hxTk ⊢
    intro J
    have hxSlice :
        x ∈ coordinate_lift_project_hull
              (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
              (Fin.castLE hp i) ∩
            {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} := ⟨hxTk J, hxi0⟩
    have hxBoundary :
        x ∈ convexHull ℝ
              (convexHull ℝ (binary_prefix_points_on_subset hp P J.1) ∩
                {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) := by
      simpa [coordinateLiftProjectHull_inter_coordinateZero
        (convexHull ℝ (binary_prefix_points_on_subset hp P J.1)) (Fin.castLE hp i)] using hxSlice
    exact convexHull_min (by intro y hy; exact hy.1) (convex_convexHull ℝ _) hxBoundary
  · intro x hx
    rcases hx with ⟨hxTk, hxi1⟩
    refine ⟨?_, hxi1⟩
    -- The `x_i = 1` boundary reduces in the same way.
    simp only [Set.mem_iInter] at hxTk ⊢
    intro J
    have hxSlice :
        x ∈ coordinate_lift_project_hull
              (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
              (Fin.castLE hp i) ∩
            {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} := ⟨hxTk J, hxi1⟩
    have hxBoundary :
        x ∈ convexHull ℝ
              (convexHull ℝ (binary_prefix_points_on_subset hp P J.1) ∩
                {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
      simpa [coordinateLiftProjectHull_inter_coordinateOne
        (convexHull ℝ (binary_prefix_points_on_subset hp P J.1)) (Fin.castLE hp i)] using hxSlice
    exact convexHull_min (by intro y hy; exact hy.1) (convex_convexHull ℝ _) hxBoundary

/-- Helper for Exercise 5.25: the intersection of the factorwise `i`-coordinate hulls of the
`k`-subset family should land in the `i`-coordinate hull of the total `k`-subset intersection. -/
private lemma iInterKSubsetCoordinateHulls_subset_coordinateHullRk
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (i : Fin p) :
    (⋂ J : {J : Finset (Fin p) // J.card = k},
      coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
        (Fin.castLE hp i)) ⊆
      coordinate_lift_project_hull
        (⋂ J : {J : Finset (Fin p) // J.card = k},
          convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
        (Fin.castLE hp i) := by
  let Rk :=
    ⋂ J : {J : Finset (Fin p) // J.card = k},
      convexHull ℝ (binary_prefix_points_on_subset hp P J.1)
  let Tk :=
    ⋂ J : {J : Finset (Fin p) // J.card = k},
      coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
        (Fin.castLE hp i)
  intro x hx
  have hSlices := iInterKSubsetCoordinateHulls_coordinateSlices hp P (k := k) i
  have hZero :
      Tk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} ⊆
        Rk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} := by
    simpa [Rk, Tk] using hSlices.1
  have hOne :
      Tk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} ⊆
        Rk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} := by
    simpa [Rk, Tk] using hSlices.2
  -- TODO: the remaining blocker is the family-specific closing theorem turning the two boundary
  -- inclusions `hZero` and `hOne` into `Tk ⊆ coordinate_lift_project_hull Rk (Fin.castLE hp i)`.
  -- The intended route is to show this particular intersection family is generated by its
  -- `x_i = 0/1` slices, then apply `coordinateLiftProjectHull_subset_ofBoundarySubsets`.
  sorry

/-- Helper for Exercise 5.25: for a fixed coordinate `i`, the restricted `(k + 1)`-subset family
already lies in the `i`-coordinate lift-project hull of the global `k`-subset family. -/
private lemma restrictedBinaryPrefixHull_subset_coordinateHullPredecessor
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (hk : k + 1 ≤ p)
    (i : Fin p) :
    (⋂ L : {L : Finset (Fin p) // L.card = k + 1 ∧ i ∈ L},
      convexHull ℝ (binary_prefix_points_on_subset hp P L.1)) ⊆
      coordinate_lift_project_hull
        (⋂ J : {J : Finset (Fin p) // J.card = k},
          convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
        (Fin.castLE hp i) := by
  intro x hx
  -- Route correction: the theorem only needs this direct bridge into the ambient `i`-coordinate
  -- hull of `Rk`, not a full fixed-point equality for the restricted family itself.
  have hxFactorwise :
      x ∈ ⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i) :=
    restrictedBinaryPrefixHull_subset_iInterCoordinateHulls hp P hk i hx
  -- Reduce the goal to the family-specific closing lemma for the factorwise `i`-coordinate hulls.
  exact iInterKSubsetCoordinateHulls_subset_coordinateHullRk hp P (k := k) i hxFactorwise

/-- Exercise 5.25. Let `P ⊆ ℝ^n` be a polyhedron, and let
`S := P ∩ ({0, 1}^p × ℝ^(n - p))`. Then the `k`th lift-and-project closure of `P` along the
first `p` coordinates is the intersection, over all `k`-element subsets `J` of the binary index
set, of the convex hull of the points of `P` whose coordinates indexed by `J` are binary. -/
theorem kth_lift_project_closure_eq_iInter_convexHull_binary_on_k_subsets
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (k : ℕ)
    (hk : k ≤ p) :
    kth_lift_project_closure hp P k =
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        convexHull ℝ (binary_prefix_points_on_subset hp P J.1) := by
  induction k with
  | zero =>
      -- The zeroth iterate is `P`, and the right-hand side reduces to the unique `0`-subset.
      simpa [kth_lift_project_closure_zero] using
        (iInter_convexHull_binary_on_zero_subsets hp P hP_polyhedron).symm
  | succ k ih =>
      -- Route correction: the unsafe "choose `k + 1` coordinates and sequentialize them" route
      -- does not work here. The viable proof must compare the global `(k + 1)`-subset family with
      -- the one-step closure of the global `k`-subset family.
      by_cases hk0 : k = 0
      · subst hk0
        -- The first successor step is just the intersection of the singleton coordinate hulls.
        ext x
        rw [kth_lift_project_closure_succ, kth_lift_project_closure_zero,
          mem_prefix_lift_project_closure_iff]
        simp only [Set.mem_iInter]
        constructor
        · intro hx J
          rcases J with ⟨J, hJcard⟩
          obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hJcard
          simpa [binaryPrefixPointsOnSingleton_eq_coordinateSlices, coordinate_lift_project_hull_def]
            using hx i
        · intro hx i
          have hxSingleton : x ∈
              convexHull ℝ
                (binary_prefix_points_on_subset hp P ({i} : Finset (Fin p))) := by
            exact hx ⟨{i}, by simp⟩
          simpa [binaryPrefixPointsOnSingleton_eq_coordinateSlices, coordinate_lift_project_hull_def]
            using hxSingleton
      · set Rk : Set (Fin n → ℝ) :=
            ⋂ J : {J : Finset (Fin p) // J.card = k},
              convexHull ℝ (binary_prefix_points_on_subset hp P J.1)
        set Rk1 : Set (Fin n → ℝ) :=
            ⋂ J : {J : Finset (Fin p) // J.card = k + 1},
              convexHull ℝ (binary_prefix_points_on_subset hp P J.1)
        have ihRk : kth_lift_project_closure hp P k = Rk := by
          simpa [Rk] using ih (Nat.le_of_succ_le hk)
        -- Route correction: the remaining successor step splits into a forward predecessor-family
        -- assembly and a reverse restricted-family fixed-point argument.
        rw [kth_lift_project_closure_succ, ihRk]
        ext x
        constructor
        · intro hx
          rw [mem_prefix_lift_project_closure_iff] at hx
          simp only [Rk1, Set.mem_iInter]
          intro L
          have hxPredecessors :
              x ∈ ⋂ j : {j : Fin p // j ∈ L.1},
                coordinate_lift_project_hull
                  (convexHull ℝ (binary_prefix_points_on_subset hp P (L.1.erase j.1)))
                  (Fin.castLE hp j.1) := by
            simp only [Set.mem_iInter]
            intro j
            have hEraseCard : (L.1.erase j.1).card = k := by
              have hEraseSucc :
                  (L.1.erase j.1).card + 1 = k + 1 := by
                simpa [L.2] using Finset.card_erase_add_one j.2
              exact Nat.succ.inj hEraseSucc
            have hRkSubset :
                Rk ⊆ convexHull ℝ (binary_prefix_points_on_subset hp P (L.1.erase j.1)) := by
              intro y hy
              have hyRk :
                  ∀ J : {J : Finset (Fin p) // J.card = k},
                    y ∈ convexHull ℝ (binary_prefix_points_on_subset hp P J.1) := by
                simpa [Rk, Set.mem_iInter] using hy
              exact hyRk ⟨L.1.erase j.1, hEraseCard⟩
            exact coordinateLiftProjectHull_mono hRkSubset (Fin.castLE hp j.1) (hx j.1)
          simpa [binaryPrefixHull_predecessorFamilyStep hp P (k := k) L.1 L.2] using
            hxPredecessors
        · intro hx
          rw [mem_prefix_lift_project_closure_iff]
          intro i
          have hxRk1 : x ∈ Rk1 := by
            simpa [Rk1, Set.mem_iInter] using hx
          have hxRestricted :
              x ∈ ⋂ L : {L : Finset (Fin p) // L.card = k + 1 ∧ i ∈ L},
                convexHull ℝ (binary_prefix_points_on_subset hp P L.1) :=
            succBinaryPrefixHull_subset_restrictedFamily hp P (k := k) i hxRk1
          exact restrictedBinaryPrefixHull_subset_coordinateHullPredecessor hp P hk i hxRestricted

end Exercise525
