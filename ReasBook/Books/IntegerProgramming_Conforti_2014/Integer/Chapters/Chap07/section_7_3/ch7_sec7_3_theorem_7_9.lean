import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_21

open scoped BigOperators

-- Semantic recall note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available in this environment, so this file uses a direct source-faithful formalization of the
-- single-node flow set and its flow-cover inequality.

section Theorem79

variable {n : ℕ}

/-- The single-node flow set
`T = {(x,y) ∈ {0,1}^n × ℝ^n_+ | ∑ j, y_j ≤ b, y_j ≤ a_j x_j for all j}`. -/
def single_node_flow_set
    (a : Fin n → ℝ) (b : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p |
    (∀ j, p.1 j = 0 ∨ p.1 j = 1) ∧
      (∀ j, 0 ≤ p.2 j) ∧
        (∑ j, p.2 j ≤ b) ∧
          ∀ j, p.2 j ≤ a j * p.1 j}

/-- Membership in `single_node_flow_set a b` is exactly the binary, nonnegativity, capacity, and
upper-bound system defining the single-node flow set. -/
theorem mem_single_node_flow_set_iff
    (a : Fin n → ℝ) (b : ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    p ∈ single_node_flow_set a b ↔
      (∀ j, p.1 j = 0 ∨ p.1 j = 1) ∧
        (∀ j, 0 ≤ p.2 j) ∧
          (∑ j, p.2 j ≤ b) ∧
            ∀ j, p.2 j ≤ a j * p.1 j :=
  Iff.rfl

/-- A flow cover for the single-node flow set is a subset whose total capacity exceeds `b`. -/
class IsFlowCover
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) : Prop where
  /-- The total capacity on `C` is strictly larger than the single-node right-hand side. -/
  sum_gt_rhs : b < (∑ j ∈ C, a j)

/-- Proofs of `IsFlowCover a b C` are subsingletons because this is a proposition. -/
instance isFlowCover_subsingleton
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) :
    Subsingleton (IsFlowCover a b C) :=
  inferInstance

/-- `IsFlowCover a b C` unfolds to the strict inequality `b < ∑ j ∈ C, a_j`. -/
theorem isFlowCover_iff
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) :
    IsFlowCover a b C ↔ b < (∑ j ∈ C, a j) := by
  constructor
  · intro hC
    exact hC.sum_gt_rhs
  · intro hC
    exact ⟨hC⟩

/-- A flow cover is nonempty whenever the right-hand side is nonnegative. -/
theorem flow_cover_nonempty
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (hb_nonneg : 0 ≤ b)
    (hC : IsFlowCover a b C) :
    C.Nonempty := by
  by_contra hCempty
  have hEmpty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hCempty
  have hlt : b < 0 := by
    simpa [hEmpty] using hC.sum_gt_rhs
  exact (not_lt_of_ge hb_nonneg) hlt

/-- The excess `λ = ∑_{j ∈ C} a_j - b` associated with the flow cover `C`. -/
def flow_cover_excess
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) : ℝ :=
  (∑ j ∈ C, a j) - b

/-- The flow-cover excess is definitionally the total cover capacity minus `b`. -/
theorem flow_cover_excess_eq_sum_sub
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) :
    flow_cover_excess a b C = (∑ j ∈ C, a j) - b :=
  rfl

/-- A flow cover has strictly positive excess. -/
theorem flow_cover_excess_pos
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (hC : IsFlowCover a b C) :
    0 < flow_cover_excess a b C := by
  rw [flow_cover_excess_eq_sum_sub]
  linarith [hC.sum_gt_rhs]

/-- The left-hand side of the flow cover inequality attached to `C` evaluated at `(x,y)`. -/
def flow_cover_value
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (∑ j ∈ C, p.2 j) +
    ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - p.1 j)

/-- `flow_cover_value a b C p` expands to the explicit left-hand side of the flow cover
inequality defined by `C`. -/
theorem flow_cover_value_eq
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    flow_cover_value a b C p =
      (∑ j ∈ C, p.2 j) +
        ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - p.1 j) :=
  rfl

/-- The equality face cut out on `conv(T)` by the flow cover inequality associated with `C`. -/
def flow_cover_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p |
    p ∈ convexHull ℝ (single_node_flow_set a b) ∧
      flow_cover_value a b C p = b}

/-- Membership in `flow_cover_face a b C` means lying in `conv(T)` and meeting the flow cover
inequality at equality. -/
theorem mem_flow_cover_face_iff
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    p ∈ flow_cover_face a b C ↔
      p ∈ convexHull ℝ (single_node_flow_set a b) ∧
        flow_cover_value a b C p = b :=
  Iff.rfl

/-- Helper for Theorem 7.9: for nonnegative capacities and positive excess `λ`, the positive-part
penalty is subadditive along two capacity contributions. -/
lemma maxSubExcess_add_le
    {u v lam : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hlam : 0 < lam) :
    max (u - lam) 0 + max (v - lam) 0 ≤ max (u + v - lam) 0 := by
  -- Split by whether each term already falls below the positive-part threshold `λ`.
  by_cases hu_le : u ≤ lam
  · by_cases hv_le : v ≤ lam
    · have hu_max : max (u - lam) 0 = 0 := by
        rw [max_eq_right]
        linarith
      have hv_max : max (v - lam) 0 = 0 := by
        rw [max_eq_right]
        linarith
      rw [hu_max, hv_max]
      simpa using (le_max_right (u + v - lam) (0 : ℝ))
    · have hu_max : max (u - lam) 0 = 0 := by
        rw [max_eq_right]
        linarith
      have hv_nonneg : 0 ≤ v - lam := by
        linarith
      have huv_nonneg : 0 ≤ u + v - lam := by
        linarith
      rw [hu_max, max_eq_left hv_nonneg, max_eq_left huv_nonneg]
      linarith
  · by_cases hv_le : v ≤ lam
    · have hv_max : max (v - lam) 0 = 0 := by
        rw [max_eq_right]
        linarith
      have hu_nonneg : 0 ≤ u - lam := by
        linarith
      have huv_nonneg : 0 ≤ u + v - lam := by
        linarith
      rw [hv_max, max_eq_left hu_nonneg, max_eq_left huv_nonneg]
      linarith
    · have hu_nonneg : 0 ≤ u - lam := by
        linarith
      have hv_nonneg : 0 ≤ v - lam := by
        linarith
      have huv_nonneg : 0 ≤ u + v - lam := by
        linarith
      rw [max_eq_left hu_nonneg, max_eq_left hv_nonneg, max_eq_left huv_nonneg]
      linarith

/-- Helper for Theorem 7.9: the total positive-part penalty over a missing cover set is bounded by
the positive part of the total missing-capacity gap. -/
lemma coverPenalty_le_missingGap
    (a : Fin n → ℝ) (lam : ℝ) (M : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hlam : 0 < lam) :
    (∑ j ∈ M, max (a j - lam) 0) ≤ max ((∑ j ∈ M, a j) - lam) 0 := by
  induction M using Finset.induction_on with
  | empty =>
      -- The empty missing set contributes no penalty.
      simp
  | @insert j M hj ih =>
      have hsum_nonneg : 0 ≤ ∑ k ∈ M, a k := by
        exact Finset.sum_nonneg (fun k hk ↦ ha_nonneg k)
      -- Add the new missing item and use the two-term positive-part bound.
      calc
        ((insert j M : Finset (Fin n))).sum (fun k ↦ max (a k - lam) 0)
            = max (a j - lam) 0 + ∑ k ∈ M, max (a k - lam) 0 := by
                simp [hj]
        _ ≤ max (a j - lam) 0 + max ((∑ k ∈ M, a k) - lam) 0 := by
              gcongr
        _ ≤ max ((a j + ∑ k ∈ M, a k) - lam) 0 := by
              exact maxSubExcess_add_le (ha_nonneg j) hsum_nonneg hlam
        _ = max (((insert j M : Finset (Fin n))).sum a - lam) 0 := by
              simp [hj, add_comm, add_left_comm, add_assoc]

/-- Helper for Theorem 7.9: the positive-part coefficients in the canonical supporting
flow-cover functional. -/
def flowCoverSupportCoeff
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) : Fin n → ℝ :=
  fun j ↦ max (a j - flow_cover_excess a b C) 0

/-- Helper for Theorem 7.9: the canonical support functional for the flow-cover inequality is
additive. -/
theorem flowCoverSupportLinearMap_map_add
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (q r : (Fin n → ℝ) × (Fin n → ℝ)) :
    (∑ j ∈ C, (q + r).2 j) -
        ∑ j ∈ C, flowCoverSupportCoeff a b C j * (q + r).1 j =
      ((∑ j ∈ C, q.2 j) - ∑ j ∈ C, flowCoverSupportCoeff a b C j * q.1 j) +
        ((∑ j ∈ C, r.2 j) - ∑ j ∈ C, flowCoverSupportCoeff a b C j * r.1 j) := by
  -- Expand the product-space addition and regroup the two sums.
  simp [flowCoverSupportCoeff, Finset.sum_add_distrib, sub_eq_add_neg, mul_add, add_comm,
    add_left_comm, add_assoc]

/-- Helper for Theorem 7.9: the canonical support functional for the flow-cover inequality is
homogeneous. -/
theorem flowCoverSupportLinearMap_map_smul
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (t : ℝ) (q : (Fin n → ℝ) × (Fin n → ℝ)) :
    (∑ j ∈ C, (t • q).2 j) -
        ∑ j ∈ C, flowCoverSupportCoeff a b C j * (t • q).1 j =
      t * ((∑ j ∈ C, q.2 j) - ∑ j ∈ C, flowCoverSupportCoeff a b C j * q.1 j) := by
  -- Pull the scalar through both sums and then factor it out.
  calc
    (∑ j ∈ C, (t • q).2 j) -
        ∑ j ∈ C, flowCoverSupportCoeff a b C j * (t • q).1 j
      = (∑ j ∈ C, t * q.2 j) -
          ∑ j ∈ C, t * (flowCoverSupportCoeff a b C j * q.1 j) := by
            simp [flowCoverSupportCoeff, Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm]
    _ = t * (∑ j ∈ C, q.2 j) - t * ∑ j ∈ C, flowCoverSupportCoeff a b C j * q.1 j := by
          simp [Finset.mul_sum, Finset.sum_mul, sub_eq_add_neg, mul_assoc]
    _ = t * ((∑ j ∈ C, q.2 j) - ∑ j ∈ C, flowCoverSupportCoeff a b C j * q.1 j) := by
          ring

/-- Helper for Theorem 7.9: the canonical linear part of the flow-cover supporting hyperplane. -/
def flowCoverSupportLinearMap
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
  { toFun := fun q ↦ (∑ j ∈ C, q.2 j) - ∑ j ∈ C, flowCoverSupportCoeff a b C j * q.1 j
    map_add' := flowCoverSupportLinearMap_map_add a b C
    map_smul' := flowCoverSupportLinearMap_map_smul a b C }

/-- Helper for Theorem 7.9: `flow_cover_value` is an affine functional whose linear part is the
cover-flow sum minus the weighted `x`-coordinates on the cover. -/
theorem flow_cover_value_eq_linear_part_add_constant
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    flow_cover_value a b C p =
      ((∑ j ∈ C, p.2 j) -
          ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * p.1 j) +
        ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 := by
  -- Expand the penalty term into a constant part minus the weighted `x`-contribution.
  rw [flow_cover_value_eq]
  calc
    (∑ j ∈ C, p.2 j) +
        ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - p.1 j)
      = (∑ j ∈ C, p.2 j) +
          ((∑ j ∈ C, max (a j - flow_cover_excess a b C) 0) -
            ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * p.1 j) := by
              congr 1
              calc
                ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - p.1 j)
                    = ∑ j ∈ C,
                        (max (a j - flow_cover_excess a b C) 0 -
                          max (a j - flow_cover_excess a b C) 0 * p.1 j) := by
                            refine Finset.sum_congr rfl ?_
                            intro j hj
                            ring
                _ = (∑ j ∈ C, max (a j - flow_cover_excess a b C) 0) -
                      ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * p.1 j := by
                        rw [Finset.sum_sub_distrib]
    _ =
        ((∑ j ∈ C, p.2 j) -
            ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * p.1 j) +
          ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 := by
            ring

/-- Theorem 7.9 (1). Let `C` be a flow cover for the single-node flow set `T`, and let
`λ = ∑_{j ∈ C} a_j - b`. Then the flow cover inequality defined by `C` is valid for `T`. -/
theorem single_node_flow_cover_inequality_valid
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ single_node_flow_set a b) :
    flow_cover_value a b C p ≤ b := by
  rcases (mem_single_node_flow_set_iff a b p).mp hp with ⟨hx_bin, hy_nonneg, hsum, hcap⟩
  let lam : ℝ := flow_cover_excess a b C
  let M : Finset (Fin n) := C.filter (fun j ↦ p.1 j = 0)
  have hlam : 0 < lam := by
    simpa [lam] using flow_cover_excess_pos a b C hC
  have hpenalty_eq :
      ∑ j ∈ C, max (a j - lam) 0 * (1 - p.1 j) =
        ∑ j ∈ M, max (a j - lam) 0 := by
    -- Binary coordinates collapse the penalty to the missing-cover subset.
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rcases hx_bin j with hzero | hone
    · simp [M, hzero]
    · simp [M, hone]
  have hweighted_eq :
      ∑ j ∈ C, a j * p.1 j = (∑ j ∈ C, a j) - ∑ j ∈ M, a j := by
    have hsplit :
        C.sum a = M.sum a + (C.filter (fun j ↦ p.1 j ≠ 0)).sum a := by
      simpa [M, add_comm, add_left_comm, add_assoc] using
        (Finset.sum_filter_add_sum_filter_not (s := C) (p := fun j ↦ p.1 j = 0) a).symm
    calc
      ∑ j ∈ C, a j * p.1 j = (C.filter (fun j ↦ p.1 j ≠ 0)).sum a := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro j hj
        rcases hx_bin j with hzero | hone
        · simp [hzero]
        · simp [hone]
      _ = C.sum a - M.sum a := by
        linarith
  have hflow_le_gap :
      ∑ j ∈ C, p.2 j ≤ b - max ((∑ j ∈ M, a j) - lam) 0 := by
    have hcover_bound :
        ∑ j ∈ C, p.2 j ≤ b - ((∑ j ∈ M, a j) - lam) := by
      calc
        ∑ j ∈ C, p.2 j ≤ ∑ j ∈ C, a j * p.1 j := by
          exact Finset.sum_le_sum (fun j hj ↦ hcap j)
        _ = (∑ j ∈ C, a j) - ∑ j ∈ M, a j := hweighted_eq
        _ = b - ((∑ j ∈ M, a j) - lam) := by
          dsimp [lam]
          rw [flow_cover_excess_eq_sum_sub]
          ring
    by_cases hgap_nonneg : 0 ≤ (∑ j ∈ M, a j) - lam
    · rw [max_eq_left hgap_nonneg]
      exact hcover_bound
    · rw [max_eq_right]
      · have hsum_cover : ∑ j ∈ C, p.2 j ≤ b := by
          calc
            ∑ j ∈ C, p.2 j ≤ ∑ j, p.2 j := by
              exact Finset.sum_le_sum_of_subset_of_nonneg
                (by intro j hj; simp)
                (fun j _ _ ↦ hy_nonneg j)
            _ ≤ b := hsum
        simpa using hsum_cover
      · linarith
  have hpenalty_le :
      ∑ j ∈ M, max (a j - lam) 0 ≤ max ((∑ j ∈ M, a j) - lam) 0 :=
    coverPenalty_le_missingGap a lam M ha_nonneg hlam
  -- Combine the flow bound and the penalty bound on the missing-cover set.
  rw [flow_cover_value_eq, hpenalty_eq]
  linarith

/-- Since the flow-cover inequality is valid on `T`, it is also valid on `conv(T)`. -/
theorem flow_cover_value_le_of_mem_convexHull
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ convexHull ℝ (single_node_flow_set a b)) :
    flow_cover_value a b C p ≤ b := by
  let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
  let δ : ℝ := b - ∑ j ∈ C, coeff j
  let H : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {q | L q ≤ δ}
  have hvalue_split :
      ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
        flow_cover_value a b C q = L q + ∑ j ∈ C, coeff j := by
    intro q
    simpa [L, coeff, flowCoverSupportLinearMap, flowCoverSupportCoeff] using
      flow_cover_value_eq_linear_part_add_constant a b C q
  have hconvex : Convex ℝ H := by
    -- The valid region is a linear halfspace after separating the constant term.
    simpa [H, L] using convex_halfSpace_le L.isLinear δ
  have hsubset : single_node_flow_set a b ⊆ H := by
    intro q hq
    have hvalid :=
      single_node_flow_cover_inequality_valid a b C ha_nonneg hC hq
    have hsplit := hvalue_split q
    dsimp [H, δ]
    linarith
  have hp_mem : p ∈ H := convexHull_min hsubset hconvex hp
  have hsplit := hvalue_split p
  dsimp [H, δ] at hp_mem
  linarith

/-- Helper for Theorem 7.9: a sharp valid linear inequality identifies its equality set with the
corresponding exposed face. -/
theorem separatorEqualitySet_eq_toExposed_of_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} {L : E →ₗ[ℝ] ℝ} {δ : ℝ} {x₀ : E}
    (hvalid : ∀ x ∈ P, L x ≤ δ)
    (hx₀P : x₀ ∈ P) (hx₀ : L x₀ = δ) :
    {x : E | x ∈ P ∧ L x = δ} =
      (⟨L, L.continuous_of_finiteDimensional⟩ : E →L[ℝ] ℝ).toExposed P := by
  ext x
  constructor
  · rintro ⟨hxP, hxEq⟩
    -- Equality points maximize the supporting functional because the same upper bound is valid on
    -- the whole set.
    refine ⟨hxP, ?_⟩
    intro y hyP
    calc
      L y ≤ δ := hvalid y hyP
      _ = L x := by simpa [hxEq]
  · intro hx
    -- A maximizer must attain the witness value where the upper bound is already sharp.
    refine ⟨hx.1, ?_⟩
    have hx₀_le : L x₀ ≤ L x := hx.2 x₀ hx₀P
    have hx_le : L x ≤ L x₀ := by
      calc
        L x ≤ δ := hvalid x hx.1
        _ = L x₀ := hx₀.symm
    have hx_eq : L x = L x₀ := le_antisymm hx_le hx₀_le
    simpa [hx₀] using hx_eq

/-- Helper for Theorem 7.9: the standard anchor point with all cover items selected and the
anchor flow reduced by the excess lies on the flow-cover equality face. -/
theorem flow_cover_anchor_point_mem_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0) :
    ((fun j ↦ if j ∈ C then 1 else 0),
        fun j ↦ (if j ∈ C then a j else 0) -
          if j = j0 then flow_cover_excess a b C else 0) ∈
      flow_cover_face a b C := by
  let x0 : Fin n → ℝ := fun j ↦ if j ∈ C then 1 else 0
  let y0 : Fin n → ℝ := fun j ↦
    (if j ∈ C then a j else 0) - if j = j0 then flow_cover_excess a b C else 0
  have hy0_nonneg : ∀ j, 0 ≤ y0 j := by
    intro j
    by_cases hjC : j ∈ C
    · by_cases hj0 : j = j0
      · subst hj0
        dsimp [y0]
        simp [hj0C]
        linarith
      · dsimp [y0]
        simp [hjC, hj0, ha_nonneg j]
    · have hj0_ne : j ≠ j0 := by
        intro hEq
        exact hjC (hEq.symm ▸ hj0C)
      dsimp [y0]
      simp [hjC, hj0_ne]
  have hpoint_mem : (x0, y0) ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    refine ⟨?_, hy0_nonneg, ?_, ?_⟩
    · -- The anchor point selects exactly the cover coordinates.
      intro j
      by_cases hjC : j ∈ C
      · simp [x0, hjC]
      · simp [x0, hjC]
    · -- The anchor flow uses exactly `b` units of total flow.
      have hsum_y :
          ∑ j, y0 j = b := by
        rw [Finset.sum_sub_distrib]
        simpa [y0, hj0C, flow_cover_excess_eq_sum_sub]
      simpa [hsum_y]
    · -- Each flow coordinate respects its own capacity upper bound.
      intro j
      by_cases hjC : j ∈ C
      · by_cases hj0 : j = j0
        · subst hj0
          dsimp [x0, y0]
          simp [hj0C]
          have hlam_pos : 0 < flow_cover_excess a b C := flow_cover_excess_pos a b C hC
          linarith
        · dsimp [x0, y0]
          simp [hjC, hj0]
      · have hj0_ne : j ≠ j0 := by
          intro hEq
          exact hjC (hEq.symm ▸ hj0C)
        dsimp [x0, y0]
        simp [hjC, hj0_ne]
  refine (mem_flow_cover_face_iff a b C (x0, y0)).2 ?_
  refine ⟨subset_convexHull ℝ _ hpoint_mem, ?_⟩
  -- On the anchor point, every cover variable is selected, so the penalty term vanishes.
  have hsum_cover :
      ∑ j ∈ C, y0 j = b := by
    simpa [y0, hj0C, flow_cover_excess_eq_sum_sub]
  rw [flow_cover_value_eq]
  have hpenalty_zero :
      ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - x0 j) = 0 := by
    -- Every cover coordinate of `x0` is `1`, so the penalty sum vanishes termwise.
    refine Finset.sum_eq_zero ?_
    intro j hj
    simp [x0, hj]
  rw [hpenalty_zero]
  simpa [hsum_cover]

/-- Helper for Theorem 7.9: once the excess is strictly smaller than one cover capacity, the
flow-cover equality set is an exposed face of `conv(T)`. -/
theorem flow_cover_face_isExposed
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j) :
    IsExposed ℝ
      (convexHull ℝ (single_node_flow_set a b))
      (flow_cover_face a b C) := by
  rcases h_excess_lt_some with ⟨j0, hj0C, hj0lt⟩
  let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
  let δ : ℝ := b - ∑ j ∈ C, coeff j
  let x0 : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦ (if j ∈ C then a j else 0) -
        if j = j0 then flow_cover_excess a b C else 0)
  have hvalue_split :
      ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
        flow_cover_value a b C q = L q + ∑ j ∈ C, coeff j := by
    intro q
    simpa [L, coeff, flowCoverSupportLinearMap, flowCoverSupportCoeff] using
      flow_cover_value_eq_linear_part_add_constant a b C q
  have hvalid :
      ∀ q ∈ convexHull ℝ (single_node_flow_set a b), L q ≤ δ := by
    intro q hq
    have hq_valid := flow_cover_value_le_of_mem_convexHull a b C ha_nonneg hC hq
    have hsplit := hvalue_split q
    dsimp [δ] at *
    linarith
  have hx0_face : x0 ∈ flow_cover_face a b C := by
    simpa [x0] using flow_cover_anchor_point_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hx0_eq : L x0 = δ := by
    have hsplit := hvalue_split x0
    have hx0_level := (mem_flow_cover_face_iff a b C x0).mp hx0_face |>.2
    dsimp [δ] at *
    linarith
  have hface_eq :
      flow_cover_face a b C =
        {q | q ∈ convexHull ℝ (single_node_flow_set a b) ∧ L q = δ} := by
    ext q
    constructor
    · intro hq
      rcases (mem_flow_cover_face_iff a b C q).mp hq with ⟨hqP, hqEq⟩
      refine ⟨hqP, ?_⟩
      have hsplit := hvalue_split q
      dsimp [δ] at *
      linarith
    · intro hq
      rcases hq with ⟨hqP, hqEq⟩
      refine (mem_flow_cover_face_iff a b C q).2 ⟨hqP, ?_⟩
      have hsplit := hvalue_split q
      dsimp [δ] at *
      linarith
  have hface_toExposed :
      flow_cover_face a b C =
        (⟨L, L.continuous_of_finiteDimensional⟩ :
          ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ℝ).toExposed
            (convexHull ℝ (single_node_flow_set a b)) := by
    rw [hface_eq]
    exact separatorEqualitySet_eq_toExposed_of_mem hvalid hx0_face.1 hx0_eq
  -- Rewriting the equality face as a `toExposed` set gives the canonical exposed-face fact.
  rw [hface_toExposed]
  exact ContinuousLinearMap.toExposed.isExposed

/-- Helper for Theorem 7.9: if one cover capacity strictly exceeds the flow-cover excess, then the
single-node right-hand side `b` is positive. -/
theorem flowCover_rhs_pos
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    {j0 : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0) :
    0 < b := by
  have hsum_split :
      C.sum a = (C.erase j0).sum a + a j0 := by
    -- Split the cover sum at the distinguished anchor index.
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := C) (f := a) hj0C).symm
  have htail_lt : (C.erase j0).sum a < b := by
    -- Rearranging `λ < a j0` isolates the remaining cover mass below `b`.
    rw [flow_cover_excess_eq_sum_sub] at hj0lt
    rw [hsum_split] at hj0lt
    linarith
  have htail_nonneg : 0 ≤ (C.erase j0).sum a := by
    -- Nonnegative capacities force the tail cover sum to be nonnegative.
    exact Finset.sum_nonneg fun j hj ↦ ha_nonneg j
  linarith

/-- Helper for Theorem 7.9: the slack point with all items selected and zero flow lies in the
single-node flow set as soon as `b` is nonnegative. -/
theorem flowCoverLoosePoint_mem_single_node_flow_set
    (a : Fin n → ℝ) (b : ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hb_nonneg : 0 ≤ b) :
    ((fun _ ↦ (1 : ℝ)), fun _ ↦ (0 : ℝ)) ∈ single_node_flow_set a b := by
  rw [mem_single_node_flow_set_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Every `x`-coordinate of the slack point equals `1`.
    intro j
    exact Or.inr rfl
  · -- The slack point has zero nonnegative flow.
    intro j
    simp
  · -- The total slack flow is zero, hence below any nonnegative right-hand side.
    simpa using hb_nonneg
  · -- Zero flow automatically satisfies every capacity upper bound.
    intro j
    simpa using ha_nonneg j

/-- Helper for Theorem 7.9: every direction of the flow-cover equality face lies in the ambient
direction and in the kernel of the supporting linear map used to expose the face. -/
theorem flowCoverFaceDirection_le_polyDirection_inf_supportKer
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j) :
    let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
    let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
    (affineSpan ℝ (flow_cover_face a b C)).direction ≤
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction ⊓ LinearMap.ker L := by
  classical
  rcases h_excess_lt_some with ⟨j0, hj0C, hj0lt⟩
  dsimp
  let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
  let δ : ℝ := b - ∑ j ∈ C, coeff j
  let x0 : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦ (if j ∈ C then a j else 0) -
        if j = j0 then flow_cover_excess a b C else 0)
  have hvalue_split :
      ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
        flow_cover_value a b C q = L q + ∑ j ∈ C, coeff j := by
    intro q
    simpa [L, coeff, flowCoverSupportLinearMap, flowCoverSupportCoeff] using
      flow_cover_value_eq_linear_part_add_constant a b C q
  have hx0_face : x0 ∈ flow_cover_face a b C := by
    -- Reuse the anchor point already constructed for the exposed-face proof.
    simpa [x0] using flow_cover_anchor_point_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hlevel :
      ∀ q ∈ flow_cover_face a b C, L q = δ := by
    intro q hq
    have hq_eq := (mem_flow_cover_face_iff a b C q).mp hq |>.2
    have hsplit := hvalue_split q
    dsimp [δ] at *
    linarith
  have hspan_level :
      (affineSpan ℝ (flow_cover_face a b C) :
        Set ((Fin n → ℝ) × (Fin n → ℝ))) ⊆ {q | L q = δ} := by
    intro q hq
    -- The level-set condition is affine, so it extends from the face to its affine span.
    refine affineSpan_induction (k := ℝ) (s := flow_cover_face a b C)
      (p := fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ L x = δ) hq ?_ ?_
    · intro x hx
      exact hlevel x hx
    · intro t x y z hx hy hz
      simp [hx, hy, hz, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc]
  intro v hv
  refine ⟨?_, ?_⟩
  · -- The face lives inside `conv(T)`, so its direction lies inside the ambient direction.
    simpa using
      (AffineSubspace.direction_le (affineSpan_mono ℝ (fun q hq ↦
        (mem_flow_cover_face_iff a b C q).mp hq |>.1)) hv)
  · have hx0_aff : x0 ∈ affineSpan ℝ (flow_cover_face a b C) :=
      subset_affineSpan ℝ _ hx0_face
    change L v = 0
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx0_aff] at hv
    rcases hv with ⟨x, hx_aff, rfl⟩
    -- Both endpoints lie on the same affine level set, so their difference is killed by `L`.
    have hx_eq : L x = δ := hspan_level hx_aff
    have hx0_eq : L x0 = δ := hlevel x0 hx0_face
    simp [vsub_eq_sub, hx_eq, hx0_eq]

/-- Helper for Theorem 7.9: the ambient support-kernel cut has codimension one because the
normalized difference between the anchor point and the slack point evaluates to `1`. -/
theorem flowCoverSupportKerCodimOne
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j) :
    let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
    let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
    let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction
    Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
  classical
  rcases h_excess_lt_some with ⟨j0, hj0C, hj0lt⟩
  dsimp
  let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
  let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction
  let x0 : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦ (if j ∈ C then a j else 0) -
        if j = j0 then flow_cover_excess a b C else 0)
  let pLoose : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun _ ↦ (1 : ℝ)), fun _ ↦ (0 : ℝ))
  let w : (Fin n → ℝ) × (Fin n → ℝ) := b⁻¹ • (x0 - pLoose)
  have hvalue_split :
      ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
        flow_cover_value a b C q = L q + ∑ j ∈ C, coeff j := by
    intro q
    simpa [L, coeff, flowCoverSupportLinearMap, flowCoverSupportCoeff] using
      flow_cover_value_eq_linear_part_add_constant a b C q
  have hx0_face : x0 ∈ flow_cover_face a b C := by
    -- Reuse the standard exposed-face anchor point.
    simpa [x0] using flow_cover_anchor_point_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hx0_mem :
      x0 ∈ convexHull ℝ (single_node_flow_set a b) :=
    (mem_flow_cover_face_iff a b C x0).mp hx0_face |>.1
  have hb_pos : 0 < b := flowCover_rhs_pos a b C ha_nonneg hj0C hj0lt
  have hpLoose_mem : pLoose ∈ single_node_flow_set a b := by
    -- The all-ones / zero-flow point is feasible because `b` is positive.
    simpa [pLoose] using
      flowCoverLoosePoint_mem_single_node_flow_set a b ha_nonneg hb_pos.le
  have hpLoose_hull :
      pLoose ∈ convexHull ℝ (single_node_flow_set a b) :=
    subset_convexHull ℝ _ hpLoose_mem
  have hx0_aff :
      x0 ∈ affineSpan ℝ (convexHull ℝ (single_node_flow_set a b)) :=
    subset_affineSpan ℝ _ hx0_mem
  have hpLoose_aff :
      pLoose ∈ affineSpan ℝ (convexHull ℝ (single_node_flow_set a b)) :=
    subset_affineSpan ℝ _ hpLoose_hull
  have hdiff_mem :
      x0 - pLoose ∈ D := by
    -- Differences of two ambient points lie in the ambient direction.
    rw [show D = (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction by rfl]
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hpLoose_aff]
    refine ⟨x0, hx0_aff, ?_⟩
    simp [vsub_eq_sub]
  have hwD : w ∈ D := by
    -- Scaling a direction vector keeps it inside the ambient direction.
    simpa [w] using D.smul_mem (b⁻¹) hdiff_mem
  have hx0_eval :
      L x0 = b - ∑ j ∈ C, coeff j := by
    -- The anchor point lies on the equality face, so the supporting functional hits `δ`.
    have hx0_eq := (mem_flow_cover_face_iff a b C x0).mp hx0_face |>.2
    have hsplit := hvalue_split x0
    linarith
  have hpLoose_eval :
      L pLoose = -∑ j ∈ C, coeff j := by
    -- The slack point has zero flow and all cover selectors equal to one.
    simp [L, coeff, pLoose, flowCoverSupportLinearMap, flowCoverSupportCoeff]
  have hw_eval : L w = 1 := by
    -- Normalizing the anchor-slack difference divides its `L`-value `b` down to `1`.
    have hdiff_eval : L (x0 - pLoose) = b := by
      calc
        L (x0 - pLoose) = L x0 - L pLoose := by
          simp [LinearMap.map_sub]
        _ = b := by
          linarith [hx0_eval, hpLoose_eval]
    calc
      L w = b⁻¹ * L (x0 - pLoose) := by
        simp [w]
      _ = b⁻¹ * b := by rw [hdiff_eval]
      _ = 1 := by
        field_simp [hb_pos.ne']
  exact submodule_finrank_inf_ker_add_one_of_eval_one D L hwD hw_eval

/-- Helper for Theorem 7.9: if a capacity coordinate is zero, then every ambient direction vector
has zero `y`-component on that coordinate. -/
theorem singleNodeFlowAmbientDirection_y_zero_of_capacity_zero
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j)
    {i : Fin n} {v : (Fin n → ℝ) × (Fin n → ℝ)}
    (hv :
      v ∈ (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction)
    (hai : a i = 0) :
    v.2 i = 0 := by
  classical
  rcases h_excess_lt_some with ⟨j0, hj0C, hj0lt⟩
  let x0 : Fin n → ℝ := fun j ↦ if j ∈ C then 1 else 0
  let y0 : Fin n → ℝ := fun j ↦
    (if j ∈ C then a j else 0) - if j = j0 then flow_cover_excess a b C else 0
  let p0 : (Fin n → ℝ) × (Fin n → ℝ) := (x0, y0)
  let P : Set ((Fin n → ℝ) × (Fin n → ℝ)) := convexHull ℝ (single_node_flow_set a b)
  have hp0_face : p0 ∈ flow_cover_face a b C := by
    -- Reuse the standard anchor point on the equality face.
    simpa [p0, x0, y0] using
      flow_cover_anchor_point_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hp0_aff : p0 ∈ affineSpan ℝ P := by
    -- The anchor point lies in the ambient affine span because it lies in the face.
    exact subset_affineSpan ℝ _ ((mem_flow_cover_face_iff a b C p0).mp hp0_face).1
  have hp0_zero : p0.2 i = 0 := by
    -- The anchor point has zero `y_i` whenever the capacity itself is zero.
    by_cases hiC : i ∈ C
    · have hij0 : i ≠ j0 := by
        intro hij0
        subst hij0
        rw [hai] at hj0lt
        have hlam_pos : 0 < flow_cover_excess a b C := flow_cover_excess_pos a b C hC
        linarith
      simp [p0, y0, hiC, hij0, hai]
    · have hij0 : i ≠ j0 := by
        intro hij0
        exact hiC (hij0.symm ▸ hj0C)
      simp [p0, y0, hiC, hij0]
  let H : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {q | q.2 i = 0}
  have hH_convex : Convex ℝ H := by
    -- The zero-coordinate slice is a convex set.
    intro x hx y hy t s ht hs hts
    dsimp [H] at hx hy ⊢
    simp [hx, hy, Pi.add_apply, Pi.smul_apply, mul_add, add_comm, add_left_comm, add_assoc]
  have hsubset_H : single_node_flow_set a b ⊆ H := by
    intro q hq
    rcases (mem_single_node_flow_set_iff a b q).mp hq with ⟨_, hy_nonneg, _, hcap⟩
    dsimp [H]
    have hqi_nonneg : 0 ≤ q.2 i := hy_nonneg i
    have hqi_le : q.2 i ≤ a i * q.1 i := hcap i
    rw [hai] at hqi_le
    linarith
  have hcoord_zero :
      ∀ q ∈ affineSpan ℝ P, q.2 i = 0 := by
    intro q hq
    -- First extend the coordinate-zero property from `T` to `conv(T)`, then to its affine span.
    refine affineSpan_induction (k := ℝ) (s := P)
      (p := fun x : (Fin n → ℝ) × (Fin n → ℝ) ↦ x.2 i = 0) hq ?_ ?_
    · intro x hx
      exact (convexHull_min hsubset_H hH_convex hx : x ∈ H)
    · intro t x y z hx hy hz
      simp [hx, hy, hz, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc]
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hp0_aff] at hv
  rcases hv with ⟨x, hx_aff, rfl⟩
  -- Subtracting two ambient points with the same zero `y_i` coordinate keeps that coordinate zero.
  have hx_zero : x.2 i = 0 := hcoord_zero x hx_aff
  simp [vsub_eq_sub, hx_zero, hp0_zero]

/-- Helper for Theorem 7.9: on nonnegative capacities, the canonical support coefficient is the
capacity minus the exchanged amount `min (a_j) λ`. -/
theorem flowCoverSupportCoeff_eq_sub_min
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (j : Fin n) :
    flowCoverSupportCoeff a b C j =
      a j - min (a j) (flow_cover_excess a b C) := by
  have hlam_pos : 0 < flow_cover_excess a b C := flow_cover_excess_pos a b C hC
  by_cases hle : flow_cover_excess a b C ≤ a j
  · -- When the excess fits inside `a j`, the coefficient is the remaining slack `a j - λ`.
    rw [flowCoverSupportCoeff, min_eq_right hle]
    rw [max_eq_left]
    · ring
    · linarith
  · have hlt : a j < flow_cover_excess a b C := by linarith
    -- When `a j < λ`, the coefficient vanishes and so does `a j - min (a j) λ`.
    rw [flowCoverSupportCoeff, min_eq_left hlt.le, max_eq_right]
    · ring
    · linarith [ha_nonneg j]

/-- Helper for Theorem 7.9: dropping the distinguished cover item leaves a feasible point on the
flow-cover equality face, with the missing penalty carried entirely by that anchor. -/
theorem flowCoverDroppedAnchorPoint_mem_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0) :
    ((fun j ↦ if j ∈ C.erase j0 then 1 else 0),
        fun j ↦ if j ∈ C.erase j0 then a j else 0) ∈
      flow_cover_face a b C := by
  classical
  let xDrop : Fin n → ℝ := fun j ↦ if j ∈ C.erase j0 then 1 else 0
  let yDrop : Fin n → ℝ := fun j ↦ if j ∈ C.erase j0 then a j else 0
  have hpoint_mem : (xDrop, yDrop) ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- The dropped-anchor selector is still binary.
      intro j
      by_cases hj : j ∈ C.erase j0
      · simp [xDrop, hj]
      · simp [xDrop, hj]
    · -- All retained cover capacities are nonnegative.
      intro j
      by_cases hj : j ∈ C.erase j0
      · simp [yDrop, hj, ha_nonneg j]
      · simp [yDrop, hj]
    · -- Removing the distinguished cover item keeps the total flow below `b`.
      have hsum_split :
          C.sum a = (C.erase j0).sum a + a j0 := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (Finset.sum_erase_add (s := C) (f := a) hj0C).symm
      have htail_lt : (C.erase j0).sum a < b := by
        rw [flow_cover_excess_eq_sum_sub] at hj0lt
        rw [hsum_split] at hj0lt
        linarith
      have hsum_y : ∑ j, yDrop j = (C.erase j0).sum a := by
        simp [yDrop]
      rw [hsum_y]
      linarith
    · -- Each retained flow still saturates its own selected capacity.
      intro j
      by_cases hj : j ∈ C.erase j0
      · simp [xDrop, yDrop, hj]
      · simp [xDrop, yDrop, hj, ha_nonneg j]
  refine (mem_flow_cover_face_iff a b C (xDrop, yDrop)).2 ?_
  refine ⟨subset_convexHull ℝ _ hpoint_mem, ?_⟩
  have hsum_split :
      C.sum a = (C.erase j0).sum a + a j0 := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := C) (f := a) hj0C).symm
  have hcoeff_j0 :
      flowCoverSupportCoeff a b C j0 = a j0 - flow_cover_excess a b C := by
    rw [flowCoverSupportCoeff, max_eq_left]
    linarith
  have hsum_cover :
      ∑ j ∈ C, yDrop j = (C.erase j0).sum a := by
    rw [Finset.sum_erase_add _ hj0C]
    simp [yDrop]
  -- The dropped-anchor point contributes exactly the anchor penalty term on the face equation.
  rw [flow_cover_value_eq]
  have hpenalty :
      ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - xDrop j) =
        flowCoverSupportCoeff a b C j0 := by
    rw [Finset.sum_eq_single j0]
    · simp [xDrop, hj0C]
    · intro j hjC hjne
      have hj : j ∈ C.erase j0 := by
        simp [hjC, hjne, Finset.mem_erase]
      simp [xDrop, hj]
    · intro hj0_not_mem
      exact hj0_not_mem hj0C
  rw [hpenalty, hcoeff_j0, hsum_cover, flow_cover_excess_eq_sum_sub, hsum_split]
  ring

/-- Helper for Theorem 7.9: toggling an outside selector on top of the dropped-anchor point keeps
the point on the same equality face because outside coordinates do not enter the face equation. -/
theorem flowCoverOutsideTogglePoint_mem_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hiC : i ∉ C) :
    ((fun j ↦ if j = i then 1 else if j ∈ C.erase j0 then 1 else 0),
        fun j ↦ if j ∈ C.erase j0 then a j else 0) ∈
      flow_cover_face a b C := by
  classical
  let xOut : Fin n → ℝ := fun j ↦ if j = i then 1 else if j ∈ C.erase j0 then 1 else 0
  let yOut : Fin n → ℝ := fun j ↦ if j ∈ C.erase j0 then a j else 0
  have hpoint_mem : (xOut, yOut) ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- The outside-toggle point only changes one binary `x`-coordinate.
      intro j
      by_cases hji : j = i
      · simp [xOut, hji]
      · by_cases hj : j ∈ C.erase j0
        · simp [xOut, hji, hj]
        · simp [xOut, hji, hj]
    · -- The `y` part is unchanged from the dropped-anchor point.
      intro j
      by_cases hj : j ∈ C.erase j0
      · simp [yOut, hj, ha_nonneg j]
      · simp [yOut, hj]
    · -- Outside toggles do not affect the total flow.
      have hsum_split :
          C.sum a = (C.erase j0).sum a + a j0 := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (Finset.sum_erase_add (s := C) (f := a) hj0C).symm
      have htail_lt : (C.erase j0).sum a < b := by
        rw [flow_cover_excess_eq_sum_sub] at hj0lt
        rw [hsum_split] at hj0lt
        linarith
      have hsum_y : ∑ j, yOut j = (C.erase j0).sum a := by
        simp [yOut]
      rw [hsum_y]
      linarith
    · -- Capacity bounds are unchanged on the cover, and trivial on outside coordinates.
      intro j
      by_cases hji : j = i
      · subst hji
        simp [xOut, yOut, hiC, ha_nonneg i]
      · by_cases hj : j ∈ C.erase j0
        · simp [xOut, yOut, hji, hj]
        · simp [xOut, yOut, hji, hj, ha_nonneg j]
  refine (mem_flow_cover_face_iff a b C (xOut, yOut)).2 ?_
  refine ⟨subset_convexHull ℝ _ hpoint_mem, ?_⟩
  have hsum_split :
      C.sum a = (C.erase j0).sum a + a j0 := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := C) (f := a) hj0C).symm
  have hcoeff_j0 :
      flowCoverSupportCoeff a b C j0 = a j0 - flow_cover_excess a b C := by
    rw [flowCoverSupportCoeff, max_eq_left]
    linarith
  have hsum_cover :
      ∑ j ∈ C, yOut j = (C.erase j0).sum a := by
    rw [Finset.sum_erase_add _ hj0C]
    simp [yOut]
  -- The outside selector is invisible to the flow-cover face equation.
  rw [flow_cover_value_eq]
  have hpenalty :
      ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - xOut j) =
        flowCoverSupportCoeff a b C j0 := by
    rw [Finset.sum_eq_single j0]
    · have hji : j0 ≠ i := by
        exact fun h ↦ hiC (h.symm ▸ hj0C)
      simp [xOut, hj0C, hji]
    · intro j hjC hjne
      have hj : j ∈ C.erase j0 := by
        simp [hjC, hjne, Finset.mem_erase]
      have hji : j ≠ i := by
        exact fun h ↦ hiC (h.symm ▸ hjC)
      simp [xOut, hj, hji]
    · intro hj0_not_mem
      exact hj0_not_mem hj0C
  rw [hpenalty, hcoeff_j0, hsum_cover, flow_cover_excess_eq_sum_sub, hsum_split]
  ring

/-- Helper for Theorem 7.9: the outside-flow witness adds as much outside flow as the dropped
anchor slack allows, while remaining on the same equality face. -/
theorem flowCoverOutsideFlowPoint_mem_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hiC : i ∉ C) :
    ((fun j ↦ if j = i then 1 else if j ∈ C.erase j0 then 1 else 0),
        fun j ↦ if j ∈ C.erase j0 then a j
          else if j = i then min (a i) (flowCoverSupportCoeff a b C j0) else 0) ∈
      flow_cover_face a b C := by
  classical
  let xOut : Fin n → ℝ := fun j ↦ if j = i then 1 else if j ∈ C.erase j0 then 1 else 0
  let yOut : Fin n → ℝ := fun j ↦
    if j ∈ C.erase j0 then a j
    else if j = i then min (a i) (flowCoverSupportCoeff a b C j0) else 0
  have hcoeff_j0 :
      flowCoverSupportCoeff a b C j0 = a j0 - flow_cover_excess a b C := by
    rw [flowCoverSupportCoeff, max_eq_left]
    linarith
  have hpoint_mem : (xOut, yOut) ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- The outside-flow witness still has binary `x`.
      intro j
      by_cases hji : j = i
      · simp [xOut, hji]
      · by_cases hj : j ∈ C.erase j0
        · simp [xOut, hji, hj]
        · simp [xOut, hji, hj]
    · -- The injected outside flow is nonnegative because it is a minimum of nonnegative terms.
      intro j
      by_cases hj : j ∈ C.erase j0
      · simp [yOut, hj, ha_nonneg j]
      · by_cases hji : j = i
        · subst hji
          have hcoeff_nonneg : 0 ≤ flowCoverSupportCoeff a b C j0 := by
            rw [hcoeff_j0]
            linarith [ha_nonneg j0]
          simp [yOut, hj, hcoeff_nonneg, ha_nonneg i]
        · simp [yOut, hj, hji]
    · -- The extra outside flow is capped by the dropped-anchor slack.
      have hsum_split :
          C.sum a = (C.erase j0).sum a + a j0 := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (Finset.sum_erase_add (s := C) (f := a) hj0C).symm
      have hsum_y :
          ∑ j, yOut j =
            (C.erase j0).sum a + min (a i) (flowCoverSupportCoeff a b C j0) := by
        simp [yOut, hiC]
      rw [hsum_y]
      have hmin_le : min (a i) (flowCoverSupportCoeff a b C j0) ≤
          flowCoverSupportCoeff a b C j0 := min_le_right _ _
      rw [hcoeff_j0, flow_cover_excess_eq_sum_sub, hsum_split] at hmin_le ⊢
      linarith
    · -- The new outside flow respects its own capacity, and the cover bounds are unchanged.
      intro j
      by_cases hji : j = i
      · subst hji
        exact by
          simp [xOut, yOut, hiC, min_le_left]
      · by_cases hj : j ∈ C.erase j0
        · simp [xOut, yOut, hji, hj]
        · simp [xOut, yOut, hji, hj, ha_nonneg j]
  refine (mem_flow_cover_face_iff a b C (xOut, yOut)).2 ?_
  refine ⟨subset_convexHull ℝ _ hpoint_mem, ?_⟩
  have hsum_split :
      C.sum a = (C.erase j0).sum a + a j0 := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := C) (f := a) hj0C).symm
  have hsum_cover :
      ∑ j ∈ C, yOut j = (C.erase j0).sum a := by
    rw [Finset.sum_erase_add _ hj0C]
    simp [yOut]
  -- Outside flow does not enter the cover equation, so the same dropped-anchor equality remains.
  rw [flow_cover_value_eq]
  have hpenalty :
      ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - xOut j) =
        flowCoverSupportCoeff a b C j0 := by
    rw [Finset.sum_eq_single j0]
    · have hji : j0 ≠ i := by
        exact fun h ↦ hiC (h.symm ▸ hj0C)
      simp [xOut, hj0C, hji]
    · intro j hjC hjne
      have hj : j ∈ C.erase j0 := by
        simp [hjC, hjne, Finset.mem_erase]
      have hji : j ≠ i := by
        exact fun h ↦ hiC (h.symm ▸ hjC)
      simp [xOut, hj, hji]
    · intro hj0_not_mem
      exact hj0_not_mem hj0C
  rw [hpenalty, hcoeff_j0, hsum_cover, flow_cover_excess_eq_sum_sub, hsum_split]
  ring

/-- Helper for Theorem 7.9: exchanging `min (a_i) λ` units of cover flow from `i` to the anchor
keeps the point on the same equality face. -/
theorem flowCoverCoverExchangePoint_mem_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hi : i ∈ C.erase j0) :
    ((fun j ↦ if j ∈ C then 1 else 0),
        fun j ↦
          if j = j0 then flowCoverSupportCoeff a b C j0 +
              min (a i) (flow_cover_excess a b C)
          else if j = i then a i - min (a i) (flow_cover_excess a b C)
          else if j ∈ C then a j else 0) ∈
      flow_cover_face a b C := by
  classical
  let xEx : Fin n → ℝ := fun j ↦ if j ∈ C then 1 else 0
  let yEx : Fin n → ℝ := fun j ↦
    if j = j0 then flowCoverSupportCoeff a b C j0 + min (a i) (flow_cover_excess a b C)
    else if j = i then a i - min (a i) (flow_cover_excess a b C)
    else if j ∈ C then a j else 0
  have hiC : i ∈ C := (Finset.mem_erase.mp hi).2
  have hij0 : i ≠ j0 := (Finset.mem_erase.mp hi).1
  have hcoeff_j0 :
      flowCoverSupportCoeff a b C j0 = a j0 - flow_cover_excess a b C := by
    rw [flowCoverSupportCoeff, max_eq_left]
    linarith
  have hpoint_mem : (xEx, yEx) ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- The exchange point keeps every cover selector at `1`.
      intro j
      by_cases hj : j ∈ C
      · simp [xEx, hj]
      · simp [xEx, hj]
    · -- All adjusted cover flows remain nonnegative.
      intro j
      by_cases hj0 : j = j0
      · subst hj0
        have hmin_nonneg : 0 ≤ min (a i) (flow_cover_excess a b C) := by
          exact le_min (ha_nonneg i) (flow_cover_excess_pos a b C hC).le
        simp [yEx, hcoeff_j0, hmin_nonneg]
      · by_cases hji : j = i
        · subst hji
          have hmin_le : min (a i) (flow_cover_excess a b C) ≤ a i := min_le_left _ _
          simp [yEx, hj0, hmin_le]
        · by_cases hjC : j ∈ C
          · simp [yEx, hj0, hji, hjC, ha_nonneg j]
          · simp [yEx, hj0, hji, hjC]
    · -- The exchange preserves the total cover flow `b`.
      have hsum_y : ∑ j, yEx j = b := by
        have hj0_univ_erase : j0 ∈ (Finset.univ.erase i : Finset (Fin n)) := by
          simp [hij0]
        rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) (f := yEx)
          (by simp)]
        rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ.erase i) (f := yEx)
          hj0_univ_erase]
        by_cases hcase : i = j0
        · exact (hij0 hcase).elim
        · simp [yEx, hiC, hj0C, hij0, hcase, hcoeff_j0, flow_cover_excess_eq_sum_sub]
      simpa [hsum_y]
    · -- Capacity bounds hold because the transfer amount is bounded by both `a_i` and `λ`.
      intro j
      by_cases hj0 : j = j0
      · subst hj0
        have hmin_le :
            min (a i) (flow_cover_excess a b C) ≤ flow_cover_excess a b C := min_le_right _ _
        simp [xEx, yEx, hj0C, hcoeff_j0]
        linarith
      · by_cases hji : j = i
        · subst hji
          have hmin_le : min (a i) (flow_cover_excess a b C) ≤ a i := min_le_left _ _
          simp [xEx, yEx, hiC, hj0, hmin_le]
        · by_cases hjC : j ∈ C
          · simp [xEx, yEx, hj0, hji, hjC]
          · simp [xEx, yEx, hj0, hji, hjC, ha_nonneg j]
  refine (mem_flow_cover_face_iff a b C (xEx, yEx)).2 ?_
  refine ⟨subset_convexHull ℝ _ hpoint_mem, ?_⟩
  -- Every cover selector remains `1`, so the penalty term still vanishes.
  rw [flow_cover_value_eq]
  have hpenalty_zero :
      ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - xEx j) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    simp [xEx, hj]
  rw [hpenalty_zero]
  have hsum_cover : ∑ j ∈ C, yEx j = b := by
    have hj0_erase : j0 ∈ (C.erase i : Finset (Fin n)) := by
      simp [hj0C, hij0]
    rw [Finset.sum_eq_add_sum_diff_singleton (s := C) (f := yEx) hiC]
    rw [Finset.sum_eq_add_sum_diff_singleton (s := C.erase i) (f := yEx) hj0_erase]
    by_cases hcase : i = j0
    · exact (hij0 hcase).elim
    · simp [yEx, hiC, hj0C, hij0, hcase, hcoeff_j0, flow_cover_excess_eq_sum_sub]
  simpa [hsum_cover]

/-- Helper for Theorem 7.9: dropping a cover selector while moving `min (a_i) λ` units of flow
to the anchor stays on the same flow-cover equality face. -/
theorem flowCoverCoverDropPoint_mem_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hi : i ∈ C.erase j0) :
    ((fun j ↦ if j = i then 0 else if j ∈ C then 1 else 0),
        fun j ↦
          if j = j0 then flowCoverSupportCoeff a b C j0 +
              min (a i) (flow_cover_excess a b C)
          else if j = i then 0
          else if j ∈ C then a j else 0) ∈
      flow_cover_face a b C := by
  classical
  let xDrop : Fin n → ℝ := fun j ↦ if j = i then 0 else if j ∈ C then 1 else 0
  let yDrop : Fin n → ℝ := fun j ↦
    if j = j0 then flowCoverSupportCoeff a b C j0 +
        min (a i) (flow_cover_excess a b C)
    else if j = i then 0
    else if j ∈ C then a j else 0
  have hiC : i ∈ C := (Finset.mem_erase.mp hi).2
  have hij0 : i ≠ j0 := (Finset.mem_erase.mp hi).1
  have hcoeff_j0 :
      flowCoverSupportCoeff a b C j0 = a j0 - flow_cover_excess a b C := by
    rw [flowCoverSupportCoeff, max_eq_left]
    linarith
  have hcoeff_i :
      flowCoverSupportCoeff a b C i =
        a i - min (a i) (flow_cover_excess a b C) := by
    simpa using flowCoverSupportCoeff_eq_sub_min a b C ha_nonneg hC i
  have hpoint_mem : (xDrop, yDrop) ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- The dropped cover selector is the only coordinate set to `0`.
      intro j
      by_cases hji : j = i
      · simp [xDrop, hji]
      · by_cases hjC : j ∈ C
        · simp [xDrop, hji, hjC]
        · simp [xDrop, hji, hjC]
    · -- All flow coordinates remain nonnegative after dropping `i` and shifting to `j0`.
      intro j
      by_cases hj0 : j = j0
      · subst hj0
        have hmin_nonneg : 0 ≤ min (a i) (flow_cover_excess a b C) := by
          exact le_min (ha_nonneg i) (flow_cover_excess_pos a b C hC).le
        simp [yDrop, hcoeff_j0, hmin_nonneg]
      · by_cases hji : j = i
        · subst hji
          simp [yDrop, hj0]
        · by_cases hjC : j ∈ C
          · simp [yDrop, hj0, hji, hjC, ha_nonneg j]
          · simp [yDrop, hj0, hji, hjC]
    · -- The cover-drop witness lowers the total flow by exactly the dropped support coefficient.
      have hsum_cover :
          ∑ j ∈ C, yDrop j = b - flowCoverSupportCoeff a b C i := by
        have hj0_erase : j0 ∈ (C.erase i : Finset (Fin n)) := by
          simp [hj0C, hij0]
        rw [Finset.sum_eq_add_sum_diff_singleton (s := C) (f := yDrop) hiC]
        rw [Finset.sum_eq_add_sum_diff_singleton (s := C.erase i) (f := yDrop) hj0_erase]
        simp [yDrop, hiC, hj0C, hij0, hcoeff_j0, hcoeff_i, flow_cover_excess_eq_sum_sub]
      have hsum_eq :
          ∑ j, yDrop j = b - flowCoverSupportCoeff a b C i := by
        calc
          ∑ j, yDrop j = ∑ j ∈ C, yDrop j := by
            symm
            refine Finset.sum_subset (Finset.subset_univ C) ?_
            intro j _ hjC
            by_cases hji : j = i
            · subst hji
              simp [yDrop, hiC]
            · simp [yDrop, hji, hjC]
          _ = b - flowCoverSupportCoeff a b C i := hsum_cover
      rw [hsum_eq]
      have hcoeff_nonneg : 0 ≤ flowCoverSupportCoeff a b C i := by
        rw [hcoeff_i]
        have hmin_le : min (a i) (flow_cover_excess a b C) ≤ a i := min_le_left _ _
        linarith
      linarith
    · -- Capacity bounds are unchanged off `i`, and the dropped coordinate has both sides zero.
      intro j
      by_cases hj0 : j = j0
      · subst hj0
        have hmin_le :
            min (a i) (flow_cover_excess a b C) ≤ flow_cover_excess a b C := min_le_right _ _
        simp [xDrop, yDrop, hj0C, hcoeff_j0]
        linarith
      · by_cases hji : j = i
        · subst hji
          simp [xDrop, yDrop, hiC, hj0]
        · by_cases hjC : j ∈ C
          · simp [xDrop, yDrop, hj0, hji, hjC]
          · simp [xDrop, yDrop, hj0, hji, hjC, ha_nonneg j]
  refine (mem_flow_cover_face_iff a b C (xDrop, yDrop)).2 ?_
  refine ⟨subset_convexHull ℝ _ hpoint_mem, ?_⟩
  -- The face equality is the cover sum plus the single dropped-index penalty.
  rw [flow_cover_value_eq]
  have hsum_cover :
      ∑ j ∈ C, yDrop j = b - flowCoverSupportCoeff a b C i := by
    have hj0_erase : j0 ∈ (C.erase i : Finset (Fin n)) := by
      simp [hj0C, hij0]
    rw [Finset.sum_eq_add_sum_diff_singleton (s := C) (f := yDrop) hiC]
    rw [Finset.sum_eq_add_sum_diff_singleton (s := C.erase i) (f := yDrop) hj0_erase]
    simp [yDrop, hiC, hj0C, hij0, hcoeff_j0, hcoeff_i, flow_cover_excess_eq_sum_sub]
  have hpenalty :
      ∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - xDrop j) =
        flowCoverSupportCoeff a b C i := by
    rw [Finset.sum_eq_single i]
    · simp [xDrop, hiC]
    · intro j hjC hjne
      have hji : j ≠ i := by simpa [eq_comm] using hjne
      simp [xDrop, hjC, hji]
    · intro hi_not_mem
      exact hi_not_mem hiC
  rw [hsum_cover, hpenalty]
  ring

/-- Helper for Theorem 7.9: subtracting the dropped-cover witness from the exchange witness gives
the exact coupled cover generator in the equality-face direction. -/
theorem flowCoverCoverXCoupled_mem_faceDirection
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hi : i ∈ C.erase j0) :
    ((fun j ↦ if j = i then 1 else 0),
        fun j ↦ if j = i then flowCoverSupportCoeff a b C i else 0) ∈
      (affineSpan ℝ (flow_cover_face a b C)).direction := by
  classical
  let pEx : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦
        if j = j0 then flowCoverSupportCoeff a b C j0 +
            min (a i) (flow_cover_excess a b C)
        else if j = i then a i - min (a i) (flow_cover_excess a b C)
        else if j ∈ C then a j else 0)
  let pDrop : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 0 else if j ∈ C then 1 else 0),
      fun j ↦
        if j = j0 then flowCoverSupportCoeff a b C j0 +
            min (a i) (flow_cover_excess a b C)
        else if j = i then 0
        else if j ∈ C then a j else 0)
  have hiC : i ∈ C := (Finset.mem_erase.mp hi).2
  have hij0 : i ≠ j0 := (Finset.mem_erase.mp hi).1
  have hcoeff_i :
      flowCoverSupportCoeff a b C i =
        a i - min (a i) (flow_cover_excess a b C) := by
    simpa using flowCoverSupportCoeff_eq_sub_min a b C ha_nonneg hC i
  have hpEx : pEx ∈ flow_cover_face a b C := by
    -- The exchange witness already lies on the equality face.
    simpa [pEx] using flowCoverCoverExchangePoint_mem_face a b C ha_nonneg hC hj0C hj0lt hi
  have hpDrop : pDrop ∈ flow_cover_face a b C := by
    -- The new cover-drop witness lies on the same equality face.
    simpa [pDrop] using flowCoverCoverDropPoint_mem_face a b C ha_nonneg hC hj0C hj0lt hi
  have hpEx_aff : pEx ∈ affineSpan ℝ (flow_cover_face a b C) := mem_affineSpan ℝ hpEx
  have hpDrop_aff : pDrop ∈ affineSpan ℝ (flow_cover_face a b C) := mem_affineSpan ℝ hpDrop
  -- Route correction: package the textbook witness difference as the exact coupled generator.
  simpa [pEx, pDrop, hcoeff_i, hiC, hij0, vsub_eq_sub, Pi.sub_apply] using
    AffineSubspace.vsub_mem_direction hpEx_aff hpDrop_aff

/-- Helper for Theorem 7.9: subtracting the dropped-anchor witness from the anchor witness gives
the anchor coupled generator in the equality-face direction. -/
theorem flowCoverAnchorXCoupled_mem_faceDirection
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0) :
    ((fun j ↦ if j = j0 then 1 else 0),
        fun j ↦ if j = j0 then flowCoverSupportCoeff a b C j0 else 0) ∈
      (affineSpan ℝ (flow_cover_face a b C)).direction := by
  classical
  let pAnchor : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦ (if j ∈ C then a j else 0) -
        if j = j0 then flow_cover_excess a b C else 0)
  let pDrop : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C.erase j0 then 1 else 0),
      fun j ↦ if j ∈ C.erase j0 then a j else 0)
  have hcoeff_j0 :
      flowCoverSupportCoeff a b C j0 = a j0 - flow_cover_excess a b C := by
    rw [flowCoverSupportCoeff, max_eq_left]
    linarith
  have hpAnchor : pAnchor ∈ flow_cover_face a b C := by
    -- The standard anchor witness lies on the equality face.
    simpa [pAnchor] using flow_cover_anchor_point_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hpDrop : pDrop ∈ flow_cover_face a b C := by
    -- Dropping the anchor produces the complementary anchor-direction witness.
    simpa [pDrop] using flowCoverDroppedAnchorPoint_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hpAnchor_aff : pAnchor ∈ affineSpan ℝ (flow_cover_face a b C) := mem_affineSpan ℝ hpAnchor
  have hpDrop_aff : pDrop ∈ affineSpan ℝ (flow_cover_face a b C) := mem_affineSpan ℝ hpDrop
  -- The two anchor witnesses differ only in the anchor `x`/`y` coordinates.
  simpa [pAnchor, pDrop, hcoeff_j0, hj0C, vsub_eq_sub, Pi.sub_apply] using
    AffineSubspace.vsub_mem_direction hpAnchor_aff hpDrop_aff

/-- Helper for Theorem 7.9: toggling an outside selector gives the outside coordinate direction in
the equality-face direction. -/
theorem flowCoverOutsideCoordinateDirection_mem_faceDirection
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hiC : i ∉ C) :
    ((fun j ↦ if j = i then 1 else 0), fun _ ↦ (0 : ℝ)) ∈
      (affineSpan ℝ (flow_cover_face a b C)).direction := by
  classical
  let pOut : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 1 else if j ∈ C.erase j0 then 1 else 0),
      fun j ↦ if j ∈ C.erase j0 then a j else 0)
  let pDrop : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C.erase j0 then 1 else 0),
      fun j ↦ if j ∈ C.erase j0 then a j else 0)
  have hpOut : pOut ∈ flow_cover_face a b C := by
    -- Outside toggles preserve both feasibility and the equality face equation.
    simpa [pOut] using flowCoverOutsideTogglePoint_mem_face a b C ha_nonneg hC hj0C hj0lt hiC
  have hpDrop : pDrop ∈ flow_cover_face a b C := by
    -- The dropped-anchor point is the basepoint for outside-coordinate differences.
    simpa [pDrop] using flowCoverDroppedAnchorPoint_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hpOut_aff : pOut ∈ affineSpan ℝ (flow_cover_face a b C) := mem_affineSpan ℝ hpOut
  have hpDrop_aff : pDrop ∈ affineSpan ℝ (flow_cover_face a b C) := mem_affineSpan ℝ hpDrop
  -- Their difference isolates the outside `x_i` coordinate.
  simpa [pOut, pDrop, hiC, hj0C, vsub_eq_sub, Pi.sub_apply] using
    AffineSubspace.vsub_mem_direction hpOut_aff hpDrop_aff

/-- Helper for Theorem 7.9: adding outside flow on top of the outside toggle witness gives the
outside flow coordinate direction in the equality-face direction. -/
theorem flowCoverOutsideFlowDirection_mem_faceDirection
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hiC : i ∉ C) :
    ((fun _ ↦ (0 : ℝ)),
        fun j ↦ if j = i then min (a i) (flowCoverSupportCoeff a b C j0) else 0) ∈
      (affineSpan ℝ (flow_cover_face a b C)).direction := by
  classical
  let pFlow : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 1 else if j ∈ C.erase j0 then 1 else 0),
      fun j ↦ if j ∈ C.erase j0 then a j
        else if j = i then min (a i) (flowCoverSupportCoeff a b C j0) else 0)
  let pToggle : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 1 else if j ∈ C.erase j0 then 1 else 0),
      fun j ↦ if j ∈ C.erase j0 then a j else 0)
  have hpFlow : pFlow ∈ flow_cover_face a b C := by
    -- The outside-flow witness stays on the equality face.
    simpa [pFlow] using flowCoverOutsideFlowPoint_mem_face a b C ha_nonneg hC hj0C hj0lt hiC
  have hpToggle : pToggle ∈ flow_cover_face a b C := by
    -- The outside-toggle witness is the natural basepoint for the added outside flow.
    simpa [pToggle] using flowCoverOutsideTogglePoint_mem_face a b C ha_nonneg hC hj0C hj0lt hiC
  have hpFlow_aff : pFlow ∈ affineSpan ℝ (flow_cover_face a b C) := mem_affineSpan ℝ hpFlow
  have hpToggle_aff : pToggle ∈ affineSpan ℝ (flow_cover_face a b C) := mem_affineSpan ℝ hpToggle
  -- Subtracting the basepoint leaves only the added outside flow at `i`.
  simpa [pFlow, pToggle, hiC, hj0C, vsub_eq_sub, Pi.sub_apply] using
    AffineSubspace.vsub_mem_direction hpFlow_aff hpToggle_aff

/-- Helper for Theorem 7.9: exchanging `min (a_i) λ` units of cover flow from `i` to the anchor
gives the cover `y`-difference direction inside the equality-face direction. -/
theorem flowCoverCoverYExchange_mem_faceDirection
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : flow_cover_excess a b C < a j0)
    (hi : i ∈ C.erase j0) :
    ((fun _ ↦ (0 : ℝ)),
        fun j ↦
          if j = j0 then min (a i) (flow_cover_excess a b C)
          else if j = i then -min (a i) (flow_cover_excess a b C)
          else 0) ∈
      (affineSpan ℝ (flow_cover_face a b C)).direction := by
  classical
  let pEx : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦
        if j = j0 then flowCoverSupportCoeff a b C j0 +
            min (a i) (flow_cover_excess a b C)
        else if j = i then a i - min (a i) (flow_cover_excess a b C)
        else if j ∈ C then a j else 0)
  let pAnchor : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦ (if j ∈ C then a j else 0) -
        if j = j0 then flow_cover_excess a b C else 0)
  have hiC : i ∈ C := (Finset.mem_erase.mp hi).2
  have hij0 : i ≠ j0 := (Finset.mem_erase.mp hi).1
  have hcoeff_j0 :
      flowCoverSupportCoeff a b C j0 = a j0 - flow_cover_excess a b C := by
    rw [flowCoverSupportCoeff, max_eq_left]
    linarith
  have hpEx : pEx ∈ flow_cover_face a b C := by
    -- The exchange witness records the `y_i ↔ y_j0` transfer on the face.
    simpa [pEx] using flowCoverCoverExchangePoint_mem_face a b C ha_nonneg hC hj0C hj0lt hi
  have hpAnchor : pAnchor ∈ flow_cover_face a b C := by
    -- The anchor witness is the basepoint before performing the cover exchange.
    simpa [pAnchor] using flow_cover_anchor_point_mem_face a b C ha_nonneg hC hj0C hj0lt
  have hpEx_aff : pEx ∈ affineSpan ℝ (flow_cover_face a b C) := mem_affineSpan ℝ hpEx
  have hpAnchor_aff : pAnchor ∈ affineSpan ℝ (flow_cover_face a b C) := mem_affineSpan ℝ hpAnchor
  -- Their difference is exactly the exchanged cover-flow direction.
  simpa [pEx, pAnchor, hcoeff_j0, hiC, hij0, hj0C, vsub_eq_sub, Pi.sub_apply] using
    AffineSubspace.vsub_mem_direction hpEx_aff hpAnchor_aff

/-- Helper for Theorem 7.9: subtracting a scaled face-direction generator from an ambient
support-kernel vector keeps the residual inside the same ambient support-kernel cut. -/
theorem supportKerSubSmul_mem
    {FD D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ))}
    {L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ}
    (hFD_le : FD ≤ D ⊓ LinearMap.ker L)
    {u g : (Fin n → ℝ) × (Fin n → ℝ)} (hu : u ∈ D ⊓ LinearMap.ker L) (hg : g ∈ FD)
    (t : ℝ) :
    u - t • g ∈ D ⊓ LinearMap.ker L := by
  -- Push the generator into the ambient support-kernel cut, then use submodule closure.
  exact sub_mem hu ((D ⊓ LinearMap.ker L).smul_mem t (hFD_le hg))

/-- Helper for Theorem 7.9: the remaining source-faithful step is to show that the anchored
textbook witness family spans every ambient support-kernel direction of the flow-cover face. -/
theorem flowCoverFaceDirection_eq_polyDirection_inf_supportKer
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j) :
    let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
    let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
    (affineSpan ℝ (flow_cover_face a b C)).direction =
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction ⊓ LinearMap.ker L := by
  classical
  -- Route correction: the witness-point membership API is now available. The remaining step is
  -- purely linear-algebraic: turn those face points into generators, eliminate outside `x/y`,
  -- then eliminate cover `x` and finally cover `y` using the kernel equation at the anchor `j0`.
  rcases h_excess_lt_some with ⟨j0, hj0C, hj0lt⟩
  dsimp
  let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
  let FD : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (flow_cover_face a b C)).direction
  let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction
  have hFD_le : FD ≤ D ⊓ LinearMap.ker L := by
    -- Reuse the already-closed forward inclusion into the ambient support-kernel cut.
    simpa [coeff, L, FD, D] using
      flowCoverFaceDirection_le_polyDirection_inf_supportKer a b C ha_nonneg hC
        ⟨j0, hj0C, hj0lt⟩
  have hlam_pos : 0 < flow_cover_excess a b C := flow_cover_excess_pos a b C hC
  have hcoeff_j0 :
      coeff j0 = a j0 - flow_cover_excess a b C := by
    -- At the anchor, the support coefficient is the strict positive slack `a_j0 - λ`.
    rw [show coeff j0 = a j0 - min (a j0) (flow_cover_excess a b C) by
      simpa [coeff] using flowCoverSupportCoeff_eq_sub_min a b C ha_nonneg hC j0]
    rw [min_eq_right hj0lt.le]
  have hcoeff_j0_pos : 0 < coeff j0 := by
    rw [hcoeff_j0]
    linarith
  have hcoeff_zero_of_capacity_zero :
      ∀ i : Fin n, a i = 0 → coeff i = 0 := by
    intro i hai
    -- Zero capacity forces the canonical support coefficient to vanish as well.
    rw [show coeff i = a i - min (a i) (flow_cover_excess a b C) by
      simpa [coeff] using flowCoverSupportCoeff_eq_sub_min a b C ha_nonneg hC i]
    rw [hai, min_eq_left hlam_pos.le]
    ring
  have hkernel_anchor :
      ∀ {v : (Fin n → ℝ) × (Fin n → ℝ)},
        v ∈ D ⊓ LinearMap.ker L →
          coeff j0 * v.1 j0 +
              (∑ i in C.erase j0, (coeff i * v.1 i - v.2 i)) =
            v.2 j0 := by
    intro v hv
    have hvL : L v = 0 := by
      -- Kernel membership is exactly vanishing of the support linear functional.
      simpa [LinearMap.mem_ker] using hv.2
    have hvL' :
        ((C.erase j0).sum fun i ↦ v.2 i) + v.2 j0 -
            (((C.erase j0).sum fun i ↦ coeff i * v.1 i) + coeff j0 * v.1 j0) = 0 := by
      -- Split both cover sums at the anchor coordinate.
      simpa [L, coeff, Finset.sum_erase_add, hj0C, add_comm, add_left_comm, add_assoc] using hvL
    linarith
  refine le_antisymm hFD_le ?_
  intro v hv
  have hvD : v ∈ D := hv.1
  have hvy_zero_of_capacity_zero : ∀ i : Fin n, a i = 0 → v.2 i = 0 := by
    intro i hai
    -- Zero-capacity coordinates already vanish in the ambient direction.
    exact singleNodeFlowAmbientDirection_y_zero_of_capacity_zero
      a b C ha_nonneg hC ⟨j0, hj0C, hj0lt⟩ hvD hai
  have hanchor_relation :
      coeff j0 * v.1 j0 +
          ∑ i in C.erase j0, (coeff i * v.1 i - v.2 i) =
        v.2 j0 := hkernel_anchor hv
  -- TODO: finish the explicit finite-sum decomposition of `v` into the outside `x/y`,
  -- non-anchor cover `x/y`, and anchor coupled generators using `hFD_le`,
  -- `hvy_zero_of_capacity_zero`, and `hanchor_relation`. The remaining blocker is packaging the
  -- filtered finite sums so the coordinate-by-coordinate `simp` normal form closes cleanly.
  sorry

/-- Theorem 7.9 (2). Let `C` be a flow cover for the single-node flow set `T`, and let
`λ = ∑_{j ∈ C} a_j - b`. If some `j ∈ C` satisfies `λ < a_j` (equivalently,
`λ < max_{j ∈ C} a_j`), then the flow cover inequality defined by `C` cuts out a facet of
`conv(T)`. -/
theorem single_node_flow_cover_inequality_facet
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j) :
    IsFacetOf
      (convexHull ℝ (single_node_flow_set a b))
      (flow_cover_face a b C) := by
  rcases h_excess_lt_some with ⟨j0, hj0C, hj0lt⟩
  rw [isFacetOf_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- The standard anchor point gives an explicit point on the equality face.
    exact ⟨_, flow_cover_anchor_point_mem_face a b C ha_nonneg hC hj0C hj0lt⟩
  · -- The exposed-face part was proved separately from the codimension computation.
    exact flow_cover_face_isExposed a b C ha_nonneg hC ⟨j0, hj0C, hj0lt⟩
  · let coeff : Fin n → ℝ := flowCoverSupportCoeff a b C
    let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
    let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction
    have hdir_eq :
        (affineSpan ℝ (flow_cover_face a b C)).direction =
          D ⊓ LinearMap.ker L := by
      -- Route correction: the remaining bridge is the source witness-family reverse inclusion.
      simpa [coeff, L, D] using
        flowCoverFaceDirection_eq_polyDirection_inf_supportKer
          a b C ha_nonneg hC ⟨j0, hj0C, hj0lt⟩
    have hcodim :
        Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
      -- The ambient support-kernel cut already has codimension one.
      simpa [coeff, L, D] using
        flowCoverSupportKerCodimOne a b C ha_nonneg hC ⟨j0, hj0C, hj0lt⟩
    calc
      Module.finrank ℝ (affineSpan ℝ (flow_cover_face a b C)).direction + 1
          = Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 := by
              rw [hdir_eq]
      _ = Module.finrank ℝ ↥D := hcodim
      _ = Module.finrank ℝ (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction := by
            rfl

end Theorem79
