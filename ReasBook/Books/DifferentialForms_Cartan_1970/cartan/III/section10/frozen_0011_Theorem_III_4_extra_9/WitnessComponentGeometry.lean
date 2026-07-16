import DifferentialForms_Cartan_1970.cartan.III.section10.frozen_0011_Theorem_III_4_extra_9.SelectorGeometry

open Metric Set
open scoped Topology unitInterval

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the closure of the Exercise 16
lens stays inside the two unit closed balls centered at `0` and `1`. -/
lemma closure_exercise16Domain_subset_closedBalls :
    closure exercise16Domain ⊆
      Metric.closedBall (0 : ℂ) 1 ∩ Metric.closedBall (1 : ℂ) 1 := by
  intro z hz
  constructor
  · refine closure_minimal ?_ Metric.isClosed_closedBall hz
    intro w hw
    exact Metric.ball_subset_closedBall hw.1
  · refine closure_minimal ?_ Metric.isClosed_closedBall hz
    intro w hw
    exact Metric.ball_subset_closedBall hw.2

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: every boundary point of the
closure of `exercise16Domain` still satisfies both unit-radius inequalities. -/
lemma norm_le_one_and_one_sub_norm_le_one_of_mem_closure_exercise16Domain {z : ℂ}
    (hz : z ∈ closure exercise16Domain) :
    ‖z‖ ≤ 1 ∧ ‖1 - z‖ ≤ 1 := by
  have hz_closed := closure_exercise16Domain_subset_closedBalls hz
  constructor
  · simpa [Metric.mem_closedBall, dist_eq_norm] using hz_closed.1
  · have hz_one : ‖z - 1‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz_closed.2
    have hnorm_eq : ‖1 - z‖ = ‖z - 1‖ := by
      simpa [sub_eq_add_neg] using norm_sub_rev (1 : ℂ) z
    rw [hnorm_eq]
    exact hz_one

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: strict positivity on an open
interval already yields a concrete right-hand positive neighborhood near the endpoint. -/
lemma rightPositiveNeighborhood_of_forall_mem_Ioo
    {u : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hpos : ∀ θ ∈ Set.Ioo a b, 0 < u θ) :
    ∃ η > 0, ∀ θ ∈ Set.Ioo (max a (b - η)) b, 0 < u θ := by
  refine ⟨(b - a) / 2, by linarith, ?_⟩
  intro θ hθ
  exact hpos θ ⟨lt_of_le_of_lt (le_max_left _ _) hθ.1, hθ.2⟩

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: strict negativity on an open
interval already yields a concrete left-hand negative neighborhood near the endpoint. -/
lemma leftNegativeNeighborhood_of_forall_mem_Ioo
    {u : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hneg : ∀ θ ∈ Set.Ioo a b, u θ < 0) :
    ∃ η > 0, ∀ θ ∈ Set.Ioo a (min (a + η) b), u θ < 0 := by
  refine ⟨(b - a) / 2, by linarith, ?_⟩
  intro θ hθ
  exact hneg θ ⟨hθ.1, lt_of_lt_of_le hθ.2 (min_le_right _ _)⟩

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the legal witness
component is `Ioo a b` and the selector is positive everywhere on that component, then the
right-hand endpoint already carries a concrete interior positive neighborhood. -/
lemma positiveComponent_rightPositiveNeighborhood
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hposall : ∀ θ ∈ C₀, 0 < selectorθ θ) :
    ∃ η > 0, ∀ θ ∈ Set.Ioo (max a (b - η)) b, 0 < selectorθ θ := by
  -- Repackage the component sign information into the endpoint-neighborhood API used downstream.
  refine rightPositiveNeighborhood_of_forall_mem_Ioo hab ?_
  intro θ hθ
  exact hposall θ <| by simpa [hC₀_eq] using hθ

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the legal witness
component is `Ioo a b` and the selector is negative everywhere on that component, then the left
endpoint already carries a concrete interior negative neighborhood. -/
lemma negativeComponent_leftNegativeNeighborhood
    {selectorθ : ℝ → ℝ} {C₀ : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hnegall : ∀ θ ∈ C₀, selectorθ θ < 0) :
    ∃ η > 0, ∀ θ ∈ Set.Ioo a (min (a + η) b), selectorθ θ < 0 := by
  -- This is the symmetric endpoint-neighborhood package for the negative component case.
  refine leftNegativeNeighborhood_of_forall_mem_Ioo hab ?_
  intro θ hθ
  exact hnegall θ <| by simpa [hC₀_eq] using hθ

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on the unit circle around `0`,
a strictly positive selector places the point strictly inside the unit ball around `1`. -/
lemma norm_one_sub_lt_one_of_selector_pos_of_norm_eq_one
    {w : ℂ} (hw0 : w ≠ 0) (h1w : 1 - w ≠ 0)
    (hselector_pos : 0 < Real.log ‖w / (1 - w)‖)
    (hw_norm_eq : ‖w‖ = 1) :
    ‖1 - w‖ < 1 := by
  have hselector_nonneg : 0 ≤ Real.log ‖w / (1 - w)‖ := le_of_lt hselector_pos
  have hreal_gt_half : (1 : ℝ) / 2 < w.re := by
    have hreal_ge_half : (1 : ℝ) / 2 ≤ w.re :=
      (selectorNonneg_iff_half_le_realPart hw0 h1w).mp hselector_nonneg
    have hreal_ne_half : w.re ≠ (1 : ℝ) / 2 := by
      intro hhalf
      have hselector_zero :
          Real.log ‖w / (1 - w)‖ = 0 :=
        (selectorEqZero_iff_realPart_eq_half hw0 h1w).2 hhalf
      exact (ne_of_gt hselector_pos) hselector_zero
    exact lt_of_le_of_ne hreal_ge_half hreal_ne_half.symm
  have hone_sub_sq :
      ‖1 - w‖ ^ 2 = 1 + ‖w‖ ^ 2 - 2 * w.re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp [Complex.normSq_eq_norm_sq, Complex.normSq_one, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm, mul_assoc]
  have hw_sq_eq : ‖w‖ ^ 2 = 1 := by
    simpa [hw_norm_eq] using congrArg (fun x : ℝ ↦ x ^ 2) hw_norm_eq
  have hone_sub_sq_lt : ‖1 - w‖ ^ 2 < 1 := by
    rw [hone_sub_sq, hw_sq_eq]
    nlinarith
  exact (sq_lt_one_iff₀ (norm_nonneg _)).1 hone_sub_sq_lt

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on the unit circle around `1`,
a strictly negative selector places the point strictly inside the unit ball around `0`. -/
lemma norm_lt_one_of_selector_neg_of_norm_one_sub_eq_one
    {w : ℂ} (hw0 : w ≠ 0) (h1w : 1 - w ≠ 0)
    (hselector_neg : Real.log ‖w / (1 - w)‖ < 0)
    (hone_sub_norm_eq : ‖1 - w‖ = 1) :
    ‖w‖ < 1 := by
  have hselector_nonpos : Real.log ‖w / (1 - w)‖ ≤ 0 := le_of_lt hselector_neg
  have hreal_lt_half : w.re < (1 : ℝ) / 2 := by
    have hreal_le_half : w.re ≤ (1 : ℝ) / 2 :=
      (selectorNonpos_iff_realPart_le_half hw0 h1w).mp hselector_nonpos
    have hreal_ne_half : w.re ≠ (1 : ℝ) / 2 := by
      intro hhalf
      have hselector_zero :
          Real.log ‖w / (1 - w)‖ = 0 :=
        (selectorEqZero_iff_realPart_eq_half hw0 h1w).2 hhalf
      exact (ne_of_lt hselector_neg) hselector_zero
    exact lt_of_le_of_ne hreal_le_half hreal_ne_half
  have hone_sub_sq :
      ‖1 - w‖ ^ 2 = 1 + ‖w‖ ^ 2 - 2 * w.re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp [Complex.normSq_eq_norm_sq, Complex.normSq_one, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm, mul_assoc]
  have hw_sq_lt : ‖w‖ ^ 2 < 1 := by
    have hone_sub_sq_eq : ‖1 - w‖ ^ 2 = 1 := by
      simpa [hone_sub_norm_eq] using congrArg (fun x : ℝ ↦ x ^ 2) hone_sub_norm_eq
    rw [hone_sub_sq] at hone_sub_sq_eq
    nlinarith
  exact (sq_lt_one_iff₀ (norm_nonneg _)).1 hw_sq_lt

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the legal witness component
is `Ioo a b`, then its left endpoint does not belong to the legal source set. -/
lemma leftEndpoint_not_mem_legalWitnessSet
    {S : Set ℝ} {a b thetaW : ℝ}
    (hS_open : IsOpen S)
    (ha_lt_thetaW : a < thetaW)
    (hthetaW_lt_b : thetaW < b)
    (hcomponent_eq : connectedComponentIn S thetaW = Set.Ioo a b) :
    a ∉ S := by
  intro ha_mem
  rcases (mem_nhds_iff_exists_Ioo_subset).1 (hS_open.mem_nhds ha_mem) with
    ⟨l, u, ha_mem_Ioo, hlu_subset⟩
  let x : ℝ := (a + min u thetaW) / 2
  have hx_mem_Ioo : x ∈ Set.Ioo a (min u thetaW) := by
    have hmin_gt : a < min u thetaW := lt_min ha_mem_Ioo.2 ha_lt_thetaW
    constructor <;> dsimp [x] <;> linarith
  have hx_mem_component : x ∈ connectedComponentIn S thetaW := by
    have hx_mem_Ioo_ab : x ∈ Set.Ioo a b := by
      refine ⟨hx_mem_Ioo.1, ?_⟩
      have hx_lt_thetaW : x < thetaW := lt_of_lt_of_le hx_mem_Ioo.2 (min_le_right _ _)
      exact lt_of_lt_of_le hx_lt_thetaW hthetaW_lt_b.le
    simpa [hcomponent_eq] using hx_mem_Ioo_ab
  have hIcc_subset_S : Set.Icc a x ⊆ S := by
    intro y hy
    have hy_mem_Ioo : y ∈ Set.Ioo l u := by
      constructor
      · linarith [ha_mem_Ioo.1, hy.1]
      · have hx_lt_u : x < u := lt_of_lt_of_le hx_mem_Ioo.2 (min_le_left _ _)
        linarith [hy.2, hx_lt_u]
    exact hlu_subset hy_mem_Ioo
  have ha_mem_component_x : a ∈ connectedComponentIn S x := by
    have hIcc_subset_component_x : Set.Icc a x ⊆ connectedComponentIn S x := by
      refine isPreconnected_Icc.subset_connectedComponentIn ?_ hIcc_subset_S
      exact ⟨hx_mem_Ioo.1.le, le_rfl⟩
    exact hIcc_subset_component_x ⟨le_rfl, hx_mem_Ioo.1.le⟩
  have hcomponent_eq_x : connectedComponentIn S thetaW = connectedComponentIn S x := by
    simpa using (connectedComponentIn_eq hx_mem_component)
  have ha_mem_component : a ∈ connectedComponentIn S thetaW := by
    rw [hcomponent_eq_x]
    exact ha_mem_component_x
  simpa [hcomponent_eq] using ha_mem_component

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the legal witness component
is `Ioo a b`, then its right endpoint does not belong to the legal source set. -/
lemma rightEndpoint_not_mem_legalWitnessSet
    {S : Set ℝ} {a b thetaW : ℝ}
    (hS_open : IsOpen S)
    (ha_lt_thetaW : a < thetaW)
    (hthetaW_lt_b : thetaW < b)
    (hcomponent_eq : connectedComponentIn S thetaW = Set.Ioo a b) :
    b ∉ S := by
  intro hb_mem
  rcases (mem_nhds_iff_exists_Ioo_subset).1 (hS_open.mem_nhds hb_mem) with
    ⟨l, u, hb_mem_Ioo, hlu_subset⟩
  let x : ℝ := (max l thetaW + b) / 2
  have hx_mem_Ioo : x ∈ Set.Ioo (max l thetaW) b := by
    have hmax_lt : max l thetaW < b := max_lt hb_mem_Ioo.1 hthetaW_lt_b
    constructor <;> dsimp [x] <;> linarith
  have hx_mem_component : x ∈ connectedComponentIn S thetaW := by
    have hx_mem_Ioo_ab : x ∈ Set.Ioo a b := by
      refine ⟨?_, hx_mem_Ioo.2⟩
      have hthetaW_lt_x : thetaW < x := lt_of_le_of_lt (le_max_right _ _) hx_mem_Ioo.1
      exact lt_of_lt_of_le ha_lt_thetaW hthetaW_lt_x.le
    simpa [hcomponent_eq] using hx_mem_Ioo_ab
  have hIcc_subset_S : Set.Icc x b ⊆ S := by
    intro y hy
    have hy_mem_Ioo : y ∈ Set.Ioo l u := by
      constructor
      · linarith [le_max_left l thetaW, hx_mem_Ioo.1, hy.1]
      · linarith [hy.2, hb_mem_Ioo.2]
    exact hlu_subset hy_mem_Ioo
  have hb_mem_component_x : b ∈ connectedComponentIn S x := by
    have hIcc_subset_component_x : Set.Icc x b ⊆ connectedComponentIn S x := by
      refine isPreconnected_Icc.subset_connectedComponentIn ?_ hIcc_subset_S
      exact ⟨le_rfl, hx_mem_Ioo.2.le⟩
    exact hIcc_subset_component_x ⟨hx_mem_Ioo.2.le, le_rfl⟩
  have hcomponent_eq_x : connectedComponentIn S thetaW = connectedComponentIn S x := by
    simpa using (connectedComponentIn_eq hx_mem_component)
  have hb_mem_component : b ∈ connectedComponentIn S thetaW := by
    rw [hcomponent_eq_x]
    exact hb_mem_component_x
  simpa [hcomponent_eq] using hb_mem_component

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: strict positivity on an open
witness component forces the left endpoint selector to be weakly nonnegative, and therefore the
left endpoint leaves the legal lens through the image condition. -/
lemma leftEndpointData_of_positiveComponent
    {g : ℂ → ℂ} {selectorθ : ℝ → ℝ} {zeta : ℝ → ℂ} {C₀ : Set ℝ}
    {a b thetaNeg thetaW : ℝ}
    (ha_lt_thetaW : a < thetaW)
    (hthetaW_lt_b : thetaW < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hselectorTheta_cont : Continuous selectorθ)
    (hposall : ∀ θ ∈ C₀, 0 < selectorθ θ)
    (hthetaNeg_le_a : thetaNeg ≤ a)
    (hselectorNeg : selectorθ thetaNeg < 0)
    (ha_not_mem_exercise16_of_lt : thetaNeg < a → g (zeta a) ∉ exercise16Domain) :
    0 ≤ selectorθ a ∧ g (zeta a) ∉ exercise16Domain := by
  have hab : a < b := lt_trans ha_lt_thetaW hthetaW_lt_b
  have hselector_a_nonneg : 0 ≤ selectorθ a := by
    by_contra hneg
    have hneg' : selectorθ a < 0 := lt_of_not_ge hneg
    rcases leftNeighborhood_lt_zero_of_continuous_of_lt
        (u := selectorθ) (a := a) (b := b) hab hselectorTheta_cont hneg' with
      ⟨η, hη_pos, hη_neg⟩
    let sigma : ℝ := (a + min (a + η) b) / 2
    have hsigma_mem_left : sigma ∈ Set.Ioo a (min (a + η) b) := by
      have hupper : a < min (a + η) b := by
        refine lt_min ?_ hab
        linarith
      constructor <;> dsimp [sigma] <;> linarith
    have hsigma_mem_C₀ : sigma ∈ C₀ := by
      rw [hC₀_eq]
      exact ⟨hsigma_mem_left.1, lt_of_lt_of_le hsigma_mem_left.2 (min_le_right _ _)⟩
    have hsigma_neg : selectorθ sigma < 0 := hη_neg sigma hsigma_mem_left
    linarith [hposall sigma hsigma_mem_C₀]
  have hthetaNeg_lt_a : thetaNeg < a := by
    by_contra hnot
    have heq : a = thetaNeg := le_antisymm (le_of_not_gt hnot) hthetaNeg_le_a
    have hnonneg : 0 ≤ selectorθ thetaNeg := by
      simpa [heq] using hselector_a_nonneg
    exact (not_lt_of_ge hnonneg) hselectorNeg
  exact ⟨hselector_a_nonneg, ha_not_mem_exercise16_of_lt hthetaNeg_lt_a⟩

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: strict negativity on an open
witness component forces the right endpoint selector to be weakly nonpositive, and therefore the
right endpoint leaves the legal lens through the image condition. -/
lemma rightEndpointData_of_negativeComponent
    {g : ℂ → ℂ} {selectorθ : ℝ → ℝ} {zeta : ℝ → ℂ} {C₀ : Set ℝ}
    {a b thetaPos thetaW : ℝ}
    (ha_lt_thetaW : a < thetaW)
    (hthetaW_lt_b : thetaW < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hselectorTheta_cont : Continuous selectorθ)
    (hnegall : ∀ θ ∈ C₀, selectorθ θ < 0)
    (hb_le_thetaPos : b ≤ thetaPos)
    (hselectorPos : 0 < selectorθ thetaPos)
    (hb_not_mem_exercise16_of_lt : b < thetaPos → g (zeta b) ∉ exercise16Domain) :
    selectorθ b ≤ 0 ∧ g (zeta b) ∉ exercise16Domain := by
  have hab : a < b := lt_trans ha_lt_thetaW hthetaW_lt_b
  have hselector_b_nonpos : selectorθ b ≤ 0 := by
    by_contra hpos
    have hpos' : 0 < selectorθ b := lt_of_not_ge hpos
    rcases rightNeighborhood_gt_zero_of_continuous_of_lt
        (u := selectorθ) (a := a) (b := b) hab hselectorTheta_cont hpos' with
      ⟨η, hη_pos, hη_pos_right⟩
    let sigma : ℝ := (max a (b - η) + b) / 2
    have hsigma_mem_right : sigma ∈ Set.Ioo (max a (b - η)) b := by
      have hlower : max a (b - η) < b := by
        refine max_lt hab ?_
        linarith
      constructor <;> dsimp [sigma] <;> linarith
    have hsigma_mem_C₀ : sigma ∈ C₀ := by
      rw [hC₀_eq]
      exact ⟨lt_of_le_of_lt (le_max_left _ _) hsigma_mem_right.1, hsigma_mem_right.2⟩
    have hsigma_pos : 0 < selectorθ sigma := hη_pos_right sigma hsigma_mem_right
    linarith [hnegall sigma hsigma_mem_C₀]
  have hb_lt_thetaPos : b < thetaPos := by
    by_contra hnot
    have heq : b = thetaPos := le_antisymm hb_le_thetaPos (le_of_not_gt hnot)
    have hnonpos : selectorθ thetaPos ≤ 0 := by
      simpa [heq] using hselector_b_nonpos
    exact (not_lt_of_ge hnonpos) hselectorPos
  exact ⟨hselector_b_nonpos, hb_not_mem_exercise16_of_lt hb_lt_thetaPos⟩

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on a positive witness
component, the left endpoint anchor lies on the unit circle for `g`, so its reciprocal logarithm
vanishes. -/
lemma positiveComponent_leftEndpointAnchor
    {g : ℂ → ℂ} {selectorθ : ℝ → ℝ} {zeta : ℝ → ℂ} {C₀ : Set ℝ}
    {a b thetaNeg thetaW : ℝ}
    (ha_lt_thetaW : a < thetaW)
    (hthetaW_lt_b : thetaW < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hselectorTheta_cont : Continuous selectorθ)
    (hselector_def : selectorθ = fun θ ↦ Real.log ‖g (zeta θ) / (1 - g (zeta θ))‖)
    (hposall : ∀ θ ∈ C₀, 0 < selectorθ θ)
    (hthetaNeg_le_a : thetaNeg ≤ a)
    (hselectorNeg : selectorθ thetaNeg < 0)
    (hg_nonzero_a : g (zeta a) ≠ 0)
    (hone_sub_nonzero_a : 1 - g (zeta a) ≠ 0)
    (ha_mem_closure_exercise16 : g (zeta a) ∈ closure exercise16Domain)
    (ha_not_mem_exercise16_of_lt : thetaNeg < a → g (zeta a) ∉ exercise16Domain) :
    Real.log ‖(g (zeta a))⁻¹‖ = 0 := by
  obtain ⟨hselector_a_nonneg, hga_not_mem⟩ :=
    leftEndpointData_of_positiveComponent
      (g := g) (selectorθ := selectorθ) (zeta := zeta) (C₀ := C₀)
      ha_lt_thetaW hthetaW_lt_b hC₀_eq hselectorTheta_cont hposall hthetaNeg_le_a
      hselectorNeg ha_not_mem_exercise16_of_lt
  have hga_norm_le : ‖g (zeta a)‖ ≤ 1 := by
    exact
      (norm_le_one_and_one_sub_norm_le_one_of_mem_closure_exercise16Domain
        ha_mem_closure_exercise16).1
  have hreal_ge_half : (1 : ℝ) / 2 ≤ (g (zeta a)).re := by
    have hselector_a_nonneg' :
        0 ≤ Real.log ‖g (zeta a) / (1 - g (zeta a))‖ := by
      simpa [hselector_def] using hselector_a_nonneg
    exact (selectorNonneg_iff_half_le_realPart hg_nonzero_a hone_sub_nonzero_a).mp
      hselector_a_nonneg'
  have hga_norm_ge : 1 ≤ ‖g (zeta a)‖ := by
    by_contra hlt
    have hga_norm_lt : ‖g (zeta a)‖ < 1 := lt_of_not_ge hlt
    have hone_sub_le :
        ‖1 - g (zeta a)‖ ≤ ‖g (zeta a)‖ :=
      (norm_one_sub_le_norm_iff_half_le_realPart).2 hreal_ge_half
    have hone_sub_lt : ‖1 - g (zeta a)‖ < 1 :=
      lt_of_le_of_lt hone_sub_le hga_norm_lt
    apply hga_not_mem
    constructor
    · simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hga_norm_lt
    · have hdist_eq : ‖g (zeta a) - 1‖ = ‖1 - g (zeta a)‖ := by
        simpa [sub_eq_add_neg] using norm_sub_rev (g (zeta a)) (1 : ℂ)
      have hdist_lt : ‖g (zeta a) - 1‖ < 1 := by
        rw [hdist_eq]
        exact hone_sub_lt
      simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hdist_lt
  have hga_norm_eq : ‖g (zeta a)‖ = 1 := le_antisymm hga_norm_le hga_norm_ge
  simpa [norm_inv, hga_norm_eq]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on a negative witness
component, the right endpoint anchor lies on the unit circle for `1 - g`, so its reciprocal
logarithm vanishes. -/
lemma negativeComponent_rightEndpointAnchor
    {g : ℂ → ℂ} {selectorθ : ℝ → ℝ} {zeta : ℝ → ℂ} {C₀ : Set ℝ}
    {a b thetaPos thetaW : ℝ}
    (ha_lt_thetaW : a < thetaW)
    (hthetaW_lt_b : thetaW < b)
    (hC₀_eq : C₀ = Set.Ioo a b)
    (hselectorTheta_cont : Continuous selectorθ)
    (hselector_def : selectorθ = fun θ ↦ Real.log ‖g (zeta θ) / (1 - g (zeta θ))‖)
    (hnegall : ∀ θ ∈ C₀, selectorθ θ < 0)
    (hb_le_thetaPos : b ≤ thetaPos)
    (hselectorPos : 0 < selectorθ thetaPos)
    (hg_nonzero_b : g (zeta b) ≠ 0)
    (hone_sub_nonzero_b : 1 - g (zeta b) ≠ 0)
    (hb_mem_closure_exercise16 : g (zeta b) ∈ closure exercise16Domain)
    (hb_not_mem_exercise16_of_lt : b < thetaPos → g (zeta b) ∉ exercise16Domain) :
    Real.log ‖((1 - g (zeta b))⁻¹)‖ = 0 := by
  obtain ⟨hselector_b_nonpos, hgb_not_mem⟩ :=
    rightEndpointData_of_negativeComponent
      (g := g) (selectorθ := selectorθ) (zeta := zeta) (C₀ := C₀)
      ha_lt_thetaW hthetaW_lt_b hC₀_eq hselectorTheta_cont hnegall hb_le_thetaPos
      hselectorPos hb_not_mem_exercise16_of_lt
  have hone_sub_norm_le : ‖1 - g (zeta b)‖ ≤ 1 := by
    exact
      (norm_le_one_and_one_sub_norm_le_one_of_mem_closure_exercise16Domain
        hb_mem_closure_exercise16).2
  have hreal_le_half : (g (zeta b)).re ≤ (1 : ℝ) / 2 := by
    have hselector_b_nonpos' :
        Real.log ‖g (zeta b) / (1 - g (zeta b))‖ ≤ 0 := by
      simpa [hselector_def] using hselector_b_nonpos
    exact (selectorNonpos_iff_realPart_le_half hg_nonzero_b hone_sub_nonzero_b).mp
      hselector_b_nonpos'
  have hone_sub_norm_ge : 1 ≤ ‖1 - g (zeta b)‖ := by
    by_contra hlt
    have hone_sub_norm_lt : ‖1 - g (zeta b)‖ < 1 := lt_of_not_ge hlt
    have hga_le : ‖g (zeta b)‖ ≤ ‖1 - g (zeta b)‖ :=
      (norm_le_norm_one_sub_iff_realPart_le_half).2 hreal_le_half
    have hga_norm_lt : ‖g (zeta b)‖ < 1 := lt_of_le_of_lt hga_le hone_sub_norm_lt
    apply hgb_not_mem
    constructor
    · simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hga_norm_lt
    · have hdist_eq : ‖g (zeta b) - 1‖ = ‖1 - g (zeta b)‖ := by
        simpa [sub_eq_add_neg] using norm_sub_rev (g (zeta b)) (1 : ℂ)
      have hdist_lt : ‖g (zeta b) - 1‖ < 1 := by
        rw [hdist_eq]
        exact hone_sub_norm_lt
      simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hdist_lt
  have hone_sub_norm_eq : ‖1 - g (zeta b)‖ = 1 :=
    le_antisymm hone_sub_norm_le hone_sub_norm_ge
  simpa [norm_inv, hone_sub_norm_eq]
