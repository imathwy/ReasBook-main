import Mathlib
import BauschkeLean.Chap01.Definition_1_8
import BauschkeLean.Chap02.Lemma_2_46
import BauschkeLean.Chap03.Corollary_3_38
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap11.Proposition_11_5
import BauschkeLean.Chap11.Proposition_11_15
import BauschkeLean.Chap11.Proposition_11_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

namespace Set

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Helper for Proposition 11 31: a closed midpoint-stable subset of `ℝ` is order-connected. -/
private theorem ordConnected_of_isClosed_of_midpoint_mem {s : Set ℝ}
    (hs_closed : IsClosed s)
    (hmid : ∀ ⦃x y : ℝ⦄, x ∈ s → y ∈ s → midpoint ℝ x y ∈ s) :
    s.OrdConnected := by
  -- Work on an ordered interval first; the unordered case follows by swapping endpoints.
  have hIcc :
      ∀ ⦃a b x : ℝ⦄, a ∈ s → b ∈ s → a ≤ b → x ∈ Set.Icc a b → x ∈ s := by
    intro a b x ha hb hab hx
    by_cases hxs : x ∈ s
    · exact hxs
    -- Route correction: instead of dyadic approximation, isolate the maximal feasible point on the
    -- left and the minimal feasible point on the right, then contradict midpoint stability.
    have hleft_nonempty : (s ∩ Set.Icc a x).Nonempty := by
      refine ⟨a, ha, ?_⟩
      exact ⟨le_rfl, hx.1⟩
    have hright_nonempty : (s ∩ Set.Icc x b).Nonempty := by
      refine ⟨b, hb, ?_⟩
      exact ⟨hx.2, le_rfl⟩
    have hleft_compact : IsCompact (s ∩ Set.Icc a x) :=
      by simpa [Set.inter_comm] using isCompact_Icc.inter_right hs_closed
    have hright_compact : IsCompact (s ∩ Set.Icc x b) :=
      by simpa [Set.inter_comm] using isCompact_Icc.inter_right hs_closed
    obtain ⟨c, hcGreat⟩ := hleft_compact.exists_isGreatest hleft_nonempty
    obtain ⟨d, hdLeast⟩ := hright_compact.exists_isLeast hright_nonempty
    have hc_mem : c ∈ s := hcGreat.1.1
    have hc_Icc : c ∈ Set.Icc a x := hcGreat.1.2
    have hd_mem : d ∈ s := hdLeast.1.1
    have hd_Icc : d ∈ Set.Icc x b := hdLeast.1.2
    have hc_lt_x : c < x := by
      refine lt_of_le_of_ne hc_Icc.2 fun hcx ↦ ?_
      exact hxs (hcx ▸ hc_mem)
    have hx_lt_d : x < d := by
      refine lt_of_le_of_ne hd_Icc.1 fun hxd ↦ ?_
      exact hxs (hxd ▸ hd_mem)
    have hcd : c < d := lt_trans hc_lt_x hx_lt_d
    have hmid_mem : midpoint ℝ c d ∈ s := hmid hc_mem hd_mem
    have hmid_Ioo : midpoint ℝ c d ∈ Set.Ioo c d := by
      exact (openSegment_subset_Ioo hcd) (midpoint_mem_openSegment c d)
    by_cases hmid_le_x : midpoint ℝ c d ≤ x
    · -- The midpoint would lie to the left of `x`, contradicting maximality of `c`.
      have hmid_left : midpoint ℝ c d ∈ s ∩ Set.Icc a x := by
        refine ⟨hmid_mem, ?_⟩
        exact ⟨le_trans hc_Icc.1 hmid_Ioo.1.le, hmid_le_x⟩
      exact False.elim <| (not_le_of_gt hmid_Ioo.1) (hcGreat.2 hmid_left)
    · -- The midpoint lies to the right of `x`, contradicting minimality of `d`.
      have hx_lt_mid : x < midpoint ℝ c d := lt_of_not_ge hmid_le_x
      have hmid_right : midpoint ℝ c d ∈ s ∩ Set.Icc x b := by
        refine ⟨hmid_mem, ?_⟩
        exact ⟨hx_lt_mid.le, le_trans hmid_Ioo.2.le hd_Icc.2⟩
      exact False.elim <| (not_le_of_gt hmid_Ioo.2) (hdLeast.2 hmid_right)
  rw [ordConnected_iff_uIcc_subset]
  intro a ha b hb x hx
  rcases le_total a b with hab | hba
  · exact hIcc ha hb hab (by simpa [uIcc_of_le hab] using hx)
  · exact hIcc hb ha hba (by simpa [uIcc_of_ge hba] using hx)

/-- Helper for Proposition 11 31: a closed set is convex once every chord midpoint stays inside
it. -/
private theorem convex_of_isClosed_of_midpoint_mem {C : Set H} (hC_closed : IsClosed C)
    (hmid : ∀ ⦃x y : H⦄, x ∈ C → y ∈ C → midpoint ℝ x y ∈ C) :
    Convex ℝ C := by
  rw [convex_iff_segment_subset]
  intro x hx y hy z hz
  -- Pull the chord back to a closed midpoint-stable subset of `ℝ`.
  rw [segment_eq_image_lineMap] at hz
  rcases hz with ⟨t, ht, rfl⟩
  let S : Set ℝ := {r : ℝ | AffineMap.lineMap x y r ∈ C}
  have hS_closed : IsClosed S := by
    -- Closedness of `C` transfers along the affine chord map.
    simpa [S] using hC_closed.preimage (AffineMap.lineMap_continuous (p := x) (q := y))
  have hS_mid : ∀ ⦃a b : ℝ⦄, a ∈ S → b ∈ S → midpoint ℝ a b ∈ S := by
    intro a b ha hb
    -- Midpoints commute with the affine chord map.
    have hmap :
        AffineMap.lineMap x y (midpoint ℝ a b) =
          midpoint ℝ (AffineMap.lineMap x y a) (AffineMap.lineMap x y b) := by
      exact (AffineMap.lineMap x y).map_midpoint a b
    simpa [S, hmap] using hmid ha hb
  have hS_ord : S.OrdConnected :=
    ordConnected_of_isClosed_of_midpoint_mem hS_closed hS_mid
  have hS_zero : (0 : ℝ) ∈ S := by
    simpa [S] using hx
  have hS_one : (1 : ℝ) ∈ S := by
    simpa [S] using hy
  exact hS_ord.out hS_zero hS_one ht

/-- Helper for Proposition 11 31: convexity plus interior midpoints upgrades to strict convexity.
-/
private theorem strictConvex_of_convex_of_midpoint_mem_interior {C : Set H}
    (hC_convex : Convex ℝ C)
    (hmid : ∀ ⦃x y : H⦄, x ∈ C → y ∈ C → x ≠ y → midpoint ℝ x y ∈ interior C) :
    StrictConvex ℝ C := by
  -- Feed the midpoint witness into mathlib's canonical strict-convexity criterion.
  refine hC_convex.strictConvex' ?_
  intro x hx y hy hxy
  refine ⟨(1 / 2 : ℝ), ?_⟩
  simpa [lineMap_one_half] using hmid hx.1 hy.1 hxy

/-- A set `C` is uniformly convex when it admits a monotone modulus, vanishing only at `0`, such
that for any two points of `C`, the closed ball centered at their midpoint with radius determined
by the distance between them is still contained in `C`. -/
def UniformlyConvex (C : Set H) : Prop :=
  ∃ φ : NNReal → NNReal,
    Monotone φ ∧
    (∀ r : NNReal, φ r = 0 ↔ r = 0) ∧
    ∀ ⦃x y : H⦄, x ∈ C → y ∈ C →
      Metric.closedBall (midpoint ℝ x y) (φ ‖x - y‖₊) ⊆ C

/-- The midpoint of two points of a uniformly convex set remains in the set. -/
theorem UniformlyConvex.midpoint_mem {C : Set H} (hC : UniformlyConvex C) {x y : H}
    (hx : x ∈ C) (hy : y ∈ C) :
    midpoint ℝ x y ∈ C := by
  rcases hC with ⟨φ, _, _, hφ⟩
  exact hφ hx hy <|
    Metric.mem_closedBall_self
      (show 0 ≤ ((φ ‖x - y‖₊ : NNReal) : ℝ) from (φ ‖x - y‖₊).2)

/-- Distinct points of a uniformly convex set have midpoint in the interior. This is the atomic
bridge from the source-facing midpoint-ball condition to the canonical convexity API. -/
theorem UniformlyConvex.midpoint_mem_interior {C : Set H} (hC : UniformlyConvex C) {x y : H}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    midpoint ℝ x y ∈ interior C := by
  rcases hC with ⟨φ, _, hφ_zero, hφ⟩
  rw [mem_interior_iff_mem_nhds]
  have hφ_pos : 0 < φ ‖x - y‖₊ := by
    refine pos_iff_ne_zero.mpr fun hφr ↦ ?_
    exact hxy <| sub_eq_zero.mp <| by
      rw [← nnnorm_eq_zero, ← (hφ_zero _).mp hφr]
  refine mem_of_superset (Metric.ball_mem_nhds _ (by exact_mod_cast hφ_pos)) ?_
  intro z hz
  exact hφ hx hy (Metric.ball_subset_closedBall hz)

/-- A closed uniformly convex set is convex. -/
theorem UniformlyConvex.convex_of_isClosed {C : Set H} (hC : UniformlyConvex C)
    (hC_closed : IsClosed C) :
    Convex ℝ C := by
  -- The source midpoint-ball condition already implies midpoint closure.
  exact convex_of_isClosed_of_midpoint_mem hC_closed
    (fun {x y} hx hy ↦ hC.midpoint_mem (x := x) (y := y) hx hy)

/-- A closed uniformly convex set is strictly convex. -/
theorem UniformlyConvex.strictConvex_of_isClosed {C : Set H} (hC : UniformlyConvex C)
    (hC_closed : IsClosed C) :
    StrictConvex ℝ C := by
  -- The interior midpoint witness is the exact hypothesis expected by `Convex.strictConvex'`.
  exact strictConvex_of_convex_of_midpoint_mem_interior
    (hC.convex_of_isClosed hC_closed)
    (fun {x y} hx hy hxy ↦ hC.midpoint_mem_interior (x := x) (y := y) hx hy hxy)

/-- Helper for Proposition 11 31: a uniform-convexity radius at distance `ε` produces an inner-core
witness at the midpoint of any pair of points that are at least `ε` apart. -/
private theorem midpoint_mem_inner_core_of_uniformlyConvex_of_dist_lower_bound
    {C : Set H} {φ : NNReal → NNReal} (hφ_mono : Monotone φ)
    (hφ_ball : ∀ ⦃u v : H⦄, u ∈ C → v ∈ C →
      Metric.closedBall (midpoint ℝ u v) (φ ‖u - v‖₊) ⊆ C)
    {ε : ℝ} (hε : 0 < ε) {x y : H} (hx : x ∈ C) (hy : y ∈ C)
    (hεdist : ε ≤ dist x y) :
    midpoint ℝ x y ∈ {z : H | Metric.ball z (((φ ⟨ε, hε.le⟩ : NNReal) : ℝ)) ⊆ C} := by
  intro z hz
  have hε_le_norm : ε ≤ ‖x - y‖ := by
    simpa [dist_eq_norm] using hεdist
  have hεnn_le : (⟨ε, hε.le⟩ : NNReal) ≤ ‖x - y‖₊ := by
    exact_mod_cast hε_le_norm
  have hφ_le : φ ⟨ε, hε.le⟩ ≤ φ ‖x - y‖₊ := hφ_mono hεnn_le
  exact hφ_ball hx hy <| by
    rw [Metric.mem_closedBall]
    exact le_trans (le_of_lt hz) (by exact_mod_cast hφ_le)

omit [NormedSpace ℝ H] in
/-- Helper for Proposition 11 31: the inner core `{z | ball z δ ⊆ C}` is closed because it is the
intersection of the distance halfspaces from points outside `C`. -/
private theorem isClosed_inner_core {C : Set H} {δ : ℝ} :
    IsClosed {z : H | Metric.ball z δ ⊆ C} := by
  have hrepr :
      {z : H | Metric.ball z δ ⊆ C} =
        ⋂ y : H, ⋂ hy : y ∉ C, {z : H | δ ≤ dist z y} := by
    ext z
    constructor
    · intro hz
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro y hy
      refine le_of_not_gt fun hyz ↦ ?_
      exact hy (hz (by simpa [Metric.mem_ball, dist_comm] using hyz))
    · intro hz
      have hz' : ∀ y, y ∉ C → δ ≤ dist z y := by
        simpa only [Set.mem_iInter, Set.mem_setOf_eq] using hz
      intro y hyball
      by_contra hyC
      have hδ : δ ≤ dist z y := by
        exact hz' y hyC
      exact (not_lt_of_ge hδ) (by simpa [Metric.mem_ball, dist_comm] using hyball)
  rw [hrepr]
  refine isClosed_iInter fun y ↦ ?_
  refine isClosed_iInter fun _ ↦ ?_
  exact isClosed_le continuous_const (continuous_id.dist continuous_const)

/-- Helper for Proposition 11 31: the inner core of a convex set is midpoint-stable. -/
private theorem midpoint_mem_inner_core_of_convex {C : Set H} {δ : ℝ}
    (hC_convex : Convex ℝ C) {z₁ z₂ : H}
    (hz₁ : Metric.ball z₁ δ ⊆ C) (hz₂ : Metric.ball z₂ δ ⊆ C) :
    Metric.ball (midpoint ℝ z₁ z₂) δ ⊆ C := by
  intro w hw
  let t : H := w - midpoint ℝ z₁ z₂
  let u : H := z₁ + t
  let v : H := z₂ + t
  have hu : u ∈ C := by
    apply hz₁
    rw [Metric.mem_ball, dist_eq_norm]
    have hu_sub : u - z₁ = w - midpoint ℝ z₁ z₂ := by
      dsimp [u, t]
      abel_nf
    rw [hu_sub]
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hv : v ∈ C := by
    apply hz₂
    rw [Metric.mem_ball, dist_eq_norm]
    have hv_sub : v - z₂ = w - midpoint ℝ z₁ z₂ := by
      dsimp [v, t]
      abel_nf
    rw [hv_sub]
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hmid : midpoint ℝ u v ∈ C := hC_convex.midpoint_mem hu hv
  have hmid_translate : midpoint ℝ u v = midpoint ℝ z₁ z₂ + t := by
    simpa [u, v, vadd_eq_add, add_comm, add_left_comm, add_assoc] using
      (midpoint_vadd_midpoint (R := ℝ) t t z₁ z₂).symm
  have hmid_eq : midpoint ℝ u v = w := by
    simpa [t, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmid_translate
  simpa [hmid_eq] using hmid

omit [NormedSpace ℝ H] in
/-- Helper for Proposition 11 31: membership in a positive-radius inner core places the center in
the interior. -/
private theorem mem_interior_of_mem_inner_core {C : Set H} {δ : ℝ} {z : H}
    (hδ : 0 < δ) (hz : Metric.ball z δ ⊆ C) :
    z ∈ interior C := by
  rw [mem_interior_iff_mem_nhds]
  exact mem_of_superset (Metric.ball_mem_nhds z hδ) hz

end

end Set

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem mem_constraint_inter_effectiveDomain_of_add_indicator
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {xₙ : ℕ → H}
    (hxₙ : IsMinimizingSequence (f.asEReal + (ι[C]).asEReal) xₙ) (n : ℕ) :
    xₙ n ∈ C ∩ effectiveDomain f := by
  have hxdom : xₙ n ∈ dom (f.asEReal + (ι[C]).asEReal) := hxₙ.mem_dom n
  rw [mem_dom_iff_ne_top] at hxdom
  by_cases hxC : xₙ n ∈ C
  · refine ⟨hxC, ?_⟩
    rw [mem_effectiveDomain_iff, lt_top_iff_ne_top]
    simpa [hxC] using hxdom
  · have hbot : (f (xₙ n) : EReal) ≠ ⊥ := ne_of_gt (f (xₙ n)).2
    exact (hxdom (by simp [hxC, hbot])).elim

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem nonempty_constraint_inter_effectiveDomain_of_add_indicator
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {xₙ : ℕ → H}
    (hxₙ : IsMinimizingSequence (f.asEReal + (ι[C]).asEReal) xₙ) :
    (C ∩ effectiveDomain f).Nonempty :=
  ⟨xₙ 0, mem_constraint_inter_effectiveDomain_of_add_indicator hxₙ 0⟩

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 31: any constrained minimizer is finite once the constraint set
contains one feasible finite point. -/
private theorem mem_effectiveDomain_of_mem_argminOn_of_nonempty_inter_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {x : H}
    (hx : x ∈ Argmin[C] f.asEReal) (hfeas : (C ∩ effectiveDomain f).Nonempty) :
    x ∈ effectiveDomain f := by
  rcases mem_argminOn_iff.mp hx with ⟨_, hxmin⟩
  rcases hfeas with ⟨z, hzC, hz_dom⟩
  -- Compare the minimizer value against one feasible finite point.
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt ((isMinOn_iff.mp hxmin) z hzC) (mem_effectiveDomain_iff.mp hz_dom)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 31: reindexing a minimizing sequence by a strictly monotone map
preserves the minimizing-sequence property. -/
private theorem minimizingSequence_comp_strictMono
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsMinimizingSequence f (fun n ↦ xₙ (φ n)) := by
  -- The subsequence stays in the domain termwise, and its values keep the same limit.
  constructor
  · intro n
    exact hxₙ.mem_dom (φ n)
  · simpa [Function.comp] using hxₙ.tendsto.comp hφ.tendsto_atTop

omit [CompleteSpace H] in
/-- Helper for Proposition 11 31: the midpoint of a constrained minimizer and any feasible finite
point has objective value bounded by the feasible point value. -/
private theorem midpoint_value_le_right_of_mem_argminOn
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {x y : H}
    (hconv : ConvexOn f (effectiveDomain f))
    (hx : x ∈ Argmin[C] f.asEReal) (hx_dom : x ∈ effectiveDomain f)
    (hyC : y ∈ C) (hy_dom : y ∈ effectiveDomain f) :
    (f (midpoint ℝ x y) : EReal) ≤ f y := by
  rcases hconv with ⟨_, hconv_ineq⟩
  rcases mem_argminOn_iff.mp hx with ⟨_, hxmin⟩
  have hhalf_pos : 0 < (⅟2 : ℝ) := invOf_pos.mpr two_pos
  have hhalf_lt_one : (⅟2 : ℝ) < 1 := invOf_lt_one one_lt_two
  have hmid_le_avg :
      (f (midpoint ℝ x y) : EReal) ≤
        ((⅟2 : ℝ) : EReal) * (f x : EReal) + ((⅟2 : ℝ) : EReal) * (f y : EReal) := by
    have hineq := hconv_ineq.2 hx_dom hy_dom hhalf_pos hhalf_lt_one
    have hone_sub_half :
        (1 - ((⅟2 : ℝ) : EReal)) = ((⅟2 : ℝ) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal)) (one_sub_invOf_two : (1 - (⅟2 : ℝ)) = (⅟2 : ℝ))
    have hineq_half :
        (f ((⅟2 : ℝ) • x + (⅟2 : ℝ) • y) : EReal) ≤
          (((⅟2 : ℝ) : EReal) * (f x : EReal) + ((⅟2 : ℝ) : EReal) * (f y : EReal)) := by
      have hineq' :=
        (show
          (f ((⅟2 : ℝ) • x + (1 - (⅟2 : ℝ)) • y) : EReal) ≤
            (((⅟2 : ℝ) : EReal) * (f x : EReal) + (1 - ((⅟2 : ℝ) : EReal)) * (f y : EReal)) from
          hineq)
      rw [hone_sub_half] at hineq'
      rw [one_sub_invOf_two] at hineq'
      exact hineq'
    simpa [midpoint_eq_smul_add, smul_add] using hineq_half
  have hxy_le : (f x : EReal) ≤ f y := (isMinOn_iff.mp hxmin) y hyC
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx_dom)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom)
  have hx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hxy_le_real : (f x : EReal).toReal ≤ (f y : EReal).toReal :=
    EReal.toReal_le_toReal hxy_le hx_bot hy_top
  have havg_le_right :
      ((⅟2 : ℝ) : EReal) * (f x : EReal) + ((⅟2 : ℝ) : EReal) * (f y : EReal) ≤
        (f y : EReal) := by
    rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_toReal hy_top hy_bot]
    have hreal :
        (⅟2 : ℝ) * (f x : EReal).toReal + (⅟2 : ℝ) * (f y : EReal).toReal ≤
          (f y : EReal).toReal := by
      have hmul :
          (⅟2 : ℝ) * (f x : EReal).toReal ≤ (⅟2 : ℝ) * (f y : EReal).toReal := by
        nlinarith [hxy_le_real]
      calc
        (⅟2 : ℝ) * (f x : EReal).toReal + (⅟2 : ℝ) * (f y : EReal).toReal ≤
            (⅟2 : ℝ) * (f y : EReal).toReal + (⅟2 : ℝ) * (f y : EReal).toReal :=
          add_le_add hmul le_rfl
        _ = (f y : EReal).toReal := by
          simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using
            (invOf_two_smul_add_invOf_two_smul ℝ ((f y : EReal).toReal))
    exact_mod_cast hreal
  calc
    (f (midpoint ℝ x y) : EReal) ≤
        ((⅟2 : ℝ) : EReal) * (f x : EReal) + ((⅟2 : ℝ) : EReal) * (f y : EReal) :=
      hmid_le_avg
    _ ≤ (f y : EReal) := havg_le_right

omit [CompleteSpace H] in
/-- Helper for Proposition 11 31: disjointness from the global argmin and strict convexity force
the constrained argmin set to be a subsingleton. -/
private theorem argminOn_subsingleton_of_disjoint_argmin_of_strictConvex
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hconv : ConvexOn f (effectiveDomain f))
    (hdisjoint : Disjoint C (Argmin f.asEReal))
    (hC_dom : (C ∩ effectiveDomain f).Nonempty)
    (hstrictC : StrictConvex ℝ C) :
    (Argmin[C] f.asEReal).Subsingleton := by
  intro x hx y hy
  by_cases hxy : x = y
  · exact hxy
  have hxC : x ∈ C := mem_of_mem_argminOn hx
  have hyC : y ∈ C := mem_of_mem_argminOn hy
  have hx_dom : x ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_argminOn_of_nonempty_inter_effectiveDomain hx hC_dom
  have hy_dom : y ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_argminOn_of_nonempty_inter_effectiveDomain hy hC_dom
  have hhalf_pos : 0 < (⅟2 : ℝ) := invOf_pos.mpr two_pos
  have hhalf_nonneg : 0 ≤ (⅟2 : ℝ) := hhalf_pos.le
  have hhalf_sum : (⅟2 : ℝ) + (⅟2 : ℝ) = 1 := by
    simpa using (invOf_two_add_invOf_two (R := ℝ))
  let m : H := midpoint ℝ x y
  have hmC : m ∈ C := by
    simpa [m, midpoint_eq_smul_add, smul_add] using
      hstrictC.convex hxC hyC hhalf_nonneg hhalf_nonneg hhalf_sum
  have hm_dom : m ∈ effectiveDomain f := by
    simpa [m, midpoint_eq_smul_add, smul_add] using
      hconv.convex_effectiveDomain hx_dom hy_dom hhalf_nonneg hhalf_nonneg hhalf_sum
  have hm_argminOn : m ∈ Argmin[C] f.asEReal := by
    refine mem_argminOn_iff.mpr ⟨hmC, ?_⟩
    rw [isMinOn_iff]
    intro z hzC
    calc
      (f m : EReal) ≤ f y := by
        simpa [m] using midpoint_value_le_right_of_mem_argminOn hconv hx hx_dom hyC hy_dom
      _ ≤ f z := (isMinOn_iff.mp (mem_argminOn_iff.mp hy).2) z hzC
  have hm_int : m ∈ interior C := by
    simpa [m, midpoint_eq_smul_add, smul_add] using
      hstrictC hxC hyC hxy hhalf_pos hhalf_pos hhalf_sum
  have hm_argmin : m ∈ Argmin f.asEReal := by
    exact mem_argmin_of_mem_argminOn_of_mem_interior_of_convexOn_effectiveDomain
      f hconv hm_dom hm_argminOn hm_int
  exact False.elim <| Set.disjoint_left.mp hdisjoint hmC hm_argmin

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 31: a pointwise lower bound along a bad subsequence passes to the
constrained minimizer value of the indicator-augmented objective. -/
private theorem le_of_subsequence_pointwise_bound_of_isMinimizingSequence_add_indicator
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {xₙ : ℕ → H} {φ : ℕ → ℕ}
    {x : H} {a : EReal}
    (hxₙ : IsMinimizingSequence (f.asEReal + (ι[C]).asEReal) xₙ)
    (hφ : StrictMono φ) (hx : x ∈ Argmin[C] f.asEReal)
    (hbound : ∀ n, a ≤ f (xₙ (φ n))) :
    a ≤ f x := by
  let g : H → EReal := f.asEReal + (ι[C]).asEReal
  have hbot : ∀ y ∉ C, f.asEReal y ≠ ⊥ := by
    intro y hyC
    exact ne_of_gt (f y).2
  have hxg : x ∈ Argmin g := by
    -- Rewrite the constrained argmin statement as a global argmin of the indicator objective.
    have hx_on : x ∈ Argmin[C] f.asEReal := hx
    rw [argminOn_eq_inter_argmin_add_indicator f.asEReal C hbot] at hx_on
    simpa [g] using hx_on.2
  have hsub : IsMinimizingSequence g (fun n ↦ xₙ (φ n)) :=
    minimizingSequence_comp_strictMono hxₙ hφ
  have hpointwise :
      ∀ n, a ≤ (g ∘ fun n ↦ xₙ (φ n)) n := by
    intro n
    have hmemC : xₙ (φ n) ∈ C :=
      (mem_constraint_inter_effectiveDomain_of_add_indicator hxₙ (φ n)).1
    simpa [g, Function.comp, add_indicator_apply, indicator_apply, hmemC] using hbound n
  have hsub_tendsto :
      Tendsto (g ∘ fun n ↦ xₙ (φ n)) atTop (𝓝 (g x)) := by
    simpa [(mem_argmin_iff_eq_sInf).1 hxg] using hsub.tendsto
  have hconst : Tendsto (fun _ : ℕ ↦ a) atTop (𝓝 a) := tendsto_const_nhds
  have hle : a ≤ g x :=
    le_of_tendsto_of_tendsto' hconst hsub_tendsto hpointwise
  have hxC : x ∈ C := (mem_argminOn_iff.mp hx).1
  -- Evaluate the indicator objective at the constrained minimizer.
  simpa [g, add_indicator_apply, indicator_apply, hxC] using hle

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 31: if the indicator augmentation has no `⊥ + ⊤` ambiguity outside
`C`, then its lower level sets are exactly the feasible lower level sets. -/
private theorem lowerLevelSet_add_indicator_eq_inter
    {f : H → EReal} {C : Set H} (hbot : ∀ x ∉ C, f x ≠ ⊥) {η : ℝ} :
    lowerLevelSet (f + (ι[C]).asEReal) η = C ∩ lowerLevelSet f η := by
  -- The indicator contributes `⊤` off the constraint and vanishes on the constraint.
  ext x
  constructor
  · intro hx
    by_cases hxC : x ∈ C
    · refine ⟨hxC, ?_⟩
      simpa [mem_lowerLevelSet_iff, add_indicator_apply, indicator_apply, hxC] using hx
    · have hxle : (f + (ι[C]).asEReal) x ≤ (η : EReal) :=
        (mem_lowerLevelSet_iff (f + (ι[C]).asEReal) η x).1 hx
      have htop : (f + (ι[C]).asEReal) x = ⊤ := by
        simp [indicator_apply, hxC, EReal.add_top_of_ne_bot (hbot x hxC)]
      have : ¬ ((⊤ : EReal) ≤ (η : EReal)) := by
        simp
      rw [htop] at hxle
      exact False.elim <| this hxle
  · rintro ⟨hxC, hxlevel⟩
    refine (mem_lowerLevelSet_iff (f + (ι[C]).asEReal) η x).2 ?_
    simpa [mem_lowerLevelSet_iff, add_indicator_apply, indicator_apply, hxC] using
      (mem_lowerLevelSet_iff f η x).1 hxlevel

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 11 31: adding the indicator of a closed set preserves lower
semicontinuity once `⊥ + ⊤` is excluded outside the set. -/
private theorem lowerSemicontinuous_add_indicator_of_isClosed
    {f : H → EReal} {C : Set H} (hf_lsc : LowerSemicontinuous f) (hC_closed : IsClosed C)
    (hbot : ∀ x ∉ C, f x ≠ ⊥) :
    LowerSemicontinuous (f + (ι[C]).asEReal) := by
  -- Closed lower level sets are stable under intersection with the closed constraint set.
  rw [lowerSemicontinuous_iff_isClosed_lowerLevelSet]
  intro η
  rw [lowerLevelSet_add_indicator_eq_inter hbot]
  exact hC_closed.inter ((lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1 hf_lsc η)

omit [CompleteSpace H] in
/-- Helper for Proposition 11 31: the indicator-augmented objective inherits quasiconvexity from
`f ∈ Γ₀(H)` and convexity of the constraint set. -/
private theorem quasiconvexOn_univ_add_indicator_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {C : Set H} (hC_convex : Convex ℝ C) :
    QuasiconvexOn ℝ Set.univ (f.asEReal + (ι[C]).asEReal) := by
  -- Rewrite every lower level set of the indicator objective as the intersection of two convex
  -- sets, namely `C` and a lower level set of `f`.
  rw [quasiconvexOn_univ_iff_convex_lowerLevelSet ℝ]
  intro η
  have hbot : ∀ x ∉ C, f.asEReal x ≠ ⊥ := by
    intro x hxC
    exact ne_of_gt (f x).2
  rw [lowerLevelSet_add_indicator_eq_inter hbot]
  exact hC_convex.inter (convex_lowerLevelSet_asEReal_of_mem_gammaZero hf η)

omit [CompleteSpace H] in
/-- Helper for Proposition 11 31: every weak sequential cluster point of a sequence in a closed
convex set stays inside that set. -/
private theorem mem_of_weakSequentialClusterPt_of_isClosed_convex {C : Set H}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {u : ℕ → H} (hu : ∀ n, u n ∈ C)
    {x : H}
    (hx : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (u n)) (toWeakSpace ℝ H x)) :
    x ∈ C := by
  -- Weak closedness of closed convex sets captures the subsequential weak limit.
  have hweakClosed : IsClosed ((toWeakSpace ℝ H) '' C) :=
    (isClosed_iff_weak_image_isClosed_of_convex hC_convex).1 hC_closed
  rcases hx.exists_subseq_tendsto with ⟨φ, hφ, hφx⟩
  have hsubseq_mem :
      ∀ n, toWeakSpace ℝ H (u (φ n)) ∈ (toWeakSpace ℝ H) '' C := by
    intro n
    exact ⟨u (φ n), hu (φ n), rfl⟩
  have hx_mem : toWeakSpace ℝ H x ∈ closure ((toWeakSpace ℝ H) '' C) :=
    mem_closure_of_tendsto hφx (Filter.Eventually.of_forall hsubseq_mem)
  rw [hweakClosed.closure_eq] at hx_mem
  rcases hx_mem with ⟨y, hyC, hyx⟩
  exact (toWeakSpace ℝ H).injective hyx ▸ hyC

omit [CompleteSpace H] in
/-- Helper for Proposition 11 31: every weak sequential cluster point of the constrained
minimizing sequence is already a constrained minimizer. -/
private theorem weakSequentialClusterPt_mem_argminOn_of_isMinimizingSequence_add_indicator
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {C : Set H}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {xₙ : ℕ → H}
    (hxₙ : IsMinimizingSequence (f.asEReal + (ι[C]).asEReal) xₙ)
    {x : H}
    (hx : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x)) :
    x ∈ Argmin[C] f.asEReal := by
  let g : H → EReal := f.asEReal + (ι[C]).asEReal
  have hbot : ∀ y ∉ C, f.asEReal y ≠ ⊥ := by
    intro y hyC
    exact ne_of_gt (f y).2
  have hxCseq : ∀ n, xₙ n ∈ C := by
    intro n
    exact (mem_constraint_inter_effectiveDomain_of_add_indicator hxₙ n).1
  have hxC : x ∈ C :=
    mem_of_weakSequentialClusterPt_of_isClosed_convex hC_closed hC_convex hxCseq hx
  have hg_lsc : LowerSemicontinuous g :=
    lowerSemicontinuous_add_indicator_of_isClosed hf.1 hC_closed hbot
  have hg_quasi : QuasiconvexOn ℝ Set.univ g :=
    quasiconvexOn_univ_add_indicator_of_mem_gammaZero hf hC_convex
  rcases hx.exists_subseq_tendsto with ⟨φ, hφ, hφx⟩
  have hsub : IsMinimizingSequence g (fun n ↦ xₙ (φ n)) :=
    minimizingSequence_comp_strictMono hxₙ hφ
  have hxg : x ∈ Argmin g :=
    mem_argmin_of_isMinimizingSequence_of_tendsto_weakly_of_quasiconvexOn_univ
      hg_quasi hg_lsc hsub hφx
  -- Rewrite the constrained argmin set as feasible global minimizers of the indicator objective.
  rw [argminOn_eq_inter_argmin_add_indicator f.asEReal C hbot]
  exact ⟨hxC, hxg⟩

/-- Helper for Proposition 11 31: the constrained minimizing sequence has a weak limit in the
constrained argmin set, and that weak limit is unique because the constrained argmin set is a
subsingleton. -/
private theorem exists_mem_argminOn_and_tendsto_toWeakSpace_of_isMinimizingSequence_add_indicator
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {C : Set H}
    (hC_bounded : Bornology.IsBounded C) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hC_disjoint : Disjoint C (Argmin f.asEReal))
    (hC_strictConvex : StrictConvex ℝ C) {xₙ : ℕ → H}
    (hxₙ : IsMinimizingSequence (f.asEReal + (ι[C]).asEReal) xₙ) :
    ∃ x ∈ Argmin[C] f.asEReal,
      Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x)) := by
  have hseq_mem : ∀ n, xₙ n ∈ C := by
    intro n
    exact (mem_constraint_inter_effectiveDomain_of_add_indicator hxₙ n).1
  have hrange_bounded : Bornology.IsBounded (Set.range xₙ) :=
    hC_bounded.subset (fun y hy ↦ by
      rcases hy with ⟨n, rfl⟩
      exact hseq_mem n)
  have hargmin_subsingleton : (Argmin[C] f.asEReal).Subsingleton :=
    argminOn_subsingleton_of_disjoint_argmin_of_strictConvex hf.2 hC_disjoint
      (nonempty_constraint_inter_effectiveDomain_of_add_indicator hxₙ) hC_strictConvex
  have hunique :
      ∀ y z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H y) →
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H z) →
        y = z := by
    intro y z hy hz
    have hy_arg : y ∈ Argmin[C] f.asEReal :=
      weakSequentialClusterPt_mem_argminOn_of_isMinimizingSequence_add_indicator
        hf hC_closed hC_convex hxₙ hy
    have hz_arg : z ∈ Argmin[C] f.asEReal :=
      weakSequentialClusterPt_mem_argminOn_of_isMinimizingSequence_add_indicator
        hf hC_closed hC_convex hxₙ hz
    exact hargmin_subsingleton hy_arg hz_arg
  rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint xₙ).2
      ⟨hrange_bounded, hunique⟩ with ⟨x, hxweak⟩
  have hxcluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x) := by
    -- The convergent full sequence is its own witnessing subsequence.
    refine ⟨fun n ↦ n, fun _ _ h ↦ h, ?_⟩
    simpa [Function.comp] using hxweak
  have hxarg : x ∈ Argmin[C] f.asEReal :=
    weakSequentialClusterPt_mem_argminOn_of_isMinimizingSequence_add_indicator
      hf hC_closed hC_convex hxₙ hxcluster
  exact ⟨x, hxarg, hxweak⟩

-- Proof sketch: Proposition 11.15 gives existence of a minimizer on the bounded closed convex set
-- `C`, with convexity coming from the midpoint-ball uniform convexity hypothesis and feasibility
-- coming from the minimizing sequence itself. Proposition 11.8 upgrades the disjointness from
-- `Argmin f` and the induced strict convexity to uniqueness over `C`. Proposition 11.29 yields
-- weak convergence of the minimizing sequence to that unique minimizer, and the midpoint-ball
-- modulus then upgrades weak convergence to norm convergence.
/-- Proposition 11 31: if `f ∈ Γ₀(H)`, `C` is bounded, closed, disjoint from `Argmin f`, and
uniformly convex in the source-facing midpoint-ball sense (11.13), then every minimizing sequence
of `f + ι_C` converges strongly to the unique minimizer of `f` over `C`. -/
theorem existsUnique_mem_argminOn_and_tendsto_of_isMinimizingSequence_add_indicator
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {C : Set H}
    (hC_bounded : Bornology.IsBounded C) (hC_closed : IsClosed C)
    (hC_disjoint : Disjoint C (Argmin f.asEReal))
    (hC_uniformlyConvex : Set.UniformlyConvex C) {xₙ : ℕ → H}
    (hxₙ : IsMinimizingSequence (f.asEReal + (ι[C]).asEReal) xₙ) :
    ∃! x : H, x ∈ Argmin[C] f.asEReal ∧ Tendsto xₙ atTop (𝓝 x) := by
  -- Route correction: rebuild the weak-convergence half locally from boundedness and weak cluster
  -- points instead of importing the broken Proposition 11.29 file.
  have hC_convex : Convex ℝ C :=
    hC_uniformlyConvex.convex_of_isClosed hC_closed
  have hC_strictConvex : StrictConvex ℝ C :=
    hC_uniformlyConvex.strictConvex_of_isClosed hC_closed
  rcases
      exists_mem_argminOn_and_tendsto_toWeakSpace_of_isMinimizingSequence_add_indicator
        hf hC_bounded hC_closed hC_convex hC_disjoint hC_strictConvex hxₙ with
    ⟨x, hxarg, hxweak⟩
  have hxC : x ∈ C := (mem_argminOn_iff.mp hxarg).1
  have hstrong : Tendsto xₙ atTop (𝓝 x) := by
    -- Route correction: start from the source midpoint-ball contradiction and isolate the inner
    -- core `D = {z | ball z δ ⊆ C}` before the final value comparison.
    by_contra hstrong
    rw [Metric.tendsto_atTop] at hstrong
    push Not at hstrong
    rcases hstrong with ⟨ε, hε, hbad⟩
    have hfreq : ∃ᶠ n in atTop, ε ≤ dist (xₙ n) x := by
      rw [frequently_atTop]
      intro N
      rcases hbad N with ⟨n, hnN, hndist⟩
      exact ⟨n, hnN, hndist⟩
    rcases extraction_of_frequently_atTop hfreq with ⟨φbad, hφbad_mono, hφbad_dist⟩
    rcases hC_uniformlyConvex with ⟨φ, hφ_mono, hφ_zero, hφ_ball⟩
    let δ : ℝ := ((φ ⟨ε, hε.le⟩ : NNReal) : ℝ)
    have hδ_pos : 0 < δ := by
      have hφ_ne_zero : φ ⟨ε, hε.le⟩ ≠ 0 := by
        intro hzero
        have hεnn_zero : (⟨ε, hε.le⟩ : NNReal) = 0 := (hφ_zero _).1 hzero
        have hε_zero : ε = 0 := by
          exact congrArg (fun r : NNReal ↦ (r : ℝ)) hεnn_zero
        exact (ne_of_gt hε) hε_zero
      exact_mod_cast (pos_iff_ne_zero.mpr hφ_ne_zero)
    let D : Set H := {z : H | Metric.ball z δ ⊆ C}
    have hmidD : ∀ n, midpoint ℝ x (xₙ (φbad n)) ∈ D := by
      intro n
      have hxnC : xₙ (φbad n) ∈ C :=
        (mem_constraint_inter_effectiveDomain_of_add_indicator hxₙ (φbad n)).1
      have hdist : ε ≤ dist x (xₙ (φbad n)) := by
        simpa [dist_comm] using hφbad_dist n
      simpa [D, δ] using
        Set.midpoint_mem_inner_core_of_uniformlyConvex_of_dist_lower_bound
          hφ_mono hφ_ball hε hxC hxnC hdist
    have hD_nonempty : D.Nonempty := ⟨midpoint ℝ x (xₙ (φbad 0)), hmidD 0⟩
    have hD_closed : IsClosed D := by
      -- The inner core is an intersection of closed distance halfspaces.
      simpa [D] using (Set.isClosed_inner_core (C := C) (δ := δ))
    have hD_mid :
        ∀ ⦃y z : H⦄, y ∈ D → z ∈ D → midpoint ℝ y z ∈ D := by
      intro y z hy hz
      simpa [D] using Set.midpoint_mem_inner_core_of_convex hC_convex hy hz
    have hD_convex : Convex ℝ D := by
      -- Reuse the closed-plus-midpoint bridge already established earlier in the file.
      exact Set.convex_of_isClosed_of_midpoint_mem hD_closed
        (fun {y z} hy hz ↦ hD_mid hy hz)
    have hD_subset_C : D ⊆ C := by
      intro z hz
      exact interior_subset <| Set.mem_interior_of_mem_inner_core hδ_pos hz
    have hD_bounded : Bornology.IsBounded D := hC_bounded.subset hD_subset_C
    have hD_argmin_nonempty : (Argmin[D] f.asEReal).Nonempty := by
      -- Proposition 11.15 now applies on the bounded closed convex inner core.
      exact
        argminOn_nonempty_of_mem_gammaZero_of_coercive_or_bounded
          hf hD_closed hD_convex hD_nonempty (Or.inr hD_bounded)
    rcases hD_argmin_nonempty with ⟨p, hpD⟩
    have hx_dom : x ∈ effectiveDomain f :=
      mem_effectiveDomain_of_mem_argminOn_of_nonempty_inter_effectiveDomain hxarg
        (nonempty_constraint_inter_effectiveDomain_of_add_indicator hxₙ)
    have hpointwise : ∀ n, (f p : EReal) ≤ f (xₙ (φbad n)) := by
      intro n
      have hxn : xₙ (φbad n) ∈ C ∩ effectiveDomain f :=
        mem_constraint_inter_effectiveDomain_of_add_indicator hxₙ (φbad n)
      have hp_le_mid : (f p : EReal) ≤ f (midpoint ℝ x (xₙ (φbad n))) := by
        -- Minimize `f` on `D` and evaluate at the midpoint witness `hmidD n`.
        exact (isMinOn_iff.mp (mem_argminOn_iff.mp hpD).2) _ (hmidD n)
      have hmid_le_right :
          (f (midpoint ℝ x (xₙ (φbad n))) : EReal) ≤ f (xₙ (φbad n)) :=
        midpoint_value_le_right_of_mem_argminOn hf.2 hxarg hx_dom hxn.1 hxn.2
      exact le_trans hp_le_mid hmid_le_right
    have hp_le_fx : (f p : EReal) ≤ f x :=
      le_of_subsequence_pointwise_bound_of_isMinimizingSequence_add_indicator
        hxₙ hφbad_mono hxarg hpointwise
    have hpD_mem : p ∈ D := mem_of_mem_argminOn hpD
    have hpC : p ∈ C := hD_subset_C hpD_mem
    have hx_le_hp : (f x : EReal) ≤ f p :=
      (isMinOn_iff.mp (mem_argminOn_iff.mp hxarg).2) p hpC
    have hpx_eq : (f p : EReal) = f x := le_antisymm hp_le_fx hx_le_hp
    have hpC_arg : p ∈ Argmin[C] f.asEReal := by
      -- The value identity upgrades the inner-core minimizer to a constrained minimizer on `C`.
      refine mem_argminOn_iff.mpr ⟨hpC, ?_⟩
      rw [isMinOn_iff]
      intro z hzC
      calc
        (f p : EReal) = f x := hpx_eq
        _ ≤ f z := (isMinOn_iff.mp (mem_argminOn_iff.mp hxarg).2) z hzC
    have hp_dom : p ∈ effectiveDomain f :=
      mem_effectiveDomain_of_mem_argminOn_of_nonempty_inter_effectiveDomain hpC_arg
        (nonempty_constraint_inter_effectiveDomain_of_add_indicator hxₙ)
    have hp_int : p ∈ interior C := by
      -- Points of the positive-radius inner core lie in the interior of `C`.
      simpa [D] using Set.mem_interior_of_mem_inner_core hδ_pos hpD_mem
    have hp_argmin : p ∈ Argmin f.asEReal := by
      -- Proposition 11.5 upgrades an interior constrained minimizer to a global minimizer.
      exact mem_argmin_of_mem_argminOn_of_mem_interior_of_convexOn_effectiveDomain
        f hf.2 hp_dom hpC_arg hp_int
    exact False.elim <| Set.disjoint_left.mp hC_disjoint hpC hp_argmin
  refine ⟨x, ⟨hxarg, hstrong⟩, ?_⟩
  intro y hy
  rcases hy with ⟨hyarg, hytendsto⟩
  -- Strong limit uniqueness identifies any other constrained minimizer-limit pair with `x`.
  exact tendsto_nhds_unique hytendsto hstrong

end ERealFunction
