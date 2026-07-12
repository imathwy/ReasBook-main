import Mathlib
import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.Chap04.Sec04_22.Theorem_4_5
import SmoothManifolds_Lee_2012.Chap04.Sec04_24.Exercise_4_16
import SmoothManifolds_Lee_2012.Chap05.Sec05_35.Definition_5_35_extra_4
import SmoothManifolds_Lee_2012.Chap05.Sec05_35.Proposition_5_35

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff
open Manifold

noncomputable section

local notation "Plane" => ℝ × ℝ

/-- Helper for Problem 5-11: the quadratic zero set used in parts (a) and (b). -/
abbrev quadraticDifferenceZeroSet : Set Plane :=
  {p : Plane | p.1 ^ 2 - p.2 ^ 2 = 0}

/-- Helper for Problem 5-11: the origin lies on the quadratic zero set. -/
theorem quadratic_difference_zero_set_origin_mem :
    (0 : Plane) ∈ quadraticDifferenceZeroSet := by
  -- Evaluate the defining equation at the origin.
  simp [quadraticDifferenceZeroSet]

/-- Helper for Problem 5-11: on the quadratic zero set, vanishing `x` forces the point to be the
origin. -/
theorem quadratic_difference_eq_origin_of_x_zero {q : quadraticDifferenceZeroSet}
    (hx : (q : Plane).1 = 0) :
    (q : Plane) = 0 := by
  -- The equation `x^2 - y^2 = 0` reduces to `y^2 = 0` once `x = 0`.
  have hy : (q : Plane).2 = 0 := by
    have hq : ((q : Plane).1) ^ 2 - ((q : Plane).2) ^ 2 = 0 := q.2
    have hy_sq : ((q : Plane).2) ^ 2 = 0 := by
      nlinarith [hq]
    exact sq_eq_zero_iff.mp hy_sq
  ext <;> simp [hx, hy]

/-- Helper for Problem 5-11: on the quadratic zero set, vanishing `y` forces the point to be the
origin. -/
theorem quadratic_difference_eq_origin_of_y_zero {q : quadraticDifferenceZeroSet}
    (hy : (q : Plane).2 = 0) :
    (q : Plane) = 0 := by
  -- The same computation with the coordinates reversed gives `x = 0`.
  have hx : (q : Plane).1 = 0 := by
    have hq : ((q : Plane).1) ^ 2 - ((q : Plane).2) ^ 2 = 0 := q.2
    have hx_sq : ((q : Plane).1) ^ 2 = 0 := by
      nlinarith [hq]
    exact sq_eq_zero_iff.mp hx_sq
  ext <;> simp [hx, hy]

/-- Helper for Problem 5-11: a preconnected subset of the punctured quadratic zero set cannot
contain both positive and negative `x`-coordinates. -/
theorem quadratic_difference_punctured_preconnected_no_mixed_x_sign
    {A : Set quadraticDifferenceZeroSet} (hA : IsPreconnected A)
    (hA_nonzero : ∀ q ∈ A, (q : Plane) ≠ 0) :
    ¬ ((∃ q ∈ A, 0 < (q : Plane).1) ∧ ∃ q ∈ A, (q : Plane).1 < 0) := by
  intro hmix
  rcases hmix with ⟨⟨qpos, hqposA, hqposx⟩, qneg, hqnegA, hqnegx⟩
  let f : quadraticDifferenceZeroSet → ℝ := fun q ↦ (q : Plane).1
  have hf : Continuous f := continuous_fst.comp continuous_subtype_val
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (f qneg) (f qpos) := by
    constructor <;> linarith
  -- Push the preconnected subset to the `x`-axis and use the intermediate value theorem there.
  rcases hA.intermediate_value hqnegA hqposA hf.continuousOn hzero_mem with
    ⟨q₀, hq₀A, hq₀x⟩
  have hq₀_zero : (q₀ : Plane) = 0 :=
    quadratic_difference_eq_origin_of_x_zero hq₀x
  exact (hA_nonzero q₀ hq₀A) hq₀_zero

/-- Helper for Problem 5-11: a preconnected subset of the punctured quadratic zero set cannot
contain both positive and negative `y`-coordinates. -/
theorem quadratic_difference_punctured_preconnected_no_mixed_y_sign
    {A : Set quadraticDifferenceZeroSet} (hA : IsPreconnected A)
    (hA_nonzero : ∀ q ∈ A, (q : Plane) ≠ 0) :
    ¬ ((∃ q ∈ A, 0 < (q : Plane).2) ∧ ∃ q ∈ A, (q : Plane).2 < 0) := by
  intro hmix
  rcases hmix with ⟨⟨qpos, hqposA, hqposy⟩, qneg, hqnegA, hqnegy⟩
  let f : quadraticDifferenceZeroSet → ℝ := fun q ↦ (q : Plane).2
  have hf : Continuous f := continuous_snd.comp continuous_subtype_val
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (f qneg) (f qpos) := by
    constructor <;> linarith
  -- The same argument on the `y`-coordinate forces a forbidden origin point.
  rcases hA.intermediate_value hqnegA hqposA hf.continuousOn hzero_mem with
    ⟨q₀, hq₀A, hq₀y⟩
  have hq₀_zero : (q₀ : Plane) = 0 :=
    quadratic_difference_eq_origin_of_y_zero hq₀y
  exact (hA_nonzero q₀ hq₀A) hq₀_zero

/-- Helper for Problem 5-11: every ambient neighborhood of the origin meets three distinct local
branches of the quadratic zero set. -/
theorem quadratic_difference_branch_points_in_open (U : Set Plane)
    (hU : IsOpen U) (h0U : (0 : Plane) ∈ U) :
    (∃ p ∈ U, p ∈ quadraticDifferenceZeroSet ∧ 0 < p.1 ∧ 0 < p.2) ∧
      (∃ p ∈ U, p ∈ quadraticDifferenceZeroSet ∧ p.1 < 0 ∧ p.2 < 0) ∧
      (∃ p ∈ U, p ∈ quadraticDifferenceZeroSet ∧ 0 < p.1 ∧ p.2 < 0) := by
  rcases Metric.isOpen_iff.mp hU (0 : Plane) h0U with ⟨ε, hε_pos, hεU⟩
  let t : ℝ := ε / 2
  have ht_pos : 0 < t := by
    dsimp [t]
    linarith
  have ht_lt : t < ε := by
    dsimp [t]
    linarith
  have hnorm_diag : ‖(t, t)‖ = t := by
    simp [Prod.norm_def, Real.norm_eq_abs, abs_of_pos ht_pos]
  have hnorm_negdiag : ‖(-t, -t)‖ = t := by
    have hneg_t : -t < 0 := by linarith
    simp [Prod.norm_def, Real.norm_eq_abs, abs_of_neg hneg_t, ht_pos.le]
  have hnorm_antidiag : ‖(t, -t)‖ = t := by
    have hneg_t : -t < 0 := by linarith
    simp [Prod.norm_def, Real.norm_eq_abs, abs_of_pos ht_pos, abs_of_neg hneg_t]
  have hdiag_mem_ball : (t, t) ∈ Metric.ball (0 : Plane) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [hnorm_diag]
  have hnegdiag_mem_ball : (-t, -t) ∈ Metric.ball (0 : Plane) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [hnorm_negdiag]
  have hantidiag_mem_ball : (t, -t) ∈ Metric.ball (0 : Plane) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [hnorm_antidiag]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨(t, t), hεU hdiag_mem_ball, ?_, ht_pos, ht_pos⟩
    -- The point `(t, t)` lies on the diagonal branch `x = y`.
    simp [quadraticDifferenceZeroSet]
  · refine ⟨(-t, -t), hεU hnegdiag_mem_ball, ?_, ?_, ?_⟩
    · simp [quadraticDifferenceZeroSet]
    · linarith
    · linarith
  · refine ⟨(t, -t), hεU hantidiag_mem_ball, ?_, ht_pos, ?_⟩
    · -- The point `(t, -t)` lies on the antidiagonal branch `x = -y`.
      simp [quadraticDifferenceZeroSet]
    · linarith

/-- Helper for Problem 5-11: an open subset of the quadratic zero-set subtype comes from an ambient
open subset of `ℝ²`. -/
theorem quadratic_difference_zero_set_open_neighborhood_to_ambient_open
    {V : Set quadraticDifferenceZeroSet} (hV : IsOpen V) :
    ∃ U : Set Plane, IsOpen U ∧
      V = (Subtype.val : quadraticDifferenceZeroSet → Plane) ⁻¹' U := by
  -- Unpack the induced-topology description of openness for the subtype.
  rcases Topology.IsInducing.subtypeVal.isOpen_iff.1 hV with ⟨U, hU, hEq⟩
  exact ⟨U, hU, hEq.symm⟩

/-- Helper for Problem 5-11: every open neighborhood of the origin in the quadratic zero-set
subtype contains the three branch witnesses. -/
theorem quadratic_difference_branch_points_in_subtype_open
    (V : Set quadraticDifferenceZeroSet) (hV : IsOpen V)
    (h0V : (⟨0, quadratic_difference_zero_set_origin_mem⟩ : quadraticDifferenceZeroSet) ∈ V) :
    (∃ q ∈ V, 0 < (q : Plane).1 ∧ 0 < (q : Plane).2) ∧
      (∃ q ∈ V, (q : Plane).1 < 0 ∧ (q : Plane).2 < 0) ∧
      (∃ q ∈ V, 0 < (q : Plane).1 ∧ (q : Plane).2 < 0) := by
  rcases quadratic_difference_zero_set_open_neighborhood_to_ambient_open hV with ⟨U, hU, hVU⟩
  have h0U : (0 : Plane) ∈ U := by
    -- Read the subtype origin neighborhood as an ambient one via the subtype pullback.
    simpa [hVU] using h0V
  rcases quadratic_difference_branch_points_in_open U hU h0U with
    ⟨⟨p₁, hp₁U, hp₁zero, hp₁x, hp₁y⟩,
      ⟨⟨p₂, hp₂U, hp₂zero, hp₂x, hp₂y⟩,
        ⟨p₃, hp₃U, hp₃zero, hp₃x, hp₃y⟩⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨p₁, hp₁zero⟩, ?_, hp₁x, hp₁y⟩
    simpa [hVU] using hp₁U
  · refine ⟨⟨p₂, hp₂zero⟩, ?_, hp₂x, hp₂y⟩
    simpa [hVU] using hp₂U
  · refine ⟨⟨p₃, hp₃zero⟩, ?_, hp₃x, hp₃y⟩
    simpa [hVU] using hp₃U

/-- Helper for Problem 5-11: in a chart at the origin on the quadratic zero set, a sufficiently
small bounded interval pulls back to a punctured neighborhood split into two preconnected sides. -/
theorem quadratic_difference_chart_interval_two_side_cover
    [ChartedSpace ℝ quadraticDifferenceZeroSet]
    [IsManifold 𝓘(ℝ) ⊤ quadraticDifferenceZeroSet] :
    let p : quadraticDifferenceZeroSet := ⟨0, quadratic_difference_zero_set_origin_mem⟩
    let e := chartAt ℝ p
    ∃ δ : Set.Ioi (0 : ℝ),
      let W : Set quadraticDifferenceZeroSet := e.symm '' Set.Ioo (e p - (δ : ℝ)) (e p + (δ : ℝ))
      let L : Set quadraticDifferenceZeroSet := e.symm '' Set.Ioo (e p - (δ : ℝ)) (e p)
      let R : Set quadraticDifferenceZeroSet := e.symm '' Set.Ioo (e p) (e p + (δ : ℝ))
      IsOpen W ∧ p ∈ W ∧ IsPreconnected L ∧ IsPreconnected R ∧
        L ∪ R = W \ ({p} : Set quadraticDifferenceZeroSet) := by
  let p : quadraticDifferenceZeroSet := ⟨0, quadratic_difference_zero_set_origin_mem⟩
  let e := chartAt ℝ p
  let ep : ℝ := e p
  -- Choose a bounded interval around the chart center contained in the chart target.
  rcases Metric.mem_nhds_iff.mp (chart_target_mem_nhds (H := ℝ) p) with ⟨δ, hδ_pos, hδsub⟩
  have htarget : Set.Ioo (ep - δ) (ep + δ) ⊆ e.target := by
    simpa [ep, Real.ball_eq_Ioo] using hδsub
  refine ⟨⟨δ, hδ_pos⟩, ?_⟩
  let W : Set quadraticDifferenceZeroSet := e.symm '' Set.Ioo (ep - δ) (ep + δ)
  let L : Set quadraticDifferenceZeroSet := e.symm '' Set.Ioo (ep - δ) ep
  let R : Set quadraticDifferenceZeroSet := e.symm '' Set.Ioo ep (ep + δ)
  have hL_subset_target : Set.Ioo (ep - δ) ep ⊆ e.target := by
    intro y hy
    exact htarget ⟨hy.1, by linarith [hy.2, hδ_pos]⟩
  have hR_subset_target : Set.Ioo ep (ep + δ) ⊆ e.target := by
    intro y hy
    exact htarget ⟨by linarith [hy.1, hδ_pos], hy.2⟩
  have hW_open : IsOpen W := by
    -- Pull the bounded interval back through the chart inverse inside the chart target.
    have hW_open_raw : IsOpen (e.symm '' (e.target ∩ Set.Ioo (ep - δ) (ep + δ))) := by
      simpa using e.symm.isOpen_image_source_inter isOpen_Ioo
    have htarget_eq : e.target ∩ Set.Ioo (ep - δ) (ep + δ) = Set.Ioo (ep - δ) (ep + δ) :=
      Set.inter_eq_right.mpr htarget
    simpa [W, htarget_eq] using hW_open_raw
  have hpW : p ∈ W := by
    refine ⟨ep, ?_, ?_⟩
    · constructor <;> linarith
    · simpa [ep, e] using e.left_inv (mem_chart_source ℝ p)
  have hL_preconnected : IsPreconnected L := by
    -- The left half comes from the connected interval `(ep - δ, ep)`.
    simpa [L] using isPreconnected_Ioo.image _ (e.continuousOn_symm.mono hL_subset_target)
  have hR_preconnected : IsPreconnected R := by
    -- The right half comes from the connected interval `(ep, ep + δ)`.
    simpa [R] using isPreconnected_Ioo.image _ (e.continuousOn_symm.mono hR_subset_target)
  have hpunctured_cover : L ∪ R = W \ ({p} : Set quadraticDifferenceZeroSet) := by
    -- Removing the midpoint from the bounded interval leaves its left and right halves.
    ext q
    constructor
    · intro hq
      rcases hq with hqL | hqR
      · rcases hqL with ⟨y, hy, rfl⟩
        refine ⟨?_, ?_⟩
        · exact ⟨y, ⟨hy.1, by linarith [hy.2, hδ_pos]⟩, rfl⟩
        · intro hqp
          have hy_target : y ∈ e.target := hL_subset_target hy
          have hy_eq : y = ep := by
            calc
              y = e (e.symm y) := by symm; exact e.right_inv hy_target
              _ = e p := congrArg e hqp
              _ = ep := rfl
          have : ep < ep := by simpa [hy_eq] using hy.2
          exact lt_irrefl _ this
      · rcases hqR with ⟨y, hy, rfl⟩
        refine ⟨?_, ?_⟩
        · exact ⟨y, ⟨by linarith [hy.1, hδ_pos], hy.2⟩, rfl⟩
        · intro hqp
          have hy_target : y ∈ e.target := hR_subset_target hy
          have hy_eq : y = ep := by
            calc
              y = e (e.symm y) := by symm; exact e.right_inv hy_target
              _ = e p := congrArg e hqp
              _ = ep := rfl
          have : ep < ep := by simpa [hy_eq] using hy.1
          exact lt_irrefl _ this
    · intro hq
      rcases hq.1 with ⟨y, hy, rfl⟩
      have hy_ne : y ≠ ep := by
        intro hy_eq
        apply hq.2
        have hsymm_eq : e.symm y = p := by
          calc
            e.symm y = e.symm (e p) := by simpa [ep, hy_eq]
            _ = p := e.left_inv (mem_chart_source ℝ p)
        simpa [Set.mem_singleton_iff, hsymm_eq]
      rcases lt_or_gt_of_ne hy_ne with hy_lt | hy_gt
      · left
        exact ⟨y, ⟨hy.1, hy_lt⟩, rfl⟩
      · right
        exact ⟨y, ⟨hy_gt, hy.2⟩, rfl⟩
  dsimp [W, L, R]
  exact ⟨hW_open, hpW, hL_preconnected, hR_preconnected, hpunctured_cover⟩

/-- Problem 5-11 (1): Part (a) for `Φ(x,y)=x^2-y^2`; its zero set is not an embedded curve in
`ℝ²`. -/
-- Proof sketch: identify the zero set with the two diagonals meeting transversely at the origin
-- and show the induced topology is not locally interval-like there.
theorem quadraticDifferenceZeroSet_not_embedded_curve :
    ¬ quadraticDifferenceZeroSet.AdmitsEmbeddedCurveStructure := by
  intro hEmbedded
  rcases hEmbedded with ⟨cs, hs, _⟩
  let p : quadraticDifferenceZeroSet := ⟨0, quadratic_difference_zero_set_origin_mem⟩
  let _ : ChartedSpace ℝ quadraticDifferenceZeroSet := cs
  let _ : IsManifold 𝓘(ℝ) ⊤ quadraticDifferenceZeroSet := hs
  let e := chartAt ℝ p
  rcases quadratic_difference_chart_interval_two_side_cover with
    ⟨δ, hW_open, hpW, hL_preconnected, hR_preconnected, hpunctured_cover⟩
  let W : Set quadraticDifferenceZeroSet := e.symm '' Set.Ioo (e p - (δ : ℝ)) (e p + (δ : ℝ))
  let L : Set quadraticDifferenceZeroSet := e.symm '' Set.Ioo (e p - (δ : ℝ)) (e p)
  let R : Set quadraticDifferenceZeroSet := e.symm '' Set.Ioo (e p) (e p + (δ : ℝ))
  have hW_open' : IsOpen W := by
    simpa [W, e, p] using hW_open
  have hpW' : p ∈ W := by
    simpa [W, e, p] using hpW
  have hL_preconnected' : IsPreconnected L := by
    simpa [L, e, p] using hL_preconnected
  have hR_preconnected' : IsPreconnected R := by
    simpa [R, e, p] using hR_preconnected
  have hpunctured_cover' : L ∪ R = W \ ({p} : Set quadraticDifferenceZeroSet) := by
    simpa [W, L, R, e, p] using hpunctured_cover
  rcases quadratic_difference_branch_points_in_subtype_open W hW_open' hpW' with
    ⟨⟨q₁, hq₁W, hq₁x_pos, hq₁y_pos⟩,
      ⟨⟨q₂, hq₂W, hq₂x_neg, hq₂y_neg⟩,
        ⟨q₃, hq₃W, hq₃x_pos, hq₃y_neg⟩⟩⟩
  have hq₁_ne_p : q₁ ≠ p := by
    intro hq₁p
    have : 0 < (p : Plane).1 := by simpa [hq₁p] using hq₁x_pos
    simpa [p] using this
  have hq₂_ne_p : q₂ ≠ p := by
    intro hq₂p
    have : (p : Plane).1 < 0 := by simpa [hq₂p] using hq₂x_neg
    simpa [p] using this
  have hq₃_ne_p : q₃ ≠ p := by
    intro hq₃p
    have : 0 < (p : Plane).1 := by simpa [hq₃p] using hq₃x_pos
    simpa [p] using this
  have hq₁_punctured : q₁ ∈ W \ ({p} : Set quadraticDifferenceZeroSet) := by
    exact ⟨hq₁W, by simpa [Set.mem_singleton_iff] using hq₁_ne_p⟩
  have hq₂_punctured : q₂ ∈ W \ ({p} : Set quadraticDifferenceZeroSet) := by
    exact ⟨hq₂W, by simpa [Set.mem_singleton_iff] using hq₂_ne_p⟩
  have hq₃_punctured : q₃ ∈ W \ ({p} : Set quadraticDifferenceZeroSet) := by
    exact ⟨hq₃W, by simpa [Set.mem_singleton_iff] using hq₃_ne_p⟩
  have hq₁_side : q₁ ∈ L ∪ R := by
    exact hpunctured_cover'.symm ▸ hq₁_punctured
  have hq₂_side : q₂ ∈ L ∪ R := by
    exact hpunctured_cover'.symm ▸ hq₂_punctured
  have hq₃_side : q₃ ∈ L ∪ R := by
    exact hpunctured_cover'.symm ▸ hq₃_punctured
  have hL_nonzero : ∀ q ∈ L, (q : Plane) ≠ 0 := by
    intro q hqL hq0
    have hq_ne_p : q ≠ p := by
      have hq_punctured : q ∈ W \ ({p} : Set quadraticDifferenceZeroSet) := by
        exact hpunctured_cover' ▸ Or.inl hqL
      simpa [Set.mem_singleton_iff] using hq_punctured.2
    apply hq_ne_p
    apply Subtype.ext
    simpa [p] using hq0
  have hR_nonzero : ∀ q ∈ R, (q : Plane) ≠ 0 := by
    intro q hqR hq0
    have hq_ne_p : q ≠ p := by
      have hq_punctured : q ∈ W \ ({p} : Set quadraticDifferenceZeroSet) := by
        exact hpunctured_cover' ▸ Or.inr hqR
      simpa [Set.mem_singleton_iff] using hq_punctured.2
    apply hq_ne_p
    apply Subtype.ext
    simpa [p] using hq0
  have hL_no_mixed_x :
      ¬ ((∃ q ∈ L, 0 < (q : Plane).1) ∧ ∃ q ∈ L, (q : Plane).1 < 0) :=
    quadratic_difference_punctured_preconnected_no_mixed_x_sign hL_preconnected' hL_nonzero
  have hR_no_mixed_x :
      ¬ ((∃ q ∈ R, 0 < (q : Plane).1) ∧ ∃ q ∈ R, (q : Plane).1 < 0) :=
    quadratic_difference_punctured_preconnected_no_mixed_x_sign hR_preconnected' hR_nonzero
  have hL_no_mixed_y :
      ¬ ((∃ q ∈ L, 0 < (q : Plane).2) ∧ ∃ q ∈ L, (q : Plane).2 < 0) :=
    quadratic_difference_punctured_preconnected_no_mixed_y_sign hL_preconnected' hL_nonzero
  have hR_no_mixed_y :
      ¬ ((∃ q ∈ R, 0 < (q : Plane).2) ∧ ∃ q ∈ R, (q : Plane).2 < 0) :=
    quadratic_difference_punctured_preconnected_no_mixed_y_sign hR_preconnected' hR_nonzero
  -- Route correction: keep the source proof's two-side-versus-three-branch contradiction inside
  -- the subtype, and contradict one side using the sign-rigidity lemmas.
  rcases hq₁_side with hq₁L | hq₁R <;>
    rcases hq₂_side with hq₂L | hq₂R <;>
    rcases hq₃_side with hq₃L | hq₃R
  · exact hL_no_mixed_x ⟨⟨q₁, hq₁L, hq₁x_pos⟩, q₂, hq₂L, hq₂x_neg⟩
  · exact hL_no_mixed_x ⟨⟨q₁, hq₁L, hq₁x_pos⟩, q₂, hq₂L, hq₂x_neg⟩
  · exact hL_no_mixed_y ⟨⟨q₁, hq₁L, hq₁y_pos⟩, q₃, hq₃L, hq₃y_neg⟩
  · exact hR_no_mixed_x ⟨⟨q₃, hq₃R, hq₃x_pos⟩, q₂, hq₂R, hq₂x_neg⟩
  · exact hL_no_mixed_x ⟨⟨q₃, hq₃L, hq₃x_pos⟩, q₂, hq₂L, hq₂x_neg⟩
  · exact hR_no_mixed_y ⟨⟨q₁, hq₁R, hq₁y_pos⟩, q₃, hq₃R, hq₃y_neg⟩
  · exact hR_no_mixed_x ⟨⟨q₁, hq₁R, hq₁x_pos⟩, q₂, hq₂R, hq₂x_neg⟩
  · exact hR_no_mixed_x ⟨⟨q₁, hq₁R, hq₁x_pos⟩, q₂, hq₂R, hq₂x_neg⟩

/-- Helper for Problem 5-11: lowering the differentiability index preserves immersions by keeping
the same chart normal forms. -/
lemma quadratic_difference_isImmersion_of_le
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H']
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {J : ModelWithCorners 𝕜 E' H'} [IsManifold J (⊤ : WithTop ℕ∞) N]
    {n m : WithTop ℕ∞} {f : M → N} (hmn : m ≤ n)
    (hf : IsImmersion I J n f) :
    IsImmersion I J m f := by
  -- Keep the same global complement and reuse the same local chart presentation.
  let hComp := hf.complement
  let hCompImm := hf.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I) (M := M) hmn) hx.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le (I := J) (M := N) hmn) hx.codChart_mem_maximalAtlas

/-- Helper for Problem 5-11: the cut source `ℝ \ {-1, 1}` carries the standard open-subset
manifold structure used in the source proof. -/
noncomputable abbrev quadratic_difference_cut_source : TopologicalSpace.Opens ℝ :=
  ⟨{t : ℝ | t ≠ -1 ∧ t ≠ 1},
    (isOpen_ne (x := (-1 : ℝ))).inter (isOpen_ne (x := (1 : ℝ)))⟩

/-- Helper for Problem 5-11: the left source component corresponds to `(-∞, -1)`. -/
def quadratic_difference_left_cut : Set quadratic_difference_cut_source :=
  {t : quadratic_difference_cut_source | (t : ℝ) < -1}

/-- Helper for Problem 5-11: the union of the left and middle source components is the cut
`(-∞, 1) \ {-1}`. -/
def quadratic_difference_middle_cut : Set quadratic_difference_cut_source :=
  {t : quadratic_difference_cut_source | (t : ℝ) < 1}

/-- Helper for Problem 5-11: the outer left branch of the crossing is an affine antidiagonal
parametrization. -/
def quadratic_difference_left_ambient : ℝ → Plane :=
  fun t ↦ (t + 1, -1 - t)

/-- Helper for Problem 5-11: the middle source component maps to the diagonal via a rational
coordinate change. -/
def quadratic_difference_middle_scalar_real : ℝ → ℝ :=
  fun t ↦ t / (1 - t ^ 2)

/-- Helper for Problem 5-11: the middle diagonal branch in ambient coordinates. -/
def quadratic_difference_middle_ambient : ℝ → Plane :=
  fun t ↦
    let u := quadratic_difference_middle_scalar_real t
    (u, u)

/-- Helper for Problem 5-11: the outer right branch is the translated antidiagonal ray. -/
def quadratic_difference_right_ambient : ℝ → Plane :=
  fun t ↦ (t - 1, 1 - t)

/-- Helper for Problem 5-11: the left branch is the ambient affine map restricted to the cut
source. -/
def quadratic_difference_left_branch : quadratic_difference_cut_source → Plane :=
  quadratic_difference_left_ambient ∘ Subtype.val

/-- Helper for Problem 5-11: the diagonal branch is the rational middle map restricted to the cut
source. -/
def quadratic_difference_middle_branch : quadratic_difference_cut_source → Plane :=
  quadratic_difference_middle_ambient ∘ Subtype.val

/-- Helper for Problem 5-11: the right branch is the other affine antidiagonal ray. -/
def quadratic_difference_right_branch : quadratic_difference_cut_source → Plane :=
  quadratic_difference_right_ambient ∘ Subtype.val

/-- Helper for Problem 5-11: the full cut parametrization is obtained by piecing together the
three connected components of the source. -/
def quadratic_difference_cut_param : quadratic_difference_cut_source → Plane :=
  by
    classical
    exact Set.piecewise quadratic_difference_left_cut quadratic_difference_left_branch
      (Set.piecewise quadratic_difference_middle_cut quadratic_difference_middle_branch
        quadratic_difference_right_branch)

/-- Helper for Problem 5-11: the inclusion derivative of an open subset is injective, so any
ambient map with injective derivative stays injective after restricting to that open subset. -/
lemma quadratic_difference_comp_open_subset_mfderiv_injective
    {U : TopologicalSpace.Opens ℝ} {g : ℝ → Plane} (x : U)
    (hg' : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Plane) g x)
    (hinj : Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) g x)) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (g ∘ (Subtype.val : U → ℝ)) x) := by
  have hsubDiff : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (Subtype.val : U → ℝ) := contMDiff_subtype_val
  have hsubImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ) ∞ (Subtype.val : U → ℝ) :=
    Manifold.IsImmersion.of_opens (I := 𝓘(ℝ)) (n := ∞) U
  have hsub_inj :
      Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ) (Subtype.val : U → ℝ) x) :=
    ((Manifold.is_immersion_iff_forall_injective_mfderiv hsubDiff).1 hsubImm) x
  rw [mfderiv_comp x hg' (hsubDiff.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))]
  exact hinj.comp hsub_inj

/-- Helper for Problem 5-11: a nonzero continuous linear map out of `ℝ` is injective. -/
lemma quadratic_difference_continuous_linearMap_injective_from_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ →L[ℝ] E} (hL : L ≠ 0) :
    Function.Injective L := by
  -- The source is one-dimensional, so a nonzero linear map has trivial kernel.
  exact LinearMap.injective_of_ne_zero (f := L.toLinearMap) <| by
    intro hzero
    exact hL <| ContinuousLinearMap.ext fun x ↦ DFunLike.congr_fun hzero x

/-- Helper for Problem 5-11: the affine antidiagonal map has nonzero Fréchet derivative. -/
lemma quadratic_difference_left_ambient_fderiv_ne_zero (t : ℝ) :
    fderiv ℝ quadratic_difference_left_ambient t ≠ 0 := by
  have hfderiv :
      fderiv ℝ quadratic_difference_left_ambient t =
        ContinuousLinearMap.toSpanSingleton ℝ (1, -1) := by
    -- Evaluate the one-variable derivative coordinatewise.
    simpa [quadratic_difference_left_ambient] using
      (((hasDerivAt_id t).add_const 1).prodMk (((hasDerivAt_id t).add_const 1).neg)).hasFDerivAt.fderiv
  intro hzero
  have happly : (fderiv ℝ quadratic_difference_left_ambient t) 1 = 0 := by
    simpa [hzero]
  simpa [hfderiv] using happly

/-- Helper for Problem 5-11: the translated antidiagonal map is an immersion on the real line. -/
lemma quadratic_difference_left_ambient_mfderiv_injective (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_left_ambient t) := by
  -- Reinterpret the manifold derivative on Euclidean space as the usual derivative.
  have hNonzero : mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_left_ambient t ≠ 0 := by
    rw [mfderiv_eq_fderiv]
    exact quadratic_difference_left_ambient_fderiv_ne_zero t
  exact quadratic_difference_continuous_linearMap_injective_from_real (E := Plane) hNonzero

/-- Helper for Problem 5-11: the right affine branch has the same nonzero derivative vector. -/
lemma quadratic_difference_right_ambient_fderiv_ne_zero (t : ℝ) :
    fderiv ℝ quadratic_difference_right_ambient t ≠ 0 := by
  have hfderiv :
      fderiv ℝ quadratic_difference_right_ambient t =
        ContinuousLinearMap.toSpanSingleton ℝ (1, -1) := by
    -- Evaluate the translated affine derivative coordinatewise.
    simpa [quadratic_difference_right_ambient] using
      (((hasDerivAt_id t).sub_const 1).prodMk (((hasDerivAt_id t).sub_const 1).neg)).hasFDerivAt.fderiv
  intro hzero
  have happly : (fderiv ℝ quadratic_difference_right_ambient t) 1 = 0 := by
    simpa [hzero]
  simpa [hfderiv] using happly

/-- Helper for Problem 5-11: the right translated antidiagonal branch is also immersive. -/
lemma quadratic_difference_right_ambient_mfderiv_injective (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_right_ambient t) := by
  have hNonzero : mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_right_ambient t ≠ 0 := by
    rw [mfderiv_eq_fderiv]
    exact quadratic_difference_right_ambient_fderiv_ne_zero t
  exact quadratic_difference_continuous_linearMap_injective_from_real (E := Plane) hNonzero

/-- Helper for Problem 5-11: the rational middle coordinate change has the expected derivative on
the punctured line away from `±1`. -/
lemma quadratic_difference_middle_scalar_real_hasDerivAt (t : ℝ)
    (htm1 : t ≠ -1) (ht1 : t ≠ 1) :
    HasDerivAt quadratic_difference_middle_scalar_real
      ((1 + t ^ 2) / (1 - t ^ 2) ^ 2) t := by
  have hnum : HasDerivAt (fun x : ℝ ↦ x) 1 t := hasDerivAt_id t
  have hden : HasDerivAt (fun x : ℝ ↦ 1 - x ^ 2) (-2 * t) t := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_const t (c := (1 : ℝ))).sub ((hasDerivAt_id t).pow 2)
  have hden_ne : 1 - t ^ 2 ≠ 0 := by
    intro hzero
    have hsquare : t ^ 2 = 1 := by nlinarith
    have hcases : t = 1 ∨ t = -1 := by
      rw [← one_pow 2, sq_eq_sq_iff_eq_or_eq_neg] at hsquare
      simpa using hsquare
    rcases hcases with hcase | hcase
    · exact ht1 hcase
    · exact htm1 hcase
  -- Differentiate the quotient using the nonvanishing denominator.
  have hquot :
      HasDerivAt quadratic_difference_middle_scalar_real
        ((1 * (1 - t ^ 2) - t * (-2 * t)) / (1 - t ^ 2) ^ 2) t := by
    simpa [quadratic_difference_middle_scalar_real] using hnum.div hden hden_ne
  convert hquot using 1 <;> ring

/-- Helper for Problem 5-11: the middle rational coordinate change has nonzero derivative on the
cut source. -/
lemma quadratic_difference_middle_scalar_real_fderiv_ne_zero (t : quadratic_difference_cut_source) :
    fderiv ℝ quadratic_difference_middle_scalar_real (t : ℝ) ≠ 0 := by
  have hderiv :=
    quadratic_difference_middle_scalar_real_hasDerivAt (t : ℝ) t.2.1 t.2.2
  have hfderiv :
      fderiv ℝ quadratic_difference_middle_scalar_real (t : ℝ) =
        (1 : ℝ →L[ℝ] ℝ).smulRight
          ((1 + (t : ℝ) ^ 2) / (1 - (t : ℝ) ^ 2) ^ 2) := by
    simpa using hderiv.hasFDerivAt.fderiv
  intro hzero
  have happly : (fderiv ℝ quadratic_difference_middle_scalar_real (t : ℝ)) 1 = 0 := by
    simpa [hzero]
  rw [hfderiv, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul] at happly
  have hnum_pos : 0 < 1 + (t : ℝ) ^ 2 := by positivity
  have hden_pos : 0 < (1 - (t : ℝ) ^ 2) ^ 2 := by
    have hden_ne : 1 - (t : ℝ) ^ 2 ≠ 0 := by
      intro hzero'
      have hsquare : (t : ℝ) ^ 2 = 1 := by nlinarith
      have hcases : (t : ℝ) = 1 ∨ (t : ℝ) = -1 := by
        rw [← one_pow 2, sq_eq_sq_iff_eq_or_eq_neg] at hsquare
        simpa using hsquare
      rcases hcases with hcase | hcase
      · exact t.2.2 hcase
      · exact t.2.1 hcase
    positivity
  have : ((1 + (t : ℝ) ^ 2) / (1 - (t : ℝ) ^ 2) ^ 2) ≠ 0 := by
    have hden_ne : 1 - (t : ℝ) ^ 2 ≠ 0 := by
      intro hzero
      have hsquare : (t : ℝ) ^ 2 = 1 := by nlinarith
      have hcases : (t : ℝ) = 1 ∨ (t : ℝ) = -1 := by
        rw [← one_pow 2, sq_eq_sq_iff_eq_or_eq_neg] at hsquare
        simpa using hsquare
      rcases hcases with hcase | hcase
      · exact t.2.2 hcase
      · exact t.2.1 hcase
    exact div_ne_zero (ne_of_gt hnum_pos) (pow_ne_zero 2 hden_ne)
  exact this happly

/-- Helper for Problem 5-11: the middle ambient diagonal map has injective manifold derivative at
every source point of the cut. -/
lemma quadratic_difference_middle_ambient_mfderiv_injective (t : quadratic_difference_cut_source) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_middle_ambient (t : ℝ)) := by
  have hscalar :=
    quadratic_difference_middle_scalar_real_hasDerivAt (t : ℝ) t.2.1 t.2.2
  have hfderiv :
      fderiv ℝ quadratic_difference_middle_ambient (t : ℝ) =
        ContinuousLinearMap.toSpanSingleton ℝ
          (((1 + (t : ℝ) ^ 2) / (1 - (t : ℝ) ^ 2) ^ 2),
            ((1 + (t : ℝ) ^ 2) / (1 - (t : ℝ) ^ 2) ^ 2)) := by
    -- Differentiate the two equal diagonal coordinates simultaneously.
    simpa [quadratic_difference_middle_ambient] using
      (hscalar.prodMk hscalar).hasFDerivAt.fderiv
  have hNonzero : mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_middle_ambient (t : ℝ) ≠ 0 := by
    rw [mfderiv_eq_fderiv]
    intro hzero
    have happly_raw :
        (fderiv ℝ quadratic_difference_middle_ambient (t : ℝ)) 1 = (0 : ℝ →L[ℝ] Plane) 1 := by
      exact congrArg (fun L : ℝ →L[ℝ] Plane ↦ L 1) hzero
    have happly : (fderiv ℝ quadratic_difference_middle_ambient (t : ℝ)) 1 = 0 := by
      simpa using happly_raw
    rw [hfderiv] at happly
    have hnum_pos : 0 < 1 + (t : ℝ) ^ 2 := by positivity
    have hden_ne : 1 - (t : ℝ) ^ 2 ≠ 0 := by
      intro hzero'
      have hsquare : (t : ℝ) ^ 2 = 1 := by nlinarith
      have hcases : (t : ℝ) = 1 ∨ (t : ℝ) = -1 := by
        rw [← one_pow 2, sq_eq_sq_iff_eq_or_eq_neg] at hsquare
        simpa using hsquare
      rcases hcases with hcase | hcase
      · exact t.2.2 hcase
      · exact t.2.1 hcase
    have hscalar_ne :
        ((1 + (t : ℝ) ^ 2) / (1 - (t : ℝ) ^ 2) ^ 2) ≠ 0 := by
      exact div_ne_zero (ne_of_gt hnum_pos) (pow_ne_zero 2 hden_ne)
    have hcoord :
        ((1 + (t : ℝ) ^ 2) / (1 - (t : ℝ) ^ 2) ^ 2) = 0 := by
      simpa [ContinuousLinearMap.toSpanSingleton_apply] using congrArg Prod.fst happly
    exact hscalar_ne hcoord
  exact quadratic_difference_continuous_linearMap_injective_from_real (E := Plane) hNonzero

/-- Helper for Problem 5-11: the explicit inverse candidate for the middle rational branch. -/
def quadratic_difference_middle_inverse_real (x : ℝ) : ℝ :=
  2 * x / (1 + Real.sqrt (1 + 4 * x ^ 2))

/-- Helper for Problem 5-11: the explicit inverse candidate lies in `(-1, 1)` and evaluates back
to the requested diagonal coordinate under the middle branch scalar map. -/
lemma quadratic_difference_middle_preimage_mem_and_eval (x : ℝ) :
    let u := quadratic_difference_middle_inverse_real x
    (-1 < u ∧ u < 1) ∧ quadratic_difference_middle_scalar_real u = x := by
  let s : ℝ := Real.sqrt (1 + 4 * x ^ 2)
  let u : ℝ := quadratic_difference_middle_inverse_real x
  have hs_nonneg : 0 ≤ 1 + 4 * x ^ 2 := by positivity
  have hs_sq : s ^ 2 = 1 + 4 * x ^ 2 := by
    -- The square of the chosen square root recovers the radicand.
    dsimp [s]
    rw [Real.sq_sqrt hs_nonneg]
  have hs_pos : 0 < 1 + s := by
    -- The denominator is strictly positive because `s = sqrt (1 + 4 x^2)`.
    have hs_nonneg' : 0 ≤ s := by
      dsimp [s]
      exact Real.sqrt_nonneg _
    positivity
  have hu_sq :
      1 - u ^ 2 = 2 / (1 + s) := by
    -- Rationalize the denominator once so the same identity yields both the bound and the
    -- evaluation formula.
    change 1 - (2 * x / (1 + s)) ^ 2 = 2 / (1 + s)
    field_simp [hs_pos.ne']
    nlinarith [hs_sq]
  have hu_sq_pos : 0 < 1 - u ^ 2 := by
    rw [hu_sq]
    positivity
  have hu_bounds : -1 < u ∧ u < 1 := by
    -- Strict positivity of `1 - u^2` is equivalent to `|u| < 1`.
    have hu_sq_lt_one : u ^ 2 < 1 := by
      nlinarith [hu_sq_pos]
    constructor <;> nlinarith [hu_sq_lt_one]
  have hu_eval : quadratic_difference_middle_scalar_real u = x := by
    -- Substitute the denominator identity back into the rational parametrization.
    change (2 * x / (1 + s)) / (1 - (2 * x / (1 + s)) ^ 2) = x
    have hu_sq' : 1 - (2 * x / (1 + s)) ^ 2 = 2 / (1 + s) := by
      simpa [u, quadratic_difference_middle_inverse_real] using hu_sq
    rw [hu_sq']
    field_simp [hs_pos.ne']
  dsimp [u]
  exact ⟨hu_bounds, hu_eval⟩

/-- Helper for Problem 5-11: on the left component, the cut parametrization is exactly the left
affine branch. -/
lemma quadratic_difference_cut_param_of_left {t : quadratic_difference_cut_source}
    (ht : (t : ℝ) < -1) :
    quadratic_difference_cut_param t = quadratic_difference_left_branch t := by
  -- On the left component the outer `piecewise` immediately selects the affine branch.
  simp [quadratic_difference_cut_param, quadratic_difference_left_cut, ht]

/-- Helper for Problem 5-11: on the middle component, the cut parametrization is exactly the
rational diagonal branch. -/
lemma quadratic_difference_cut_param_of_middle {t : quadratic_difference_cut_source}
    (htm1 : -1 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    quadratic_difference_cut_param t = quadratic_difference_middle_branch t := by
  -- Outside the left component but still before `1`, the inner `piecewise` chooses the middle
  -- branch.
  have hnot_left : ¬ ((t : ℝ) < -1) := by
    linarith
  simp [quadratic_difference_cut_param, quadratic_difference_left_cut, quadratic_difference_middle_cut,
    hnot_left, ht1]

/-- Helper for Problem 5-11: on the right component, the cut parametrization is exactly the right
affine branch. -/
lemma quadratic_difference_cut_param_of_right {t : quadratic_difference_cut_source}
    (ht : 1 < (t : ℝ)) :
    quadratic_difference_cut_param t = quadratic_difference_right_branch t := by
  -- Once `t` is past `1`, both earlier components are skipped.
  have hnot_left : ¬ ((t : ℝ) < -1) := by
    linarith
  have hnot_mid : ¬ ((t : ℝ) < 1) := by
    linarith
  simp [quadratic_difference_cut_param, quadratic_difference_left_cut,
    quadratic_difference_middle_cut, hnot_left, hnot_mid]

/-- Helper for Problem 5-11: the cut parametrization lands in the quadratic zero set. -/
lemma quadratic_difference_cut_param_mem (t : quadratic_difference_cut_source) :
    quadratic_difference_cut_param t ∈ quadraticDifferenceZeroSet := by
  by_cases ht_left : (t : ℝ) < -1
  · -- The left affine antidiagonal branch satisfies `x^2 - y^2 = 0` identically.
    rw [quadratic_difference_cut_param_of_left ht_left]
    dsimp [quadraticDifferenceZeroSet, quadratic_difference_left_branch,
      quadratic_difference_left_ambient]
    ring
  · by_cases ht_mid : (t : ℝ) < 1
    · have htm1 : -1 < (t : ℝ) := by
        have hle : -1 ≤ (t : ℝ) := by linarith
        exact lt_of_le_of_ne hle (Ne.symm t.2.1)
      -- The middle branch lies on the diagonal `y = x`, so the defining equation vanishes.
      rw [quadratic_difference_cut_param_of_middle htm1 ht_mid]
      simp [quadraticDifferenceZeroSet, quadratic_difference_middle_branch,
        quadratic_difference_middle_ambient, quadratic_difference_middle_scalar_real]
    · have ht_right : 1 < (t : ℝ) := by
        have hle : 1 ≤ (t : ℝ) := by linarith
        exact lt_of_le_of_ne hle (Ne.symm t.2.2)
      -- The right affine antidiagonal branch also satisfies the same quadratic identity.
      rw [quadratic_difference_cut_param_of_right ht_right]
      dsimp [quadraticDifferenceZeroSet, quadratic_difference_right_branch,
        quadratic_difference_right_ambient]
      ring

/-- Helper for Problem 5-11: the cut parametrization viewed as a map into the quadratic zero-set
subtype. -/
def quadratic_difference_cut_paramSubtype :
    quadratic_difference_cut_source → quadraticDifferenceZeroSet :=
  fun t ↦ ⟨quadratic_difference_cut_param t, quadratic_difference_cut_param_mem t⟩

/-- Helper for Problem 5-11: every point on the quadratic zero set is hit by the explicit
three-branch parametrization. -/
lemma quadratic_difference_cut_paramSubtype_surjective :
    Function.Surjective quadratic_difference_cut_paramSubtype := by
  intro q
  let x : ℝ := (q : Plane).1
  let y : ℝ := (q : Plane).2
  have hsq : y ^ 2 = x ^ 2 := by
    -- Rewriting the zero-set equation isolates the equality of squares.
    have hq : (q : Plane).1 ^ 2 - (q : Plane).2 ^ 2 = 0 := q.2
    have hq' : x ^ 2 - y ^ 2 = 0 := by
      simpa [x, y] using hq
    nlinarith [hq']
  have hxy : y = x ∨ y = -x := by
    -- On the quadratic zero set, the point lies on either the diagonal or the antidiagonal.
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  rcases hxy with hdiag | hantidiag
  · let u : ℝ := quadratic_difference_middle_inverse_real x
    have hu_data := quadratic_difference_middle_preimage_mem_and_eval x
    rcases hu_data with ⟨hu_bounds, hu_eval⟩
    let t : quadratic_difference_cut_source := ⟨u, by
      constructor
      · linarith [hu_bounds.1]
      · linarith [hu_bounds.2]⟩
    refine ⟨t, Subtype.ext ?_⟩
    -- The diagonal case is handled by the explicit inverse of the middle rational branch.
    change quadratic_difference_cut_param t = q
    rw [quadratic_difference_cut_param_of_middle
      (show -1 < (t : ℝ) from hu_bounds.1)
      (show (t : ℝ) < 1 from hu_bounds.2)]
    ext
    · change quadratic_difference_middle_scalar_real (t : ℝ) = x
      simpa [t, u] using hu_eval
    · change quadratic_difference_middle_scalar_real (t : ℝ) = y
      simpa [t, u, hdiag, x, y] using hu_eval
  · by_cases hx0 : x = 0
    · have hy0 : y = 0 := by simpa [hx0] using hantidiag
      let t : quadratic_difference_cut_source := ⟨0, by constructor <;> norm_num⟩
      refine ⟨t, Subtype.ext ?_⟩
      -- The origin is shared by the diagonal branch, so we reuse the middle component.
      change quadratic_difference_cut_param t = q
      rw [quadratic_difference_cut_param_of_middle (by norm_num) (by norm_num)]
      ext <;> simp [quadratic_difference_middle_branch, quadratic_difference_middle_ambient,
        quadratic_difference_middle_scalar_real, x, y, hx0, hy0, t]
    · rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
      · let t : quadratic_difference_cut_source := ⟨x - 1, by
          constructor
          · linarith
          · linarith⟩
        refine ⟨t, Subtype.ext ?_⟩
        -- Negative antidiagonal points come from the left affine ray.
        change quadratic_difference_cut_param t = q
        rw [quadratic_difference_cut_param_of_left (by dsimp [t]; linarith)]
        ext
        · simp [quadratic_difference_left_branch, quadratic_difference_left_ambient,
            x, y, hantidiag, t]
        · dsimp [quadratic_difference_left_branch, quadratic_difference_left_ambient]
          change -1 - (x - 1) = y
          rw [hantidiag]
          ring
      · let t : quadratic_difference_cut_source := ⟨x + 1, by
          constructor
          · linarith
          · linarith⟩
        refine ⟨t, Subtype.ext ?_⟩
        -- Positive antidiagonal points come from the right affine ray.
        change quadratic_difference_cut_param t = q
        rw [quadratic_difference_cut_param_of_right (by dsimp [t]; linarith)]
        ext <;> simp [quadratic_difference_right_branch, quadratic_difference_right_ambient,
          x, y, hantidiag, t]

/-- Helper for Problem 5-11: on `(-1, 1)`, the middle scalar branch is injective. -/
lemma quadratic_difference_middle_scalar_real_injective_on_interval
    {u v : ℝ} (hu_left : -1 < u) (hu_right : u < 1)
    (hv_left : -1 < v) (hv_right : v < 1)
    (huv :
      quadratic_difference_middle_scalar_real u =
        quadratic_difference_middle_scalar_real v) :
    u = v := by
  have hu_den_ne : 1 - u ^ 2 ≠ 0 := by
    nlinarith
  have hv_den_ne : 1 - v ^ 2 ≠ 0 := by
    nlinarith
  have hcross :
      u * (1 - v ^ 2) = v * (1 - u ^ 2) := by
    have huv' : u / (1 - u ^ 2) = v / (1 - v ^ 2) := by
      simpa [quadratic_difference_middle_scalar_real] using huv
    exact (div_eq_div_iff hu_den_ne hv_den_ne).mp huv'
  have hfactor : (u - v) * (1 + u * v) = 0 := by
    nlinarith [hcross]
  have hfactor_pos : 0 < 1 + u * v := by
    nlinarith
  have huv_eq : u - v = 0 := by
    nlinarith [hfactor, hfactor_pos]
  linarith

/-- Helper for Problem 5-11: the explicit inverse really inverts the middle scalar branch on the
middle interval. -/
lemma quadratic_difference_middle_inverse_comp_scalar {t : ℝ}
    (htm1 : -1 < t) (ht1 : t < 1) :
    quadratic_difference_middle_inverse_real (quadratic_difference_middle_scalar_real t) = t := by
  -- Use the explicit inverse candidate together with injectivity of the middle scalar branch on
  -- `(-1, 1)`.
  rcases quadratic_difference_middle_preimage_mem_and_eval
      (quadratic_difference_middle_scalar_real t) with ⟨hu_bounds, hu_eval⟩
  exact quadratic_difference_middle_scalar_real_injective_on_interval
    hu_bounds.1 hu_bounds.2 htm1 ht1 (by simpa [hu_eval])

/-- Helper for Problem 5-11: the three-branch cut parametrization is injective. -/
lemma quadratic_difference_cut_param_injective :
    Function.Injective quadratic_difference_cut_param := by
  intro s t hst
  have hs_cases : (s : ℝ) < -1 ∨ (-1 < (s : ℝ) ∧ (s : ℝ) < 1) ∨ 1 < (s : ℝ) := by
    by_cases hs_left : (s : ℝ) < -1
    · exact Or.inl hs_left
    · by_cases hs_mid : (s : ℝ) < 1
      · have hsm1 : -1 < (s : ℝ) := by
          have hle : -1 ≤ (s : ℝ) := by linarith
          exact lt_of_le_of_ne hle (Ne.symm s.2.1)
        exact Or.inr <| Or.inl ⟨hsm1, hs_mid⟩
      · have hs1 : 1 < (s : ℝ) := by
          have hle : 1 ≤ (s : ℝ) := by linarith
          exact lt_of_le_of_ne hle (Ne.symm s.2.2)
        exact Or.inr <| Or.inr hs1
  have ht_cases : (t : ℝ) < -1 ∨ (-1 < (t : ℝ) ∧ (t : ℝ) < 1) ∨ 1 < (t : ℝ) := by
    by_cases ht_left : (t : ℝ) < -1
    · exact Or.inl ht_left
    · by_cases ht_mid : (t : ℝ) < 1
      · have htm1 : -1 < (t : ℝ) := by
          have hle : -1 ≤ (t : ℝ) := by linarith
          exact lt_of_le_of_ne hle (Ne.symm t.2.1)
        exact Or.inr <| Or.inl ⟨htm1, ht_mid⟩
      · have ht1 : 1 < (t : ℝ) := by
          have hle : 1 ≤ (t : ℝ) := by linarith
          exact lt_of_le_of_ne hle (Ne.symm t.2.2)
        exact Or.inr <| Or.inr ht1
  -- Split by the three source components and use the source-faithful branch formulas.
  rcases hs_cases with hs_left | hs_mid | hs_right
  · rcases ht_cases with ht_left | ht_mid | ht_right
    · -- On the left component, the affine antidiagonal branch is injective.
      have hs_formula := quadratic_difference_cut_param_of_left hs_left
      have ht_formula := quadratic_difference_cut_param_of_left ht_left
      have hfst :
          (quadratic_difference_left_branch s).1 =
            (quadratic_difference_left_branch t).1 := by
        simpa [hs_formula, ht_formula] using congrArg Prod.fst hst
      apply Subtype.ext
      dsimp [quadratic_difference_left_branch, quadratic_difference_left_ambient] at hfst
      linarith
    · -- A left-branch point cannot coincide with a middle-branch point: the first has `y = -x`
      -- with `x < 0`, while the second lies on the diagonal.
      have hs_formula := quadratic_difference_cut_param_of_left hs_left
      have ht_formula := quadratic_difference_cut_param_of_middle ht_mid.1 ht_mid.2
      have hs_neg :
          (quadratic_difference_cut_param s).1 < 0 := by
        rw [hs_formula]
        dsimp [quadratic_difference_left_branch, quadratic_difference_left_ambient]
        linarith
      have hs_anti :
          (quadratic_difference_cut_param s).2 =
            - (quadratic_difference_cut_param s).1 := by
        rw [hs_formula]
        dsimp [quadratic_difference_left_branch, quadratic_difference_left_ambient]
        ring
      have ht_diag :
          (quadratic_difference_cut_param t).1 =
            (quadratic_difference_cut_param t).2 := by
        rw [ht_formula]
        simp [quadratic_difference_middle_branch, quadratic_difference_middle_ambient]
      have hzero : (quadratic_difference_cut_param s).1 = 0 := by
        have hdiag_s :
            (quadratic_difference_cut_param s).1 =
              (quadratic_difference_cut_param s).2 := by
          simpa [hst] using ht_diag
        rw [hs_anti] at hdiag_s
        linarith
      linarith
    · -- A left-branch point cannot land on the positive antidiagonal ray.
      have hs_formula := quadratic_difference_cut_param_of_left hs_left
      have ht_formula := quadratic_difference_cut_param_of_right ht_right
      have hs_neg :
          (quadratic_difference_cut_param s).1 < 0 := by
        rw [hs_formula]
        dsimp [quadratic_difference_left_branch, quadratic_difference_left_ambient]
        linarith
      have ht_pos :
          0 < (quadratic_difference_cut_param t).1 := by
        rw [ht_formula]
        dsimp [quadratic_difference_right_branch, quadratic_difference_right_ambient]
        linarith
      linarith [congrArg Prod.fst hst]
  · rcases hs_mid with ⟨hsm1, hs1⟩
    rcases ht_cases with ht_left | ht_mid | ht_right
    · -- This is symmetric to the left-middle contradiction handled above.
      have hs_formula := quadratic_difference_cut_param_of_middle hsm1 hs1
      have ht_formula := quadratic_difference_cut_param_of_left ht_left
      have ht_neg :
          (quadratic_difference_cut_param t).1 < 0 := by
        rw [ht_formula]
        dsimp [quadratic_difference_left_branch, quadratic_difference_left_ambient]
        linarith
      have ht_anti :
          (quadratic_difference_cut_param t).2 =
            - (quadratic_difference_cut_param t).1 := by
        rw [ht_formula]
        dsimp [quadratic_difference_left_branch, quadratic_difference_left_ambient]
        ring
      have hs_diag :
          (quadratic_difference_cut_param s).1 =
            (quadratic_difference_cut_param s).2 := by
        rw [hs_formula]
        simp [quadratic_difference_middle_branch, quadratic_difference_middle_ambient]
      have hzero : (quadratic_difference_cut_param t).1 = 0 := by
        have hdiag_t :
            (quadratic_difference_cut_param t).1 =
              (quadratic_difference_cut_param t).2 := by
          simpa [hst] using hs_diag
        rw [ht_anti] at hdiag_t
        linarith
      linarith
    · -- On the middle component, injectivity reduces to the scalar rational map.
      have hs_formula := quadratic_difference_cut_param_of_middle hsm1 hs1
      have ht_formula := quadratic_difference_cut_param_of_middle ht_mid.1 ht_mid.2
      have hscalar :
          quadratic_difference_middle_scalar_real (s : ℝ) =
            quadratic_difference_middle_scalar_real (t : ℝ) := by
        have hfst :
            (quadratic_difference_middle_branch s).1 =
              (quadratic_difference_middle_branch t).1 := by
          simpa [hs_formula, ht_formula] using congrArg Prod.fst hst
        simpa [quadratic_difference_middle_branch, quadratic_difference_middle_ambient,
          quadratic_difference_middle_scalar_real] using hfst
      apply Subtype.ext
      exact quadratic_difference_middle_scalar_real_injective_on_interval
        hsm1 hs1 ht_mid.1 ht_mid.2 hscalar
    · -- A diagonal point cannot land on the positive antidiagonal ray.
      have hs_formula := quadratic_difference_cut_param_of_middle hsm1 hs1
      have ht_formula := quadratic_difference_cut_param_of_right ht_right
      have ht_pos :
          0 < (quadratic_difference_cut_param t).1 := by
        rw [ht_formula]
        dsimp [quadratic_difference_right_branch, quadratic_difference_right_ambient]
        linarith
      have ht_anti :
          (quadratic_difference_cut_param t).2 =
            - (quadratic_difference_cut_param t).1 := by
        rw [ht_formula]
        dsimp [quadratic_difference_right_branch, quadratic_difference_right_ambient]
        ring
      have hs_diag :
          (quadratic_difference_cut_param s).1 =
            (quadratic_difference_cut_param s).2 := by
        rw [hs_formula]
        simp [quadratic_difference_middle_branch, quadratic_difference_middle_ambient]
      have hzero : (quadratic_difference_cut_param t).1 = 0 := by
        have hdiag_t :
            (quadratic_difference_cut_param t).1 =
              (quadratic_difference_cut_param t).2 := by
          simpa [hst] using hs_diag
        rw [ht_anti] at hdiag_t
        linarith
      linarith
  · rcases ht_cases with ht_left | ht_mid | ht_right
    · -- Positive and negative antidiagonal rays are disjoint.
      have hs_formula := quadratic_difference_cut_param_of_right hs_right
      have ht_formula := quadratic_difference_cut_param_of_left ht_left
      have hs_pos :
          0 < (quadratic_difference_cut_param s).1 := by
        rw [hs_formula]
        dsimp [quadratic_difference_right_branch, quadratic_difference_right_ambient]
        linarith
      have ht_neg :
          (quadratic_difference_cut_param t).1 < 0 := by
        rw [ht_formula]
        dsimp [quadratic_difference_left_branch, quadratic_difference_left_ambient]
        linarith
      linarith [congrArg Prod.fst hst]
    · -- This is symmetric to the middle-right contradiction.
      have hs_formula := quadratic_difference_cut_param_of_right hs_right
      have ht_formula := quadratic_difference_cut_param_of_middle ht_mid.1 ht_mid.2
      have hs_pos :
          0 < (quadratic_difference_cut_param s).1 := by
        rw [hs_formula]
        dsimp [quadratic_difference_right_branch, quadratic_difference_right_ambient]
        linarith
      have hs_anti :
          (quadratic_difference_cut_param s).2 =
            - (quadratic_difference_cut_param s).1 := by
        rw [hs_formula]
        dsimp [quadratic_difference_right_branch, quadratic_difference_right_ambient]
        ring
      have ht_diag :
          (quadratic_difference_cut_param t).1 =
            (quadratic_difference_cut_param t).2 := by
        rw [ht_formula]
        simp [quadratic_difference_middle_branch, quadratic_difference_middle_ambient]
      have hzero : (quadratic_difference_cut_param s).1 = 0 := by
        have hdiag_s :
            (quadratic_difference_cut_param s).1 =
              (quadratic_difference_cut_param s).2 := by
          simpa [hst] using ht_diag
        rw [hs_anti] at hdiag_s
        linarith
      linarith
    · -- On the right component, the affine antidiagonal branch is injective.
      have hs_formula := quadratic_difference_cut_param_of_right hs_right
      have ht_formula := quadratic_difference_cut_param_of_right ht_right
      have hfst :
          (quadratic_difference_right_branch s).1 =
            (quadratic_difference_right_branch t).1 := by
        simpa [hs_formula, ht_formula] using congrArg Prod.fst hst
      apply Subtype.ext
      dsimp [quadratic_difference_right_branch, quadratic_difference_right_ambient] at hfst
      linarith

/-- Helper for Problem 5-11: the cut parametrization is bijective onto the quadratic zero-set
subtype. -/
lemma quadratic_difference_cut_paramSubtype_bijective :
    Function.Bijective quadratic_difference_cut_paramSubtype := by
  constructor
  · intro s t hst
    apply quadratic_difference_cut_param_injective
    exact congrArg Subtype.val hst
  · exact quadratic_difference_cut_paramSubtype_surjective

/-- Helper for Problem 5-11: the cut parametrization gives an explicit equivalence from the cut
source to the quadratic zero-set subtype. -/
noncomputable def quadratic_difference_cut_equiv :
    quadratic_difference_cut_source ≃ quadraticDifferenceZeroSet :=
  Equiv.ofBijective quadratic_difference_cut_paramSubtype
    quadratic_difference_cut_paramSubtype_bijective

/-- Helper for Problem 5-11: the transported topology on the quadratic zero-set subtype is pulled
back from the cut source by the explicit parametrization equivalence. -/
noncomputable abbrev quadraticDifferenceZeroSet_topology :
    TopologicalSpace quadraticDifferenceZeroSet :=
  quadratic_difference_cut_equiv.symm.topologicalSpace

/-- Helper for Problem 5-11: transport the source charted-space structure across a homeomorphism
onto a chosen subset of the plane. -/
noncomputable abbrev quadratic_difference_transport_subset_chartedSpace
    {N : Type*} [TopologicalSpace N] [ChartedSpace ℝ N] {S : Set Plane} [TopologicalSpace S]
    (e : N ≃ₜ S) :
    ChartedSpace ℝ S :=
  let _ : ChartedSpace N S :=
    (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp)
  ChartedSpace.comp ℝ N S

/-- Helper for Problem 5-11: the transported range charted space is again a smooth `1`-manifold
at the outer regularity `⊤`. -/
lemma quadratic_difference_transport_subset_isManifold_top
    {N : Type*} [TopologicalSpace N] [ChartedSpace ℝ N]
    [IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) N] {S : Set Plane} [TopologicalSpace S] (e : N ≃ₜ S) :
    let _ : ChartedSpace ℝ S := quadratic_difference_transport_subset_chartedSpace e
    IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := by
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace ℝ S := quadratic_difference_transport_subset_chartedSpace e
  have hGroupoid : HasGroupoid S (contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eS]) f hf
    have hf'Eq : f' = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eS]) f' hf'
    subst f
    subst f'
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    -- The transported charts differ only by the source charts on `N`, so compatibility reduces
    -- to the known compatibility on the source manifold.
    have hcompat :
        ((c.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
          contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ) := by
      rw [hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible
        (G := contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ)) hc hc'
    simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  -- The explicit transported atlas therefore defines a smooth manifold structure on the range.
  exact IsManifold.mk' 𝓘(ℝ) (⊤ : WithTop ℕ∞) S

/-- Helper for Problem 5-11: once the transported topology and atlas on the range are fixed
definitionally, the subtype inclusion uses the same immersion charts as the original map. -/
lemma quadratic_difference_transport_subset_val_isImmersionAt_explicit
    {N : Type*} [TopologicalSpace N] [ChartedSpace ℝ N]
    [IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) N] {g : N → Plane}
    {S : Set Plane} [TopologicalSpace S]
    (hg : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) g) (e : N ≃ₜ S)
    (he : ∀ x, ((e x : S) : Plane) = g x) (x : S) :
    let _ : ChartedSpace ℝ S := quadratic_difference_transport_subset_chartedSpace e
    let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S :=
      quadratic_difference_transport_subset_isManifold_top e
    IsImmersionAtOfComplement hg.complement 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
      (Subtype.val : S → Plane) x := by
  let instCharted : ChartedSpace ℝ S := quadratic_difference_transport_subset_chartedSpace e
  let _ : ChartedSpace ℝ S := instCharted
  let instManifold :
      IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S :=
    quadratic_difference_transport_subset_isManifold_top e
  let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := instManifold
  let hCompImm := hg.isImmersionOfComplement_complement
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext z
    simp [eS])
  let hx := hCompImm (e.symm x)
  -- Transport the source chart of `g` across the homeomorphism onto `S`.
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv (e.symm.toOpenPartialHomeomorph.trans hx.domChart) hx.codChart ?_ ?_ ?_ ?_ ?_ ?_
  · -- The transported source chart still contains the point `x`.
    simpa [OpenPartialHomeomorph.trans_source] using hx.mem_domChart_source
  · -- The codomain chart condition is the same pointwise statement as for `g`.
    have hxe : g (e.symm x) = (x : Plane) := by
      simpa using (he (e.symm x)).symm
    simpa [hxe] using hx.mem_codChart_source
  · -- The transported source chart stays in the maximal atlas after chart transport.
    intro d hd
    rcases hd with ⟨f, hf, c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (h := by
        ext z
        simp [eS]) f hf
    subst f
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    constructor
    · have hleft :
          ((hx.domChart.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
            contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ) := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').1
      simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hleft
    · have hright :
          ((c'.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ hx.domChart) ∈
            contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ) := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').2
      simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hright
  · exact hx.codChart_mem_maximalAtlas
  · -- Source points in the transported chart map into the codomain chart source because
    -- `Subtype.val ∘ e = g`.
    intro z hz
    have hz' : e.symm z ∈ hx.domChart.source := by
      simpa [OpenPartialHomeomorph.trans_source] using hz
    have hze : g (e.symm z) = (z : Plane) := by
      simpa using (he (e.symm z)).symm
    simpa [hze] using hx.source_subset_preimage_source hz'
  · -- In the transported source chart, the inclusion `S ↪ ℝ²` has the same normal form as `g`.
    intro u hu
    have hu' : u ∈ (hx.domChart.extend 𝓘(ℝ)).target := by
      simpa [OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target] using hu
    have hpoint : ((e (hx.domChart.symm u) : S) : Plane) = g (hx.domChart.symm u) := by
      exact he (hx.domChart.symm u)
    simpa [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe, hpoint] using
      hx.writtenInCharts hu'

/-- Helper for Problem 5-11: once the transported topology and atlas on the range are fixed
definitionally, the subtype inclusion uses the same immersion charts as the original map. -/
lemma quadratic_difference_transport_subset_val_isImmersion_explicit
    {N : Type*} [TopologicalSpace N] [ChartedSpace ℝ N]
    [IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) N] {g : N → Plane}
    {S : Set Plane} [TopologicalSpace S]
    (hg : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) g) (e : N ≃ₜ S)
    (he : ∀ x, ((e x : S) : Plane) = g x) :
    let _ : ChartedSpace ℝ S := quadratic_difference_transport_subset_chartedSpace e
    let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S :=
      quadratic_difference_transport_subset_isManifold_top e
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) (Subtype.val : S → Plane) := by
  let instCharted : ChartedSpace ℝ S := quadratic_difference_transport_subset_chartedSpace e
  let _ : ChartedSpace ℝ S := instCharted
  let instManifold :
      IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S :=
    quadratic_difference_transport_subset_isManifold_top e
  let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := instManifold
  -- Route correction: prove the global immersion by reusing the transported pointwise witness.
  refine ⟨hg.complement, inferInstance, inferInstance, ?_⟩
  intro x
  exact quadratic_difference_transport_subset_val_isImmersionAt_explicit hg e he x

/-- Helper for Problem 5-11: transporting the source manifold structure along a range equivalence
gives an immersed-curve structure on the image subset. -/
lemma quadratic_difference_transport_subset_isImmersedCurveWithTopology
    {N : Type*} [TopologicalSpace N] [ChartedSpace ℝ N]
    [IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) N] {g : N → Plane}
    {S : Set Plane} [TopologicalSpace S]
    (hg : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) g) (e : N ≃ₜ S)
    (he : ∀ x, ((e x : S) : Plane) = g x) :
    Set.IsImmersedCurveWithTopology S (inferInstance : TopologicalSpace S) := by
  let instCharted : ChartedSpace ℝ S := quadratic_difference_transport_subset_chartedSpace e
  let _ : ChartedSpace ℝ S := instCharted
  let instManifold :
      IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S :=
    quadratic_difference_transport_subset_isManifold_top e
  let _ : IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := instManifold
  -- Package the transported atlas and manifold structure, then discharge immersion explicitly.
  refine ⟨instCharted, instManifold, ?_⟩
  simpa using quadratic_difference_transport_subset_val_isImmersion_explicit hg e he

/-- Helper for Problem 5-11: the left affine branch is smooth on the cut source. -/
lemma quadratic_difference_left_branch_contMDiff_top :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ quadratic_difference_left_branch := by
  intro t
  change ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, Plane) ∞
    (fun x : quadratic_difference_cut_source ↦ quadratic_difference_left_ambient x) t
  refine (contMDiffAt_subtype_iff (U := quadratic_difference_cut_source)
    (f := quadratic_difference_left_ambient) (x := t)).2 ?_
  rw [contMDiffAt_iff_contDiffAt]
  -- The left branch is affine in the ambient real coordinate.
  simpa [quadratic_difference_left_ambient] using
    (contDiffAt_id.add contDiffAt_const).prodMk (contDiffAt_const.sub contDiffAt_id)

/-- Helper for Problem 5-11: the rational diagonal branch is smooth on the punctured source
line. -/
lemma quadratic_difference_middle_branch_contMDiff_top :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ quadratic_difference_middle_branch := by
  intro t
  change ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, Plane) ∞
    (fun x : quadratic_difference_cut_source ↦ quadratic_difference_middle_ambient x) t
  refine (contMDiffAt_subtype_iff (U := quadratic_difference_cut_source)
    (f := quadratic_difference_middle_ambient) (x := t)).2 ?_
  rw [contMDiffAt_iff_contDiffAt]
  have hden_ne : 1 - (t : ℝ) ^ 2 ≠ 0 := by
    intro hzero
    have hsquare : (t : ℝ) ^ 2 = 1 := by
      nlinarith
    have hcases : (t : ℝ) = 1 ∨ (t : ℝ) = -1 := by
      rw [← one_pow 2, sq_eq_sq_iff_eq_or_eq_neg] at hsquare
      simpa using hsquare
    rcases hcases with hcase | hcase
    · exact t.2.2 hcase
    · exact t.2.1 hcase
  have hscalar :
      ContDiffAt ℝ ∞ quadratic_difference_middle_scalar_real (t : ℝ) := by
    have hsq : ContDiffAt ℝ ∞ (fun x : ℝ ↦ x ^ 2) (t : ℝ) := by
      simpa using (contDiffAt_id : ContDiffAt ℝ ∞ (fun x : ℝ ↦ x) (t : ℝ)).pow 2
    -- The middle scalar map is a quotient with nonvanishing denominator on the cut source.
    simpa [quadratic_difference_middle_scalar_real] using
      (contDiffAt_id.div (contDiffAt_const.sub hsq) hden_ne)
  -- Pair the scalar map with itself to obtain the ambient diagonal branch.
  simpa [quadratic_difference_middle_ambient] using hscalar.prodMk hscalar

/-- Helper for Problem 5-11: the right affine branch is smooth on the cut source. -/
lemma quadratic_difference_right_branch_contMDiff_top :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ quadratic_difference_right_branch := by
  intro t
  change ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, Plane) ∞
    (fun x : quadratic_difference_cut_source ↦ quadratic_difference_right_ambient x) t
  refine (contMDiffAt_subtype_iff (U := quadratic_difference_cut_source)
    (f := quadratic_difference_right_ambient) (x := t)).2 ?_
  rw [contMDiffAt_iff_contDiffAt]
  -- The right branch is affine in the ambient real coordinate as well.
  simpa [quadratic_difference_right_ambient] using
    (contDiffAt_id.sub contDiffAt_const).prodMk (contDiffAt_const.sub contDiffAt_id)

/-- Helper for Problem 5-11: near every cut-source point, the piecewise parametrization agrees
with one active branch. -/
lemma quadratic_difference_cut_param_eventuallyEq_active_branch (t : quadratic_difference_cut_source) :
    (quadratic_difference_cut_param =ᶠ[nhds t] quadratic_difference_left_branch) ∨
      (quadratic_difference_cut_param =ᶠ[nhds t] quadratic_difference_middle_branch) ∨
      (quadratic_difference_cut_param =ᶠ[nhds t] quadratic_difference_right_branch) := by
  by_cases ht_left : (t : ℝ) < -1
  · left
    have hleft_open : IsOpen quadratic_difference_left_cut := by
      simpa [quadratic_difference_left_cut] using
        (isOpen_lt continuous_subtype_val continuous_const :
          IsOpen {s : quadratic_difference_cut_source | (s : ℝ) < -1})
    have hEqOn :
        Set.EqOn quadratic_difference_cut_param quadratic_difference_left_branch
          quadratic_difference_left_cut := by
      intro s hs
      exact quadratic_difference_cut_param_of_left hs
    exact hEqOn.eventuallyEq_of_mem (hleft_open.mem_nhds ht_left)
  · by_cases ht_mid : (t : ℝ) < 1
    · right
      left
      have htm1 : -1 < (t : ℝ) := by
        have hle : -1 ≤ (t : ℝ) := by
          linarith
        exact lt_of_le_of_ne hle (Ne.symm t.2.1)
      have hmid_open :
          IsOpen {s : quadratic_difference_cut_source | -1 < (s : ℝ) ∧ (s : ℝ) < 1} := by
        simpa [Set.setOf_and] using
          (isOpen_lt continuous_const continuous_subtype_val).inter
            (isOpen_lt continuous_subtype_val continuous_const)
      have hEqOn :
          Set.EqOn quadratic_difference_cut_param quadratic_difference_middle_branch
            {s : quadratic_difference_cut_source | -1 < (s : ℝ) ∧ (s : ℝ) < 1} := by
        intro s hs
        exact quadratic_difference_cut_param_of_middle hs.1 hs.2
      exact hEqOn.eventuallyEq_of_mem <| hmid_open.mem_nhds ⟨htm1, ht_mid⟩
    · right
      right
      have ht_right : 1 < (t : ℝ) := by
        have hle : 1 ≤ (t : ℝ) := by
          linarith
        exact lt_of_le_of_ne hle (Ne.symm t.2.2)
      have hright_open : IsOpen {s : quadratic_difference_cut_source | 1 < (s : ℝ)} := by
        simpa using
          (isOpen_lt continuous_const continuous_subtype_val :
            IsOpen {s : quadratic_difference_cut_source | 1 < (s : ℝ)})
      have hEqOn :
          Set.EqOn quadratic_difference_cut_param quadratic_difference_right_branch
            {s : quadratic_difference_cut_source | 1 < (s : ℝ)} := by
        intro s hs
        exact quadratic_difference_cut_param_of_right hs
      exact hEqOn.eventuallyEq_of_mem (hright_open.mem_nhds ht_right)

/-- Helper for Problem 5-11: the piecewise cut parametrization is smooth because it is locally one
of the smooth branches. -/
lemma quadratic_difference_cut_param_contMDiff_top :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ quadratic_difference_cut_param := by
  intro t
  rcases quadratic_difference_cut_param_eventuallyEq_active_branch t with
    hleft | hmiddle | hright
  · -- Near a left-source point, the piecewise map is exactly the left affine branch.
    exact (quadratic_difference_left_branch_contMDiff_top t).congr_of_eventuallyEq hleft
  · rcases hmiddle with hmiddle
    -- Near a middle-source point, the piecewise map is exactly the diagonal rational branch.
    exact (quadratic_difference_middle_branch_contMDiff_top t).congr_of_eventuallyEq hmiddle
  · -- Near a right-source point, the piecewise map is exactly the right affine branch.
    exact (quadratic_difference_right_branch_contMDiff_top t).congr_of_eventuallyEq hright

/-- Helper for Problem 5-11: the manifold derivative of the cut parametrization is injective at
every source point. -/
lemma quadratic_difference_cut_param_mfderiv_injective (t : quadratic_difference_cut_source) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_cut_param t) := by
  rcases quadratic_difference_cut_param_eventuallyEq_active_branch t with
    hleft | hmiddle | hright
  · have hmfderiv_eq :
        mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_cut_param t =
          mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_left_branch t := by
      -- Differentiate the eventual branch equality at the base point.
      exact hleft.mfderiv_eq
    have hleft_ambient_contMDiff :
        ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ quadratic_difference_left_ambient (t : ℝ) := by
      -- Unwrap the subtype branch smoothness back to the ambient affine map.
      have hleft_sub :
          ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, Plane) ∞
            (fun x : quadratic_difference_cut_source ↦ quadratic_difference_left_ambient x) t := by
        simpa [quadratic_difference_left_branch] using quadratic_difference_left_branch_contMDiff_top t
      exact (contMDiffAt_subtype_iff (U := quadratic_difference_cut_source)
        (f := quadratic_difference_left_ambient) (x := t)).1 hleft_sub
    have hleft_ambient_mdifferentiable :
        MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_left_ambient (t : ℝ) := by
      exact hleft_ambient_contMDiff.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hleft_inj :
        Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_left_branch t) :=
      quadratic_difference_comp_open_subset_mfderiv_injective
        (g := quadratic_difference_left_ambient) t hleft_ambient_mdifferentiable
        (quadratic_difference_left_ambient_mfderiv_injective (t : ℝ))
    exact hmfderiv_eq ▸ hleft_inj
  · rcases hmiddle with hmiddle
    have hmfderiv_eq :
        mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_cut_param t =
          mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_middle_branch t := by
      -- Differentiate the eventual middle-branch equality at the base point.
      exact hmiddle.mfderiv_eq
    have hmiddle_ambient_contMDiff :
        ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ quadratic_difference_middle_ambient (t : ℝ) := by
      -- Unwrap the subtype branch smoothness back to the ambient rational diagonal map.
      have hmiddle_sub :
          ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, Plane) ∞
            (fun x : quadratic_difference_cut_source ↦ quadratic_difference_middle_ambient x) t := by
        simpa [quadratic_difference_middle_branch] using
          quadratic_difference_middle_branch_contMDiff_top t
      exact (contMDiffAt_subtype_iff (U := quadratic_difference_cut_source)
        (f := quadratic_difference_middle_ambient) (x := t)).1 hmiddle_sub
    have hmiddle_ambient_mdifferentiable :
        MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_middle_ambient (t : ℝ) := by
      exact hmiddle_ambient_contMDiff.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hmiddle_inj :
        Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_middle_branch t) :=
      quadratic_difference_comp_open_subset_mfderiv_injective
        (g := quadratic_difference_middle_ambient) t hmiddle_ambient_mdifferentiable
        (quadratic_difference_middle_ambient_mfderiv_injective t)
    exact hmfderiv_eq ▸ hmiddle_inj
  · have hmfderiv_eq :
        mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_cut_param t =
          mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_right_branch t := by
      -- Differentiate the eventual right-branch equality at the base point.
      exact hright.mfderiv_eq
    have hright_ambient_contMDiff :
        ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ quadratic_difference_right_ambient (t : ℝ) := by
      -- Unwrap the subtype branch smoothness back to the ambient affine map.
      have hright_sub :
          ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, Plane) ∞
            (fun x : quadratic_difference_cut_source ↦ quadratic_difference_right_ambient x) t := by
        simpa [quadratic_difference_right_branch] using
          quadratic_difference_right_branch_contMDiff_top t
      exact (contMDiffAt_subtype_iff (U := quadratic_difference_cut_source)
        (f := quadratic_difference_right_ambient) (x := t)).1 hright_sub
    have hright_ambient_mdifferentiable :
        MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_right_ambient (t : ℝ) := by
      exact hright_ambient_contMDiff.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hright_inj :
        Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) quadratic_difference_right_branch t) :=
      quadratic_difference_comp_open_subset_mfderiv_injective
        (g := quadratic_difference_right_ambient) t hright_ambient_mdifferentiable
        (quadratic_difference_right_ambient_mfderiv_injective (t : ℝ))
    exact hmfderiv_eq ▸ hright_inj

/-- Helper for Problem 5-11: the cut parametrization is an immersion because it is smooth and its
manifold derivative is injective at every source point. -/
theorem quadratic_difference_cut_param_isImmersion :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ quadratic_difference_cut_param := by
  -- The immersion criterion reduces the claim to pointwise injectivity of the manifold derivative.
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv
    quadratic_difference_cut_param_contMDiff_top).2 ?_
  intro t
  exact quadratic_difference_cut_param_mfderiv_injective t

/-- Helper for Problem 5-11: the standard real-axis inclusion used as the fixed model branch. -/
def quadratic_difference_real_axis_inclusion : ℝ → Plane :=
  fun u ↦ (u, 0)

/-- Helper for Problem 5-11: every branchwise top-level immersion proof uses the same explicit
complement built from the two source-coordinate steps, the real-axis inclusion, and the final
codomain straightening inverse. -/
abbrev quadratic_difference_branch_complement : Type :=
  (((PUnit × PUnit) × ℝ) × PUnit)

/-- Helper for Problem 5-11: a nonzero scalar multiple of the real line is an invertible
continuous linear map. -/
theorem quadratic_difference_real_line_map_isInvertible_of_ne_zero (c : ℝ) (hc : c ≠ 0) :
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c).IsInvertible := by
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc), ?_⟩
  ext x
  -- Every continuous linear endomorphism of `ℝ` is multiplication by its value at `1`.
  simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-- Helper for Problem 5-11: on a model vector space, a top-regularity local diffeomorphism is a
pointwise immersion with the trivial complement. -/
lemma quadratic_difference_model_localDiffeomorphAt_isImmersionAtOfComplement_punit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {x : E}
    (hf : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) (⊤ : WithTop ℕ∞) f x) :
    IsImmersionAtOfComplement PUnit.{1} 𝓘(ℝ, E) 𝓘(ℝ, E) (⊤ : WithTop ℕ∞) f x := by
  have hCont : ContinuousAt f x := (IsLocalDiffeomorphAt.contMDiffAt hf).continuousAt
  rcases hf with ⟨Φ, hx, hEq⟩
  let domChart : OpenPartialHomeomorph E E := Φ.toOpenPartialHomeomorph
  have hdom_groupoid :
      domChart ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ, E) := by
    simpa [domChart] using
      Manifold.IsImmersionAtOfComplement.ex416_model_partial_diffeomorph_mem_contDiffGroupoid
        (K := 𝓘(ℝ, E)) (Φ := Φ)
  have hdom_mem :
      domChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) (⊤ : WithTop ℕ∞) E := by
    exact StructureGroupoid.mem_maximalAtlas_of_mem_groupoid
      (G := contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ, E)) hdom_groupoid
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    hCont
    (.prodUnique ℝ E PUnit.{1})
    domChart
    (OpenPartialHomeomorph.refl E)
    hx
    (by simp)
    hdom_mem
    (by
      simpa using
        (contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ, E)).id_mem_maximalAtlas)
    ?_
  intro u hu
  have hu_target : u ∈ domChart.target := by
    simpa [OpenPartialHomeomorph.extend_target] using hu
  have hu_source : domChart.symm u ∈ domChart.source := by
    simpa using domChart.map_target hu_target
  have hfu : f (domChart.symm u) = domChart (domChart.symm u) := hEq hu_source
  have hright : domChart (domChart.symm u) = u := domChart.right_inv hu_target
  -- In the chosen local-diffeomorphism chart, the map is literally the identity.
  simpa [domChart, Function.comp, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm] using hfu.trans hright

/-- Helper for Problem 5-11: translation by a real constant is a top-regularity diffeomorphism of
the model real line. -/
noncomputable def quadratic_difference_real_add_const_diffeomorph (c : ℝ) :
    ℝ ≃ₘ^((⊤ : WithTop ℕ∞))⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ where
  toEquiv := Equiv.addRight c
  contMDiff_toFun := by
    -- The forward map is affine, so it is `C^⊤`.
    simpa using
      ((contDiff_id.add contDiff_const :
        ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x : ℝ ↦ x + c))).contMDiff
  contMDiff_invFun := by
    -- The inverse translation is the same affine formula with `-c`.
    simpa [sub_eq_add_neg] using
      ((contDiff_id.add contDiff_const :
        ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x : ℝ ↦ x + (-c)))).contMDiff

/-- Helper for Problem 5-11: the antidiagonal straightening map sends `y = -x` to the real axis
while keeping the first coordinate fixed. -/
noncomputable def quadratic_difference_antidiagonal_straightening : Plane ≃L[ℝ] Plane where
  toLinearEquiv :=
    { toFun := fun p ↦ (p.1, p.1 + p.2)
      invFun := fun p ↦ (p.1, p.2 - p.1)
      left_inv := by
        intro p
        ext <;> simp
      right_inv := by
        intro p
        ext <;> simp
      map_add' := by
        intro p q
        ext <;> simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro a p
        ext <;> simp [mul_add, add_comm, add_left_comm, add_assoc] }
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

/-- Helper for Problem 5-11: the diagonal straightening map sends `y = x` to the real axis while
keeping the first coordinate fixed. -/
noncomputable def quadratic_difference_diagonal_straightening : Plane ≃L[ℝ] Plane where
  toLinearEquiv :=
    { toFun := fun p ↦ (p.1, p.2 - p.1)
      invFun := fun p ↦ (p.1, p.1 + p.2)
      left_inv := by
        intro p
        ext <;> simp
      right_inv := by
        intro p
        ext <;> simp
      map_add' := by
        intro p q
        ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro a p
        ext <;> simp [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc] }
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

/-- Helper for Problem 5-11: the antidiagonal straightening map is a top-regularity
diffeomorphism of the ambient plane. -/
noncomputable def quadratic_difference_antidiagonal_straightening_diffeomorph :
    Plane ≃ₘ^((⊤ : WithTop ℕ∞))⟮𝓘(ℝ, Plane), 𝓘(ℝ, Plane)⟯ Plane where
  toEquiv := quadratic_difference_antidiagonal_straightening.toLinearEquiv.toEquiv
  contMDiff_toFun := by
    -- Continuous linear maps between Euclidean spaces are `C^⊤`.
    simpa [quadratic_difference_antidiagonal_straightening] using
      quadratic_difference_antidiagonal_straightening.contDiff.contMDiff
  contMDiff_invFun := by
    -- The inverse shear is continuous linear as well.
    simpa [quadratic_difference_antidiagonal_straightening] using
      quadratic_difference_antidiagonal_straightening.symm.contDiff.contMDiff

/-- Helper for Problem 5-11: the diagonal straightening map is likewise a top-regularity
diffeomorphism of the ambient plane. -/
noncomputable def quadratic_difference_diagonal_straightening_diffeomorph :
    Plane ≃ₘ^((⊤ : WithTop ℕ∞))⟮𝓘(ℝ, Plane), 𝓘(ℝ, Plane)⟯ Plane where
  toEquiv := quadratic_difference_diagonal_straightening.toLinearEquiv.toEquiv
  contMDiff_toFun := by
    -- This shear is continuous linear, hence `C^⊤`.
    simpa [quadratic_difference_diagonal_straightening] using
      quadratic_difference_diagonal_straightening.contDiff.contMDiff
  contMDiff_invFun := by
    -- The inverse shear is again continuous linear.
    simpa [quadratic_difference_diagonal_straightening] using
      quadratic_difference_diagonal_straightening.symm.contDiff.contMDiff

/-- Helper for Problem 5-11: the inverse antidiagonal straightening map has the explicit affine
formula `(u, v) ↦ (u, v - u)`. -/
@[simp] lemma quadratic_difference_antidiagonal_straightening_symm_apply (p : Plane) :
    quadratic_difference_antidiagonal_straightening.symm p = (p.1, p.2 - p.1) := rfl

/-- Helper for Problem 5-11: the inverse diagonal straightening map has the explicit affine
formula `(u, v) ↦ (u, u + v)`. -/
@[simp] lemma quadratic_difference_diagonal_straightening_symm_apply (p : Plane) :
    quadratic_difference_diagonal_straightening.symm p = (p.1, p.1 + p.2) := rfl

/-- Helper for Problem 5-11: the real-axis inclusion is already in the normal form for a
top-regularity immersion with complement `ℝ`. -/
lemma quadratic_difference_real_axis_inclusion_isImmersionOfComplement_top :
    IsImmersionOfComplement ℝ 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
      quadratic_difference_real_axis_inclusion := by
  intro u
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (by
      -- The model inclusion is assembled from the identity and constant coordinates.
      simpa [quadratic_difference_real_axis_inclusion] using
        ((continuous_id : Continuous fun x : ℝ ↦ x).prodMk continuous_const).continuousAt)
    (ContinuousLinearEquiv.refl ℝ Plane)
    (OpenPartialHomeomorph.refl ℝ)
    (OpenPartialHomeomorph.refl Plane)
  · simp
  · simp
  · simpa using (contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ)).id_mem_maximalAtlas
  · simpa using (contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ, Plane)).id_mem_maximalAtlas
  · intro x hx
    -- In identity charts, the written-in-charts map is literally `u ↦ (u, 0)`.
    simp [quadratic_difference_real_axis_inclusion]

/-- Helper for Problem 5-11: the rational middle scalar map is `C^⊤` on the whole punctured cut
source because the denominator never vanishes there. -/
lemma quadratic_difference_middle_scalar_real_contDiffOn_cut :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) quadratic_difference_middle_scalar_real
      (quadratic_difference_cut_source : Set ℝ) := by
  intro x hx
  have hden_ne : 1 - x ^ 2 ≠ 0 := by
    intro hzero
    have hsquare : x ^ 2 = 1 := by
      nlinarith
    have hcases : x = 1 ∨ x = -1 := by
      rw [← one_pow 2, sq_eq_sq_iff_eq_or_eq_neg] at hsquare
      simpa using hsquare
    rcases hcases with hcase | hcase
    · exact hx.2 hcase
    · exact hx.1 hcase
  -- The inverse-function-theorem input is the ordinary smooth quotient formula.
  simpa [quadratic_difference_middle_scalar_real] using
    (contDiffAt_id.div (contDiffAt_const.sub ((contDiffAt_id : ContDiffAt ℝ
      (⊤ : WithTop ℕ∞) (fun x : ℝ ↦ x) x).pow 2)) hden_ne).contDiffWithinAt

/-- Helper for Problem 5-11: the rational middle scalar coordinate is a top-regularity local
diffeomorphism at every cut-source point. -/
lemma quadratic_difference_middle_scalar_isLocalDiffeomorphAt_top
    (t : quadratic_difference_cut_source) :
    IsLocalDiffeomorphAt 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
      quadratic_difference_middle_scalar_real (t : ℝ) := by
  let c : ℝ := ((1 + (t : ℝ) ^ 2) / (1 - (t : ℝ) ^ 2) ^ 2)
  have hc_ne : c ≠ 0 := by
    have hnum_pos : 0 < 1 + (t : ℝ) ^ 2 := by positivity
    have hden_ne : 1 - (t : ℝ) ^ 2 ≠ 0 := by
      intro hzero
      have hsquare : (t : ℝ) ^ 2 = 1 := by
        nlinarith
      have hcases : (t : ℝ) = 1 ∨ (t : ℝ) = -1 := by
        rw [← one_pow 2, sq_eq_sq_iff_eq_or_eq_neg] at hsquare
        simpa using hsquare
      rcases hcases with hcase | hcase
      · exact t.2.2 hcase
      · exact t.2.1 hcase
    exact div_ne_zero (ne_of_gt hnum_pos) (pow_ne_zero 2 hden_ne)
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc_ne)
  have hΩ : ((quadratic_difference_cut_source : Set ℝ)) ∈ nhds (t : ℝ) :=
    quadratic_difference_cut_source.2.mem_nhds t.2
  have hContDiffOn :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞) quadratic_difference_middle_scalar_real
        (quadratic_difference_cut_source : Set ℝ) :=
    quadratic_difference_middle_scalar_real_contDiffOn_cut
  have hContDiffAt :
      ContDiffAt ℝ (⊤ : WithTop ℕ∞) quadratic_difference_middle_scalar_real (t : ℝ) := by
    exact (hContDiffOn (t : ℝ) t.2).contDiffAt hΩ
  have hderiv :=
    quadratic_difference_middle_scalar_real_hasDerivAt (t : ℝ) t.2.1 t.2.2
  have hfderiv_eq :
      fderiv ℝ quadratic_difference_middle_scalar_real (t : ℝ) =
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c) := by
    simpa [c] using hderiv.hasFDerivAt.fderiv
  have he_map :
      (e : ℝ →L[ℝ] ℝ) =
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c := by
    ext x
    simp [e, c, ContinuousLinearMap.smulRight_apply]
  have he_eq :
      fderiv ℝ quadratic_difference_middle_scalar_real (t : ℝ) = (e : ℝ →L[ℝ] ℝ) := by
    rw [hfderiv_eq, he_map.symm]
  have hg_fderiv :
      HasFDerivAt quadratic_difference_middle_scalar_real (e : ℝ →L[ℝ] ℝ) (t : ℝ) := by
    simpa [he_eq, ContinuousLinearMap.toSpanSingleton, c] using hderiv.hasFDerivAt
  have hInv : (fderiv ℝ quadratic_difference_middle_scalar_real (t : ℝ)).IsInvertible := by
    rw [he_eq]
    simpa using (ContinuousLinearMap.isInvertible_equiv (f := e))
  obtain ⟨Ψ, hΨt, _hsource, _htarget, hEqΨ⟩ :=
    model_partialDiffeomorph_of_inverse_function_theorem
      (𝕜 := ℝ) (E := ℝ) (F := ℝ)
      (g := quadratic_difference_middle_scalar_real)
      (a := (t : ℝ))
      (Ω := (quadratic_difference_cut_source : Set ℝ))
      (T := Set.univ)
      (f' := e)
      hΩ
      hContDiffOn
      (by intro x hx; simp)
      hContDiffAt
      hg_fderiv
      (by simp)
      hInv
  -- Package the inverse-function-theorem branch directly as the local-diffeomorphism witness.
  exact ⟨Ψ, hΨt, hEqΨ⟩

/-- Helper for Problem 5-11: the left affine source coordinate is a top-level immersion because it
is the open inclusion followed by translation by `1`. -/
lemma quadratic_difference_left_source_coordinate_isImmersionAt_top
    (t : quadratic_difference_cut_source) :
    IsImmersionAtOfComplement (PUnit.{1} × PUnit.{1}) 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
      (fun s : quadratic_difference_cut_source ↦ (s : ℝ) + 1) t := by
  let hOpen :
      IsImmersionAtOfComplement PUnit 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
        (Subtype.val : quadratic_difference_cut_source → ℝ) t :=
    Manifold.IsImmersionAtOfComplement.of_opens
      (I := 𝓘(ℝ)) (n := (⊤ : WithTop ℕ∞)) quadratic_difference_cut_source t
  let hShift :
      IsImmersionAtOfComplement PUnit 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
        (fun x : ℝ ↦ x + 1) (t : ℝ) :=
    quadratic_difference_model_localDiffeomorphAt_isImmersionAtOfComplement_punit
      ((quadratic_difference_real_add_const_diffeomorph 1).isLocalDiffeomorph (t : ℝ))
  -- Compose the open inclusion with the ambient translation to get the source coordinate.
  simpa [Function.comp] using Manifold.IsImmersionAtOfComplement.ex416_comp hShift hOpen

/-- Helper for Problem 5-11: the right affine source coordinate is a top-level immersion because
it is the open inclusion followed by translation by `-1`. -/
lemma quadratic_difference_right_source_coordinate_isImmersionAt_top
    (t : quadratic_difference_cut_source) :
    IsImmersionAtOfComplement (PUnit.{1} × PUnit.{1}) 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
      (fun s : quadratic_difference_cut_source ↦ (s : ℝ) - 1) t := by
  let hOpen :
      IsImmersionAtOfComplement PUnit 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
        (Subtype.val : quadratic_difference_cut_source → ℝ) t :=
    Manifold.IsImmersionAtOfComplement.of_opens
      (I := 𝓘(ℝ)) (n := (⊤ : WithTop ℕ∞)) quadratic_difference_cut_source t
  let hShift :
      IsImmersionAtOfComplement PUnit 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
        (fun x : ℝ ↦ x - 1) (t : ℝ) :=
    quadratic_difference_model_localDiffeomorphAt_isImmersionAtOfComplement_punit
      ((quadratic_difference_real_add_const_diffeomorph (-1)).isLocalDiffeomorph (t : ℝ))
  -- The right coordinate uses the same open-inclusion route with the opposite translation.
  simpa [Function.comp, sub_eq_add_neg] using
    Manifold.IsImmersionAtOfComplement.ex416_comp hShift hOpen

/-- Helper for Problem 5-11: the middle rational source coordinate is a top-level immersion on the
cut source because it is the open inclusion followed by a local diffeomorphism on `ℝ`. -/
lemma quadratic_difference_middle_source_coordinate_isImmersionAt_top
    (t : quadratic_difference_cut_source) :
    IsImmersionAtOfComplement (PUnit.{1} × PUnit.{1}) 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
      (fun s : quadratic_difference_cut_source ↦ quadratic_difference_middle_scalar_real s) t := by
  let hOpen :
      IsImmersionAtOfComplement PUnit 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
        (Subtype.val : quadratic_difference_cut_source → ℝ) t :=
    Manifold.IsImmersionAtOfComplement.of_opens
      (I := 𝓘(ℝ)) (n := (⊤ : WithTop ℕ∞)) quadratic_difference_cut_source t
  let hMid :
      IsImmersionAtOfComplement PUnit 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
        quadratic_difference_middle_scalar_real (t : ℝ) :=
    quadratic_difference_model_localDiffeomorphAt_isImmersionAtOfComplement_punit
      (quadratic_difference_middle_scalar_isLocalDiffeomorphAt_top t)
  -- This is the source-faithful middle coordinate from the textbook branch parametrization.
  simpa [Function.comp] using Manifold.IsImmersionAtOfComplement.ex416_comp hMid hOpen

/-- Helper for Problem 5-11: the left affine antidiagonal branch is a top-level immersion once we
straighten the antidiagonal to the real axis. -/
lemma quadratic_difference_left_branch_isImmersionAtOfComplement_top
    (t : quadratic_difference_cut_source) :
    IsImmersionAtOfComplement quadratic_difference_branch_complement
      𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) quadratic_difference_left_branch t := by
  let hCoord := quadratic_difference_left_source_coordinate_isImmersionAt_top t
  let hAxisBase :
      IsImmersionOfComplement ℝ 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        quadratic_difference_real_axis_inclusion :=
    quadratic_difference_real_axis_inclusion_isImmersionOfComplement_top
  have hAxis :
      IsImmersionAtOfComplement ((PUnit × PUnit) × ℝ) 𝓘(ℝ) 𝓘(ℝ, Plane)
        (⊤ : WithTop ℕ∞)
        (fun s : quadratic_difference_cut_source ↦ ((s : ℝ) + 1, (0 : ℝ))) t := by
    -- First map the source coordinate to the real axis model inclusion.
    exact Manifold.IsImmersionAtOfComplement.ex416_comp
      (x := t)
      (f := fun s : quadratic_difference_cut_source ↦ (s : ℝ) + 1)
      (g := quadratic_difference_real_axis_inclusion)
      (hAxisBase.isImmersionAt ((t : ℝ) + 1))
      hCoord
  have hStraight :
      IsImmersionAtOfComplement PUnit 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        quadratic_difference_antidiagonal_straightening_diffeomorph.symm
        ((t : ℝ) + 1, (0 : ℝ)) := by
    -- Then invert the ambient straightening map to recover the original branch.
    exact quadratic_difference_model_localDiffeomorphAt_isImmersionAtOfComplement_punit
      (quadratic_difference_antidiagonal_straightening_diffeomorph.symm.isLocalDiffeomorph
        ((t : ℝ) + 1, (0 : ℝ)))
  have hStraight' :
      IsImmersionAtOfComplement PUnit 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        (fun p : Plane ↦ (p.1, p.2 - p.1))
        ((t : ℝ) + 1, (0 : ℝ)) := by
    simpa [quadratic_difference_antidiagonal_straightening_diffeomorph,
      quadratic_difference_antidiagonal_straightening] using hStraight
  have hComp :
      IsImmersionAtOfComplement quadratic_difference_branch_complement
        𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        ((fun p : Plane ↦ (p.1, p.2 - p.1)) ∘
          (fun s : quadratic_difference_cut_source ↦ ((s : ℝ) + 1, (0 : ℝ)))) t := by
    exact Manifold.IsImmersionAtOfComplement.ex416_comp
      (x := t)
      (f := fun s : quadratic_difference_cut_source ↦ ((s : ℝ) + 1, (0 : ℝ)))
      (g := fun p : Plane ↦ (p.1, p.2 - p.1))
      hStraight' hAxis
  have hEq :
      ((fun p : Plane ↦ (p.1, p.2 - p.1)) ∘
        (fun s : quadratic_difference_cut_source ↦ ((s : ℝ) + 1, (0 : ℝ)))) =
        quadratic_difference_left_branch := by
    funext s
    ext
    · rfl
    · simp [quadratic_difference_left_branch, quadratic_difference_left_ambient,
        Function.comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Re-identify the straightened composition with the original left branch.
  exact hEq ▸ hComp

/-- Helper for Problem 5-11: the middle diagonal branch is a top-level immersion after
straightening the diagonal to the real axis and using the rational middle coordinate. -/
lemma quadratic_difference_middle_branch_isImmersionAtOfComplement_top
    (t : quadratic_difference_cut_source) :
    IsImmersionAtOfComplement quadratic_difference_branch_complement
      𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) quadratic_difference_middle_branch t := by
  let hCoord := quadratic_difference_middle_source_coordinate_isImmersionAt_top t
  let hAxisBase :
      IsImmersionOfComplement ℝ 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        quadratic_difference_real_axis_inclusion :=
    quadratic_difference_real_axis_inclusion_isImmersionOfComplement_top
  have hAxis :
      IsImmersionAtOfComplement ((PUnit × PUnit) × ℝ) 𝓘(ℝ) 𝓘(ℝ, Plane)
        (⊤ : WithTop ℕ∞)
        (fun s : quadratic_difference_cut_source ↦
          (quadratic_difference_middle_scalar_real s, (0 : ℝ))) t := by
    -- The middle branch uses the same real-axis model after the scalar coordinate change.
    exact Manifold.IsImmersionAtOfComplement.ex416_comp
      (x := t)
      (f := fun s : quadratic_difference_cut_source ↦ quadratic_difference_middle_scalar_real s)
      (g := quadratic_difference_real_axis_inclusion)
      (hAxisBase.isImmersionAt (quadratic_difference_middle_scalar_real (t : ℝ)))
      hCoord
  have hStraight :
      IsImmersionAtOfComplement PUnit 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        quadratic_difference_diagonal_straightening_diffeomorph.symm
        (quadratic_difference_middle_scalar_real (t : ℝ), 0) := by
    -- The inverse diagonal straightening recovers the original diagonal branch.
    exact quadratic_difference_model_localDiffeomorphAt_isImmersionAtOfComplement_punit
      (quadratic_difference_diagonal_straightening_diffeomorph.symm.isLocalDiffeomorph
        (quadratic_difference_middle_scalar_real (t : ℝ), (0 : ℝ)))
  have hStraight' :
      IsImmersionAtOfComplement PUnit 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        (fun p : Plane ↦ (p.1, p.1 + p.2))
        (quadratic_difference_middle_scalar_real (t : ℝ), (0 : ℝ)) := by
    simpa [quadratic_difference_diagonal_straightening_diffeomorph,
      quadratic_difference_diagonal_straightening] using hStraight
  have hComp :
      IsImmersionAtOfComplement quadratic_difference_branch_complement
        𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        ((fun p : Plane ↦ (p.1, p.1 + p.2)) ∘
          (fun s : quadratic_difference_cut_source ↦
            (quadratic_difference_middle_scalar_real s, (0 : ℝ)))) t := by
    exact Manifold.IsImmersionAtOfComplement.ex416_comp
      (x := t)
      (f := fun s : quadratic_difference_cut_source ↦
        (quadratic_difference_middle_scalar_real s, (0 : ℝ)))
      (g := fun p : Plane ↦ (p.1, p.1 + p.2))
      hStraight' hAxis
  have hEq :
      ((fun p : Plane ↦ (p.1, p.1 + p.2)) ∘
        (fun s : quadratic_difference_cut_source ↦
          (quadratic_difference_middle_scalar_real s, (0 : ℝ)))) =
        quadratic_difference_middle_branch := by
    funext s
    ext
    · rfl
    · simp [quadratic_difference_middle_branch, quadratic_difference_middle_ambient, Function.comp]
  -- Re-identify the straightened composition with the original diagonal branch.
  exact hEq ▸ hComp

/-- Helper for Problem 5-11: the right affine antidiagonal branch is a top-level immersion after
the same antidiagonal straightening and the translated source coordinate `t - 1`. -/
lemma quadratic_difference_right_branch_isImmersionAtOfComplement_top
    (t : quadratic_difference_cut_source) :
    IsImmersionAtOfComplement quadratic_difference_branch_complement
      𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) quadratic_difference_right_branch t := by
  let hCoord := quadratic_difference_right_source_coordinate_isImmersionAt_top t
  let hAxisBase :
      IsImmersionOfComplement ℝ 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        quadratic_difference_real_axis_inclusion :=
    quadratic_difference_real_axis_inclusion_isImmersionOfComplement_top
  have hAxis :
      IsImmersionAtOfComplement ((PUnit × PUnit) × ℝ) 𝓘(ℝ) 𝓘(ℝ, Plane)
        (⊤ : WithTop ℕ∞)
        (fun s : quadratic_difference_cut_source ↦ ((s : ℝ) - 1, (0 : ℝ))) t := by
    -- Straighten the source coordinate to the real axis before undoing the codomain shear.
    exact Manifold.IsImmersionAtOfComplement.ex416_comp
      (x := t)
      (f := fun s : quadratic_difference_cut_source ↦ (s : ℝ) - 1)
      (g := quadratic_difference_real_axis_inclusion)
      (hAxisBase.isImmersionAt ((t : ℝ) - 1))
      hCoord
  have hStraight :
      IsImmersionAtOfComplement PUnit 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        quadratic_difference_antidiagonal_straightening_diffeomorph.symm
        ((t : ℝ) - 1, 0) := by
    -- The same inverse shear recovers the translated antidiagonal ray.
    exact quadratic_difference_model_localDiffeomorphAt_isImmersionAtOfComplement_punit
      (quadratic_difference_antidiagonal_straightening_diffeomorph.symm.isLocalDiffeomorph
        ((t : ℝ) - 1, (0 : ℝ)))
  have hStraight' :
      IsImmersionAtOfComplement PUnit 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        (fun p : Plane ↦ (p.1, p.2 - p.1))
        ((t : ℝ) - 1, (0 : ℝ)) := by
    simpa [quadratic_difference_antidiagonal_straightening_diffeomorph,
      quadratic_difference_antidiagonal_straightening] using hStraight
  have hComp :
      IsImmersionAtOfComplement quadratic_difference_branch_complement
        𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        ((fun p : Plane ↦ (p.1, p.2 - p.1)) ∘
          (fun s : quadratic_difference_cut_source ↦ ((s : ℝ) - 1, (0 : ℝ)))) t := by
    exact Manifold.IsImmersionAtOfComplement.ex416_comp
      (x := t)
      (f := fun s : quadratic_difference_cut_source ↦ ((s : ℝ) - 1, (0 : ℝ)))
      (g := fun p : Plane ↦ (p.1, p.2 - p.1))
      hStraight' hAxis
  have hEq :
      ((fun p : Plane ↦ (p.1, p.2 - p.1)) ∘
        (fun s : quadratic_difference_cut_source ↦ ((s : ℝ) - 1, (0 : ℝ)))) =
        quadratic_difference_right_branch := by
    funext s
    ext
    · rfl
    · simp [quadratic_difference_right_branch, quadratic_difference_right_ambient, Function.comp]
  -- Re-identify the straightened composition with the original right branch.
  exact hEq ▸ hComp

/-- Helper for Problem 5-11: the cut parametrization should satisfy the same immersion chart
normal forms at the outer regularity level used by immersed-curve structures. -/
theorem quadratic_difference_cut_param_isImmersion_top :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) quadratic_difference_cut_param := by
  -- Route correction: the `mfderiv` criterion above closes only the inner `∞` immersion.
  -- Here we follow the source proof and prove `⊤`-regularity by explicit branchwise normal forms.
  refine ⟨quadratic_difference_branch_complement, inferInstance, inferInstance, ?_⟩
  intro t
  rcases quadratic_difference_cut_param_eventuallyEq_active_branch t with
    hleft | hmiddle | hright
  · -- Near a left-source point, the piecewise map agrees with the affine left branch.
    exact (quadratic_difference_left_branch_isImmersionAtOfComplement_top t).congr_of_eventuallyEq
      hleft.symm
  · rcases hmiddle with hmiddle
    -- Near a middle-source point, the piecewise map agrees with the rational diagonal branch.
    exact
      (quadratic_difference_middle_branch_isImmersionAtOfComplement_top t).congr_of_eventuallyEq
        hmiddle.symm
  · -- Near a right-source point, the piecewise map agrees with the translated right branch.
    exact (quadratic_difference_right_branch_isImmersionAtOfComplement_top t).congr_of_eventuallyEq
      hright.symm

/-- Problem 5-11 (2): the crossing `x^2 - y^2 = 0` admits a smooth immersed-curve structure after
changing the topology on the subtype. This is stated directly in the chapter owner
`Set.AdmitsImmersedCurveStructure`. -/
theorem quadraticDifferenceZeroSet_admits_immersed_curve_structure :
    quadraticDifferenceZeroSet.AdmitsImmersedCurveStructure := by
  let _ : TopologicalSpace quadraticDifferenceZeroSet := quadraticDifferenceZeroSet_topology
  have htransport_immersion :
      IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞)
        (fun t ↦
          (((quadratic_difference_cut_equiv.symm.homeomorph).symm t :
            quadraticDifferenceZeroSet) : Plane)) := by
    -- The transported homeomorphism evaluates to the original cut parametrization in ambient
    -- coordinates.
    have htransport_fun :
        (fun t ↦
          (((quadratic_difference_cut_equiv.symm.homeomorph).symm t :
            quadraticDifferenceZeroSet) : Plane)) = quadratic_difference_cut_param := by
      funext t
      rfl
    exact htransport_fun ▸ quadratic_difference_cut_param_isImmersion_top
  refine ⟨quadraticDifferenceZeroSet_topology, ?_⟩
  -- Transport the cut-source manifold structure across the explicit equivalence onto the crossing.
  simpa [quadraticDifferenceZeroSet_topology] using
    quadratic_difference_transport_subset_isImmersedCurveWithTopology
      htransport_immersion
      ((quadratic_difference_cut_equiv.symm.homeomorph).symm) (fun t ↦ rfl)

/-- Helper for Problem 5-11: lowering the differentiability index preserves immersions by keeping
the same chart normal forms. -/
lemma isImmersion_of_le
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H']
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {J : ModelWithCorners 𝕜 E' H'} [IsManifold J (⊤ : WithTop ℕ∞) N]
    {n m : WithTop ℕ∞} {f : M → N} (hmn : m ≤ n)
    (hf : IsImmersion I J n f) :
    IsImmersion I J m f := by
  -- Keep the same global complement and reuse the same local chart presentation.
  let hComp := hf.complement
  let hCompImm := hf.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I) (M := M) hmn) hx.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le (I := J) (M := N) hmn) hx.codChart_mem_maximalAtlas

/-- Helper for Problem 5-11: the cusp zero set used in part (c). -/
abbrev cuspPolynomialZeroSet : Set Plane :=
  {p : Plane | p.1 ^ 2 - p.2 ^ 3 = 0}

/-- Helper for Problem 5-11: pulling back the model-space unit tangent through a local chart
produces a genuine nonzero tangent vector on any smooth curve manifold. -/
lemma exists_nonzero_chart_tangent
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (p : S) :
    ∃ w : TangentSpace 𝓘(ℝ) p, w ≠ 0 := by
  -- Pull the unit tangent in the model chart back through the chart derivative.
  let x : ℝ := extChartAt 𝓘(ℝ) p p
  let u : TangentSpace 𝓘(ℝ) x := (NormedSpace.fromTangentSpace x).symm 1
  obtain ⟨w, hw⟩ :=
    (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ)) (x := p) (y := p)
      (mem_extChartAt_source p)).surjective u
  refine ⟨w, ?_⟩
  intro hw0
  have hu_zero : u = 0 := by
    calc
      u = (mfderiv 𝓘(ℝ) 𝓘(ℝ) (extChartAt 𝓘(ℝ) p) p) 0 := by
        simpa [hw0] using hw.symm
      _ = 0 := by
        simpa using (mfderiv 𝓘(ℝ) 𝓘(ℝ) (extChartAt 𝓘(ℝ) p) p).map_zero
  have hone_zero : (1 : ℝ) = 0 := by
    simpa [u] using congrArg (NormedSpace.fromTangentSpace x) hu_zero
  exact one_ne_zero hone_zero

/-- Helper for Problem 5-11: the subtype inclusion of an immersed curve is smooth because the
immersion normal form writes it as the linear inclusion `u ↦ (u, 0)` in suitable charts. -/
lemma subtype_val_contMDiff_of_isImmersedCurve {S : Set Plane}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane)) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane) := by
  have hSmoothTop :
      ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) (Subtype.val : S → Plane) := by
    intro x
    let hImmAt :
        IsImmersionAt 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) (Subtype.val : S → Plane) x :=
      hImm.isImmersionAt x
    let x' : ℝ := (hImmAt.domChart.extend 𝓘(ℝ)) x
    let L : ℝ →L[ℝ] Plane :=
      hImmAt.equiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ ℝ hImmAt.complement)
    have hcont : ContinuousAt (Subtype.val : S → Plane) x := by
      let h := hImmAt.isImmersionAtOfComplement_complement
      have hdomChart_source : h.domChart.source ∈ nhds x :=
        IsOpen.mem_nhds h.domChart.open_source h.mem_domChart_source
      have hsource : (Subtype.val : S → Plane) ⁻¹' h.codChart.source ∈ nhds x :=
        Filter.mem_of_superset hdomChart_source h.source_subset_preimage_source
      have hEqOn :
          Set.EqOn ((h.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane))
            (h.equiv ∘ fun y : S ↦ (h.domChart.extend 𝓘(ℝ) y, (0 : hImmAt.complement)))
            h.domChart.source := by
        intro y hy
        have hy_target :
            h.domChart.extend 𝓘(ℝ) y ∈ (h.domChart.extend 𝓘(ℝ)).target :=
          (h.domChart.extend 𝓘(ℝ)).map_source <| by
            simpa [OpenPartialHomeomorph.extend_source] using hy
        simpa [Function.comp, OpenPartialHomeomorph.extend_coe, h.domChart.left_inv hy] using
          h.writtenInCharts hy_target
      have hEq :
          ((h.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane)) =ᶠ[nhds x]
            h.equiv ∘ fun y : S ↦ (h.domChart.extend 𝓘(ℝ) y, (0 : hImmAt.complement)) :=
        hEqOn.eventuallyEq_of_mem hdomChart_source
      have hcont_rhs :
          ContinuousAt
            (h.equiv ∘ fun y : S ↦ (h.domChart.extend 𝓘(ℝ) y, (0 : hImmAt.complement))) x := by
        have hcont_dom : ContinuousAt (h.domChart.extend 𝓘(ℝ)) x :=
          h.domChart.continuousAt_extend h.mem_domChart_source
        have hcont_pair :
            ContinuousAt (fun y : S ↦ (h.domChart.extend 𝓘(ℝ) y, (0 : hImmAt.complement))) x :=
          hcont_dom.prodMk continuousAt_const
        simpa [Function.comp] using ContinuousAt.comp h.equiv.continuousAt hcont_pair
      have hcont_extend :
          ContinuousAt ((h.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane)) x :=
        hcont_rhs.congr hEq.symm
      have hcont_chart : ContinuousAt (h.codChart ∘ (Subtype.val : S → Plane)) x := by
        simpa [Function.comp] using (𝓘(ℝ, Plane)).continuousAt_symm.comp hcont_extend
      exact (h.codChart.continuousAt_iff_continuousAt_comp_left hsource).2 hcont_chart
    have hx : x ∈ hImmAt.domChart.source := hImmAt.mem_domChart_source
    have hy : (Subtype.val : S → Plane) x ∈ hImmAt.codChart.source := hImmAt.mem_codChart_source
    -- Rewrite the inclusion in immersion charts and replace it by the linear model map.
    rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas (s := Set.univ)
      (e := hImmAt.domChart) (e' := hImmAt.codChart) hImmAt.domChart_mem_maximalAtlas
      hImmAt.codChart_mem_maximalAtlas hx hy, continuousWithinAt_univ, Set.preimage_univ,
      Set.univ_inter]
    refine ⟨hcont, ?_⟩
    have hmodel :
        ContDiffWithinAt ℝ (⊤ : WithTop ℕ∞) L (Set.range 𝓘(ℝ)) x' := by
      exact L.contDiff.contDiffWithinAt
    have htarget_mem : (hImmAt.domChart.extend 𝓘(ℝ)).target ∈ nhdsWithin x' (Set.range 𝓘(ℝ)) := by
      simpa [x'] using hImmAt.domChart.extend_target_mem_nhdsWithin (I := 𝓘(ℝ)) hx
    have hEq :
        ((hImmAt.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane) ∘
            (hImmAt.domChart.extend 𝓘(ℝ)).symm)
          =ᶠ[nhdsWithin x' (Set.range 𝓘(ℝ))] L := by
      refine Filter.eventuallyEq_of_mem htarget_mem ?_
      intro z hz
      simpa [Function.comp, L] using hImmAt.writtenInCharts hz
    have hx'_target : x' ∈ (hImmAt.domChart.extend 𝓘(ℝ)).target :=
      (hImmAt.domChart.extend 𝓘(ℝ)).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hx
    have hx'_range : x' ∈ Set.range 𝓘(ℝ) :=
      hImmAt.domChart.extend_target_subset_range hx'_target
    exact hmodel.congr_of_eventuallyEq hEq <| hEq.eq_of_nhdsWithin hx'_range
  exact hSmoothTop.of_le le_top

/-- Helper for Problem 5-11: differentiating the immersion normal form gives the chart-level
pushforward identity needed to control subtype tangent vectors. -/
lemma plane_subtype_val_chart_pushforward_eq_model {S : Set Plane}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane))
    (p : S) (w : TangentSpace 𝓘(ℝ) p) :
    let hImmAt := hImm.isImmersionAt p
    let L : ℝ →L[ℝ] Plane :=
      hImmAt.equiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ ℝ hImmAt.complement)
    (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (hImmAt.codChart.extend 𝓘(ℝ, Plane))
        ((Subtype.val : S → Plane) p))
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p w) =
      L ((mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w) := by
  let hImmAt := hImm.isImmersionAt p
  let L : ℝ →L[ℝ] Plane :=
    hImmAt.equiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ ℝ hImmAt.complement)
  have hdomChart_source : hImmAt.domChart.source ∈ nhds p :=
    IsOpen.mem_nhds hImmAt.domChart.open_source hImmAt.mem_domChart_source
  have hEqOn :
      Set.EqOn ((hImmAt.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane))
        (L ∘ (hImmAt.domChart.extend 𝓘(ℝ))) hImmAt.domChart.source := by
    intro y hy
    -- Read the immersion normal form directly on the source chart neighborhood.
    have hy_target :
        hImmAt.domChart.extend 𝓘(ℝ) y ∈ (hImmAt.domChart.extend 𝓘(ℝ)).target :=
      (hImmAt.domChart.extend 𝓘(ℝ)).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hy
    simpa [Function.comp, L, OpenPartialHomeomorph.extend_coe,
      hImmAt.domChart.left_inv hy, ContinuousLinearMap.comp_apply] using
      hImmAt.writtenInCharts hy_target
  have hEq :
      ((hImmAt.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane)) =ᶠ[nhds p]
        L ∘ (hImmAt.domChart.extend 𝓘(ℝ)) :=
    hEqOn.eventuallyEq_of_mem hdomChart_source
  have hsub :
      MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p := by
    -- The immersed inclusion is already smooth by the chart-normal-form argument.
    exact
      (subtype_val_contMDiff_of_isImmersedCurve hImm).mdifferentiableAt
        (by simp : (⊤ : ℕ∞ω) ≠ 0)
  have hdomChart_mem_maximalAtlas_one :
      hImmAt.domChart ∈ IsManifold.maximalAtlas 𝓘(ℝ) 1 S :=
    IsManifold.maximalAtlas_subset_of_le (I := 𝓘(ℝ)) (M := S)
      (m := 1) (n := (⊤ : ℕ∞ω)) (by simp) hImmAt.domChart_mem_maximalAtlas
  have hcodChart_mem_maximalAtlas_one :
      hImmAt.codChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) 1 Plane :=
    IsManifold.maximalAtlas_subset_of_le (I := 𝓘(ℝ, Plane)) (M := Plane)
      (m := 1) (n := (⊤ : ℕ∞ω)) (by simp) hImmAt.codChart_mem_maximalAtlas
  have hdom :
      MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p := by
    -- Maximal-atlas charts are differentiable at source points.
    exact
      (contMDiffAt_extend (I := 𝓘(ℝ)) (e := hImmAt.domChart)
        hdomChart_mem_maximalAtlas_one hImmAt.mem_domChart_source).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hcod :
      MDifferentiableAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane)
        (hImmAt.codChart.extend 𝓘(ℝ, Plane)) ((Subtype.val : S → Plane) p) := by
    -- The ambient chart is differentiable for the same reason.
    exact
      (contMDiffAt_extend (I := 𝓘(ℝ, Plane)) (e := hImmAt.codChart)
        hcodChart_mem_maximalAtlas_one hImmAt.mem_codChart_source).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hL :
      MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Plane) L (hImmAt.domChart.extend 𝓘(ℝ) p) := by
    -- The model linear map has the expected derivative.
    exact L.contMDiffAt.mdifferentiableAt (by simp : (1 : ℕ∞ω) ≠ 0)
  have hmfderiv_eq :
      mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane)
        (((hImmAt.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane))) p =
      mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (L ∘ (hImmAt.domChart.extend 𝓘(ℝ))) p := by
    -- Differentiate the two eventually equal chart expressions.
    exact hEq.mfderiv_eq
  have hleft :
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (hImmAt.codChart.extend 𝓘(ℝ, Plane))
          ((Subtype.val : S → Plane) p))
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p w) =
      mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane)
        (((hImmAt.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane))) p w := by
    symm
    exact mfderiv_comp_apply (x := p) hcod hsub w
  have hright :
      mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (L ∘ (hImmAt.domChart.extend 𝓘(ℝ))) p w =
        L ((mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w) := by
    simpa [Function.comp, mfderiv_eq_fderiv] using
      (mfderiv_comp_apply (x := p) (g := L) (f := hImmAt.domChart.extend 𝓘(ℝ))
        hL hdom w)
  -- Apply the chain rule to the chart-normal-form identity.
  exact hleft.trans <| hmfderiv_eq ▸ hright

/-- Helper for Problem 5-11: chart inverses are differentiable within the model range at source
points of maximal-atlas charts. -/
lemma plane_chart_extend_symm_mdifferentiableWithin_range {S : Type*}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    {e : OpenPartialHomeomorph S ℝ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ) ⊤ S) {p : S} (hp : p ∈ e.source) :
    MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)).symm (Set.range 𝓘(ℝ))
      (e.extend 𝓘(ℝ) p) := by
  letI : IsManifold 𝓘(ℝ) 1 S :=
    IsManifold.of_le (m := 1) (n := (⊤ : ℕ∞ω)) (by simp)
  have he_one : e ∈ IsManifold.maximalAtlas 𝓘(ℝ) 1 S :=
    IsManifold.maximalAtlas_subset_of_le (I := 𝓘(ℝ)) (M := S)
      (m := 1) (n := (⊤ : ℕ∞ω)) (by simp) he
  have hid :
      MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ) (id : S → S) Set.univ p := by
    -- Start from the trivial differentiability of the identity map.
    simpa using (mdifferentiableWithinAt_id (I := 𝓘(ℝ)) (s := Set.univ) (x := p) :
      MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ) (id : S → S) Set.univ p)
  -- Re-express the identity in source-chart coordinates.
  simpa [Function.comp] using
    (mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas
      (I := 𝓘(ℝ)) (I' := 𝓘(ℝ)) (e := e) (f := id) (s := Set.univ) he_one hp).mp hid

/-- Helper for Problem 5-11: differentiating the chart left-inverse identity gives a concrete
left inverse for the derivative of the source chart. -/
lemma plane_chart_extend_mfderiv_left_inverse {S : Type*}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    {e : OpenPartialHomeomorph S ℝ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ) ⊤ S) {p : S} (hp : p ∈ e.source) :
    (mfderivWithin 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)).symm (Set.range 𝓘(ℝ))
        (e.extend 𝓘(ℝ) p)).comp
      (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ) p) := by
  letI : IsManifold 𝓘(ℝ) 1 S :=
    IsManifold.of_le (m := 1) (n := (⊤ : ℕ∞ω)) (by simp)
  have he_one : e ∈ IsManifold.maximalAtlas 𝓘(ℝ) 1 S :=
    IsManifold.maximalAtlas_subset_of_le (I := 𝓘(ℝ)) (M := S)
      (m := 1) (n := (⊤ : ℕ∞ω)) (by simp) he
  have hsource_unique : UniqueMDiffWithinAt 𝓘(ℝ) e.source p :=
    e.open_source.uniqueMDiffWithinAt hp
  have hchart :
      MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p := by
    -- Maximal-atlas charts are differentiable at source points.
    exact
      (contMDiffAt_extend (I := 𝓘(ℝ)) (e := e) he_one hp).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hrange :
      MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)).symm (Set.range 𝓘(ℝ))
        (e.extend 𝓘(ℝ) p) :=
    plane_chart_extend_symm_mdifferentiableWithin_range he hp
  have hchart_within :
      mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p =
        mfderivWithin 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) e.source p := by
    -- On the open chart source, within and ordinary derivatives agree.
    symm
    exact mfderivWithin_eq_mfderiv hsource_unique hchart
  rw [hchart_within, ← mfderivWithin_comp_of_eq]
  · -- Route correction: differentiate the left-inverse identity on `e.source`.
    rw [← mfderivWithin_id hsource_unique]
    apply Filter.EventuallyEq.mfderivWithin_eq_of_mem
    · refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
      intro z hz
      simpa [Function.comp] using e.extend_left_inv (I := 𝓘(ℝ)) hz
    · exact hp
  · exact hrange
  · exact hchart.mdifferentiableWithinAt
  · intro z hz
    have hz_target : e.extend 𝓘(ℝ) z ∈ (e.extend 𝓘(ℝ)).target :=
      (e.extend 𝓘(ℝ)).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hz
    exact e.extend_target_subset_range hz_target
  · exact hsource_unique
  · rfl

/-- Helper for Problem 5-11: the derivative of a source chart is injective because the chart
inverse cancels it on the chart source. -/
lemma plane_chart_extend_mfderiv_injective {S : Type*}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    {e : OpenPartialHomeomorph S ℝ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ) ⊤ S) {p : S} (hp : p ∈ e.source) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p) := by
  let Linv :=
    mfderivWithin 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)).symm (Set.range 𝓘(ℝ)) (e.extend 𝓘(ℝ) p)
  intro w₁ w₂ hw
  have hleft := plane_chart_extend_mfderiv_left_inverse he hp
  have hp_left : (e.extend 𝓘(ℝ)).symm (e.extend 𝓘(ℝ) p) = p :=
    e.extend_left_inv (I := 𝓘(ℝ)) hp
  have hw_push :
      Linv (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p w₁) =
        Linv (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p w₂) := by
    simpa [Linv] using congrArg Linv hw
  have hw₁ :
      ((Linv.comp (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p)) w₁) = w₁ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L w₁) hleft
  have hw₂ :
      ((Linv.comp (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p)) w₂) = w₂ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L w₂) hleft
  have hw₁' : w₁ = Linv (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p w₁) := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using hw₁.symm
  have hw₂' : Linv (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p w₂) = w₂ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using hw₂
  -- Apply the derivative-level left inverse to both source-chart tangent vectors.
  exact hw₁'.trans (hw_push.trans hw₂')

/-- Helper for Problem 5-11: the differential of an immersed plane-subtype inclusion is injective
at every point. -/
lemma plane_subtype_val_mfderiv_injective_of_isImmersion {S : Set Plane}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane))
    (p : S) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p) := by
  let hImmAt := hImm.isImmersionAt p
  let L : ℝ →L[ℝ] Plane :=
    hImmAt.equiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ ℝ hImmAt.complement)
  have hL_injective : Function.Injective L := by
    intro u v huv
    have hpair :
        (u, (0 : hImmAt.complement)) = (v, (0 : hImmAt.complement)) := by
      apply hImmAt.equiv.injective
      simpa [L, ContinuousLinearMap.comp_apply] using huv
    exact (Prod.mk.inj hpair).1
  intro w₁ w₂ hw
  have hw_chart :
      L ((mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w₁) =
        L ((mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w₂) := by
    have hw₁_model :
        L ((mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w₁) =
          (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (hImmAt.codChart.extend 𝓘(ℝ, Plane))
            ((Subtype.val : S → Plane) p))
            (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p w₁) := by
      simpa [hImmAt, L] using
        (plane_subtype_val_chart_pushforward_eq_model hImm p w₁).symm
    have hw₂_model :
        (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (hImmAt.codChart.extend 𝓘(ℝ, Plane))
          ((Subtype.val : S → Plane) p))
          (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p w₂) =
        L ((mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w₂) := by
      simpa [hImmAt, L] using plane_subtype_val_chart_pushforward_eq_model hImm p w₂
    -- Compare the two vectors after applying the codomain chart derivative.
    exact hw₁_model.trans <| by simpa [hw] using hw₂_model
  have hsource_chart :
      (mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w₁ =
        (mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w₂ :=
    hL_injective hw_chart
  exact
    plane_chart_extend_mfderiv_injective hImmAt.domChart_mem_maximalAtlas
      hImmAt.mem_domChart_source hsource_chart

/-- Helper for Problem 5-11: an immersed subtype inclusion sends every nonzero intrinsic tangent
vector to a nonzero ambient tangent vector. -/
lemma problem_5_11_pushforward_nonzero_tangent {S : Set Plane}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane))
    (p : S) {w : TangentSpace 𝓘(ℝ) p} (hw : w ≠ 0) :
    let v := mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p w
    v ∈ (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p).range ∧ v ≠ 0 := by
  dsimp
  constructor
  · exact ⟨w, rfl⟩
  · intro hzero
    have hinj :
        Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p) :=
      plane_subtype_val_mfderiv_injective_of_isImmersion hImm p
    exact hw <| hinj <| by simpa using hzero

/-- Helper for Problem 5-11: the ambient velocity of a subtype-valued smooth curve is the
subtype inclusion derivative applied to its intrinsic tangent vector. -/
lemma plane_ambient_curve_velocity_eq_subtype_mfderiv_tangent
    {S : Set Plane} [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane))
    {p : S} (γ : SmoothCurveAt 𝓘(ℝ) p) :
    γ.source ▸ curve_velocityWithin 𝓘(ℝ, Plane) (((↑) : S → Plane) ∘ γ) γ.sourceSet 0 =
      mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p γ.tangentVector := by
  rcases γ with ⟨r, f, hs, hsm⟩
  let γ0 : SmoothCurveAt 𝓘(ℝ) p := ⟨r, f, hs, hsm⟩
  have hsub : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) (f 0) := by
    simpa [hs] using
      (subtype_val_contMDiff_of_isImmersedCurve hImm).mdifferentiableAt (by simp : (⊤ : ℕ∞ω) ≠ 0)
  have hγ :
      MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ) f γ0.sourceSet 0 := by
    exact (γ0.smooth.mdifferentiableOn (by simp)) 0 γ0.zero_mem_sourceSet
  -- Differentiate the ambient curve using the chain rule for the subtype inclusion.
  have hcomp :
      curve_velocityWithin 𝓘(ℝ, Plane) (((↑) : S → Plane) ∘ f) γ0.sourceSet 0 =
        mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) (f 0)
          (curve_velocityWithin 𝓘(ℝ) f γ0.sourceSet 0) :=
    composite_curve_velocity
      (I := 𝓘(ℝ)) (I' := 𝓘(ℝ, Plane)) (J := γ0.sourceSet) (t₀ := 0)
      (F := (Subtype.val : S → Plane)) (γ := f) γ0.uniqueMDiffWithinAt_sourceSet hsub hγ
  cases hs
  simpa [γ0, SmoothCurveAt.tangentVector, Function.comp] using hcomp

/-- Helper for Problem 5-11: a tangent vector in the image of the immersed subtype inclusion comes
from a subtype smooth curve whose ambient velocity realizes that vector. -/
lemma problem_5_11_subtype_tangent_curve_bridge {S : Set Plane}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane))
    {p : S} {v : TangentSpace 𝓘(ℝ, Plane) (p : Plane)}
    (hv : v ∈ (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p).range) :
    ∃ γ : SmoothCurveAt 𝓘(ℝ) p,
      γ.source ▸ curve_velocityWithin 𝓘(ℝ, Plane) (((↑) : S → Plane) ∘ γ) γ.sourceSet 0 = v := by
  letI : IsManifold 𝓘(ℝ) ∞ S := IsManifold.of_le le_top
  rcases hv with ⟨w, rfl⟩
  rcases exists_smoothCurveAt_tangentVector_eq (I := 𝓘(ℝ)) p w with ⟨γ, hγ⟩
  refine ⟨γ, ?_⟩
  -- Realize the ambient velocity by differentiating the subtype inclusion along `γ`.
  simpa [hγ] using plane_ambient_curve_velocity_eq_subtype_mfderiv_tangent (hImm := hImm) (γ := γ)

/-- Helper for Problem 5-11: if `g` has zero derivative at the origin and eventually dominates
`|f|`, then `f` also has zero derivative at the origin. -/
lemma hasDerivAt_zero_of_eventually_abs_le {f g : ℝ → ℝ}
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hg : HasDerivAt g 0 0)
    (hbound : ∀ᶠ t in nhds 0, |f t| ≤ g t) :
    HasDerivAt f 0 0 := by
  -- Convert the zero derivative of `g` into a little-`o` estimate.
  have hgLittleRaw :
      (fun h : ℝ ↦ g (0 + h) - g 0 - h • (0 : ℝ)) =o[nhds 0] fun h ↦ h :=
    (hasDerivAt_iff_isLittleO_nhds_zero).mp hg
  have hgLittle :
      (fun h : ℝ ↦ g h) =o[nhds 0] fun h ↦ h := by
    simpa [hg0] using hgLittleRaw
  -- The eventual domination upgrades `f` to an `O(g)` estimate.
  have hfgBig :
      (fun h : ℝ ↦ f h) =O[nhds 0] fun h ↦ g h := by
    refine Asymptotics.IsBigO.of_bound' ?_
    filter_upwards [hbound] with h hh
    have hnonneg : 0 ≤ g h := le_trans (abs_nonneg _) hh
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hh
  have hfLittle :
      (fun h : ℝ ↦ f h) =o[nhds 0] fun h ↦ h :=
    hfgBig.trans_isLittleO hgLittle
  have hfLittleRaw :
      (fun h : ℝ ↦ f (0 + h) - f 0 - h • (0 : ℝ)) =o[nhds 0] fun h ↦ h := by
    simpa [hf0] using hfLittle
  -- Repackage the little-`o` estimate as a zero derivative statement.
  exact (hasDerivAt_iff_isLittleO_nhds_zero).2 hfLittleRaw

/-- Helper for Problem 5-11: every differentiable ambient curve through the cusp origin has zero
ambient velocity there. -/
lemma ambient_velocity_zero_of_cusp_curve
    {r : Set.Ioi (0 : ℝ)} {g : ℝ → Plane}
    (h0 : g 0 = (0, 0))
    (hgDiff0 : DifferentiableAt ℝ g 0)
    (hcusp : ∀ t ∈ Set.Ioo (-(r : ℝ)) (r : ℝ), g t ∈ cuspPolynomialZeroSet) :
    curve_velocityWithin 𝓘(ℝ, Plane) g (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 = 0 := by
  let s : Set ℝ := Set.Ioo (-(r : ℝ)) (r : ℝ)
  let x : ℝ → ℝ := fun t ↦ (g t).1
  let y : ℝ → ℝ := fun t ↦ (g t).2
  have hsOpen : IsOpen s := by
    simpa [s] using isOpen_Ioo
  have hrpos : (0 : ℝ) < r := r.2
  have hzero : (0 : ℝ) ∈ s := by
    constructor
    · exact neg_lt_zero.mpr hrpos
    · exact hrpos
  have hsNhds : s ∈ nhds (0 : ℝ) := hsOpen.mem_nhds hzero
  have hsUnique : UniqueMDiffWithinAt 𝓘(ℝ) s 0 := by
    simpa [s] using hsOpen.uniqueMDiffWithinAt (I := 𝓘(ℝ)) hzero
  have hgMDiff0 : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Plane) g 0 :=
    hgDiff0.mdifferentiableAt
  have hwithin_eq :
      curve_velocityWithin 𝓘(ℝ, Plane) g s 0 = curve_velocity 𝓘(ℝ, Plane) g 0 :=
    curve_velocityWithin_eq_curve_velocity hsUnique hgMDiff0
  have hx0 : x 0 = 0 := by
    simpa [x] using congrArg Prod.fst h0
  have hy0 : y 0 = 0 := by
    simpa [y] using congrArg Prod.snd h0
  have hy_nonneg : ∀ t ∈ s, 0 ≤ y t := by
    intro t ht
    have hEq : x t ^ 2 - y t ^ 3 = 0 := by
      have ht' : g t ∈ cuspPolynomialZeroSet := hcusp t (by simpa [s] using ht)
      simpa [x, y, cuspPolynomialZeroSet] using ht'
    have hy_cube_nonneg : 0 ≤ y t ^ 3 := by
      nlinarith [sq_nonneg (x t), hEq]
    by_contra hy_nonneg_t
    have hy_neg : y t < 0 := lt_of_not_ge hy_nonneg_t
    have hy_sq_pos : 0 < y t ^ 2 := by
      nlinarith
    have hy_cube_neg : y t ^ 3 < 0 := by
      have : y t * (y t ^ 2) < 0 := mul_neg_of_neg_of_pos hy_neg hy_sq_pos
      simpa [pow_succ, pow_two, mul_assoc] using this
    linarith
  have hyMinOn : IsMinOn y s 0 := by
    intro t ht
    -- The cusp relation forces `y(t) ≥ 0 = y(0)`.
    calc
      y 0 = 0 := hy0
      _ ≤ y t := hy_nonneg t ht
  have hyLocalMin : IsLocalMin y 0 := hyMinOn.isLocalMin hsNhds
  have hxDiff0 : DifferentiableAt ℝ x 0 := by
    simpa [x] using hgDiff0.fst
  have hyDiff0 : DifferentiableAt ℝ y 0 := by
    simpa [y] using hgDiff0.snd
  have hyderiv_zero : deriv y 0 = 0 := hyLocalMin.deriv_eq_zero
  have hyHasDerivZero : HasDerivAt y 0 0 := by
    simpa [hyderiv_zero] using hyDiff0.hasDerivAt
  have hy_small : ∀ᶠ t in nhds 0, |y t| < 1 := by
    have hIoo : Set.Ioo (-1 : ℝ) 1 ∈ nhds (y 0) := by
      simpa [hy0] using Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)
    have hy_mem : ∀ᶠ t in nhds 0, y t ∈ Set.Ioo (-1 : ℝ) 1 := hyDiff0.continuousAt hIoo
    filter_upwards [hy_mem] with t ht
    exact abs_lt.mpr ht
  have hx_abs_le : ∀ᶠ t in nhds 0, |x t| ≤ y t := by
    filter_upwards [hsNhds, hy_small] with t ht hylt
    have hxy : x t ^ 2 = y t ^ 3 := by
      have hEq : x t ^ 2 - y t ^ 3 = 0 := by
        have ht' : g t ∈ cuspPolynomialZeroSet := hcusp t (by simpa [s] using ht)
        simpa [x, y, cuspPolynomialZeroSet] using ht'
      nlinarith
    have hy_nonneg_t : 0 ≤ y t := hy_nonneg t (by simpa [s] using ht)
    have hy_le_one : y t ≤ 1 := by
      exact le_of_lt ((abs_lt.mp hylt).2)
    have hxy_abs : |x t| ^ 2 = y t ^ 3 := by
      calc
        |x t| ^ 2 = x t ^ 2 := by rw [sq_abs]
        _ = y t ^ 3 := hxy
    have hy_sq_bound : y t ^ 3 ≤ y t ^ 2 := by
      nlinarith [hy_nonneg_t, hy_le_one]
    have habs_sq : |x t| ^ 2 ≤ y t ^ 2 := by
      simpa [hxy_abs] using hy_sq_bound
    nlinarith [abs_nonneg (x t), hy_nonneg_t, habs_sq]
  have hxHasDerivZero : HasDerivAt x 0 0 :=
    hasDerivAt_zero_of_eventually_abs_le hx0 hy0 hyHasDerivZero hx_abs_le
  -- Assemble the ambient derivative from the two coordinate derivatives.
  apply (NormedSpace.fromTangentSpace (g 0)).injective
  rw [hwithin_eq]
  have hpair :
      HasDerivAt g (0, 0) 0 := by
    simpa [x, y] using hxHasDerivZero.prodMk hyHasDerivZero
  have hvelocity :
      NormedSpace.fromTangentSpace (g 0) (curve_velocity 𝓘(ℝ, Plane) g 0) = (0, 0) := by
    have happly :
        fderiv ℝ g 0 1 = (0, 0) := by
      simpa using DFunLike.congr_fun hpair.hasFDerivAt.fderiv 1
    simpa [curve_velocity, mfderiv_eq_fderiv] using happly
  simpa [h0] using hvelocity

/-- Helper for Problem 5-11: every ambient tangent vector in the cusp tangent image at the origin
must vanish. -/
lemma ambient_tangent_zero_at_cusp_origin
    [TopologicalSpace ↥cuspPolynomialZeroSet] [ChartedSpace ℝ ↥cuspPolynomialZeroSet]
    [IsManifold 𝓘(ℝ) ⊤ ↥cuspPolynomialZeroSet]
    (p0 : cuspPolynomialZeroSet) (hp0 : (p0 : Plane) = (0, 0))
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : cuspPolynomialZeroSet → Plane))
    {v : TangentSpace 𝓘(ℝ, Plane) (p0 : Plane)}
    (hv : v ∈ (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane)
      (Subtype.val : cuspPolynomialZeroSet → Plane) p0).range) :
    v = 0 := by
  letI : IsManifold 𝓘(ℝ) ∞ ↥cuspPolynomialZeroSet := IsManifold.of_le le_top
  rcases problem_5_11_subtype_tangent_curve_bridge (hImm := hImm) hv with ⟨γ, hγv⟩
  rcases γ with ⟨r, f, hsource, hsm⟩
  let γ0 : SmoothCurveAt 𝓘(ℝ) p0 := ⟨r, f, hsource, hsm⟩
  let g : ℝ → Plane := fun t ↦ (f t : Plane)
  cases hsource
  have hzero : 0 ∈ Set.Ioo (-(r : ℝ)) (r : ℝ) := by
    constructor
    · exact neg_lt_zero.mpr r.2
    · exact r.2
  have hsNhds : Set.Ioo (-(r : ℝ)) (r : ℝ) ∈ nhds (0 : ℝ) := by
    exact isOpen_Ioo.mem_nhds hzero
  have hgSmooth :
      ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ g (Set.Ioo (-(r : ℝ)) (r : ℝ)) := by
    have hIncl :
        ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) ∞
          (Subtype.val : cuspPolynomialZeroSet → Plane) :=
      (subtype_val_contMDiff_of_isImmersedCurve hImm).of_le le_top
    -- The ambient curve is the subtype curve followed by the immersed inclusion.
    simpa [g] using hIncl.comp_contMDiffOn hsm
  have hgDiff0 : DifferentiableAt ℝ g 0 := by
    have hgContDiffOn : ContDiffOn ℝ ∞ g (Set.Ioo (-(r : ℝ)) (r : ℝ)) := by
      rw [← contMDiffOn_iff_contDiffOn]
      exact hgSmooth
    exact (hgContDiffOn.contDiffAt hsNhds).differentiableAt (by simp)
  have hg0 : g 0 = (0, 0) := by
    simpa [g] using hp0
  have hcusp : ∀ t ∈ Set.Ioo (-(r : ℝ)) (r : ℝ), g t ∈ cuspPolynomialZeroSet := by
    intro t ht
    exact (f t).property
  have hzero_velocity :
      curve_velocityWithin 𝓘(ℝ, Plane) g (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 = 0 :=
    ambient_velocity_zero_of_cusp_curve (r := r) (g := g) hg0 hgDiff0 hcusp
  have hv_zero :
      v = curve_velocityWithin 𝓘(ℝ, Plane) g (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 := by
    simpa [γ0, g, Function.comp, SmoothCurveAt.sourceSet] using hγv.symm
  -- The cusp calculation forces every ambient tangent represented by such a curve to vanish.
  exact hv_zero.trans hzero_velocity

/-- Helper for Problem 5-11: the cusp zero set admits no topology making the subtype inclusion an
immersed smooth curve. -/
theorem cusp_polynomial_zero_set_no_immersed_curve_structure :
    ¬ cuspPolynomialZeroSet.AdmitsImmersedCurveStructure := by
  intro hCurve
  rcases hCurve with ⟨t, hCurve⟩
  letI : TopologicalSpace ↥cuspPolynomialZeroSet := t
  rcases hCurve with ⟨cs, hMan, hImm⟩
  letI : ChartedSpace ℝ ↥cuspPolynomialZeroSet := cs
  letI : IsManifold 𝓘(ℝ) ⊤ ↥cuspPolynomialZeroSet := hMan
  letI : IsManifold 𝓘(ℝ) ∞ ↥cuspPolynomialZeroSet := IsManifold.of_le le_top
  let p0 : cuspPolynomialZeroSet := ⟨(0, 0), by simp [cuspPolynomialZeroSet]⟩
  have hp0 : (p0 : Plane) = (0, 0) := rfl
  obtain ⟨w, hw_ne⟩ := exists_nonzero_chart_tangent (p := p0)
  let v : TangentSpace 𝓘(ℝ, Plane) (p0 : Plane) :=
    mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : cuspPolynomialZeroSet → Plane) p0 w
  have hv :
      v ∈ (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane)
        (Subtype.val : cuspPolynomialZeroSet → Plane) p0).range ∧ v ≠ 0 :=
    problem_5_11_pushforward_nonzero_tangent hImm p0 hw_ne
  have hv_zero : v = 0 :=
    ambient_tangent_zero_at_cusp_origin p0 hp0 hImm hv.1
  -- The immersed chart supplies a nonzero intrinsic tangent, but the cusp kills every ambient one.
  exact hv.2 hv_zero

/-- Problem 5-11 (3): Part (c) for `Ψ(x,y)=x^2-y^3`; its zero set is not an embedded curve in
`ℝ²`. -/
-- Proof sketch: analyze the cusp at the origin and show that the subset topology cannot make the
-- zero set into a smooth embedded `1`-manifold of the plane.
theorem cuspPolynomialZeroSet_not_embedded_curve :
    ¬ ({p : Plane | p.1 ^ 2 - p.2 ^ 3 = 0} : Set Plane).AdmitsEmbeddedCurveStructure := by
  intro hEmbedded
  rcases hEmbedded with ⟨cs, hs, hEmb⟩
  -- Any embedded-curve structure is in particular an immersed-curve structure with the same
  -- subtype topology.
  have hImmersed : cuspPolynomialZeroSet.AdmitsImmersedCurveStructure := by
    refine ⟨inferInstance, ?_⟩
    exact ⟨cs, hs, hEmb.isSmoothEmbedding_subtype_val.isImmersion⟩
  exact cusp_polynomial_zero_set_no_immersed_curve_structure hImmersed

/-- Problem 5-11 (4): Part (c) for `Ψ(x,y)=x^2-y^3`; its zero set admits no topology and smooth
structure making its inclusion into `ℝ²` an immersed curve. -/
-- Proof sketch: any such structure would yield a smooth immersed parametrization of the cusp, but
-- every parametrization through the singular point has vanishing derivative there.
theorem cuspPolynomialZeroSet_no_immersed_curve_structure :
    ¬ ({p : Plane | p.1 ^ 2 - p.2 ^ 3 = 0} : Set Plane).AdmitsImmersedCurveStructure := by
  -- This is the previously established cusp obstruction, rewritten in the original notation.
  simpa [cuspPolynomialZeroSet] using cusp_polynomial_zero_set_no_immersed_curve_structure
