module

public import Topology_Munkres_2000.Book.Example_24_7.Connectedness
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Order.IntermediateValue

public section

open Set

namespace TopologistsSineCurve

/-- Helper for Example 25.2: points on the oscillating graph have positive first coordinate. -/
private lemma curve_fst_pos {p : ℝ × ℝ} (hp : p ∈ curve) : 0 < p.1 := by
  -- Unpack the graph parameter, which lies in `(0, 1]`.
  rcases hp with ⟨x, hx, rfl⟩
  exact hx.1

/-- Helper for Example 25.2: the second coordinate on the graph is `sin (1 / x)`. -/
private lemma curve_snd_eq {p : ℝ × ℝ} (hp : p ∈ curve) :
    p.2 = Real.sin (1 / p.1) := by
  -- Unpack the defining image of the graph.
  rcases hp with ⟨x, hx, rfl⟩
  rfl

/-- Helper for Example 25.2: a carrier point with nonzero first coordinate is on the graph. -/
private lemma mem_curve_of_mem_carrier_fst_ne_zero {p : ℝ × ℝ}
    (hp : p ∈ carrier) (hp_ne : p.1 ≠ 0) : p ∈ curve := by
  -- The carrier partition leaves only the graph once the vertical alternative is excluded.
  rw [carrier_eq_curve_union_vertical] at hp
  rcases hp with hp_curve | hp_vertical
  · exact hp_curve
  · exact False.elim (hp_ne ((mem_vertical_iff p).mp hp_vertical).1)

/-- Helper for Example 25.2: the vertical part's complement is the oscillating part. -/
private lemma verticalPart_compl_eq_curvePart : verticalPartᶜ = curvePart := by
  -- Use the ambient carrier partition and distinguish the two possible pieces.
  ext p
  constructor
  · intro hp
    have hp_union : p.1 ∈ curve ∪ vertical := by
      rw [← carrier_eq_curve_union_vertical]
      exact p.property
    rcases hp_union with hp_curve | hp_vertical
    · exact (mem_curvePart_iff p).mpr hp_curve
    · exact False.elim (hp ((mem_verticalPart_iff p).mpr hp_vertical))
  · intro hp_curve hp_vertical
    have hpos : 0 < p.1.1 := curve_fst_pos ((mem_curvePart_iff p).mp hp_curve)
    have hzero : p.1.1 = 0 :=
      ((mem_vertical_iff p.1).mp ((mem_verticalPart_iff p).mp hp_vertical)).1
    linarith

/-- Helper for Example 25.2: every carrier point lies in one of the two named parts. -/
private lemma mem_curvePart_or_verticalPart (p : Space) :
    p ∈ curvePart ∨ p ∈ verticalPart := by
  -- The complement identity turns membership into a direct case split.
  by_cases hp : p ∈ verticalPart
  · exact Or.inr hp
  · left
    rw [← verticalPart_compl_eq_curvePart]
    exact hp

/-- Helper for Example 25.2: the oscillating part is path connected. -/
private lemma curvePart_isPathConnected : IsPathConnected curvePart := by
  -- Parametrize the graph by the convex interval `(0, 1]`.
  have hone : (1 : ℝ) ∈ Ioc 0 1 := by
    norm_num
  have hinterval : IsPathConnected (Ioc (0 : ℝ) 1) :=
    (convex_Ioc (0 : ℝ) 1).isPathConnected ⟨1, hone⟩
  have hcurve : IsPathConnected curve := by
    rw [curve]
    apply hinterval.image'
    intro x hx
    have hx_ne : x ≠ 0 := ne_of_gt hx.1
    have hrecip : ContinuousAt (fun y : ℝ ↦ 1 / y) x :=
      continuousAt_const.div continuousAt_id hx_ne
    have hsin : ContinuousAt (fun y : ℝ ↦ Real.sin (1 / y)) x :=
      Real.continuous_sin.continuousAt.comp hrecip
    exact (continuousAt_id.prodMk hsin).continuousWithinAt
  -- Pull the ambient path-connected set back to the carrier subtype.
  have hpart : curvePart = Subtype.val ⁻¹' curve := by
    ext p
    exact mem_curvePart_iff p
  rw [hpart]
  exact hcurve.preimage_coe subset_closure

/-- Helper for Example 25.2: the vertical part is path connected. -/
private lemma verticalPart_isPathConnected : IsPathConnected verticalPart := by
  -- The ambient vertical interval is the product of a point and a convex interval.
  have hzero : (0 : ℝ) ∈ Icc (-1) 1 := by
    norm_num
  have hinterval : IsPathConnected (Icc (-1 : ℝ) 1) :=
    (convex_Icc (-1 : ℝ) 1).isPathConnected ⟨0, hzero⟩
  have hvertical : IsPathConnected vertical := by
    have hvertical_eq : vertical = ({0} : Set ℝ) ×ˢ Icc (-1) 1 := by
      ext p
      exact mem_vertical_iff p
    rw [hvertical_eq]
    exact (isPathConnected_singleton 0).prod hinterval
  have hvertical_subset : vertical ⊆ carrier := by
    rw [carrier_eq_curve_union_vertical]
    exact subset_union_right
  -- Pull the ambient product back to the carrier subtype.
  have hpart : verticalPart = Subtype.val ⁻¹' vertical := by
    ext p
    exact mem_verticalPart_iff p
  rw [hpart]
  exact hvertical.preimage_coe hvertical_subset

/-- Helper for Example 25.2: the vertical part is closed in the sine curve. -/
private lemma verticalPart_isClosed_aux : IsClosed verticalPart := by
  -- The ambient vertical interval is closed, and subtype coercion is continuous.
  have hvertical : IsClosed vertical := by
    have hvertical_eq : vertical = ({0} : Set ℝ) ×ˢ Icc (-1) 1 := by
      ext p
      exact mem_vertical_iff p
    rw [hvertical_eq]
    exact isClosed_singleton.prod isClosed_Icc
  have hpart : verticalPart = Subtype.val ⁻¹' vertical := by
    ext p
    exact mem_verticalPart_iff p
  rw [hpart]
  exact hvertical.preimage continuous_subtype_val

/-- Helper for Example 25.2: `sin (1 / u)` attains either extreme arbitrarily near zero. -/
private lemma exists_pos_lt_sin_inv_eq_sign {ε z : ℝ} (hε : 0 < ε)
    (hz : z = 1 ∨ z = -1) :
    ∃ u, 0 < u ∧ u < ε ∧ Real.sin (1 / u) = z := by
  -- Large quarter-period phases have small positive reciprocals and the required sine value.
  rcases hz with rfl | rfl
  · obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (1 / (2 * Real.pi * ε))
    let a : ℝ := Real.pi / 2 + n * (2 * Real.pi)
    have ha_pos : 0 < a := by
      dsimp [a]
      positivity
    have ha_large : 1 / ε < a := by
      have hpi : 0 < 2 * Real.pi := by
        positivity
      have hn' : 1 / ε < (n : ℝ) * (2 * Real.pi) := by
        calc
          1 / ε = (1 / (2 * Real.pi * ε)) * (2 * Real.pi) := by
            field_simp
          _ < (n : ℝ) * (2 * Real.pi) := mul_lt_mul_of_pos_right hn hpi
      dsimp [a]
      linarith [Real.pi_pos]
    refine ⟨1 / a, one_div_pos.mpr ha_pos, ?_, ?_⟩
    · apply (div_lt_iff₀ ha_pos).2
      have hscaled := (div_lt_iff₀ hε).1 ha_large
      nlinarith
    · simp only [one_div, inv_inv]
      exact (Real.sin_add_nat_mul_two_pi _ _).trans Real.sin_pi_div_two
  · obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (1 / (2 * Real.pi * ε))
    let a : ℝ := 3 * Real.pi / 2 + n * (2 * Real.pi)
    have ha_pos : 0 < a := by
      dsimp [a]
      positivity
    have ha_large : 1 / ε < a := by
      have hpi : 0 < 2 * Real.pi := by
        positivity
      have hn' : 1 / ε < (n : ℝ) * (2 * Real.pi) := by
        calc
          1 / ε = (1 / (2 * Real.pi * ε)) * (2 * Real.pi) := by
            field_simp
          _ < (n : ℝ) * (2 * Real.pi) := mul_lt_mul_of_pos_right hn hpi
      dsimp [a]
      linarith [Real.pi_pos]
    refine ⟨1 / a, one_div_pos.mpr ha_pos, ?_, ?_⟩
    · apply (div_lt_iff₀ ha_pos).2
      have hscaled := (div_lt_iff₀ hε).1 ha_large
      nlinarith
    · simp only [one_div, inv_inv]
      dsimp [a]
      rw [Real.sin_add_nat_mul_two_pi]
      have hphase : (3 : ℝ) * Real.pi / 2 = Real.pi / 2 + Real.pi := by
        ring
      rw [hphase, Real.sin_add_pi, Real.sin_pi_div_two]

/-- Helper for Example 25.2: no path in the carrier joins a vertical point to the graph. -/
private lemma not_joinedIn_zero_curve {p q : ℝ × ℝ}
    (hp_zero : p.1 = 0) (hq : q ∈ curve) : ¬ JoinedIn carrier p q := by
  -- Choose a joining path and isolate its greatest parameter with zero first coordinate.
  intro hpq
  classical
  let γ : Path p q := hpq.somePath
  let zeroSet : Set unitInterval := {t | (γ t).1 = 0}
  have hx_cont : Continuous (fun t : unitInterval ↦ (γ t).1) :=
    continuous_fst.comp γ.continuous
  have hy_cont : Continuous (fun t : unitInterval ↦ (γ t).2) :=
    continuous_snd.comp γ.continuous
  have hzero_closed : IsClosed zeroSet := by
    exact isClosed_eq hx_cont continuous_const
  have hzero_nonempty : zeroSet.Nonempty := by
    refine ⟨0, ?_⟩
    dsimp [zeroSet, γ]
    rw [hpq.somePath.source]
    exact hp_zero
  obtain ⟨b, hb_mem, hb_greatest⟩ :=
    hzero_closed.isCompact.exists_isGreatest hzero_nonempty
  have hb_zero : (γ b).1 = 0 := hb_mem
  have hq_fst_pos : 0 < q.1 := curve_fst_pos hq
  have hb_lt_one : b < 1 := by
    rw [unitInterval.lt_one_iff_ne_one]
    intro hb_one
    subst b
    rw [γ.target] at hb_zero
    linarith
  -- Every later path point is nonvertical and therefore lies on the graph.
  have hafter_curve {t : unitInterval} (hbt : b < t) : γ t ∈ curve := by
    apply mem_curve_of_mem_carrier_fst_ne_zero (hpq.somePath_mem t)
    intro ht_zero
    have ht_mem : t ∈ zeroSet := ht_zero
    exact (not_le_of_gt hbt) (hb_greatest ht_mem)
  have hafter_pos {t : unitInterval} (hbt : b < t) : 0 < (γ t).1 :=
    curve_fst_pos (hafter_curve hbt)
  have hafter_snd {t : unitInterval} (hbt : b < t) :
      (γ t).2 = Real.sin (1 / (γ t).1) :=
    curve_snd_eq (hafter_curve hbt)
  -- Choose the extreme value at distance at least one from the limiting ordinate.
  obtain ⟨z : ℝ, hz_sign, hz_far⟩ :
      ∃ z : ℝ, (z = 1 ∨ z = -1) ∧ 1 ≤ |z - (γ b).2| := by
    by_cases hnonneg : 0 ≤ (γ b).2
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [abs_of_nonpos]
      · linarith
      · linarith
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [abs_of_nonneg]
      · linarith
      · linarith
  have hy_at : ContinuousAt (fun t : unitInterval ↦ (γ t).2) b := hy_cont.continuousAt
  have hhalf : (0 : ℝ) < 1 / 2 := by
    norm_num
  obtain ⟨δ, hδ_pos, hδ⟩ := (Metric.continuousAt_iff.mp hy_at) (1 / 2) hhalf
  let η : ℝ := min ((1 - (b : ℝ)) / 2) (δ / 2)
  have hb_real : (b : ℝ) < 1 := by
    exact_mod_cast hb_lt_one
  have hη_pos : 0 < η := by
    dsimp [η]
    have hleft : 0 < (1 - (b : ℝ)) / 2 := by
      linarith
    have hright : 0 < δ / 2 := by
      linarith
    exact lt_min hleft hright
  have hη_lt_one : (b : ℝ) + η < 1 := by
    have hη_le : η ≤ (1 - (b : ℝ)) / 2 := min_le_left _ _
    linarith
  have ht_mem : (b : ℝ) + η ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact add_nonneg b.property.1 hη_pos.le
    · exact hη_lt_one.le
  let t : unitInterval := ⟨(b : ℝ) + η, ht_mem⟩
  have hbt : b < t := by
    rw [← Subtype.coe_lt_coe]
    dsimp [t]
    linarith
  have ht_close : dist t b < δ := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hη_le : η ≤ δ / 2 := min_le_right _ _
    dsimp [t]
    rw [abs_of_nonneg]
    · linarith
    · linarith
  -- Realize the distant extreme below the later first coordinate, then apply the IVT.
  obtain ⟨u, hu_pos, hu_lt, hu_sin⟩ :=
    exists_pos_lt_sin_inv_eq_sign (hafter_pos hbt) hz_sign
  have hu_between : u ∈ Icc ((γ b).1) ((γ t).1) := by
    rw [hb_zero]
    exact ⟨hu_pos.le, hu_lt.le⟩
  obtain ⟨s, hs_bounds, hs_x⟩ :=
    (intermediate_value_Icc hbt.le hx_cont.continuousOn) hu_between
  have hbs : b < s := by
    apply lt_of_not_ge
    intro hsb
    have hsb_eq : s = b := le_antisymm hsb hs_bounds.1
    subst s
    change (γ b).1 = u at hs_x
    rw [hb_zero] at hs_x
    linarith
  have hs_close : dist s b < δ := by
    calc
      dist s b = (s : ℝ) - b := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
        exact sub_nonneg.mpr hs_bounds.1
      _ ≤ (t : ℝ) - b := by
        have hst : (s : ℝ) ≤ t := by
          exact_mod_cast hs_bounds.2
        exact sub_le_sub_right hst _
      _ = dist t b := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
        exact sub_nonneg.mpr hbt.le
      _ < δ := ht_close
  have hy_close := hδ hs_close
  have hs_snd : (γ s).2 = z := by
    rw [hafter_snd hbs]
    change Real.sin (1 / (fun r : unitInterval ↦ (γ r).1) s) = z
    rw [hs_x, hu_sin]
  -- Continuity makes the chosen ordinate too close to also be the distant extreme.
  rw [hs_snd, Real.dist_eq] at hy_close
  linarith

/-- Helper for Example 25.2: no path joins the oscillating and vertical parts. -/
private lemma not_joined_curvePart_verticalPart {p q : Space}
    (hp : p ∈ curvePart) (hq : q ∈ verticalPart) : ¬ Joined p q := by
  -- Reverse a hypothetical subtype path and view it as a path inside the ambient carrier.
  intro hpq
  have hp_curve : p.1 ∈ curve := (mem_curvePart_iff p).mp hp
  have hq_zero : q.1.1 = 0 :=
    ((mem_vertical_iff q.1).mp ((mem_verticalPart_iff q).mp hq)).1
  apply not_joinedIn_zero_curve hq_zero hp_curve
  exact (joinedIn_iff_joined q.property p.property).mpr hpq.symm

/-- Helper for Example 25.2: the oscillating part is dense in the carrier subtype. -/
private lemma curvePart_dense : Dense curvePart := by
  -- Subtype closure reduces to the defining ambient closure of `curve`.
  have himage : Subtype.val '' curvePart = curve := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (mem_curvePart_iff q).mp hq
    · intro hp
      have hp_carrier : p ∈ carrier := subset_closure hp
      let q : Space := ⟨p, hp_carrier⟩
      exact ⟨q, (mem_curvePart_iff q).mpr hp, rfl⟩
  rw [dense_iff_closure_eq]
  ext p
  rw [closure_subtype, himage]
  simp only [mem_univ, iff_true]
  exact p.property

/- Example 25.2 (1): The topologist's sine curve has a single connected component. -/
#check (inferInstance : ConnectedSpace Space)

/-- Helper for Example 25.2: the oscillating curve is a path component of the topologist's sine
curve. -/
theorem pathComponent_curve (p : Space) (hp : p ∈ curvePart) :
    pathComponent p = curvePart := by
  -- The no-crossing lemma gives one inclusion; path-connectedness gives the other.
  ext q
  constructor
  · intro hq
    rcases mem_curvePart_or_verticalPart q with hq_curve | hq_vertical
    · exact hq_curve
    · exact False.elim
        (not_joined_curvePart_verticalPart hp hq_vertical (mem_pathComponent_iff.mp hq))
  · intro hq
    exact curvePart_isPathConnected.subset_pathComponent hp hq

/-- Helper for Example 25.2: the vertical interval is a path component of the topologist's sine
curve. -/
theorem pathComponent_vertical (p : Space) (hp : p ∈ verticalPart) :
    pathComponent p = verticalPart := by
  -- Again exclude crossing to the other piece, then use vertical path-connectedness.
  ext q
  constructor
  · intro hq
    rcases mem_curvePart_or_verticalPart q with hq_curve | hq_vertical
    · exact False.elim
        (not_joined_curvePart_verticalPart hq_curve hp (mem_pathComponent_iff.mp hq).symm)
    · exact hq_vertical
  · intro hq
    exact verticalPart_isPathConnected.subset_pathComponent hp hq

/-- Example 25.2 (4): The topologist's sine curve has exactly the oscillating curve and the
vertical interval as its path components. -/
theorem range_pathComponent :
    Set.range (fun p : Space ↦ pathComponent p) = {curvePart, verticalPart} := by
  -- Classify each point by its piece, and use nonemptiness to realize both components.
  ext A
  constructor
  · rintro ⟨p, rfl⟩
    rcases mem_curvePart_or_verticalPart p with hp_curve | hp_vertical
    · exact mem_insert_iff.mpr (Or.inl (pathComponent_curve p hp_curve))
    · exact mem_insert_iff.mpr
        (Or.inr (mem_singleton_iff.mpr (pathComponent_vertical p hp_vertical)))
  · intro hA
    rw [mem_insert_iff, mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · obtain ⟨p, hp⟩ := curvePart_isPathConnected.nonempty
      exact ⟨p, pathComponent_curve p hp⟩
    · obtain ⟨p, hp⟩ := verticalPart_isPathConnected.nonempty
      exact ⟨p, pathComponent_vertical p hp⟩

/-- Helper for Example 25.2: the oscillating curve is open in the topologist's sine curve. -/
theorem curvePart_isOpen : IsOpen curvePart := by
  -- The curve part is the complement of the closed vertical interval.
  rw [← verticalPart_compl_eq_curvePart]
  exact verticalPart_isClosed_aux.isOpen_compl

/-- Helper for Example 25.2: the oscillating curve is not closed in the topologist's sine curve. -/
theorem curvePart_not_isClosed : ¬ IsClosed curvePart := by
  -- A closed dense curve part would be the whole carrier, contradicting the vertical piece.
  intro hclosed
  have hcurve_univ : curvePart = (Set.univ : Set Space) :=
    hclosed.closure_eq.symm.trans (dense_iff_closure_eq.mp curvePart_dense)
  obtain ⟨p, hp_vertical⟩ := verticalPart_isPathConnected.nonempty
  have hp_not_curve : p ∉ curvePart := by
    intro hp_curve
    have hp_compl : p ∈ verticalPartᶜ := by
      rwa [verticalPart_compl_eq_curvePart]
    exact hp_compl hp_vertical
  apply hp_not_curve
  rw [hcurve_univ]
  exact mem_univ p

/-- Helper for Example 25.2: the vertical interval is closed in the topologist's sine curve. -/
theorem verticalPart_isClosed : IsClosed verticalPart := by
  -- Reuse the ambient closed-product calculation isolated above.
  exact verticalPart_isClosed_aux

/-- Helper for Example 25.2: the vertical interval is not open in the topologist's sine curve. -/
theorem verticalPart_not_isOpen : ¬ IsOpen verticalPart := by
  -- Openness would make the dense complementary curve part closed.
  intro hopen
  have hclosed : IsClosed verticalPartᶜ := hopen.isClosed_compl
  rw [verticalPart_compl_eq_curvePart] at hclosed
  exact curvePart_not_isClosed hclosed

end TopologistsSineCurve
