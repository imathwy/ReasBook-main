import BauschkeLean.Chap03.Theorem_3_37
import BauschkeLean.Chap07.Proposition_7_5
import BauschkeLean.Chap08.Corollary_8_39
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap08.Proposition_8_45
import BauschkeLean.Chap08.Theorem_8_38
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_16

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise
open WithLp

universe u

namespace ERealFunction

noncomputable section

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

section SubdifferentialContinuity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2
  prod_normedSpace_l2 prod_innerProductSpace_l2

/-- A point is a continuity point of `f` when the finite-valued restriction of `f` to its
effective domain is continuous there. -/
def ContinuousAtOnEffectiveDomain (f : H → Set.Ioi (⊥ : EReal)) (x : H) : Prop :=
  x ∈ effectiveDomain f ∧
    ContinuousWithinAt (fun y : H ↦ (f y : EReal).toReal) (effectiveDomain f) x

/-- A point is a source continuity point of `f` when some open ball around it lies in
`effectiveDomain f` and the finite-valued representative of `f` is ambiently continuous there. -/
def ContinuousAtInEffectiveDomain (f : H → Set.Ioi (⊥ : EReal)) (x : H) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain f ∧
    ContinuousAt (fun y : H ↦ (f y : EReal).toReal) x

/-- A source continuity point of `f`, corresponding to `x ∈ cont f` in Proposition 16.17. -/
abbrev ContinuousPoint (f : H → Set.Ioi (⊥ : EReal)) (x : H) : Prop :=
  ContinuousAtInEffectiveDomain f x

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- A continuity point on the effective domain belongs to the effective domain. -/
theorem ContinuousAtOnEffectiveDomain.mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x : H}
    (hx : ContinuousAtOnEffectiveDomain f x) :
    x ∈ effectiveDomain f := by
  -- Unpack the definition and keep only the effective-domain component.
  exact hx.1

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- A continuity point on the effective domain is continuous for the finite-valued restriction of
`f` to its effective domain. -/
theorem ContinuousAtOnEffectiveDomain.continuousWithinAt
    {f : H → Set.Ioi (⊥ : EReal)} {x : H}
    (hx : ContinuousAtOnEffectiveDomain f x) :
    ContinuousWithinAt (fun y : H ↦ (f y : EReal).toReal) (effectiveDomain f) x := by
  -- The second component of the definition is exactly the restricted continuity statement.
  exact hx.2

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- A source continuity point yields the Chapter 16 continuity-on-effective-domain owner. -/
theorem ContinuousAtOnEffectiveDomain.of_continuousAtInEffectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x : H}
    (hx : ContinuousAtInEffectiveDomain f x) :
    ContinuousAtOnEffectiveDomain f x := by
  rcases hx with ⟨ρ, hρ, hball, hcont⟩
  -- The ball witness supplies effective-domain membership, and ambient continuity restricts.
  refine ⟨hball (Metric.mem_ball_self hρ), hcont.continuousWithinAt⟩

/-- Helper for Proposition 16.17: a positive common factor can be canceled from a quadratic
inequality to bound the norm parameter. -/
private lemma norm_le_of_pos_mul_sq_le_mul
    {a β c : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β) (hc : 0 < c)
    (hineq : c * a ^ 2 ≤ β * (c * a)) :
    a ≤ β := by
  by_cases ha0 : a = 0
  · simpa [ha0] using hβ
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hca_pos : 0 < c * a := mul_pos hc ha_pos
  have hineq' : (c * a) * a ≤ (c * a) * β := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hineq
  exact le_of_mul_le_mul_left hineq' hca_pos

/-- Helper for Proposition 16.17: the support inequality on the translate `C - {p}` is
equivalent to the pointwise inner-product inequalities against all points of `C`. -/
private lemma innerSupremumOn_sub_singleton_le_zero_iff_forall_inner_nonpos_local
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} {u p : E} :
    innerSupremumOn (C - ({p} : Set E)) u ≤ 0 ↔
      ∀ z ∈ C, ⟪z - p, u⟫_ℝ ≤ 0 := by
  constructor
  · intro hsup
    -- Compare the translated set against `{0}` to recover the pointwise inequalities.
    have hsep :
        innerSupremumOn (C - ({p} : Set E)) u ≤ innerInfimumOn ({0} : Set E) u := by
      simpa using hsup
    have hinner :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({p} : Set E)) ({0} : Set E) u).1 hsep
    intro z hz
    have hz_sub : z - p ∈ C - ({p} : Set E) := by
      exact ⟨z, hz, p, by simp, rfl⟩
    simpa using hinner (z - p) hz_sub 0 (by simp)
  · intro hinner
    -- Every element of the translate is a difference `z - p`, so the pointwise inequalities
    -- repackage exactly as the support inequality.
    have hsep :
        innerSupremumOn (C - ({p} : Set E)) u ≤ innerInfimumOn ({0} : Set E) u := by
      refine (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({p} : Set E)) ({0} : Set E) u).2 ?_
      intro v hv w hw
      have hw0 : w = 0 := by
        simpa using hw
      subst hw0
      rcases hv with ⟨z, hz, q, hq, hvq⟩
      have hq_eq : q = p := by
        simpa using hq
      have hv_eq : v = z - p := by
        simpa [hq_eq] using hvq.symm
      simpa [hv_eq] using hinner z hz
    simpa using hsep

/-- Helper for Proposition 16.17: every effective-domain point contributes its canonical
real-height graph point to the epigraph. -/
private lemma mem_epigraph_toReal_of_mem_effectiveDomain_local
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} (hy : y ∈ effectiveDomain f) :
    (y, (f y : EReal).toReal) ∈ epigraph f.asEReal := by
  -- Finiteness of `f y` says that the canonical graph point lies on the epigraph.
  rw [mem_epigraph_iff]
  exact EReal.le_coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hy))

/-- Helper for Proposition 16.17: a real-height epigraph point has finite base value, and its
ordinate dominates the canonical graph height. -/
private lemma effectiveDomain_and_toReal_le_of_mem_epigraph_local
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} {η : ℝ}
    (hyη : (y, η) ∈ epigraph f.asEReal) :
    y ∈ effectiveDomain f ∧ (f y : EReal).toReal ≤ η := by
  -- Epigraph membership bounds `f y` above by a finite real height, so `y` lies in the effective
  -- domain and `toReal` preserves the comparison.
  have hfy_le : (f y : EReal) ≤ (η : EReal) := (mem_epigraph_iff _ _ _).mp hyη
  have hy_dom : y ∈ effectiveDomain f := by
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_lt hfy_le (EReal.coe_lt_top η)
  have hfy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hη_top : ((η : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top η
  have htoReal : (f y : EReal).toReal ≤ ((η : EReal)).toReal := by
    simpa using EReal.toReal_le_toReal hfy_le hfy_bot hη_top
  exact ⟨hy_dom, htoReal⟩

/-- Helper for Proposition 16.17: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul_local (a b : ℝ) :
    ⟪a, b⟫_ℝ = a * b := by
  calc
    ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
    _ = a * b := by simp

/-- Helper for Proposition 16.17: the product Hilbert inner product on `H × ℝ` splits into the
two coordinates. -/
private lemma inner_pair_eq_add_mul_local
    {p u : H} {r a : ℝ} :
    ⟪(p, r), (u, a)⟫_ℝ = ⟪p, u⟫_ℝ + r * a := by
  change ⟪p, u⟫_ℝ + ⟪r, a⟫_ℝ = ⟪p, u⟫_ℝ + r * a
  rw [real_inner_eq_mul_local]

/-- Helper for Proposition 16.17: after translating by a graph point, the product inner product
splits into the horizontal and vertical contributions. -/
private lemma inner_sub_graphPoint_eq_local
    {x y u : H} {ξ η a : ℝ} :
    ⟪(y, η) - (x, ξ), (u, a)⟫_ℝ = ⟪y - x, u⟫_ℝ + (η - ξ) * a := by
  -- Rewrite the translated pair and then split the product inner product coordinatewise.
  change ⟪(y - x, η - ξ), (u, a)⟫_ℝ = ⟪y - x, u⟫_ℝ + (η - ξ) * a
  rw [inner_pair_eq_add_mul_local]

/-- Helper for Proposition 16.17: epigraph normal-cone membership at the real-height graph point
is equivalent to the translated pointwise inner-product inequalities against all epigraph
points. -/
private lemma mem_normalCone_epigraph_iff_forall_inner_pair_nonpos_local
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ effectiveDomain f) {u : H} {a : ℝ} :
    (u, a) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) ↔
      ∀ y η, (y, η) ∈ epigraph f.asEReal →
        ⟪(y, η) - (x, (f x : EReal).toReal), (u, a)⟫_ℝ ≤ 0 := by
  have hx_epi : (x, (f x : EReal).toReal) ∈ epigraph f.asEReal :=
    mem_epigraph_toReal_of_mem_effectiveDomain_local (f := f) hx
  -- Unfold the normal cone at the graph point and rewrite the support inequality pointwise.
  rw [Set.normalCone_of_mem hx_epi]
  have hnormal_iff :
      innerSupremumOn
          (epigraph f.asEReal - ({(x, (f x : EReal).toReal)} : Set (H × ℝ))) (u, a) ≤ 0 ↔
        ∀ z ∈ epigraph f.asEReal,
          ⟪z - (x, (f x : EReal).toReal), (u, a)⟫_ℝ ≤ 0 := by
    exact
      (innerSupremumOn_sub_singleton_le_zero_iff_forall_inner_nonpos_local :
        innerSupremumOn
            (epigraph f.asEReal - ({(x, (f x : EReal).toReal)} : Set (H × ℝ))) (u, a) ≤ 0 ↔
          ∀ z ∈ epigraph f.asEReal,
            ⟪z - (x, (f x : EReal).toReal), (u, a)⟫_ℝ ≤ 0)
  constructor
  · intro hu
    have hpointwise := hnormal_iff.1 hu
    intro y η hyη
    exact hpointwise (y, η) hyη
  · intro hu
    have hpointwise :
        ∀ z ∈ epigraph f.asEReal,
          ⟪z - (x, (f x : EReal).toReal), (u, a)⟫_ℝ ≤ 0 := by
      intro z hz
      rcases z with ⟨y, η⟩
      exact hu y η hz
    exact hnormal_iff.2 hpointwise

/-- Helper for Proposition 16.17: if a vector has nonpositive inner product with every point of a
nontrivial ball around the origin, then the vector is zero. -/
private lemma eq_zero_of_forall_mem_ball_inner_nonpos
    {u : H} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ∀ z ∈ Metric.ball (0 : H) ρ, ⟪z, u⟫_ℝ ≤ 0) :
    u = 0 := by
  by_contra hu_ne
  let t : ℝ := ρ / (2 * ‖u‖)
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have ht_ball : t • u ∈ Metric.ball (0 : H) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc
      ‖t • u‖ = |t| * ‖u‖ := norm_smul t u
      _ = t * ‖u‖ := by rw [abs_of_pos ht_pos]
      _ = ρ / 2 := by
        dsimp [t]
        field_simp [norm_ne_zero_iff.mpr hu_ne]
      _ < ρ := by linarith
  have hnonpos : ⟪t • u, u⟫_ℝ ≤ 0 := hu (t • u) ht_ball
  have hpositive : 0 < ⟪t • u, u⟫_ℝ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    positivity
  linarith

/-- Helper for Proposition 16.17: source continuity at `x` yields a positive ball on which `f`
has a finite real upper bound. -/
private lemma continuousAtInEffectiveDomain_has_boundedAbove_ball
    {f : H → Set.Ioi (⊥ : EReal)} {x : H}
    (hxcont : ContinuousAtInEffectiveDomain f x) :
    ∃ δ M : ℝ, 0 < δ ∧ ∀ y ∈ Metric.ball x δ, (f y : EReal) ≤ (M : EReal) := by
  rcases hxcont with ⟨ρ, hρ, hball, hcont⟩
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ₀, hδ₀, hδ₀prop⟩ := hcont 1 zero_lt_one
  refine ⟨min ρ δ₀, (f x : EReal).toReal + 1, lt_min hρ hδ₀, ?_⟩
  intro y hy
  have hyρ : y ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball] at hy ⊢
    exact lt_of_lt_of_le hy (min_le_left _ _)
  have hyδ₀ : dist y x < δ₀ := by
    rw [Metric.mem_ball] at hy
    exact lt_of_lt_of_le hy (min_le_right _ _)
  have hy_dom : y ∈ effectiveDomain f := hball hyρ
  have hdist : dist ((f y : EReal).toReal) ((f x : EReal).toReal) < 1 := hδ₀prop hyδ₀
  have htoReal_le : (f y : EReal).toReal ≤ (f x : EReal).toReal + 1 := by
    have habs : |(f y : EReal).toReal - (f x : EReal).toReal| < 1 := by
      simpa [Real.dist_eq] using hdist
    have hright := (abs_lt.mp habs).2
    linarith
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  rw [show (f y : EReal) = (((f y : EReal).toReal : ℝ) : EReal) by
    symm
    exact EReal.coe_toReal hy_top hy_bot]
  exact_mod_cast htoReal_le

/-- Helper for Proposition 16.17: a supporting direction of the effective domain generates a
subgradient ray at `x`. -/
private lemma subdifferential_add_nonneg_smul_of_supporting_direction
    {f : H → Set.Ioi (⊥ : EReal)} {x u v : H}
    (hx : x ∈ effectiveDomain f)
    (hu : ∀ y ∈ effectiveDomain f, ⟪y - x, u⟫_ℝ ≤ 0)
    (hv : v ∈ (∂ f) x) {a : ℝ} (ha : 0 ≤ a) :
    v + a • u ∈ (∂ f) x := by
  -- Work with the affine half-space description of the subdifferential at the finite point `x`.
  rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂]
  rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂] at hv
  intro y hy
  have hvy : ⟪y - x, v⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := hv y hy
  have huy : ⟪y - x, a • u⟫_ℝ ≤ 0 := by
    rw [real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos ha (hu y hy)
  -- The support-direction term is nonpositive, so adding it preserves the half-space inequality.
  calc
    ⟪y - x, v + a • u⟫_ℝ = ⟪y - x, v⟫_ℝ + ⟪y - x, a • u⟫_ℝ := by
      rw [inner_add_right]
    _ ≤ ⟪y - x, v⟫_ℝ + 0 := by gcongr
    _ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by simpa using hvy

/-- Helper for Proposition 16.17: a support point is exactly a point admitting a nonzero
supporting direction with nonpositive translated inner products on the whole set. -/
private lemma mem_supportPoints_iff_exists_nonzero_inner_sub_right_nonpos_local
    {C : Set H} {x : H} :
    x ∈ Set.supportPoints C ↔ x ∈ C ∧ ∃ u : H, u ≠ 0 ∧ ∀ y ∈ C, ⟪y - x, u⟫_ℝ ≤ 0 := by
  -- Rewrite the support-value equality into pointwise upper bounds and use `x ∈ C` for the
  -- reverse inequality.
  rw [Set.mem_supportPoints_iff]
  constructor
  · rintro ⟨hxC, u, hu_ne, hu_eq⟩
    refine ⟨hxC, u, hu_ne, ?_⟩
    intro y hy
    have hy_le : (⟪y, u⟫_ℝ : EReal) ≤ innerSupremumOn C u := by
      rw [innerSupremumOn_eq_sSup_image]
      exact le_sSup ⟨y, hy, rfl⟩
    have hyx_le : (⟪y, u⟫_ℝ : EReal) ≤ (⟪x, u⟫_ℝ : EReal) := by
      exact le_trans hy_le hu_eq
    have hyx_le' : ⟪y, u⟫_ℝ ≤ ⟪x, u⟫_ℝ := by
      exact_mod_cast hyx_le
    simpa [inner_sub_left] using sub_nonpos.mpr hyx_le'
  · rintro ⟨hxC, u, hu_ne, hu_nonpos⟩
    refine ⟨hxC, u, hu_ne, ?_⟩
    -- The translated supporting inequalities make `⟪x, u⟫` an upper bound for the image set.
    rw [innerSupremumOn_eq_sSup_image]
    refine (isLUB_sSup _).2 ?_
    rintro _ ⟨y, hy, rfl⟩
    have hyx_le : ⟪y, u⟫_ℝ ≤ ⟪x, u⟫_ℝ := by
      have := hu_nonpos y hy
      simpa [inner_sub_left] using this
    exact show ((⟪y, u⟫_ℝ : EReal) ≤ (⟪x, u⟫_ℝ : EReal)) by
      exact_mod_cast hyx_le

/-- Helper for Proposition 16.17: a uniform real upper bound on a ball gives a finite `EReal`
supremum for the image of that ball. -/
private lemma finite_sup_ball_lt_top_of_boundedAbove_ball_local
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {ρ M : ℝ}
    (hM : ∀ y ∈ Metric.ball x ρ, (f y : EReal) ≤ (M : EReal)) :
    sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x ρ) < ⊤ := by
  -- Every image value is bounded by the same real number `M`, so the supremum stays finite.
  refine lt_of_le_of_lt ?_ (EReal.coe_lt_top M)
  refine sSup_le ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hM y hy

/-- Helper for Proposition 16.17: a nontrivial normal to the real-height epigraph over a ball in
the effective domain has strictly negative vertical component. -/
private lemma vertical_component_neg_of_epigraph_normal_of_ball_in_domain
    {f : H → Set.Ioi (⊥ : EReal)} {x u : H} {ν ρ : ℝ}
    (hρ : 0 < ρ)
    (hball : Metric.ball x ρ ⊆ effectiveDomain f)
    (hnormal : (u, ν) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal))
    (hne : (u, ν) ≠ 0) :
    ν < 0 := by
  have hx : x ∈ effectiveDomain f := hball (Metric.mem_ball_self hρ)
  have hpointwise :=
    (mem_normalCone_epigraph_iff_forall_inner_pair_nonpos_local (f := f) hx).1 hnormal
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hν_nonpos : ν ≤ 0 := by
    have hx_epi_up : (x, (f x : EReal).toReal + 1) ∈ epigraph f.asEReal := by
      rw [mem_epigraph_iff]
      exact le_trans (EReal.le_coe_toReal hx_top) (by exact_mod_cast le_add_of_nonneg_right zero_le_one)
    -- Testing the normal inequality at a purely vertical upward perturbation forces `ν ≤ 0`.
    have hineq := hpointwise x ((f x : EReal).toReal + 1) hx_epi_up
    rw [inner_sub_graphPoint_eq_local] at hineq
    simpa using hineq
  have hν_ne_zero : ν ≠ 0 := by
    intro hν_zero
    have hu_nonpos : ∀ z ∈ Metric.ball (0 : H) ρ, ⟪z, u⟫_ℝ ≤ 0 := by
      intro z hz
      have hz_norm : ‖z‖ < ρ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      have hy : x + z ∈ Metric.ball x ρ := by
        rw [Metric.mem_ball, dist_eq_norm]
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz_norm
      have hy_dom : x + z ∈ effectiveDomain f := hball hy
      have hy_epi :
          (x + z, (f (x + z) : EReal).toReal) ∈ epigraph f.asEReal :=
        mem_epigraph_toReal_of_mem_effectiveDomain_local (f := f) hy_dom
      -- Setting the vertical component to zero leaves only the horizontal supporting inequality.
      have hineq := hpointwise (x + z) ((f (x + z) : EReal).toReal) hy_epi
      rw [inner_sub_graphPoint_eq_local] at hineq
      simpa [hν_zero, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hineq
    have hu_zero : u = 0 := eq_zero_of_forall_mem_ball_inner_nonpos hρ hu_nonpos
    have hpair_zero : (u, ν) = 0 := by
      ext <;> simp [hu_zero, hν_zero]
    exact hne hpair_zero
  -- The pair is nontrivial, so the already proved nonpositivity is strict.
  exact lt_of_le_of_ne hν_nonpos hν_ne_zero

/-- Helper for Proposition 16.17: on a strictly negative vertical slice, epigraph normals are
exactly the positive scalar multiples of subgradients. -/
private lemma mem_normalCone_epigraph_pair_neg_iff_mem_smul_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) {x u : H} {v : ℝ} (hx : x ∈ effectiveDomain f) (hv : 0 < v) :
    (u, -v) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) ↔ u ∈ v • (∂ f) x := by
  constructor
  · intro hu
    have hv_ne : v ≠ 0 := ne_of_gt hv
    have hpointwise :=
      (mem_normalCone_epigraph_iff_forall_inner_pair_nonpos_local (f := f) hx).1 hu
    have hsubgrad : v⁻¹ • u ∈ (∂ f) x := by
      -- Rewrite the normal inequalities on canonical graph points into the subgradient inequality.
      rw [mem_subdifferential_iff]
      intro y
      by_cases hy : y ∈ effectiveDomain f
      · have hy_epi : (y, (f y : EReal).toReal) ∈ epigraph f.asEReal :=
          mem_epigraph_toReal_of_mem_effectiveDomain_local (f := f) hy
        have hineq := hpointwise y ((f y : EReal).toReal) hy_epi
        have hlinear :
            ⟪y - x, u⟫_ℝ + (((f y : EReal).toReal - (f x : EReal).toReal) * (-v)) ≤ 0 := by
          simpa [inner_pair_eq_add_mul_local] using hineq
        have hreal_le :
            ⟪y - x, u⟫_ℝ ≤ v * ((f y : EReal).toReal - (f x : EReal).toReal) := by
          have hlinear' := hlinear
          ring_nf at hlinear'
          have hgoal :
              ⟪y - x, u⟫_ℝ - (f y : EReal).toReal * v + (f x : EReal).toReal * v ≤ 0 :=
            hlinear'
          linarith
        have hscaled :
            ⟪y - x, v⁻¹ • u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
          have hmul := mul_le_mul_of_nonneg_left hreal_le (inv_pos.mpr hv).le
          calc
            ⟪y - x, v⁻¹ • u⟫_ℝ = v⁻¹ * ⟪y - x, u⟫_ℝ := by
              rw [real_inner_smul_right]
            _ ≤ v⁻¹ * (v * ((f y : EReal).toReal - (f x : EReal).toReal)) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
            _ = (f y : EReal).toReal - (f x : EReal).toReal := by
              rw [← mul_assoc, inv_mul_cancel₀ hv_ne, one_mul]
        have hreal_minor :
            ⟪y - x, v⁻¹ • u⟫_ℝ + (f x : EReal).toReal ≤ (f y : EReal).toReal := by
          have hscaled' := hscaled
          linarith
        have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
        have hx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
        have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
        have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
        change ((⟪y - x, v⁻¹ • u⟫_ℝ : EReal) + (f x : EReal)) ≤ (f y : EReal)
        rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_add]
        exact_mod_cast hreal_minor
      · have hy_not_lt : ¬ (f y : EReal) < ⊤ := by
          simpa [mem_effectiveDomain_iff] using hy
        have hy_top : (f y : EReal) = ⊤ := by
          by_contra hy_top
          exact hy_not_lt ((lt_top_iff_ne_top).2 hy_top)
        change ((⟪y - x, v⁻¹ • u⟫_ℝ : EReal) + (f x : EReal)) ≤ (f y : EReal)
        rw [hy_top]
        simp
    -- Repackage the scaled subgradient witness as membership in the positive ray `v • ∂f(x)`.
    refine Set.mem_smul_set.mpr ?_
    refine ⟨v⁻¹ • u, hsubgrad, ?_⟩
    simp [smul_smul, mul_inv_cancel₀ hv_ne]
  · intro hu
    rcases Set.mem_smul_set.mp hu with ⟨w, hw, rfl⟩
    have hsubgrad := (mem_subdifferential_iff (f := f) (x := x) (u := w)).1 hw
    -- The subgradient inequality at the graph height extends to every epigraph point above it.
    refine (mem_normalCone_epigraph_iff_forall_inner_pair_nonpos_local (f := f) hx).2 ?_
    intro y η hyη
    rcases effectiveDomain_and_toReal_le_of_mem_epigraph_local (f := f) hyη with ⟨hy, hη⟩
    have hsub := hsubgrad y
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
    change ((⟪y - x, w⟫_ℝ : EReal) + (f x : EReal)) ≤ (f y : EReal) at hsub
    rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_add]
      at hsub
    have hsub_real :
        ⟪y - x, w⟫_ℝ + (f x : EReal).toReal ≤ (f y : EReal).toReal := by
      exact_mod_cast hsub
    have hminor :
        ⟪y - x, w⟫_ℝ + (f x : EReal).toReal ≤ η := le_trans hsub_real hη
    have hscaled := mul_le_mul_of_nonneg_left hminor hv.le
    have hlinear_aux :
        v * ⟪y - x, w⟫_ℝ + (((η - (f x : EReal).toReal) * (-v)) : ℝ) ≤ 0 := by
      have hscaled' := hscaled
      ring_nf at hscaled'
      have hgoal : v * ⟪y - x, w⟫_ℝ + v * (f x : EReal).toReal ≤ v * η := hscaled'
      linarith
    -- Reassemble the product-space inequality from the scaled subgradient inequality.
    simpa [inner_pair_eq_add_mul_local, real_inner_smul_right, mul_assoc, mul_left_comm, mul_comm]
      using hlinear_aux

-- Semantic recall via `lean_leansearch` was unavailable; local Chapter 16 precedent, especially
-- Proposition 16.27, uses `ContinuousPoint`/`ContinuousAtInEffectiveDomain` for the source
-- continuity set `cont f`, while `ContinuousAtOnEffectiveDomain` remains the reusable helper API.
-- Proof sketch: use the supporting-functional argument at a boundary point of the effective domain
-- to produce a nonzero outward normal `u`, then show that every `v ∈ ∂ f x` generates the ray
-- `v + ℝ≥0 • u ⊆ ∂ f x`; hence a nonempty subdifferential cannot be bounded.
/-- Proposition 16.17 (1): clause (i). If the effective domain has nonempty interior and `x` lies
on its boundary, then the subdifferential at `x` is either empty or unbounded. -/
theorem subdifferential_eq_empty_or_unbounded_of_mem_frontier_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f)
    (hinter : (interior (effectiveDomain f)).Nonempty)
    (hfrontier : x ∈ frontier (effectiveDomain f)) :
    (∂ f) x = ∅ ∨ ¬Bornology.IsBounded ((∂ f) x) := by
  by_cases hsub_ne : ((∂ f) x).Nonempty
  · right
    intro hsub_bounded
    have hx_support : x ∈ Set.supportPoints (effectiveDomain f) := by
      -- Boundary points of the convex effective domain are support points by Proposition 7.5.
      exact
        Set.inter_frontier_subset_supportPoints_of_convex_nonempty_interior
          (hconv.convex_effectiveDomain) hinter ⟨hx, hfrontier⟩
    rw [mem_supportPoints_iff_exists_nonzero_inner_sub_right_nonpos_local] at hx_support
    rcases hx_support with ⟨_, u, hu_ne, hu_support⟩
    rcases hsub_ne with ⟨v, hv⟩
    obtain ⟨R, hR⟩ := hsub_bounded.subset_closedBall (0 : H)
    let a : ℝ := (R + ‖v‖ + 1) / ‖u‖
    have hR_nonneg : 0 ≤ R := by
      have hv_ball : v ∈ Metric.closedBall (0 : H) R := hR hv
      have hv_norm : ‖v‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hv_ball
      exact le_trans (norm_nonneg v) hv_norm
    have ha : 0 ≤ a := by
      dsimp [a]
      have hnum : 0 ≤ R + ‖v‖ + 1 := by
        linarith [hR_nonneg, norm_nonneg v]
      exact div_nonneg hnum (norm_nonneg _)
    have hva : v + a • u ∈ (∂ f) x :=
      subdifferential_add_nonneg_smul_of_supporting_direction hx hu_support hv ha
    have hva_ball : v + a • u ∈ Metric.closedBall (0 : H) R := hR hva
    have hva_norm : ‖v + a • u‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hva_ball
    have hu_norm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu_ne
    have hsmul_norm : ‖a • u‖ = R + ‖v‖ + 1 := by
      calc
        ‖a • u‖ = |a| * ‖u‖ := norm_smul a u
        _ = a * ‖u‖ := by rw [abs_of_nonneg ha]
        _ = R + ‖v‖ + 1 := by
          dsimp [a]
          field_simp [hu_norm_ne]
    have htriangle : ‖a • u‖ ≤ ‖v + a • u‖ + ‖v‖ := by
      -- Compare `a • u = (v + a • u) - v` and apply the triangle inequality once.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using norm_sub_le (v + a • u) v
    linarith
  · left
    exact Set.not_nonempty_iff_eq_empty.mp hsub_ne

-- Proof sketch: apply the epigraph normal-cone characterization of Proposition 16.16 at a point
-- where the finite-valued representative is continuous on a neighborhood contained in the
-- effective domain. Then combine closedness and convexity of `∂ f x`, and conclude weak
-- compactness from the bounded closed convex criterion.
-- Route correction: `ContinuousAtOnEffectiveDomain f x` is too weak here; the indicator of
-- `[0, ∞)` is relatively continuous at `0` on its effective domain but has an unbounded
-- subdifferential there. The source proof needs the stronger textbook continuity notion.
/-- Helper for Proposition 16.17: every finite graph point of the epigraph lies on its frontier,
because every neighborhood also contains a nearby lowered point on the same vertical line. -/
private lemma graph_point_mem_frontier_epigraph_of_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ effectiveDomain f) :
    (x, (f x : EReal).toReal) ∈ frontier (epigraph f.asEReal) := by
  have hx_epi : (x, (f x : EReal).toReal) ∈ epigraph f.asEReal :=
    mem_epigraph_toReal_of_mem_effectiveDomain_local (f := f) hx
  refine (mem_frontier_iff_notMem_interior hx_epi).2 ?_
  intro hx_int
  let ξ : ℝ := (f x : EReal).toReal
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hline_nhds :
      (fun η : ℝ ↦ (x, η)) ⁻¹' interior (epigraph f.asEReal) ∈ nhds ξ := by
    -- Pull the interior neighborhood back along the vertical line through the graph point.
    have hcont : Continuous fun η : ℝ ↦ (x, η) := continuous_const.prodMk continuous_id
    have hmem :
        interior (epigraph f.asEReal) ∈ nhds (x, ξ) := isOpen_interior.mem_nhds (by
          simpa [ξ] using hx_int)
    simpa [ξ] using hcont.continuousAt.preimage_mem_nhds hmem
  rcases Metric.mem_nhds_iff.mp hline_nhds with ⟨ε, hε, hεball⟩
  have hhalf_mem : ξ - ε / 2 ∈ Metric.ball ξ ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    calc
      |(ξ - ε / 2) - ξ| = |-(ε / 2)| := by ring_nf
      _ = ε / 2 := by
        simpa using (abs_of_neg (show -(ε / 2 : ℝ) < 0 by nlinarith [hε]))
      _ < ε := by linarith
  have hlower_int : (x, ξ - ε / 2) ∈ interior (epigraph f.asEReal) := hεball hhalf_mem
  have hlower_not_epi : (x, ξ - ε / 2) ∉ epigraph f.asEReal := by
    rw [mem_epigraph_iff]
    have hfx_eq : Function.asEReal f x = (ξ : EReal) := by
      calc
        Function.asEReal f x = (f x : EReal) := by simp [Function.asEReal_apply]
        _ = (ξ : EReal) := by
          dsimp [ξ]
          symm
          exact EReal.coe_toReal hx_top hx_bot
    have hlower_lt : ((ξ - ε / 2 : ℝ) : EReal) < Function.asEReal f x := by
      calc
        ((ξ - ε / 2 : ℝ) : EReal) < (ξ : EReal) := by
          exact_mod_cast (show ξ - ε / 2 < ξ by linarith)
        _ = Function.asEReal f x := by simpa [hfx_eq] using hfx_eq.symm
    exact not_le_of_gt hlower_lt
  exact hlower_not_epi (interior_subset hlower_int)

/-- Helper for Proposition 16.17: a frontier graph point of the epigraph carries a nontrivial
normal vector once the epigraph has nonempty interior. -/
private lemma epigraph_normal_nontrivial_of_frontier_graph_point
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f)
    (hinter : (interior (epigraph f.asEReal)).Nonempty) :
    ∃ p : H × ℝ, p ≠ 0 ∧ p ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) := by
  have hx_epi : (x, (f x : EReal).toReal) ∈ epigraph f.asEReal :=
    mem_epigraph_toReal_of_mem_effectiveDomain_local (f := f) hx
  have hx_frontier :
      (x, (f x : EReal).toReal) ∈ frontier (epigraph f.asEReal) :=
    graph_point_mem_frontier_epigraph_of_mem_effectiveDomain (f := f) hx
  have hx_support : (x, (f x : EReal).toReal) ∈ Set.supportPoints (epigraph f.asEReal) := by
    -- Proposition 7.5 turns the frontier graph point into a support point of the epigraph.
    exact
      Set.inter_frontier_subset_supportPoints_of_convex_nonempty_interior
        hconv.convex_epigraph_asEReal hinter ⟨hx_epi, hx_frontier⟩
  -- Rewrite the support-point witness as punctured normal-cone nonemptiness.
  rw [Set.supportPoints_eq_setOf_nontrivial_normalCone] at hx_support
  rcases Set.nonempty_iff_ne_empty.mpr hx_support with ⟨p, hp⟩
  refine ⟨p, ?_, hp.1⟩
  simpa using hp.2

/-- Helper for Proposition 16.17: source continuity at `x` yields a nonempty subdifferential. -/
private lemma subdifferential_nonempty_of_continuousAtInEffectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtInEffectiveDomain f x) :
    ((∂ f) x).Nonempty := by
  rcases hxcont with ⟨ρ, hρ, hball, hcont⟩
  have hx : x ∈ effectiveDomain f := hball (Metric.mem_ball_self hρ)
  obtain ⟨δ, M, hδ, hM⟩ :=
    continuousAtInEffectiveDomain_has_boundedAbove_ball (f := f) ⟨ρ, hρ, hball, hcont⟩
  have hinter0 :
      (interior (epigraph (fun y : H ↦ (f y : EReal)))).Nonempty :=
    interior_epigraph_nonempty_of_convexOn_of_boundedAbove_ball (f := f) hconv hδ hM
  have hinter : (interior (epigraph f.asEReal)).Nonempty := by
    -- Proposition 8.45 supplies the nonempty interior required by the support-point argument.
    simpa [Function.asEReal_apply] using hinter0
  obtain ⟨p, hp_ne, hp_normal⟩ :=
    epigraph_normal_nontrivial_of_frontier_graph_point (f := f) hconv hx hinter
  have hp₂_neg : p.2 < 0 :=
    vertical_component_neg_of_epigraph_normal_of_ball_in_domain
      (f := f) (u := p.1) (ν := p.2) hρ hball hp_normal hp_ne
  let v : ℝ := -p.2
  have hv_pos : 0 < v := by
    -- The previous step is exactly the source claim `ν < 0`.
    dsimp [v]
    linarith
  have hp_neg : (p.1, -v) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) := by
    -- Rewrite the normal with positive vertical scale `v = -ν`.
    simpa [v] using hp_normal
  have hp_sub :
      p.1 ∈ v • (∂ f) x :=
    (mem_normalCone_epigraph_pair_neg_iff_mem_smul_subdifferential
      (f := f) hx hv_pos).1 hp_neg
  rcases Set.mem_smul_set.mp hp_sub with ⟨u, hu, _⟩
  -- Any witness in the positive ray already gives a genuine subgradient at `x`.
  exact ⟨u, hu⟩

/-- Helper for Proposition 16.17: a subgradient on a locally Lipschitz ball has norm at most the
Lipschitz constant. -/
private lemma step_point_mem_ball_two_rho_of_subgradient_direction
    {x y v : H} {ρ : ℝ} (hρ : 0 < ρ) (hy : y ∈ Metric.ball x ρ) :
    let t : ℝ := ρ / (‖v‖ + 1)
    0 < t ∧ ‖t • v‖ < ρ ∧ y + t • v ∈ Metric.ball x (2 * ρ) := by
  let t : ℝ := ρ / (‖v‖ + 1)
  have hy_norm : ‖y - x‖ < ρ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  have hden_pos : 0 < ‖v‖ + 1 := by positivity
  have ht_pos : 0 < t := by
    -- The step size is a positive fraction of the positive radius `ρ`.
    dsimp [t]
    exact div_pos hρ hden_pos
  have hstep_norm : ‖t • v‖ < ρ := by
    -- The chosen step scales `v` by a factor strictly smaller than `ρ / ‖v‖`.
    rw [norm_smul, Real.norm_of_nonneg ht_pos.le]
    have hv_lt : ‖v‖ < ‖v‖ + 1 := by linarith [norm_nonneg v]
    have hmul_lt : t * ‖v‖ < t * (‖v‖ + 1) := mul_lt_mul_of_pos_left hv_lt ht_pos
    calc
      t * ‖v‖ < t * (‖v‖ + 1) := hmul_lt
      _ = ρ := by
        dsimp [t]
        field_simp [hden_pos.ne']
  have htriangle :
      ‖(y + t • v) - x‖ ≤ ‖y - x‖ + ‖t • v‖ := by
    -- Rewrite the increment as `(y - x) + t • v` and apply the triangle inequality once.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using norm_add_le (y - x) (t • v)
  have hball_two : y + t • v ∈ Metric.ball x (2 * ρ) := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt htriangle (by
      have : ‖y - x‖ + ‖t • v‖ < ρ + ρ := add_lt_add hy_norm hstep_norm
      simpa [two_mul] using this)
  exact ⟨ht_pos, hstep_norm, hball_two⟩

/-- Helper for Proposition 16.17: a subgradient on a locally Lipschitz ball has norm at most the
Lipschitz constant. -/
private lemma subgradient_step_test_le_lipschitz_scalar
    (f : H → Set.Ioi (⊥ : EReal)) {x y v : H} {ρ : ℝ} {β : NNReal}
    (hρ : 0 < ρ)
    (hball_dom : Metric.ball x (2 * ρ) ⊆ effectiveDomain f)
    (hLip : LipschitzOnWith β (fun z ↦ (f z : EReal).toReal) (Metric.ball x (2 * ρ)))
    (hy : y ∈ Metric.ball x ρ) (hv : v ∈ (∂ f) y) :
    let t : ℝ := ρ / (‖v‖ + 1)
    t * ‖v‖ ^ 2 ≤ (β : ℝ) * (t * ‖v‖) := by
  let t : ℝ := ρ / (‖v‖ + 1)
  change t * ‖v‖ ^ 2 ≤ (β : ℝ) * (t * ‖v‖)
  let z : H := y + t • v
  rcases step_point_mem_ball_two_rho_of_subgradient_direction (v := v) hρ hy with
    ⟨ht_pos, _, hz_ball⟩
  have hy_two_rho : y ∈ Metric.ball x (2 * ρ) := by
    -- The center point of the short step stays inside the doubled Lipschitz ball.
    rw [Metric.mem_ball] at hy ⊢
    linarith
  have hy_dom : y ∈ effectiveDomain f := hball_dom hy_two_rho
  have hz_dom : z ∈ effectiveDomain f := hball_dom hz_ball
  have hsubE :
      (⟪z - y, v⟫_ℝ : EReal) + (f y : EReal) ≤ (f z : EReal) :=
    (mem_subdifferential_iff (f := f) (x := y) (u := v)).1 hv z
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)
  have hz_bot : (f z : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
  have hsubR : ⟪z - y, v⟫_ℝ + (f y : EReal).toReal ≤ (f z : EReal).toReal := by
    -- On the doubled ball both function values are finite, so the subgradient inequality can be
    -- read in `ℝ`.
    rw [← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_toReal hz_top hz_bot, ← EReal.coe_add]
      at hsubE
    exact_mod_cast hsubE
  have hz_sub : z - y = t • v := by
    -- The test point differs from `y` exactly by the chosen short step.
    dsimp [z]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hinner :
      ⟪z - y, v⟫_ℝ = t * ‖v‖ ^ 2 := by
    -- The horizontal contribution is the standard quadratic form `t * ‖v‖²`.
    calc
      ⟪z - y, v⟫_ℝ = ⟪t • v, v⟫_ℝ := by rw [hz_sub]
      _ = t * ⟪v, v⟫_ℝ := by rw [real_inner_smul_left]
      _ = t * ‖v‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  have hsub_step :
      t * ‖v‖ ^ 2 ≤ (f z : EReal).toReal - (f y : EReal).toReal := by
    linarith [hsubR, hinner]
  have hLip_dist :
      dist ((f z : EReal).toReal) ((f y : EReal).toReal) ≤ (β : ℝ) * dist z y := by
    -- Use the metric-space form of the Lipschitz bound on the doubled ball.
    exact hLip.dist_le_mul z hz_ball y hy_two_rho
  have hLip_real :
      (f z : EReal).toReal - (f y : EReal).toReal ≤ (β : ℝ) * (t * ‖v‖) := by
    have habs :
        |(f z : EReal).toReal - (f y : EReal).toReal| ≤ (β : ℝ) * ‖z - y‖ := by
      simpa [Real.dist_eq, dist_eq_norm] using hLip_dist
    have hz_norm :
        ‖z - y‖ = t * ‖v‖ := by
      rw [hz_sub, norm_smul, Real.norm_of_nonneg ht_pos.le]
    -- Keep only the forward Lipschitz estimate along the chosen step.
    simpa [hz_norm, mul_assoc, mul_left_comm, mul_comm] using (abs_le.mp habs).2
  exact le_trans hsub_step hLip_real

/-- Helper for Proposition 16.17: a subgradient on a locally Lipschitz ball has norm at most the
Lipschitz constant. -/
private lemma norm_le_of_mem_subdifferential_on_lipschitz_ball
    (f : H → Set.Ioi (⊥ : EReal)) {x y v : H} {ρ : ℝ} {β : NNReal}
    (hρ : 0 < ρ)
    (hball_dom : Metric.ball x (2 * ρ) ⊆ effectiveDomain f)
    (hLip : LipschitzOnWith β (fun z ↦ (f z : EReal).toReal) (Metric.ball x (2 * ρ)))
    (hy : y ∈ Metric.ball x ρ) (hv : v ∈ (∂ f) y) :
    ‖v‖ ≤ β := by
  let t : ℝ := ρ / (‖v‖ + 1)
  have ht_pos : 0 < t := by
    -- The source step size is strictly positive.
    dsimp [t]
    positivity
  have hscalar :
      t * ‖v‖ ^ 2 ≤ (β : ℝ) * (t * ‖v‖) := by
    -- First isolate the textbook scalar inequality along the short step.
    simpa [t] using
      subgradient_step_test_le_lipschitz_scalar
        (f := f) hρ hball_dom hLip hy hv
  -- Cancel the positive factor `t` to recover the uniform norm bound.
  exact
    norm_le_of_pos_mul_sq_le_mul (a := ‖v‖) (β := (β : ℝ)) (c := t)
      (norm_nonneg v) β.2 ht_pos hscalar

/-- Helper for Proposition 16.17 (2): a source continuity point implies that the subdifferential
at `x` is nonempty and weakly compact. -/
theorem subdifferential_nonempty_and_weaklyCompact_of_continuousAtOnEffectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtInEffectiveDomain f x) :
    ((∂ f) x).Nonempty ∧ IsCompact (toWeakSpace ℝ H '' ((∂ f) x)) := by
  have hsub_nonempty :
      ((∂ f) x).Nonempty :=
    subdifferential_nonempty_of_continuousAtInEffectiveDomain (f := f) hconv hxcont
  have hx : x ∈ effectiveDomain f :=
    (ContinuousAtOnEffectiveDomain.of_continuousAtInEffectiveDomain hxcont).mem_effectiveDomain
  obtain ⟨ρ, M, hρ, hM⟩ :=
    continuousAtInEffectiveDomain_has_boundedAbove_ball (f := f) hxcont
  have hsup :
      sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x ρ) < ⊤ :=
    finite_sup_ball_lt_top_of_boundedAbove_ball_local (f := f) hM
  have hfour : ∃ r > 0, sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x r) < ⊤ :=
    ⟨ρ, hρ, hsup⟩
  have htfae :=
    convex_tfae_locallyLipschitzNear_continuousAt_boundedBall_finiteSupBall
      f hconv hx
  obtain ⟨β, r, hr, hball_dom, hLip⟩ := (List.TFAE.out htfae 3 0).mp hfour
  have hhalf : 0 < r / 2 := by positivity
  have hball_dom_half : Metric.ball x (2 * (r / 2)) ⊆ effectiveDomain f := by
    simpa [two_mul] using hball_dom
  have hLip_half :
      LipschitzOnWith β (fun z ↦ (f z : EReal).toReal) (Metric.ball x (2 * (r / 2))) := by
    simpa [two_mul] using hLip
  have hsubset : (∂ f) x ⊆ Metric.closedBall (0 : H) β := by
    intro v hv
    have hv_norm :
        ‖v‖ ≤ β :=
      norm_le_of_mem_subdifferential_on_lipschitz_ball
        (f := f) hhalf hball_dom_half hLip_half (Metric.mem_ball_self hhalf) hv
    -- The local Lipschitz estimate bounds every subgradient by the same closed ball.
    simpa [Metric.mem_closedBall, dist_eq_norm] using hv_norm
  have hbounded : Bornology.IsBounded ((∂ f) x) :=
    Metric.isBounded_closedBall.subset hsubset
  -- Closedness and convexity are already available from Proposition 16.4.
  refine ⟨hsub_nonempty, weaklyCompact_of_bounded_closed_convex hbounded ?_ ?_⟩
  · exact isClosed_subdifferential f x
  · exact convex_subdifferential f x

/-- Proposition 16.17 (2): clause (ii). If `x ∈ cont f`, represented here by `ContinuousPoint f x`,
then the subdifferential at `x` is nonempty and weakly compact. -/
theorem subdifferential_nonempty_and_weaklyCompact_of_continuousPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x) :
    ((∂ f) x).Nonempty ∧ IsCompact (toWeakSpace ℝ H '' ((∂ f) x)) := by
  -- `ContinuousPoint` is just the source-continuity abbreviation used in this chapter.
  simpa [ContinuousPoint] using
    subdifferential_nonempty_and_weaklyCompact_of_continuousAtOnEffectiveDomain
      f hconv hxcont

-- Proof sketch: source continuity yields local Lipschitz control on a surrounding ball; then
-- every nearby subgradient is norm-bounded by the same Lipschitz constant.
-- Route correction: the same counterexample as above shows that relative continuity on
-- `effectiveDomain f` is not enough for local boundedness of nearby subdifferentials.
/-- Helper for Proposition 16.17 (3): a source continuity point yields a positive radius for which
the union of the nearby subdifferentials is bounded. -/
theorem subdifferential_ball_union_bounded_of_continuousAtOnEffectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtInEffectiveDomain f x) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Bornology.IsBounded (⋃ y ∈ Metric.ball x ρ, (∂ f) y) := by
  have hx : x ∈ effectiveDomain f :=
    (ContinuousAtOnEffectiveDomain.of_continuousAtInEffectiveDomain hxcont).mem_effectiveDomain
  obtain ⟨ρ, M, hρ, hM⟩ :=
    continuousAtInEffectiveDomain_has_boundedAbove_ball (f := f) hxcont
  have hsup :
      sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x ρ) < ⊤ :=
    finite_sup_ball_lt_top_of_boundedAbove_ball_local (f := f) hM
  have hfour : ∃ r > 0, sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x r) < ⊤ :=
    ⟨ρ, hρ, hsup⟩
  have htfae :=
    convex_tfae_locallyLipschitzNear_continuousAt_boundedBall_finiteSupBall
      f hconv hx
  obtain ⟨β, r, hr, hball_dom, hLip⟩ := (List.TFAE.out htfae 3 0).mp hfour
  have hhalf : 0 < r / 2 := by positivity
  have hball_dom_half : Metric.ball x (2 * (r / 2)) ⊆ effectiveDomain f := by
    simpa [two_mul] using hball_dom
  have hLip_half :
      LipschitzOnWith β (fun z ↦ (f z : EReal).toReal) (Metric.ball x (2 * (r / 2))) := by
    simpa [two_mul] using hLip
  refine ⟨r / 2, hhalf, ?_⟩
  have hsubset : ⋃ y ∈ Metric.ball x (r / 2), (∂ f) y ⊆ Metric.closedBall (0 : H) β := by
    intro v hv
    rcases mem_iUnion.mp hv with ⟨y, hv⟩
    rcases mem_iUnion.mp hv with ⟨hy, hvy⟩
    have hv_norm :
        ‖v‖ ≤ β :=
      norm_le_of_mem_subdifferential_on_lipschitz_ball
        (f := f) hhalf hball_dom_half hLip_half hy hvy
    -- Every nearby subgradient lies in the same radius-`β` closed ball.
    simpa [Metric.mem_closedBall, dist_eq_norm] using hv_norm
  exact Metric.isBounded_closedBall.subset hsubset

/-- Proposition 16.17 (3): clause (iii). If `x ∈ cont f`, represented here by `ContinuousPoint f x`,
then there exists `ρ ∈ ℝ₊₊` such that `∂ f(B(x; ρ))` is bounded. -/
theorem subdifferential_ball_union_bounded_of_continuousPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Bornology.IsBounded (⋃ y ∈ Metric.ball x ρ, (∂ f) y) := by
  -- `ContinuousPoint` is just the source-continuity abbreviation used in this chapter.
  simpa [ContinuousPoint] using
    subdifferential_ball_union_bounded_of_continuousAtOnEffectiveDomain
      f hconv hxcont

-- Proof sketch: Corollary 8.39 transports one source continuity point to every interior-domain
-- point, and clause (ii) then supplies a nonempty subdifferential at each of those points.
/-- Proposition 16.17 (4): clause (iv). If the source continuity set of `f` is nonempty, then
every interior point of the effective domain is a subdifferentiability point. -/
theorem interior_effectiveDomain_subset_subdifferentiabilityDomain_of_exists_continuityPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    (hcont : ∃ x : H, ContinuousPoint f x) :
    interior (effectiveDomain f) ⊆ {x : H | SubdifferentiableAt f x} := by
  rcases hcont with ⟨x₀, hx₀cont⟩
  obtain ⟨ρ, M, hρ, hM⟩ :=
    continuousAtInEffectiveDomain_has_boundedAbove_ball (f := f) hx₀cont
  have hsup :
      sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) < ⊤ :=
    finite_sup_ball_lt_top_of_boundedAbove_ball_local (f := f) hM
  have hcont_eq :
      {x : H | ContinuousPoint f x} = interior (effectiveDomain f) := by
    -- Corollary 8.39 propagates one finite-sup ball to every interior-domain point.
    simpa [ContinuousPoint] using
      continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
        (f := f) hconv (Or.inl ⟨x₀, ρ, hρ, hsup⟩)
  intro y hy
  have hy_cont : ContinuousPoint f y := by
    have hy_mem : y ∈ ({x : H | ContinuousPoint f x} : Set H) := by
      -- Read Corollary 8.39 at the point `y`.
      rw [hcont_eq]
      exact hy
    simpa using hy_mem
  rcases
      (subdifferential_nonempty_and_weaklyCompact_of_continuousPoint
        (f := f) hconv hy_cont).1 with ⟨u, hu⟩
  -- Nonemptiness of `∂ f y` is exactly subdifferentiability at `y`.
  exact ⟨u, hu⟩

end SubdifferentialContinuity

end

end ERealFunction
