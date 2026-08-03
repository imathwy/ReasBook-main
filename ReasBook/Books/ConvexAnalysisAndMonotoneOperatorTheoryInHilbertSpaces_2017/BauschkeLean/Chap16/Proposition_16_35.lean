import Mathlib
import BauschkeLean.Chap06.Definition_6_38
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise
open WithLp

universe u

namespace ERealFunction

noncomputable section

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

/-- Helper for Proposition 16 35: the support inequality on the translate `C - {p}` is equivalent
to the pointwise inner-product inequalities against all points of `C`. -/
private lemma innerSupremumOn_sub_singleton_le_zero_iff_forall_inner_nonpos
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} {u p : E} :
    innerSupremumOn (C - ({p} : Set E)) u ≤ 0 ↔
      ∀ z ∈ C, ⟪z - p, u⟫_ℝ ≤ 0 := by
  constructor
  · intro hsup
    -- Compare the translate against `{0}` to recover the pointwise inequalities.
    have hsep :
        innerSupremumOn (C - ({p} : Set E)) u ≤ innerInfimumOn ({0} : Set E) u := by
      simpa using hsup
    have hinner :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({p} : Set E)) ({0} : Set E) u).1 hsep
    intro z hz
    have hp_mem : p ∈ ({p} : Set E) := by
      simp
    have hzero_mem : (0 : E) ∈ ({0} : Set E) := by
      simp
    have hz_sub : z - p ∈ C - ({p} : Set E) := by
      exact ⟨z, hz, p, hp_mem, rfl⟩
    simpa using hinner (z - p) hz_sub 0 hzero_mem
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

section Subdifferentials

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2
  prod_normedSpace_l2 prod_innerProductSpace_l2

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 16 35: every point of the effective domain contributes its canonical
real-height graph point to the epigraph. -/
private lemma mem_epigraph_toReal_of_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} (hy : y ∈ effectiveDomain f) :
    (y, (f y : EReal).toReal) ∈ epigraph f.asEReal := by
  -- Finiteness of `f y` says that the canonical real height lies on the epigraph.
  rw [mem_epigraph_iff]
  exact EReal.le_coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hy))

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 16 35: a real-height epigraph point has finite base value, and its
ordinate dominates the canonical graph height. -/
private lemma effectiveDomain_and_toReal_le_of_mem_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} {η : ℝ}
    (hyη : (y, η) ∈ epigraph f.asEReal) :
    y ∈ effectiveDomain f ∧ (f y : EReal).toReal ≤ η := by
  -- Epigraph membership gives a finite upper bound on `f y`, so `y` lies in the effective domain
  -- and `toReal` preserves the comparison.
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

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 16 35: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul (a b : ℝ) :
    ⟪a, b⟫_ℝ = a * b := by
  calc
    ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
    _ = a * b := by simp

/-- Helper for Proposition 16 35: the product Hilbert inner product on `H × ℝ` splits into the
two coordinates. -/
private lemma inner_pair_eq_add_mul
    {p u : H} {r a : ℝ} :
    ⟪(p, r), (u, a)⟫_ℝ = ⟪p, u⟫_ℝ + r * a := by
  change ⟪p, u⟫_ℝ + ⟪r, a⟫_ℝ = ⟪p, u⟫_ℝ + r * a
  rw [real_inner_eq_mul]

/-- Helper for Proposition 16 35: the product Hilbert inner product on `H × ℝ` splits into the
horizontal and vertical contributions after translating by a graph point. -/
private lemma inner_sub_graphPoint_eq
    {x y u : H} {ξ η a : ℝ} :
    ⟪(y, η) - (x, ξ), (u, a)⟫_ℝ = ⟪y - x, u⟫_ℝ + (η - ξ) * a := by
  -- Under the canonical `ℓ²` product Hilbert structure, this is definitionally the textbook
  -- componentwise formula.
  change ⟪(y - x, η - ξ), (u, a)⟫_ℝ = ⟪y - x, u⟫_ℝ + (η - ξ) * a
  simpa using
    (inner_pair_eq_add_mul (p := y - x) (u := u) (r := η - ξ) (a := a))

/-- Helper for Proposition 16 35: epigraph normal-cone membership at the finite graph point is
equivalent to the translated pointwise inner-product inequalities against all epigraph points. -/
private lemma mem_normalCone_epigraph_iff_forall_inner_pair_nonpos
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ effectiveDomain f) {u : H} {a : ℝ} :
    (u, a) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) ↔
      ∀ y η, (y, η) ∈ epigraph f.asEReal →
        ⟪(y, η) - (x, (f x : EReal).toReal), (u, a)⟫_ℝ ≤ 0 := by
  have hx_epi : (x, (f x : EReal).toReal) ∈ epigraph f.asEReal :=
    mem_epigraph_toReal_of_mem_effectiveDomain (f := f) hx
  -- Rewrite the normal cone at a point of the epigraph into the translated support inequality.
  rw [Set.normalCone_of_mem hx_epi]
  have hnormal_iff :
      innerSupremumOn
          (epigraph f.asEReal - ({(x, (f x : EReal).toReal)} : Set (H × ℝ))) (u, a) ≤ 0 ↔
        ∀ z ∈ epigraph f.asEReal,
          ⟪z - (x, (f x : EReal).toReal), (u, a)⟫_ℝ ≤ 0 := by
    exact
      (innerSupremumOn_sub_singleton_le_zero_iff_forall_inner_nonpos :
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

/-- Helper for Proposition 16 35: any normal vector to the epigraph at the finite graph point has
nonpositive scalar component. -/
private lemma snd_nonpos_of_mem_normalCone_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ effectiveDomain f) {u : H} {a : ℝ}
    (hu : (u, a) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal)) :
    a ≤ 0 := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hone_nonneg : 0 ≤ (1 : ℝ) := by
    norm_num
  have htoReal_le : (f x : EReal).toReal ≤ (f x : EReal).toReal + 1 := by
    exact le_add_of_nonneg_right hone_nonneg
  have hheight_aux :
      (((f x : EReal).toReal + 1 : ℝ) : EReal) =
        (((f x : EReal).toReal : ℝ) : EReal) + 1 := by
    exact_mod_cast rfl
  have htoReal_le' :
      (((f x : EReal).toReal : ℝ) : EReal) ≤ (((f x : EReal).toReal + 1 : ℝ) : EReal) := by
    exact_mod_cast htoReal_le
  have hheight : (f x : EReal) ≤ (((f x : EReal).toReal + 1 : ℝ) : EReal) := by
    exact le_trans (EReal.le_coe_toReal hx_top) htoReal_le'
  have hpoint : (x, (f x : EReal).toReal + 1) ∈ epigraph f.asEReal := by
    -- Testing against a strictly higher point above the same base point isolates the scalar
    -- component of the normal.
    rw [mem_epigraph_iff]
    exact hheight
  have hineq :=
    (mem_normalCone_epigraph_iff_forall_inner_pair_nonpos (f := f) hx).1 hu
      x ((f x : EReal).toReal + 1) hpoint
  have hpair : ⟪(0 : H), u⟫_ℝ + (1 : ℝ) * a ≤ 0 := by
    simpa [inner_pair_eq_add_mul] using hineq
  simpa using hpair

/-- Helper for Proposition 16 35: the zero scalar slice of the epigraph normal cone is exactly the
horizontal slice over the normal cone to the effective domain. -/
private lemma mem_normalCone_epigraph_zero_slice_iff
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ effectiveDomain f) {u : H} :
    (u, (0 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) ↔
      (u, (0 : ℝ)) ∈ N[effectiveDomain f] x ×ˢ ({0} : Set ℝ) := by
  -- Route correction: first identify the zero vertical slice with `N[effectiveDomain f] x`, then
  -- repackage it as a product slice over `{0}`.
  have hbase :
      (u, (0 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) ↔
        u ∈ N[effectiveDomain f] x := by
    constructor
    · intro hu
      have hpointwise : ∀ y ∈ effectiveDomain f, ⟪y - x, u⟫_ℝ ≤ 0 := by
        intro y hy
        have hy_epi : (y, (f y : EReal).toReal) ∈ epigraph f.asEReal :=
          mem_epigraph_toReal_of_mem_effectiveDomain (f := f) hy
        have hineq :=
          (mem_normalCone_epigraph_iff_forall_inner_pair_nonpos (f := f) hx).1 hu
            y ((f y : EReal).toReal) hy_epi
        have hpair :
            ⟪y - x, u⟫_ℝ + (((f y : EReal).toReal - (f x : EReal).toReal) * 0) ≤ 0 := by
          simpa [inner_pair_eq_add_mul] using hineq
        simpa using hpair
      rw [Set.normalCone_of_mem hx]
      have hnormal_iff :
          innerSupremumOn (effectiveDomain f - ({x} : Set H)) u ≤ 0 ↔
            ∀ y ∈ effectiveDomain f, ⟪y - x, u⟫_ℝ ≤ 0 := by
        exact
          (innerSupremumOn_sub_singleton_le_zero_iff_forall_inner_nonpos :
            innerSupremumOn (effectiveDomain f - ({x} : Set H)) u ≤ 0 ↔
              ∀ y ∈ effectiveDomain f, ⟪y - x, u⟫_ℝ ≤ 0)
      exact hnormal_iff.2 hpointwise
    · intro hu
      rw [Set.normalCone_of_mem hx] at hu
      have hdomain_iff :
          innerSupremumOn (effectiveDomain f - ({x} : Set H)) u ≤ 0 ↔
            ∀ y ∈ effectiveDomain f, ⟪y - x, u⟫_ℝ ≤ 0 := by
        exact
          (innerSupremumOn_sub_singleton_le_zero_iff_forall_inner_nonpos :
            innerSupremumOn (effectiveDomain f - ({x} : Set H)) u ≤ 0 ↔
              ∀ y ∈ effectiveDomain f, ⟪y - x, u⟫_ℝ ≤ 0)
      have hdomain_pointwise := hdomain_iff.1 hu
      have hepigraph_pointwise :
          ∀ y η, (y, η) ∈ epigraph f.asEReal →
            ⟪(y, η) - (x, (f x : EReal).toReal), (u, (0 : ℝ))⟫_ℝ ≤ 0 := by
        intro y η hyη
        rcases effectiveDomain_and_toReal_le_of_mem_epigraph (f := f) hyη with ⟨hy, _⟩
        have hpair : ⟪y - x, u⟫_ℝ + ((η - (f x : EReal).toReal) * 0) ≤ 0 := by
          simpa using hdomain_pointwise y hy
        simpa [inner_pair_eq_add_mul] using hpair
      exact
        (mem_normalCone_epigraph_iff_forall_inner_pair_nonpos (f := f) hx).2 hepigraph_pointwise
  simpa using hbase

/-- Helper for Proposition 16 35: on a strictly negative vertical slice, epigraph normals are
exactly the positive scalar multiples of subgradients. -/
private lemma mem_normalCone_epigraph_pair_neg_iff_mem_smul_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) {x u : H} {v : ℝ} (hx : x ∈ effectiveDomain f) (hv : 0 < v) :
    (u, -v) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) ↔ u ∈ v • (∂ f) x := by
  constructor
  · intro hu
    have hv_ne : v ≠ 0 := ne_of_gt hv
    have hpointwise :=
      (mem_normalCone_epigraph_iff_forall_inner_pair_nonpos (f := f) hx).1 hu
    have hsubgrad : v⁻¹ • u ∈ (∂ f) x := by
      -- Rewrite the normal inequalities on canonical graph points into the subgradient inequality.
      rw [mem_subdifferential_iff]
      intro y
      by_cases hy : y ∈ effectiveDomain f
      · have hy_epi : (y, (f y : EReal).toReal) ∈ epigraph f.asEReal :=
          mem_epigraph_toReal_of_mem_effectiveDomain (f := f) hy
        have hineq := hpointwise y ((f y : EReal).toReal) hy_epi
        have hlinear :
            ⟪y - x, u⟫_ℝ + (((f y : EReal).toReal - (f x : EReal).toReal) * (-v)) ≤ 0 := by
          simpa [inner_pair_eq_add_mul] using hineq
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
          have hmul :=
            mul_le_mul_of_nonneg_left hreal_le (inv_pos.mpr hv).le
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
    -- The subgradient inequality at height `(f y).toReal` extends to every epigraph point
    -- because epigraph ordinates dominate the graph height.
    refine (mem_normalCone_epigraph_iff_forall_inner_pair_nonpos (f := f) hx).2 ?_
    intro y η hyη
    rcases effectiveDomain_and_toReal_le_of_mem_epigraph (f := f) hyη with ⟨hy, hη⟩
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
    have hlinear :
        ⟪(y, η) - (x, (f x : EReal).toReal), (v • w, -v)⟫_ℝ ≤ 0 := by
      simpa [inner_pair_eq_add_mul, real_inner_smul_right, mul_assoc, mul_left_comm, mul_comm]
        using hlinear_aux
    exact hlinear

/-- Helper for Proposition 16 35: membership in the positive ray generated by
`(∂ f x) × {-1}` is equivalent to a positive scalar slice description. -/
private lemma mem_positive_ray_subdifferential_slice_iff
    {f : H → Set.Ioi (⊥ : EReal)} {x u : H} {a : ℝ} :
    (u, a) ∈ Ioi (0 : ℝ) • ((∂ f) x ×ˢ ({-1} : Set ℝ)) ↔
      ∃ v : ℝ, 0 < v ∧ u ∈ v • (∂ f) x ∧ a = -v := by
  constructor
  · intro hu
    change (u, a) ∈ Set.image2 (· • ·) (Ioi (0 : ℝ)) ((∂ f) x ×ˢ ({-1} : Set ℝ)) at hu
    rcases hu with ⟨v, hv, z, hz, hz_eq⟩
    rcases z with ⟨w, b⟩
    rcases hz with ⟨hw, hb⟩
    have hu_eq : v • w = u := by
      simpa using congrArg Prod.fst hz_eq
    have ha_eq : a = -v := by
      have hb_eq : b = -1 := by
        simpa using hb
      have hsnd_eq : v * b = a := by
        simpa using congrArg Prod.snd hz_eq
      simpa [hb_eq, mul_comm] using hsnd_eq.symm
    have hu_mem : u ∈ v • (∂ f) x := by
      refine Set.mem_smul_set.mpr ?_
      exact ⟨w, hw, hu_eq⟩
    exact ⟨v, hv, hu_mem, ha_eq⟩
  · rintro ⟨v, hv, hu, ha_eq⟩
    rcases Set.mem_smul_set.mp hu with ⟨w, hw, hw_eq⟩
    have hminus_mem : (-1 : ℝ) ∈ ({-1} : Set ℝ) := by
      simp
    have hpair_mem : (w, (-1 : ℝ)) ∈ (∂ f) x ×ˢ ({-1} : Set ℝ) := by
      exact ⟨hw, hminus_mem⟩
    have hpair_eq : v • (w, (-1 : ℝ)) = (u, a) := by
      ext <;> simp [hw_eq, ha_eq]
    change (u, a) ∈ Set.image2 (· • ·) (Ioi (0 : ℝ)) ((∂ f) x ×ˢ ({-1} : Set ℝ))
    exact ⟨v, hv, (w, (-1 : ℝ)), hpair_mem, hpair_eq⟩

/-- Helper for Proposition 16 35: on the strictly negative scalar slice, epigraph normal-cone
membership is exactly the positive ray generated by the subdifferential slice `(∂ f x) × {-1}`. -/
private lemma mem_normalCone_epigraph_neg_slice_iff_mem_positive_subdifferential_ray
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ effectiveDomain f) {u : H} {a : ℝ}
    (ha : a < 0) :
    (u, a) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) ↔
      (u, a) ∈ Ioi (0 : ℝ) • ((∂ f) x ×ˢ ({-1} : Set ℝ)) := by
  have hv : 0 < -a := by
    linarith
  constructor
  · intro hu
    -- Rewrite the negative scalar slice as `(u, -v)` with `v = -a`, then apply the cleaner
    -- scaled-subdifferential characterization.
    have hsmul : u ∈ (-a) • (∂ f) x := by
      have hpair : (u, -(-a)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) := by
        simpa using hu
      exact
        (mem_normalCone_epigraph_pair_neg_iff_mem_smul_subdifferential
          (f := f) (x := x) (u := u) (v := -a) hx hv).1 hpair
    have ha_eq : a = -(-a) := by
      exact (neg_neg a).symm
    exact
      (mem_positive_ray_subdifferential_slice_iff (f := f) (x := x) (u := u) (a := a)).2
        ⟨-a, hv, hsmul, ha_eq⟩
  · intro hu
    rcases (mem_positive_ray_subdifferential_slice_iff (f := f) (x := x) (u := u) (a := a)).1 hu
      with ⟨v, hv, huv, ha_eq⟩
    have hpair :=
      (mem_normalCone_epigraph_pair_neg_iff_mem_smul_subdifferential
        (f := f) (x := x) (u := u) (v := v) hx hv).2 huv
    simpa [ha_eq] using hpair

-- Proof sketch: unfold the normal cone to `epigraph f.asEReal` at the finite graph point
-- `(x, (f x : EReal).toReal)` and split a normal vector according to whether its scalar component
-- is `0` or negative. The zero slice gives the normal cone to `effectiveDomain f`, while the
-- negative slice rewrites to a positive multiple of a subgradient at `x`.
/-- Proposition 16 35: for `x ∈ effectiveDomain f`, the normal cone to the real-height epigraph of
`f` at the graph point `(x, (f x).toReal)` is the union of the horizontal slice over the normal
cone to `effectiveDomain f` at `x` and the positive ray generated by the subdifferential slice
`(∂ f x) × {-1}`. -/
theorem normalCone_epigraph_eq_effectiveDomain_normal_zero_union_positive_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ effectiveDomain f) :
    N[epigraph f.asEReal] (x, (f x : EReal).toReal) =
      N[effectiveDomain f] x ×ˢ ({0} : Set ℝ) ∪
        Ioi (0 : ℝ) • ((∂ f) x ×ˢ ({-1} : Set ℝ)) := by
  ext p
  rcases p with ⟨u, a⟩
  constructor
  · intro hu
    -- The scalar component of any epigraph normal is nonpositive, so only the zero or strictly
    -- negative slices can occur.
    have ha_nonpos :=
      snd_nonpos_of_mem_normalCone_epigraph (f := f) (x := x) hx (u := u) (a := a) hu
    rcases eq_or_lt_of_le ha_nonpos with ha_zero | ha_neg
    · left
      have hu_zero : (u, (0 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) := by
        simpa [ha_zero] using hu
      simpa [ha_zero] using
        (mem_normalCone_epigraph_zero_slice_iff (f := f) (x := x) hx (u := u)).1
          hu_zero
    · right
      exact
        (mem_normalCone_epigraph_neg_slice_iff_mem_positive_subdifferential_ray
          (f := f) (x := x) hx (u := u) (a := a) ha_neg).1 hu
  · intro hu
    rcases hu with hu_zero | hu_neg
    · have ha_zero : a = 0 := by
        simpa using hu_zero.2
      have hu_zero' : (u, (0 : ℝ)) ∈ N[effectiveDomain f] x ×ˢ ({0} : Set ℝ) := by
        simpa [ha_zero] using hu_zero
      simpa [ha_zero] using
        (mem_normalCone_epigraph_zero_slice_iff (f := f) (x := x) hx (u := u)).2 hu_zero'
    · rcases
        (mem_positive_ray_subdifferential_slice_iff (f := f) (x := x) (u := u) (a := a)).1 hu_neg
          with ⟨v, hv, huv, ha_eq⟩
      have ha_neg : a < 0 := by
        linarith [hv]
      exact
        (mem_normalCone_epigraph_neg_slice_iff_mem_positive_subdifferential_ray
          (f := f) (x := x) hx (u := u) (a := a) ha_neg).2 hu_neg

end Subdifferentials

end

end ERealFunction
