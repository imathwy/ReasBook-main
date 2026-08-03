import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap08.Proposition_8_35
import BauschkeLean.Chap12.Definition_12_34

-- Declarations for this item will be appended below by the statement pipeline.

open Set

noncomputable section

universe u v

namespace ERealFunction

variable {H : Type u} {K : Type v}

/-- Proposition 12 36 (1): the effective domain of the infimal postcomposition is the image under
`L` of the effective domain of `f`. -/
theorem dom_infimalPostcomposition (L : H → K) (f : H → Set.Ioi (⊥ : EReal)) :
    dom (L ▷ f) = L '' effectiveDomain f := by
  ext y
  rw [mem_dom_iff, Set.mem_image]
  change sInf ((fun x ↦ (f x : EReal)) '' (L ⁻¹' {y})) < ⊤ ↔
      ∃ x, ((f x : EReal) < ⊤) ∧ L x = y
  constructor
  · intro hy
    obtain ⟨z, hzmem, hzlt⟩ := (sInf_lt_iff).1 hy
    rcases hzmem with ⟨x, hxLy, rfl⟩
    exact ⟨x, hzlt, by simpa using hxLy⟩
  · rintro ⟨x, hxdom, hxLy⟩
    refine lt_of_le_of_lt (sInf_le ?_) hxdom
    exact ⟨x, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hxLy, rfl⟩

section RealVectorSpace

variable [AddCommGroup H] [Module ℝ H]
variable [AddCommGroup K] [Module ℝ K]

omit [AddCommGroup H] [Module ℝ H] [AddCommGroup K] [Module ℝ K] in
/-- Helper for Proposition 12 36: a strict upper bound on `(L ▷ f) y` is exceeded by some finite
value of `f` on the fiber `L ⁻¹' {y}`. -/
private lemma exists_lt_fiber_of_infimalPostcomposition_lt
    (L : H → K) (f : H → Set.Ioi (⊥ : EReal)) {y : K} {ξ : EReal}
    (hξ : (L ▷ f) y < ξ) :
    ∃ x : H, L x = y ∧ (f x : EReal) < ξ := by
  -- Unfold the fiber infimum and extract one fiber point lying below the chosen upper bound.
  change sInf ((fun x ↦ (f x : EReal)) '' (L ⁻¹' {y})) < ξ at hξ
  obtain ⟨z, hzmem, hzlt⟩ := (sInf_lt_iff).1 hξ
  rcases hzmem with ⟨x, hxmem, rfl⟩
  refine ⟨x, ?_, hzlt⟩
  simpa [Set.mem_preimage, Set.mem_singleton_iff] using hxmem

omit [AddCommGroup H] [Module ℝ H] [AddCommGroup K] [Module ℝ K] in
/-- Helper for Proposition 12 36: evaluating `L ▷ f` at a point `y` is bounded above by any value
of `f` attained on the fiber `L ⁻¹' {y}`. -/
private lemma infimalPostcomposition_le_of_eq
    (L : H → K) (f : H → Set.Ioi (⊥ : EReal)) {x : H} {y : K}
    (hxy : L x = y) :
    (L ▷ f) y ≤ (f x : EReal) := by
  -- The chosen fiber point is an admissible witness for the defining infimum.
  change sInf ((fun z ↦ (f z : EReal)) '' (L ⁻¹' {y})) ≤ (f x : EReal)
  refine sInf_le ?_
  exact ⟨x, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hxy, rfl⟩

/-- Helper for Proposition 12 36: an affine map sends the textbook convex combination
`α • x₁ + (1 - α) • x₂` to the corresponding convex combination of the endpoint images. -/
private lemma map_affine_combination_infimalPostcomposition
    (L : H →ᵃ[ℝ] K) (x₁ x₂ : H) (α : ℝ) :
    L (α • x₁ + (1 - α) • x₂) = α • L x₁ + (1 - α) • L x₂ := by
  -- Rewrite the combination as a line map and use that affine maps preserve line maps.
  simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
    L.apply_lineMap x₂ x₁ α

-- Proof sketch: treat the source hypothesis “`f` is convex” through the project owner
-- `Convex ℝ (epigraph f.asEReal)`. Then consider the jointly convex function on `K × H` obtained
-- by adding `f.asEReal` to the indicator of the graph of `L`. Proposition 8.35 gives convexity
-- of its marginal, which is exactly `L ▷ f`.
/-- Proposition 12 36 (2): if `f` has convex real-height epigraph and `L` is affine, then the
real-height epigraph of `L ▷ f` is convex. -/
theorem convex_epigraph_infimalPostcomposition (f : H → Set.Ioi (⊥ : EReal))
    (L : H →ᵃ[ℝ] K) (hf : Convex ℝ (epigraph f.asEReal)) :
    Convex ℝ (epigraph (L ▷ f)) := by
  -- Route correction: the graph-indicator marginal route does not fit the available API, so we
  -- follow Proposition 8.35 directly on the fibers defining `L ▷ f`.
  have hfJ := (convex_epigraph_iff_jensen_on_dom f.asEReal).1 hf
  -- Proposition 8.4 again reduces the goal to Jensen's inequality on `dom (L ▷ f)`.
  refine (convex_epigraph_iff_jensen_on_dom (L ▷ f)).2 ?_
  intro y₁ y₂ hy₁_dom hy₂_dom α hα0 hα1
  have h_one_sub_pos : 0 < 1 - α := sub_pos.mpr hα1
  have hαE_pos : (0 : EReal) < (α : EReal) := by
    exact_mod_cast hα0
  have h_one_sub_E_pos : (0 : EReal) < (((1 - α : ℝ)) : EReal) := by
    exact_mod_cast h_one_sub_pos
  have hterm₁_ne_top : (α : EReal) * (L ▷ f) y₁ ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot α), Or.inl (by exact_mod_cast hα0.le),
      Or.inl (EReal.coe_ne_top α), ?_⟩
    exact Or.inr ((mem_dom_iff (L ▷ f) y₁).mp hy₁_dom).ne
  have hterm₂_ne_top : (((1 - α : ℝ)) : EReal) * (L ▷ f) y₂ ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 - α)),
      Or.inl (by exact_mod_cast h_one_sub_pos.le), Or.inl (EReal.coe_ne_top (1 - α)), ?_⟩
    exact Or.inr ((mem_dom_iff (L ▷ f) y₂).mp hy₂_dom).ne
  -- Reserve separate budgets above the two weighted fiber infima and close the inequality by
  -- taking approximate minimizers on each fiber.
  refine EReal.le_add_of_forall_gt (Or.inr hterm₂_ne_top) (Or.inl hterm₁_ne_top) ?_
  intro a' ha' b' hb'
  have hy₁_lt_div : (L ▷ f) y₁ < a' / (α : EReal) := by
    refine (EReal.lt_div_iff hαE_pos (EReal.coe_ne_top α)).2 ?_
    simpa [mul_comm] using ha'
  have hy₂_lt_div : (L ▷ f) y₂ < b' / (((1 - α : ℝ)) : EReal) := by
    refine (EReal.lt_div_iff h_one_sub_E_pos (EReal.coe_ne_top (1 - α))).2 ?_
    simpa [mul_comm] using hb'
  obtain ⟨ξ₁, hξ₁_lower, hξ₁_upper⟩ := EReal.exists_between_coe_real hy₁_lt_div
  obtain ⟨ξ₂, hξ₂_lower, hξ₂_upper⟩ := EReal.exists_between_coe_real hy₂_lt_div
  obtain ⟨x₁, hx₁_map, hx₁_lt⟩ := exists_lt_fiber_of_infimalPostcomposition_lt L f hξ₁_lower
  obtain ⟨x₂, hx₂_map, hx₂_lt⟩ := exists_lt_fiber_of_infimalPostcomposition_lt L f hξ₂_lower
  have hx₁_dom : x₁ ∈ dom f.asEReal := by
    rw [mem_dom_iff]
    exact lt_trans hx₁_lt (EReal.coe_lt_top ξ₁)
  have hx₂_dom : x₂ ∈ dom f.asEReal := by
    rw [mem_dom_iff]
    exact lt_trans hx₂_lt (EReal.coe_lt_top ξ₂)
  have hmap_combo :
      L (α • x₁ + (1 - α) • x₂) = α • y₁ + (1 - α) • y₂ := by
    simpa [hx₁_map, hx₂_map] using
      map_affine_combination_infimalPostcomposition L x₁ x₂ α
  have h_eval :
      (L ▷ f) (α • y₁ + (1 - α) • y₂) ≤
        (f (α • x₁ + (1 - α) • x₂) : EReal) := by
    exact infimalPostcomposition_le_of_eq (L := L) (f := f) hmap_combo
  have h_convex_eval :
      (f (α • x₁ + (1 - α) • x₂) : EReal) ≤
        (α : EReal) * (f x₁ : EReal) +
          (((1 - α : ℝ)) : EReal) * (f x₂ : EReal) := by
    -- Apply Jensen's inequality for `f` at the two approximate minimizers on the fibers.
    simpa using hfJ hx₁_dom hx₂_dom hα0 hα1
  have h_weight₁ : (α : EReal) * (f x₁ : EReal) < (α : EReal) * (ξ₁ : EReal) := by
    -- Scaling preserves the strict approximation on the first fiber because `α > 0`.
    have : (f x₁ : EReal) * (α : EReal) < (ξ₁ : EReal) * (α : EReal) := by
      exact strict_right_mul_lt hαE_pos (EReal.coe_ne_top α) hx₁_lt
    simpa [mul_comm] using this
  have h_weight₂ :
      (((1 - α : ℝ)) : EReal) * (f x₂ : EReal) <
        (((1 - α : ℝ)) : EReal) * (ξ₂ : EReal) := by
    -- The same positive-scaling argument applies to the second fiber with coefficient `1 - α`.
    have : (f x₂ : EReal) * (((1 - α : ℝ)) : EReal) <
        (ξ₂ : EReal) * (((1 - α : ℝ)) : EReal) := by
      exact strict_right_mul_lt h_one_sub_E_pos (EReal.coe_ne_top (1 - α)) hx₂_lt
    simpa [mul_comm] using this
  have h_budget₁ : (α : EReal) * (ξ₁ : EReal) < a' := by
    -- The first approximation level was chosen strictly below the reserved first budget.
    have : (ξ₁ : EReal) * (α : EReal) < a' :=
      (EReal.lt_div_iff hαE_pos (EReal.coe_ne_top α)).1 hξ₁_upper
    simpa [mul_comm] using this
  have h_budget₂ : (((1 - α : ℝ)) : EReal) * (ξ₂ : EReal) < b' := by
    -- The second approximation level was chosen strictly below the reserved second budget.
    have : (ξ₂ : EReal) * (((1 - α : ℝ)) : EReal) < b' :=
      (EReal.lt_div_iff h_one_sub_E_pos (EReal.coe_ne_top (1 - α))).1 hξ₂_upper
    simpa [mul_comm] using this
  have h_weighted_lt :
      (α : EReal) * (f x₁ : EReal) +
          (((1 - α : ℝ)) : EReal) * (f x₂ : EReal) <
        a' + b' := by
    -- Combine the two strict fiber estimates and then compare with the two budgets.
    exact lt_trans (EReal.add_lt_add h_weight₁ h_weight₂) (EReal.add_lt_add h_budget₁ h_budget₂)
  exact (lt_of_le_of_lt (le_trans h_eval h_convex_eval) h_weighted_lt).le

end RealVectorSpace

end ERealFunction
