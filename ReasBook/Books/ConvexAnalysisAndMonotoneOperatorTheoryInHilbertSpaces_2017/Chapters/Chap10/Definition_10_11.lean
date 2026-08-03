import BauschkeLean.Chap10.Definition_10_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Semantic recall: the source defines the exact modulus for proper convex functions, but the
-- infimum formula itself depends only on `f`; properness and convexity belong on the theorem
-- surface that uses this modulus, not in the data owner.
/-- Definition 10.11: the exact modulus of convexity of an `]-∞,+∞]`-valued function assigns to
each radius `t ≥ 0` the infimum of the normalized Jensen gaps over all effective-domain pairs at
distance `t` and all coefficients `α ∈ ]0,1[`. For proper convex functions, this is the
source-facing exact modulus used throughout Chapter 10. -/
noncomputable def exactModulusOfConvexity (f : H → Set.Ioi (⊥ : EReal)) : NNReal → EReal :=
  fun t ↦ sInf
    {δ : EReal |
      ∃ x ∈ effectiveDomain f, ∃ y ∈ effectiveDomain f,
        ‖x - y‖₊ = t ∧
        ∃ α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 ∧
          δ = jensenGap f α x y / (α * (1 - α) : ℝ)}

/-- The exact modulus of convexity is bounded above by every normalized Jensen gap realized at the
given radius. -/
-- Proof sketch: unfold `exactModulusOfConvexity` and apply `sInf_le` to the witness
-- corresponding to the chosen points `x`, `y`, and coefficient `α`.
theorem exactModulusOfConvexity_le_normalizedGap
    (f : H → Set.Ioi (⊥ : EReal)) {t : NNReal} {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (ht : ‖x - y‖₊ = t)
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    exactModulusOfConvexity f t ≤
      jensenGap f α x y / (α * (1 - α) : ℝ) := by
  -- Realize the target normalized gap as one witness in the defining infimum set.
  refine sInf_le ?_
  exact ⟨x, hx, y, hy, ht, α, hα, rfl⟩

/-- Helper for Definition 10.11: convexity on the effective domain makes every Jensen gap
nonnegative. -/
private theorem jensenGap_nonneg_of_convexOn
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ jensenGap f α x y := by
  rcases Set.mem_Ioo.mp hα with ⟨hα0, hα1⟩
  have hcombo_ne_bot : (f (α • x + (1 - α) • y) : EReal) ≠ ⊥ :=
    ne_of_gt (f _).2
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hα_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα0.le
  have h1α0 : 0 < 1 - α := by
    linarith
  have h1α_nonneg : 0 ≤ (1 - α : EReal) := by
    exact_mod_cast h1α0.le
  have hα_mul_ne_top : (α : EReal) * (f x : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot α), Or.inl hα_nonneg, Or.inl (EReal.coe_ne_top α),
      Or.inr hfx_top⟩
  have h1α_mul_ne_top : (1 - α : EReal) * (f y : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 - α)), Or.inl h1α_nonneg,
      Or.inl (EReal.coe_ne_top (1 - α)), Or.inr hfy_top⟩
  have hsum_ne_top :
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) ≠ ⊤ :=
    EReal.add_ne_top hα_mul_ne_top h1α_mul_ne_top
  -- Rewrite the convex Jensen inequality into the gap form used in the infimum.
  rw [jensenGap, EReal.sub_nonneg (Or.inl hsum_ne_top) (Or.inr hcombo_ne_bot)]
  exact hconv.ineq hx hy hα0 hα1

/-- Helper for Definition 10.11: dividing a nonnegative Jensen gap by the positive normalization
factor keeps it nonnegative. -/
private theorem normalizedJensenGap_nonneg_of_convexOn
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ jensenGap f α x y / (α * (1 - α) : ℝ) := by
  rcases Set.mem_Ioo.mp hα with ⟨hα0, hα1⟩
  have hjensen_nonneg : 0 ≤ jensenGap f α x y :=
    jensenGap_nonneg_of_convexOn f hconv hx hy hα
  have hdenom_nonneg : 0 ≤ (α * (1 - α) : ℝ) := by
    nlinarith
  have hdenom_nonneg' : (0 : EReal) ≤ (((α * (1 - α) : ℝ) : EReal)) := by
    exact_mod_cast hdenom_nonneg
  -- Transport the nonnegativity statement through division by the positive real factor.
  exact EReal.div_nonneg hjensen_nonneg hdenom_nonneg'

/-- For a proper convex `]-∞,+∞]`-valued function, the exact modulus of convexity is nonnegative.
-/
theorem exactModulusOfConvexity_nonneg
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) (t : NNReal) :
    0 ≤ exactModulusOfConvexity f t := by
  -- Show that every witness in the defining set of normalized gaps is nonnegative.
  refine le_sInf ?_
  intro δ hδ
  rcases hδ with ⟨x, hx, y, hy, _ht, α, hα, rfl⟩
  -- Reduce the infimum claim to the normalized Jensen-gap lower bound for this witness.
  exact normalizedJensenGap_nonneg_of_convexOn f hconv hx hy hα

end ERealFunction
