import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_4 (from Chap06) -/
section

variable {α : Type*} [AddGroup α] [LinearOrder α]

/- Definition 6.4 is `source-facing`: domain sampling against Chapter 6's generic scalar
`soft_thresholding` owner in `Definition_6_2`, its coordinatewise lift in `Definition_6_3`, and
mathlib's generic absolute-value API shows that the primitive data here is only an ordered additive
group with `0`, `|·|`, and singleton sets. The owner abstraction is therefore the thresholding map
itself at that generic ordered layer, while the three branch formulas remain derived API. -/

/-- Definition 6.4: the hard-thresholding operator with threshold `a` sends `s` to `{0}` when
`|s| < a`, to `{s}` when `a < |s|`, and to `{0, s}` on the threshold `|s| = a`. -/
def hard_thresholding (a : α) : α → Set α :=
  fun s ↦
    if |s| < a then
      {0}
    else if a < |s| then
      {s}
    else
      {0, s}

end

@[inherit_doc] notation "𝓗[" a "]" => hard_thresholding a

section

variable {α : Type*} [AddGroup α] [LinearOrder α]

-- Proof sketch: evaluating `𝓗[a]` at `s` is exactly the defining three-branch formula.
/-- Evaluating the hard-thresholding operator gives its defining three-branch set-valued formula. -/
@[simp] theorem hard_thresholding_apply (a s : α) :
    𝓗[a] s = if |s| < a then {0} else if a < |s| then {s} else {0, s} :=
  rfl

-- Proof sketch: Unfold `hard_thresholding` and simplify the outer `if` using `h`.
/-- Hard thresholding returns only `0` below the threshold. -/
theorem hard_thresholding_of_abs_lt {a s : α} (h : |s| < a) :
    𝓗[a] s = {0} := by
  simp [hard_thresholding, h]

-- Proof sketch: Unfold `hard_thresholding`, use that the first branch is false by `h`, and then
-- simplify the second `if`.
/-- Hard thresholding returns only `s` above the threshold. -/
theorem hard_thresholding_of_lt_abs {a s : α} (h : a < |s|) :
    𝓗[a] s = {s} := by
  simp [hard_thresholding, h, not_lt_of_gt h]

-- Proof sketch: Unfold `hard_thresholding` and use the equality `|s| = a` to rule out the strict
-- inequality branches.
/-- Hard thresholding returns both `0` and `s` exactly on the threshold. -/
theorem hard_thresholding_of_abs_eq {a s : α} (h : |s| = a) :
    𝓗[a] s = {0, s} := by
  simp [hard_thresholding, h]

end

/-! ### Theorem_6_4 (from Chap06) -/
universe u

section

variable {E : Type u}
variable [NormedAddCommGroup E] [ProperSpace E]

/- Theorem 6.4 is `source-facing` for the Chapter 6 proximal-operator existence theory. Domain
sampling shows that the relevant owner abstractions for this statement already live upstream:

- `IsCoerciveExtendedRealFunction` and `attains_min_on_closed_set_of_coercive` from Chapter 2,
- `proximal_objective` and the set-valued proximal map `prox[f]` from Definition 6.1.

Accordingly, this file should only state the existence theorem for `prox[f] x`; it should not
duplicate local owners for coercivity, minimizer existence, or proximal-set membership. -/

-- Proof sketch: the quadratic penalty `u ↦ (1 / 2) ‖u - x‖²` is continuous, hence closed after
-- coercing to `EReal`. Adding it to the closed function `f` yields a closed proximal objective.
omit [ProperSpace E] in
/-- If `f` is lower semicontinuous, then its proximal objective at `x` is lower semicontinuous. -/
theorem lowerSemicontinuous_proximal_objective
    {f : E → EReal} (hf_closed : LowerSemicontinuous f) (x : E) :
    LowerSemicontinuous (proximal_objective f x) := by
  have hpenalty_closed : LowerSemicontinuous
      (fun u : E ↦ ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal)) :=
    continuous_real_isClosed (by fun_prop)
  simpa only [proximal_objective_apply] using
    hf_closed.add' hpenalty_closed <| fun u ↦
      EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))

-- Proof sketch: fix `x`. The function `proximal_objective f x` is coercive by `hcoercive`, hence
-- proper. It is also lower semicontinuous because `f` is lower semicontinuous and the quadratic
-- penalty `u ↦ (1 / 2) ‖u - x‖²` is continuous. Apply
-- `attains_min_on_closed_set_of_coercive` to `proximal_objective f x` on `Set.univ`; the
-- resulting minimizer belongs to `prox[f] x` by definition.
/-- Theorem 6.4: if `f` is closed and the proximal objective at `x`,
`u ↦ f u + (1 / 2) * ‖u - x‖^2`, is coercive, then the proximal set `prox[f] x` is nonempty. The
ambient assumption `[ProperSpace E]` is the canonical abstraction capturing the finite-dimensional
Euclidean setting used in the text, and the textbook properness hypothesis on `f` is redundant
once this proximal objective is assumed coercive. -/
theorem prox_nonempty_of_closed_and_proximal_objective_coercive
    (f : E → EReal) (hf_closed : LowerSemicontinuous f) (x : E)
    (hcoercive : IsCoerciveExtendedRealFunction (proximal_objective f x)) :
    (prox[f] x).Nonempty := by
  rcases attains_min_on_closed_set_of_coercive (proximal_objective f x)
      (lowerSemicontinuous_proximal_objective hf_closed x) hcoercive isClosed_univ
      (by simpa using hcoercive.effective_domain_nonempty) with ⟨u, -, hu⟩
  refine ⟨u, ?_⟩
  simpa [mem_proximal_mapping_iff] using hu

end
