import Mathlib
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H]
variable (f g : H → Set.Ioi (⊥ : EReal))

/-- Helper for Proposition 12 8: an exact minimizing decomposition rules out the value `-∞` for
the infimal convolution. -/
private lemma infimalConvolution_ne_bot_of_exactAt {x : H}
    (hExactAt : infimalConvolution.ExactAt f g x) :
    (f □ g) x ≠ ⊥ := by
  rcases hExactAt with ⟨y, hy⟩
  have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hgz_bot : (g (x - y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (g (x - y) : EReal) from (g (x - y)).2)
  -- Rewrite the exact value as a sum of two strictly-below-top summands.
  rw [hy]
  exact (EReal.add_ne_bot_iff).2 ⟨hfy_bot, hgz_bot⟩

omit [AddCommGroup H] in
/-- Helper for Proposition 12 8: a real-height epigraph point lies over a domain point. -/
private lemma mem_dom_of_mem_epigraph {h : H → EReal} {x : H} {ξ : ℝ}
    (hxξ : (x, ξ) ∈ epigraph h) :
    x ∈ dom h := by
  -- The epigraph inequality bounds `h x` above by the finite real height `ξ`.
  rw [mem_dom_iff]
  exact lt_of_le_of_lt ((mem_epigraph_iff h x ξ).mp hxξ) (EReal.coe_lt_top ξ)

/-- Helper for Proposition 12 8: an exact decomposition below a real height has finite-above
summands. -/
private lemma exactSummands_lt_top_of_le_real {x y : H} {ξ : ℝ}
    (hEq : (f □ g) x = (f y : EReal) + (g (x - y) : EReal))
    (hLe : (f □ g) x ≤ (ξ : EReal)) :
    (f y : EReal) < ⊤ ∧ (g (x - y) : EReal) < ⊤ := by
  have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hgz_bot : (g (x - y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (g (x - y) : EReal) from (g (x - y)).2)
  have hsum_le : (f y : EReal) + (g (x - y) : EReal) ≤ (ξ : EReal) := by
    simpa [hEq] using hLe
  have hfy_top : (f y : EReal) ≠ ⊤ := by
    intro hfy_top
    have : (⊤ : EReal) ≤ (ξ : EReal) := by
      rw [hfy_top, EReal.top_add_of_ne_bot hgz_bot] at hsum_le
      exact hsum_le
    exact (not_le_of_gt (EReal.coe_lt_top ξ)) this
  have hgz_top : (g (x - y) : EReal) ≠ ⊤ := by
    intro hgz_top
    have : (⊤ : EReal) ≤ (ξ : EReal) := by
      rw [hgz_top, EReal.add_top_of_ne_bot hfy_bot] at hsum_le
      exact hsum_le
    exact (not_le_of_gt (EReal.coe_lt_top ξ)) this
  exact ⟨lt_of_le_of_ne le_top hfy_top, lt_of_le_of_ne le_top hgz_top⟩

/-- Helper for Proposition 12 8: an exact minimizing decomposition turns a point of
`epigraph (f □ g)` into a point of `epigraph f.asEReal + epigraph g.asEReal`. -/
private lemma mem_add_epigraph_of_mem_epigraph_infimalConvolution_of_exactAt
    {x : H} {ξ : ℝ} (hExactAt : infimalConvolution.ExactAt f g x)
    (hxξ : (x, ξ) ∈ epigraph (f □ g)) :
    (x, ξ) ∈ epigraph f.asEReal + epigraph g.asEReal := by
  rcases hExactAt with ⟨y, hyExact⟩
  have hvalue_le : (f y : EReal) + (g (x - y) : EReal) ≤ (ξ : EReal) := by
    simpa [hyExact] using (mem_epigraph_iff (f □ g) x ξ).mp hxξ
  have hfinite := exactSummands_lt_top_of_le_real (f := f) (g := g) hyExact
    ((mem_epigraph_iff (f □ g) x ξ).mp hxξ)
  have hfy_top : (f y : EReal) ≠ ⊤ := (ne_of_lt hfinite.1)
  have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hgz_top : (g (x - y) : EReal) ≠ ⊤ := (ne_of_lt hfinite.2)
  have hgz_bot : (g (x - y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (g (x - y) : EReal) from (g (x - y)).2)
  have hy_mem :
      (y, (f y : EReal).toReal) ∈ epigraph f.asEReal := by
    -- The first summand uses the canonical real representative of the finite value `f y`.
    rw [mem_epigraph_iff]
    simp [Function.asEReal, EReal.coe_toReal hfy_top hfy_bot]
  have hsum_real :
      (f y : EReal).toReal + (g (x - y) : EReal).toReal ≤ ξ := by
    have hsum_top :
        ((f y : EReal) + (g (x - y) : EReal)) ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt hvalue_le (EReal.coe_lt_top ξ))
    have hsum_bot :
        ((f y : EReal) + (g (x - y) : EReal)) ≠ ⊥ := by
      exact (EReal.add_ne_bot_iff).2 ⟨hfy_bot, hgz_bot⟩
    have hcast :
        ((((f y : EReal) + (g (x - y) : EReal)).toReal : ℝ) : EReal) ≤ (ξ : EReal) := by
      simpa [EReal.coe_toReal hsum_top hsum_bot] using hvalue_le
    have hreal : (((f y : EReal) + (g (x - y) : EReal)).toReal : ℝ) ≤ ξ := by
      exact_mod_cast hcast
    simpa [EReal.toReal_add hfy_top hfy_bot hgz_top hgz_bot] using hreal
  have hgz_real :
      (g (x - y) : EReal).toReal ≤ ξ - (f y : EReal).toReal := by
    linarith
  have hresidual_mem :
      (x - y, ξ - (f y : EReal).toReal) ∈ epigraph g.asEReal := by
    -- Convert the exact decomposition to real heights after ruling out the `⊤` branches.
    rw [mem_epigraph_iff]
    have hcast :
        ((((g (x - y) : EReal).toReal : ℝ) : EReal)) ≤
          ((ξ - (f y : EReal).toReal : ℝ) : EReal) := by
      exact_mod_cast hgz_real
    simpa [Function.asEReal, EReal.coe_toReal hgz_top hgz_bot] using hcast
  -- Assemble the original epigraph point from the exact minimizing decomposition.
  refine Set.mem_add.2 ⟨(y, (f y : EReal).toReal), hy_mem,
    (x - y, ξ - (f y : EReal).toReal), hresidual_mem, ?_⟩
  ext <;> simp [sub_eq_add_neg, add_left_comm]

-- Proof sketch: unpack membership in the pointwise sum of the two epigraphs, rewrite each
-- epigraph condition with `mem_epigraph_iff`, and compare the defining infimum of `f □ g` with the
-- single decomposition coming from the chosen summands.
/-- Part (i) of Proposition 12.8: the pointwise sum of the real-height epigraphs of `f` and `g` is
contained in the real-height epigraph of their infimal convolution. -/
theorem add_epigraph_subset_epigraph_infimalConvolution :
    epigraph f.asEReal + epigraph g.asEReal ⊆
      epigraph (f □ g) := by
  intro p hp
  rcases Set.mem_add.mp hp with ⟨p₁, hp₁, p₂, hp₂, rfl⟩
  rcases p₁ with ⟨x, ξ⟩
  rcases p₂ with ⟨y, η⟩
  have hfx : (f x : EReal) ≤ (ξ : EReal) := (mem_epigraph_iff f.asEReal x ξ).mp hp₁
  have hgy : (g y : EReal) ≤ (η : EReal) := (mem_epigraph_iff g.asEReal y η).mp hp₂
  -- Use the chosen decomposition point `x` in the defining infimum for `(f □ g) (x + y)`.
  rw [mem_epigraph_iff, infimalConvolution_apply]
  refine le_trans (iInf_le (fun z : H ↦ (f z : EReal) + (g (x + y - z) : EReal)) x) ?_
  simpa [EReal.coe_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using add_le_add hfx hgy

-- Proof sketch: one inclusion is Proposition 12.8 (1). For the reverse inclusion, take a point
-- of `epigraph (f □ g)`, use exactness to choose a minimizing decomposition `x = y + (x - y)`,
-- and place the two resulting summands in the epigraphs of `f` and `g`.
/-- Proposition 12.8 (2): if the infimal convolution is exact, then its real-height epigraph is
exactly the pointwise sum of the real-height epigraphs of `f` and `g`. -/
theorem epigraph_infimalConvolution_eq_add_epigraph_of_exact
    (hExact : infimalConvolution.Exact f g) :
    epigraph (f □ g) =
      epigraph f.asEReal + epigraph g.asEReal := by
  ext p
  constructor
  · rintro hp
    rcases p with ⟨x, ξ⟩
    have hx_dom : x ∈ dom (f □ g) := mem_dom_of_mem_epigraph hp
    -- Exactness supplies the minimizing decomposition used to build the two epigraph summands.
    exact mem_add_epigraph_of_mem_epigraph_infimalConvolution_of_exactAt
      (f := f) (g := g) (hExact hx_dom) hp
  · intro hp
    exact add_epigraph_subset_epigraph_infimalConvolution (f := f) (g := g) hp

end ERealFunction
