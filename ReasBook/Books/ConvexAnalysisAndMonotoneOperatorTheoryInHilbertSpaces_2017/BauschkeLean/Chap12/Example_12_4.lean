import Mathlib
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped translate

universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H]

/-- Helper for Example 12 4: away from the singleton center, the indicator term in the
infimal-convolution formula is `⊤`. -/
lemma singleton_indicator_term_eq_top_of_ne
    {f : H → Set.Ioi (⊥ : EReal)} {x y z : H} (hz : z ≠ y) :
    ((ι[{y}] z : EReal) + f.asEReal (x - z)) = ⊤ := by
  -- Outside the singleton, the indicator contributes `⊤`, so the whole summand is `⊤`.
  have hterm_ne_bot : f.asEReal (x - z) ≠ ⊥ := by
    have hlt : (⊥ : EReal) < f.asEReal (x - z) := by
      exact (f (x - z)).2
    intro hbot
    rw [hbot] at hlt
    exact lt_irrefl _ hlt
  calc
    ((ι[{y}] z : EReal) + f.asEReal (x - z))
        = (⊤ : EReal) + f.asEReal (x - z) := by
            simp [indicator_apply, Set.mem_singleton_iff, hz]
    _ = ⊤ := EReal.top_add_of_ne_bot hterm_ne_bot

/-- Helper for Example 12 4: the defining infimum for `ι[{y}] □ f` is attained at the singleton
point `y`. -/
lemma singleton_indicator_iInf_eq_asEReal_sub
    (f : H → Set.Ioi (⊥ : EReal)) (x y : H) :
    (⨅ z : H, (ι[{y}] z : EReal) + f.asEReal (x - z)) = f.asEReal (x - y) := by
  refine le_antisymm ?_ ?_
  · -- The singleton point `y` is an admissible witness for the infimum.
    have hy :
        (⨅ z : H, (ι[{y}] z : EReal) + f.asEReal (x - z)) ≤
          (ι[{y}] y : EReal) + f.asEReal (x - y) :=
      iInf_le (fun z : H ↦ (ι[{y}] z : EReal) + f.asEReal (x - z)) y
    simpa [Function.asEReal_apply, indicator_apply] using hy
  · -- Every other summand is `⊤`, so `f (x - y)` is below each term of the infimum family.
    refine le_iInf ?_
    intro z
    by_cases hz : z = y
    · subst hz
      simp [Function.asEReal_apply, indicator_apply]
    · rw [singleton_indicator_term_eq_top_of_ne hz]
      exact le_top

-- Proof sketch: unfold the defining infimum for `ι[{y}] □ f`. The singleton indicator is `0`
-- exactly at `y` and `⊤` elsewhere, so the only finite contribution comes from the decomposition
-- using `y`, yielding the translate of the canonical `EReal` view `f.asEReal`.
/-- Example 12 4: the infimal convolution of the singleton indicator at `y` with `f` is the
translate of `f` by `y`. -/
theorem indicator_singleton_infimalConvolution_eq_translate
    (f : H → Set.Ioi (⊥ : EReal)) (y : H) :
    ι[{y}] □ f = τ y f.asEReal := by
  ext x
  -- Rewrite both sides pointwise and collapse the defining infimum to the singleton term.
  rw [infimalConvolution_apply, translate_apply]
  exact singleton_indicator_iInf_eq_asEReal_sub f x y

end ERealFunction
