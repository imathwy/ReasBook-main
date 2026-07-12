import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.Limits

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/- Source/core/bridge triage for Lemma 12.3.2:
- source-facing: the textbook equivalences between initiality, terminality, vanishing identity, and
  factorization through a zero object
- core/canonical owner: `IsZero`
- bridge/view: the TFAE packaging in part (1) and the factorization criterion in part (2) -/

/- Lemma 12.3.2 (1), canonical owner theorem: in a category with zero morphisms, an object is zero
if and only if its identity endomorphism is zero. -/
recall IsZero.iff_id_eq_zero

/-- Lemma 12.3.2 (1): in a category with zero morphisms, an object is initial, terminal, and has
zero identity endomorphism in equivalent ways. -/
lemma isInitial_isTerminal_id_eq_zero_tfae (x : C) :
    ([Nonempty (IsInitial x),
      Nonempty (IsTerminal x),
      𝟙 x = 0] : List Prop).TFAE := by
  have hzero : IsZero x ↔ 𝟙 x = 0 := IsZero.iff_id_eq_zero x
  tfae_have 1 ↔ 3 := by
    constructor
    · rintro ⟨h⟩
      exact hzero.1 h.isZero
    · intro hx
      exact ⟨(hzero.2 hx).isInitial⟩
  tfae_have 2 ↔ 3 := by
    constructor
    · rintro ⟨h⟩
      exact hzero.1 h.isZero
    · intro hx
      exact ⟨(hzero.2 hx).isTerminal⟩
  tfae_finish

-- Proof sketch: if `α = β ≫ γ` factors through a zero object `x`, then `β = 0` and `γ = 0` by
-- the owner lemmas `IsZero.eq_zero_of_tgt` and `IsZero.eq_zero_of_src`. Conversely, the zero
-- morphism factors through any object, hence in particular through `x`.
/-- Lemma 12.3.2 (2): a morphism factors through a zero object if and only if it is the zero
morphism. -/
lemma factor_thru_isZero_iff_eq_zero {x y z : C} (hx : IsZero x) (α : y ⟶ z) :
    (∃ β : y ⟶ x, ∃ γ : x ⟶ z, α = β ≫ γ) ↔ α = 0 := by
  constructor
  · rintro ⟨β, γ, rfl⟩
    simp [hx.eq_zero_of_tgt β, hx.eq_zero_of_src γ]
  · rintro rfl
    exact ⟨hx.from_ y, hx.to_ z, by simp [hx.eq_zero_of_tgt (hx.from_ y)]⟩

end

end CategoryTheory.Limits
