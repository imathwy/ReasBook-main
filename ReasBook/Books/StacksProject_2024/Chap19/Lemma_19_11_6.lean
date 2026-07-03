import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits ZeroObject
open CategoryTheory.MorphismProperty

universe w v u

namespace CategoryTheory

/-- Lemma 19.11.6: in a Grothendieck abelian category with generator `U`, an object `I` is
injective exactly when every morphism from a subobject `M ⊆ U` to `I` extends along the inclusion
`M.arrow : M ⟶ U`. -/
-- Proof sketch: interpret the stated extension property as saying that the zero map `I ⟶ 0` has
-- the right lifting property with respect to every generating monomorphism coming from a subobject
-- of `U`. Then use `generatingMonomorphisms_rlp hU` to identify these with all monomorphisms in a
-- Grothendieck abelian category, and conclude by `injective_iff_rlp_monomorphisms_zero`.
theorem injective_iff_generator_subobject_extension
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {U I : C} (hU : IsSeparator U) :
    Injective I ↔
      ∀ (M : Subobject U) (φ : (M : C) ⟶ I), ∃ ψ : U ⟶ I, M.arrow ≫ ψ = φ := by
  rw [injective_iff_rlp_monomorphisms_zero,
    ← IsGrothendieckAbelian.generatingMonomorphisms_rlp hU]
  constructor
  · intro h M φ
    let _ : HasLiftingProperty M.arrow (0 : I ⟶ 0) := h _ ⟨M⟩
    let sq : CommSq φ M.arrow (0 : I ⟶ 0) 0 := ⟨by simp⟩
    exact ⟨sq.lift, sq.fac_left⟩
  · intro h A B g hg
    rcases hg with ⟨M⟩
    refine ⟨fun {f b} _ ↦ ?_⟩
    rcases h M f with ⟨l, hl⟩
    exact ⟨⟨{ l := l, fac_left := hl, fac_right := (isZero_zero C).eq_of_tgt _ _ }⟩⟩

end CategoryTheory
