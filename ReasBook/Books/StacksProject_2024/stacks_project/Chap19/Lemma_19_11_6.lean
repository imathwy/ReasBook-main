import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits ZeroObject
open CategoryTheory.IsGrothendieckAbelian
open CategoryTheory.MorphismProperty

universe w v u

namespace CategoryTheory

/-
Domain-style sampling for Lemma 19.11.6:
- primary domain: injective objects in Grothendieck abelian categories, organized through right
  lifting properties against the canonical family of generating monomorphisms attached to a
  separator;
- sampled owner declarations:
  `injective_iff_rlp_monomorphisms_zero`,
  `generatingMonomorphisms`,
  `generatingMonomorphisms_rlp`,
  `IsSeparator`;
- best owner abstraction: the core owner is the RLP predicate
  `(generatingMonomorphisms U).rlp (0 : I ⟶ 0)`, while the Stacks-project formulation is the
  source-facing extension property along the subobject arrows `M.arrow`;
- primitive data: for the bridge theorem, a category with zero morphisms and zero object together
  with the objects `U` and `I`; for the final injectivity criterion, the ambient Grothendieck
  abelian category with separator `U`;
- derived API: the bridge identifying the explicit extension property with the canonical RLP
  predicate, and the source-facing injectivity criterion below.

Source/core/bridge triage:
- `source-facing`: the extension property for every morphism `(M : C) ⟶ I` from a subobject
  `M ⊆ U`;
- `core/canonical`: `Injective I`, `generatingMonomorphisms U`, and the owner theorem
  `generatingMonomorphisms_rlp`;
- `bridge/view`: `subobject_extension_iff_rlp_generatingMonomorphisms_zero`, which converts the
  explicit extension condition to the canonical lifting-property owner.
-/

/-- The explicit extension property along the inclusions of subobjects of `U` is exactly the
canonical right lifting property against `generatingMonomorphisms U` for the zero map `I ⟶ 0`. -/
theorem subobject_extension_iff_rlp_generatingMonomorphisms_zero
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C] {U I : C} :
    (∀ (M : Subobject U) (φ : (M : C) ⟶ I), ∃ ψ : U ⟶ I, M.arrow ≫ ψ = φ) ↔
      (generatingMonomorphisms U).rlp (0 : I ⟶ 0) := by
  constructor
  · intro h A B g hg
    rcases hg with ⟨M⟩
    refine ⟨fun {f b} _ ↦ ?_⟩
    rcases h M f with ⟨l, hl⟩
    exact ⟨⟨{ l := l, fac_left := hl, fac_right := (isZero_zero C).eq_of_tgt _ _ }⟩⟩
  · intro h M φ
    let _ : HasLiftingProperty M.arrow (0 : I ⟶ 0) := h _ ⟨M⟩
    let sq : CommSq φ M.arrow (0 : I ⟶ 0) 0 := ⟨by simp⟩
    exact ⟨sq.lift, sq.fac_left⟩

/-- Lemma 19.11.6: in a Grothendieck abelian category with generator `U`, an object `I` is
injective exactly when every morphism from a subobject `M ⊆ U` to `I` extends along the inclusion
`M.arrow : M ⟶ U`. -/
-- Proof sketch: first identify the explicit extension condition with the canonical statement that
-- `0 : I ⟶ 0` has the right lifting property with respect to `generatingMonomorphisms U`. Then use
-- `generatingMonomorphisms_rlp hU` to replace those generating monomorphisms by all monomorphisms,
-- and conclude by `injective_iff_rlp_monomorphisms_zero`.
theorem injective_iff_generator_subobject_extension
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {U I : C} (hU : IsSeparator U) :
    Injective I ↔
      ∀ (M : Subobject U) (φ : (M : C) ⟶ I), ∃ ψ : U ⟶ I, M.arrow ≫ ψ = φ := by
  rw [injective_iff_rlp_monomorphisms_zero,
    ← generatingMonomorphisms_rlp hU,
    ← subobject_extension_iff_rlp_generatingMonomorphisms_zero]

end CategoryTheory
