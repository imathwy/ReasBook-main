import Mathlib
import stacks_project.Chap04.Definition_4_27_20

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]
variable (S : MorphismProperty C) [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]

/- Domain-style sampling for Lemma 4.27.21:
- source-facing content: the Stacks description of the saturated closure
  `S' = { f | ∃ g h, S (f ≫ g) ∧ S (h ≫ f) }`
- core/canonical owner abstraction: the localization functor `S.Q` and the induced morphism
  property `S.saturatedClosure` of morphisms inverted by `S.Q`
- upstream owner facts inspected before refining:
  `MorphismProperty.Q_inverts`,
  `MorphismProperty.IsInvertedBy.iff_le_inverseImage_isomorphisms`,
  `Functor.q_isLocalization`,
  `Adjunction.isLocalization`

Primitive data: the two calculus-of-fractions owner instances on `S`.
Derived API: the owner `S.saturatedClosure`, its saturation, and the comparison with the textbook
source-facing description. In particular, the inclusion `S ≤ S.saturatedClosure` is already the
canonical owner fact `S.Q_inverts`, so no parallel inclusion wrapper is kept.

Source/core/bridge triage:
- `source-facing`: the textbook characterization of `S.saturatedClosure`
- `core/canonical`: the owner `S.saturatedClosure`
- `bridge/view`: the minimality theorem `saturatedClosure_le_iff`
-/

/-- The saturated closure of `S`, i.e. the morphisms inverted by the canonical localization
functor `S.Q`. -/
abbrev saturatedClosure : MorphismProperty C :=
  (isomorphisms S.Localization).inverseImage S.Q

/-- Lemma 4.27.21: for a multiplicative system `S`, the morphisms whose image under the canonical
localization functor `S.Q : C ⥤ S.Localization` is an isomorphism are exactly the textbook set
`S'` of morphisms `f` for which there exist arrows `g` and `h` with `f ≫ g ∈ S` and
`h ≫ f ∈ S`. -/
theorem saturatedClosure_eq :
    S.saturatedClosure =
      fun X Y f ↦
        ∃ (Z₁ Z₂ : C) (g : Y ⟶ Z₁) (h : Z₂ ⟶ X), S (f ≫ g) ∧ S (h ≫ f) := sorry

/-- The morphisms inverted by `S.Q` form a saturated multiplicative system. -/
instance saturatedClosure_isSaturatedMultiplicativeSystem :
    IsSaturatedMultiplicativeSystem S.saturatedClosure := by
  sorry

/- The owner `S.saturatedClosure` is the smallest saturated multiplicative system containing `S`.
-/
theorem saturatedClosure_le_iff
    {T : MorphismProperty C} [IsSaturatedMultiplicativeSystem T] :
    S.saturatedClosure ≤ T ↔ S ≤ T := by
  constructor
  · intro h
    exact
      ((IsInvertedBy.iff_le_inverseImage_isomorphisms S S.Q).1 S.Q_inverts).trans h
  · intro hST
    rw [saturatedClosure_eq S]
    intro X Y f hf
    rcases hf with ⟨Z₁, Z₂, g, h, hfg, hhf⟩
    exact IsSaturatedMultiplicativeSystem.saturation h f g (hST _ hhf) (hST _ hfg)

/- The owner `S.saturatedClosure` lies in every saturated multiplicative system containing `S`. -/
theorem saturatedClosure_le
    {T : MorphismProperty C} [IsSaturatedMultiplicativeSystem T] (hST : S ≤ T) :
    S.saturatedClosure ≤ T :=
  (saturatedClosure_le_iff S).2 hST

end MorphismProperty
end CategoryTheory
