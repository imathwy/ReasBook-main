import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap04.Definition_4_27_4

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory
namespace MorphismProperty

open LeftFraction
open LeftFraction.Localization
open scoped CategoryTheory.MorphismProperty.LeftFractionNotation

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
variable {X Y Y' : C}

local notation "Q" => LeftFraction.Localization.Q

/-
Domain-style sampling for Lemma 4.27.6:
- primary domain: left-fraction localizations and equality criteria for roofs with fixed
  denominator;
- inspected owner declarations:
  `LeftFraction.Localization.homMk_eq_iff_leftFractionRel`,
  `LeftFraction.Localization.Q_map_comp_Qinv`,
  `MorphismProperty.LeftFractionRel`,
  `MorphismProperty.map_eq_iff_postcomp`;
- best owner abstraction: the localization functor `Q W`, with the represented morphism `s⁻¹ f`
  viewed through the owner morphism `homMk (mk f s hs)` and the canonical comparison
  `Q_map_comp_Qinv`;
- primitive data: numerators `f`, `g` and a common denominator `s` with `W s`;
- derived API: the fixed-denominator equality criterion below, together with the canonical
  postcomposition criterion extracted by `map_eq_iff_postcomp`.

Source/core/bridge triage:
- `source-facing`: `left_fraction_hom_eq_iff_exists_postcomp`;
- `core/canonical`: the owner-level localization API above;
- `bridge/view`: the relation witness for the fixed-denominator fractions
  `mk f s hs` and `mk g s hs`, used to discharge condition `(3)` of the TFAE statement. -/

/-- A morphism of `W` with source `Y'` that equalizes the numerators `f` and `g` by
postcomposition. -/
def left_fraction_has_postcomp_eq
    (f g : X ⟶ Y') :
    Prop :=
  ∃ (Y'' : C) (t : Y' ⟶ Y''), W t ∧ f ≫ t = g ≫ t

/-- A postcomposition equalizer for `f` and `g` whose composite with the denominator `s`
lies in `W`. -/
def left_fraction_has_postcomp_comp_eq
    (f g : X ⟶ Y') (s : Y ⟶ Y') :
    Prop :=
  ∃ (Y'' : C) (a : Y' ⟶ Y''), f ≫ a = g ≫ a ∧ W (s ≫ a)

/-- Equality of left fractions with fixed denominator is equivalent to postcomposition
equalization in `W`. -/
-- Proof sketch: rewrite `s⁻¹ f = s⁻¹ g` using `Q_map_comp_Qinv`, then apply the canonical
-- localization criterion `map_eq_iff_postcomp`.
theorem left_fraction_hom_eq_iff_has_postcomp_eq
    (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    s⁻¹ f = s⁻¹ g ↔ left_fraction_has_postcomp_eq W f g := sorry

/-- Lemma 4.27.6: for two left fractions with common denominator `s`, the following are
equivalent:

1. the induced morphisms in the localization are equal;
2. the numerators become equal after postcomposition with a morphism of `W`;
3. the numerators become equal after postcomposition with a morphism whose composite with `s`
   lies in `W`. -/
-- Proof sketch: use `left_fraction_hom_eq_iff_has_postcomp_eq` for `(1) ↔ (2)`, and compare
-- clauses `(2)` and `(3)` by composing with `s` and by invoking the fixed-denominator relation
-- criterion `homMk_eq_iff_leftFractionRel`.
theorem left_fraction_hom_tfae
    (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    [ s⁻¹ f = s⁻¹ g,
      left_fraction_has_postcomp_eq W f g,
      left_fraction_has_postcomp_comp_eq W f g s ].TFAE := sorry

end MorphismProperty
end CategoryTheory
