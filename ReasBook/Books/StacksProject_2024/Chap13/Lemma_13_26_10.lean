import Mathlib
import StacksProject_2024.Chap13.Definition_13_13_2
import StacksProject_2024.Chap13.Lemma_13_26_3

open CategoryTheory
open CochainComplex
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "QhFilt" => HomotopyCategory.quotient FilF (ComplexShape.up ℤ)
local notation "ιFiltInjPlus" =>
  CochainComplex.PlusWithTermsIn.ι (IsFilteredInjective : ObjectProperty FilF)
local notation "FAcOrth" => ObjectProperty.rightOrthogonal (FAc(𝒜))

variable {K : CochainComplex FilF ℤ}

/- Domain-style sampling for Lemma `13.26.10`.
- primary domain: filtered acyclic objects in the homotopy category `K(Fil^f(𝒜))`, bounded-below
  filtered-injective complexes, and right orthogonality against `FAc(𝒜)`;
- sampled owner declarations:
  `FAc(𝒜)`,
  `ObjectProperty.rightOrthogonal`,
  `HomotopyCategory.quotient_map_eq_zero_iff`,
  `CochainComplex.FilteredInjectivePlus`,
  `IsFilteredInjective`;
- best owner abstraction: the canonical owner is the right orthogonal
  `FAcOrth` in the filtered homotopy category, with the bounded-below filtered-injective target
  owned by the chapter abbreviation `CochainComplex.FilteredInjectivePlus 𝒜`;
- primitive data: a bounded-below filtered-injective complex
  `I : CochainComplex.FilteredInjectivePlus 𝒜`;
- derived API: membership of `((ιFiltInjPlus ⋙ QhFilt).obj I)` in `FAcOrth`, and the
  source-facing homotopy-to-zero statement obtained by
  `HomotopyCategory.quotient_map_eq_zero_iff`.

Source/core/bridge triage:
- `source-facing`: the textbook null-homotopy statement below;
- `core/canonical`: `ObjectProperty.rightOrthogonal` applied to `FAc(𝒜)`;
- `bridge/view`: `HomotopyCategory.quotient_map_eq_zero_iff`, which translates vanishing in the
  homotopy category into existence of a homotopy to zero.

This file therefore keeps the textbook statement as a thin bridge, while exposing the owner-level
orthogonality theorem directly on the filtered homotopy category. -/
namespace CochainComplex.FilteredInjectivePlus

-- Proof sketch: pass to the homotopy category of `Fil^f(𝒜)` and argue degreewise on associated
-- graded pieces as in the ordinary injective case. Filtered acyclicity kills the source, while
-- bounded-belowness and termwise filtered injectivity place the target in the right orthogonal of
-- `FAc(𝒜)`.
/-- A bounded-below complex of filtered injectives lies in the right orthogonal of the filtered
acyclic subcategory of `K(Fil^f(𝒜))`. -/
theorem rightOrthogonal (I : CochainComplex.FilteredInjectivePlus 𝒜) :
    FAcOrth ((ιFiltInjPlus ⋙ QhFilt).obj I) := by
  sorry

end CochainComplex.FilteredInjectivePlus

-- Proof sketch: apply the owner theorem
-- `CochainComplex.FilteredInjectivePlus.rightOrthogonal` in the filtered homotopy
-- category and translate the resulting vanishing statement back to a homotopy by
-- `HomotopyCategory.quotient_map_eq_zero_iff`.
/-- Lemma 13.26.10: if `K^•` is filtered acyclic and `I^•` is bounded below with filtered
injective terms, then every morphism `K^• ⟶ I^•` is homotopic to zero. -/
theorem homotopic_to_zero_of_filteredAcyclic_to_boundedBelow_termwiseFilteredInjective
    (I : CochainComplex.FilteredInjectivePlus 𝒜) (α : K ⟶ I)
    (hK : FAc(𝒜) ((QhFilt).obj K)) :
    Nonempty (Homotopy α 0) :=
  let hI : FAcOrth ((ιFiltInjPlus ⋙ QhFilt).obj I) := I.rightOrthogonal
  exact (HomotopyCategory.quotient_map_eq_zero_iff α).1 <|
    hI ((QhFilt).map α) hK

end CategoryTheory
