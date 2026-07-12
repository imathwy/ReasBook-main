import Mathlib
import StacksProject_2024.Chap13.Definition_13_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)

/- Domain-style sampling:
- primary domain: morphisms into bounded-below injective cochain complexes in the homotopy and
  derived categories;
- sampled owner declarations:
  `CochainComplex.InjectivePlus`,
  `PlusWithTermsIn.instIsKInjective`,
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `CochainComplex.isKInjective_of_injective`;
- best owner abstraction: `CochainComplex.InjectivePlus`, the chapter owner for bounded-below
  cochain complexes with injective terms; K-injectivity and the `Qh.map` bijection are derived API
  from that owner;
- primitive data: the source complex `L` and the bounded-below injective target `I :
  InjectivePlus 𝒜`;
- derived API: the canonical `IsKInjective` instance on `I` and the induced bijection on morphisms
  from `L` in the homotopy category to the derived category.

Source/core/bridge triage:
- `source-facing`: the textbook statement for bounded-below injective targets;
- `core/canonical`: `CochainComplex.IsKInjective.Qh_map_bijective`;
- `bridge/view`: `PlusWithTermsIn.instIsKInjective`, which upgrades the bounded-below injective owner
  to the canonical K-injective owner.
-/

-- Proof sketch: the chapter owner `InjectivePlus 𝒜` carries the canonical `IsKInjective`
-- instance from Definition `13.18.1`, so the statement is exactly
-- `CochainComplex.IsKInjective.Qh_map_bijective` specialized to the homotopy-category image of
-- `L` and the owner object `I`.
/-- Lemma 13.18.8: if `I^•` is a bounded-below cochain complex of injective objects in an abelian
category `𝒜`, then for every cochain complex `L^•` the canonical map from morphisms
`L^• ⟶ I^•` in the homotopy category `K(𝒜)` to morphisms `L^• ⟶ I^•` in the derived category
`D(𝒜)` is bijective. -/
@[stacks 05TG]
theorem homotopyCategory_to_derived_bijective_of_boundedBelow_injective
    (L : CochainComplex 𝒜 ℤ) (I : InjectivePlus 𝒜) :
    Function.Bijective
      (DerivedCategory.Qh.map :
        ((KQ).obj L ⟶ (KQ).obj I) → _) := by
  simpa using IsKInjective.Qh_map_bijective ((KQ).obj L) I

end CochainComplex
