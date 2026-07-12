import Mathlib
import StacksProject_2024.Chap13.Definition_13_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)

/- Domain-style sampling:
- primary domain: morphisms from bounded-above projective cochain complexes in the homotopy and
  derived categories;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.MinusWithTermsIn.instIsKProjective`,
  `CochainComplex.IsKProjective.Qh_map_bijective`,
  `CochainComplex.isKProjective_of_projective`;
- best owner abstraction: `ProjectiveMinus 𝒜`, the chapter owner for bounded-above cochain
  complexes with projective terms; the bijection on morphisms is derived API coming from its
  canonical `IsKProjective` instance;
- primitive data: the bounded-above projective source
  `P : ProjectiveMinus 𝒜` and the target
  complex `L`;
- derived API: the canonical bijection induced by `DerivedCategory.Qh.map`.

Source/core/bridge triage:
- `source-facing`: the textbook bounded-above/projective comparison statement;
- `core/canonical`: `CochainComplex.IsKProjective.Qh_map_bijective`;
- `bridge/view`: `MinusWithTermsIn.instIsKProjective`, which upgrades the canonical owner to the
  canonical K-projective owner.
-/

-- Proof sketch: the canonical owner `MinusWithTermsIn (isProjective 𝒜)` already packages the
-- bounded-above and termwise-projective hypotheses and carries the canonical `IsKProjective`
-- instance from Definition `13.19.1`, so the statement is exactly
-- `CochainComplex.IsKProjective.Qh_map_bijective` specialized to the homotopy-category image of
-- `L`.
/-- Lemma 13.19.8: if `P^•` is a bounded-above cochain complex of projective objects in an abelian
category `𝒜`, then for every cochain complex `L^•` the canonical map from morphisms
`P^• ⟶ L^•` in the homotopy category `K(𝒜)` to morphisms `P^• ⟶ L^•` in the derived category
`D(𝒜)` is bijective. -/
@[stacks 064B]
theorem homotopyCategory_to_derived_bijective_of_boundedAbove_projective
    (P : ProjectiveMinus 𝒜) (L : CochainComplex 𝒜 ℤ) :
    Function.Bijective
      (DerivedCategory.Qh.map : ((KQ).obj P ⟶ (KQ).obj L) → _) := by
  simpa using IsKProjective.Qh_map_bijective (P : CochainComplex 𝒜 ℤ) ((KQ).obj L)

end CochainComplex
