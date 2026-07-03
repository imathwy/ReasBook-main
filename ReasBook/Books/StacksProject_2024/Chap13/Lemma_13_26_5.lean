import Mathlib
import StacksProject_2024.Chap13.Lemma_13_26_3

open CategoryTheory
open CategoryTheory.Limits
open FilteredObject.Hom
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]

section FilteredInjectives

/-- The strictly full subcategory `𝓘^f ⊂ Fil^f(𝒜)` of filtered injective objects. -/
abbrev filteredInjectiveSubcategory (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  ObjectProperty.FullSubcategory (IsFilteredInjective : ObjectProperty (Fil^f(𝒜)))

/- The Stacks Project writes the full subcategory of filtered injective finite filtered objects as
`𝓘^f(𝒜)`. This is notation for the chapter owner `filteredInjectiveSubcategory 𝒜`. -/
scoped notation "𝓘^f(" C:arg ")" => filteredInjectiveSubcategory C

instance (I : 𝓘^f(𝒜)) : IsFilteredInjective I.obj :=
  I.property

/-- The inclusion `𝓘^f(𝒜) ⥤ Fil^f(𝒜)` forgetting that an object is filtered injective. -/
abbrev filteredInjectiveInclusion (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    𝓘^f(𝒜) ⥤ Fil^f(𝒜) :=
  ObjectProperty.ι (IsFilteredInjective : ObjectProperty (Fil^f(𝒜)))

end FilteredInjectives

/- Domain-style sampling for Lemma `13.26.5`.
- primary domain: finite filtered objects, strict monomorphisms, and filtered-injective targets in
  an abelian category with enough injectives;
- sampled owner declarations:
  `FilteredObject.Hom.Strict`,
  `IsFilteredInjective`,
  `filteredInjectiveSubcategory`,
  `IsFilteredInjective.isSplitMono_of_strict`,
  `EnoughInjectives.presentation`;
- best owner abstraction: the source-facing category owners `Fil^f(𝒜)` and `𝓘^f(𝒜)` together
  with the canonical inclusion `filteredInjectiveInclusion 𝒜`; the ambient
  monomorphism-into-injective data comes from the canonical mathlib owner
  `EnoughInjectives.presentation`;
- primitive data: a finite filtered object `A`;
- derived API: a strict monomorphism from `A` into an object of `𝓘^f(𝒜)`;
- source/core/bridge triage:
  `source-facing`: the existence of a strict monomorphism in `Fil^f(𝒜)` into a filtered
    injective object;
  `core/canonical`: `Fil^f(𝒜)`, `𝓘^f(𝒜)`, `filteredInjectiveInclusion`, `Strict`,
    `IsFilteredInjective`, and `EnoughInjectives.presentation`;
  `bridge/view`: the existence theorem below, which upgrades enough injectives in `𝒜` to a
    strict filtered embedding in `Fil^f(𝒜)`.

The target theorem should therefore stay a source-facing existence statement, but its surface
should reuse the chapter notations `Fil^f(𝒜)` and `𝓘^f(𝒜)` and the owner predicate `Strict`
directly rather than spelling parallel long forms or exposing the filtered-injective witness as a
separate proof argument. -/

-- Proof sketch: choose bounds for the finite filtration of `A`, embed each quotient
-- `A.obj.obj / F^{n + 1}A` into an injective object of `𝒜`, and assemble these maps into a
-- morphism from `A` to the finite direct sum equipped with the tail filtration. The resulting
-- codomain is filtered injective, and the componentwise construction makes the map a strict
-- monomorphism.
/-- Lemma 13.26.5: every object of `Fil^f(𝒜)` admits a strict monomorphism into a filtered
injective object. -/
theorem exists_strictMono_to_filteredInjective
    (A : Fil^f(𝒜)) :
    ∃ (I : 𝓘^f(𝒜)) (u : A ⟶ I.obj), Mono u ∧ Strict u.hom := sorry

end CategoryTheory
