import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_3_6
import StacksProject_2024.stacks_project.Chap13.Definition_13_8_1
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open DerivedCategory
open scoped CategoryTheory

universe w v u

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/- Domain-style sampling for Lemma 13.12.1:
- primary domain: connecting morphisms for short exact sequences of cochain complexes in the
  derived category;
- sampled owner declarations in this domain:
  `CategoryTheory.DeltaFunctor`,
  `DerivedCategory.triangleOfSESδ`,
  `DerivedCategory.triangleOfSES_distinguished`,
  `DerivedCategory.triangleOfSESδ_naturality`;
- best owner abstraction: the source-facing item is the canonical `DeltaFunctor` structure on the
  functor `Comp(𝒜) ⥤ D(𝒜)`;
- source/core/bridge triage:
  `source-facing`: the canonical `δ`-functor on cochain complexes valued in the derived category;
  `core/canonical`: `DerivedCategory.Q` together with the owner declarations
    `triangleOfSESδ`, `triangleOfSES_distinguished`, and `triangleOfSESδ_naturality`;
  `bridge/view`: the `DeltaFunctor` packaging from `Definition_13_3_6`, which collects exactly the
    connecting morphisms, distinguished triangles, and naturality squares required by the source.

Primitive data are only the underlying functor `DerivedCategory.Q` and the owner-level connecting
morphisms for short exact sequences. The distinguished-triangle and naturality statements are
derived API from these owners, so this file should expose the canonical `DeltaFunctor` rather than
re-package those facts as a conjunction theorem.
-/

-- Proof sketch: take the connecting morphisms to be `DerivedCategory.triangleOfSESδ hS`. The
-- associated distinguished-triangle and naturality fields are exactly the canonical owner lemmas
-- `DerivedCategory.triangleOfSES_distinguished hS` and
-- `DerivedCategory.triangleOfSESδ_naturality hS hS' φ`.
/-- Lemma 13.12.1: the canonical functor
`\mathrm{Comp}(\mathcal A)=\mathrm{CoCh}(\mathcal A) \to D(\mathcal A)` carries the canonical
connecting morphisms attached to short exact sequences of cochain complexes, making it into a
`δ`-functor. -/
noncomputable def cochainComplexToDerivedDeltaFunctor :
    DeltaFunctor (Comp(𝒜)) (D(𝒜)) where
  toFunctor := Q
  additive := inferInstance
  δ := fun {_} hS ↦ triangleOfSESδ hS
  map_distinguished := fun {_} hS ↦ triangleOfSES_distinguished hS
  δ_naturality := fun {_ _} hS hS' φ ↦
    ⟨(triangleOfSESδ_naturality hS hS' φ).symm⟩

end CategoryTheory
