import Mathlib
import stacks_project.Chap12.Definition_12_19_3
import stacks_project.Chap13.Definition_13_13_1
import stacks_project.Chap13.Lemma_13_15_5

open CategoryTheory
open FilteredObject.Hom
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "FilF" => Fil^f(𝒜)

/- Domain-style sampling for Lemma `13.26.3`.
- primary domain: finite filtered objects and strict monomorphisms in an abelian category;
- sampled owner declarations:
  `finiteFilteredObjectCat`,
  `Injective`,
  `CochainComplex.PlusWithTermsIn`,
  `CochainComplex.FilteredInjectivePlus`,
  `CochainComplex.IsKInjective`,
  `FilteredObject.Hom.Strict`,
  `gr^{p}`;
- best owner abstraction: the source-facing chapter owner is `finiteFilteredObjectCat 𝒜` with
  notation `Fil^f(𝒜)` for finite filtered objects, and filtered injectivity should be owned by a
  reusable class parallel to `Injective` and `CochainComplex.IsKInjective`; the bounded-below
  filtered-injective cochain complexes are then canonically owned by
  `CochainComplex.FilteredInjectivePlus 𝒜`;
- primitive data: a finite filtered object `I : FilF`;
- derived API: the split-mono theorem for strict monomorphisms out of a filtered-injective source;
- source/core/bridge triage:
  `source-facing`: filtered injectivity on `FilF` and the split-mono theorem;
  `core/canonical`: the class owner `IsFilteredInjective`, together with
    `FilteredObject.Hom.Strict`;
  `bridge/view`: the graded-piece characterization built directly into `IsFilteredInjective`. -/

/-- A finite filtered object is filtered injective if each of its graded pieces is injective in
the ambient abelian category. -/
class IsFilteredInjective (I : FilF) : Prop where
  injective (p : ℤ) : Injective (gr^{p} I.obj)

attribute [instance] IsFilteredInjective.injective

namespace CochainComplex

/-- The bounded-below cochain complexes of finite filtered objects whose terms are filtered
injective. -/
abbrev FilteredInjectivePlus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  CochainComplex.PlusWithTermsIn
    (IsFilteredInjective : ObjectProperty FilF)

end CochainComplex

namespace IsFilteredInjective

-- Proof sketch: choose the largest filtration index with nonzero graded piece, use strictness and
-- Lemma 12.19.13 to obtain a monomorphism on the top graded piece, split that monomorphism by
-- injectivity of the graded piece, decompose source and target into that top piece and its kernel,
-- and conclude by induction on the finite filtration length of `I`.
/-- Lemma 13.26.3: if `u : I.obj ⟶ A` is a strict monomorphism in `Fil(𝒜)` with finite filtered-
injective source `I : Fil^f(𝒜)`, then `u` is a split injection. -/
theorem isSplitMono_of_strict
    {I : FilF} {A : FilteredObject 𝒜} (u : I.obj ⟶ A) [IsFilteredInjective I] [Mono u]
    (hu : Strict u) :
    IsSplitMono u := sorry

end IsFilteredInjective

end CategoryTheory
