import StacksProject_2024.stacks_project.Chap12.Lemma_12_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]

/- Definition 12.24.1: a filtered complex is a cochain complex in the category `Fil(𝒜)` of
filtered objects. In this project, `Fil(𝒜)` is represented by the owner abstraction
`FilteredObject 𝒜`, so the notion is recorded directly as `CochainComplex (Fil(𝒜)) ℤ`. The
source text uses this in the abelian setting, but the owner expression itself only needs the
filtered-object category structure together with zero morphisms; later cohomological
constructions add `[Abelian 𝒜]` when homology is involved. The abbreviation `FilteredComplex` is
kept as stable chapter vocabulary because the owner type is used pervasively downstream. -/
abbrev FilteredComplex (𝒜 : Type u) [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] :=
  CochainComplex (Fil(𝒜)) ℤ

end CategoryTheory
