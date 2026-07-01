import Mathlib
import stacks_project.Chap10.Lemma_10_147_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty Limits
open CommRingCat

universe u

namespace RingHom

section

variable {R A : Type u} [CommRing R] [CommRing A]

/- Domain-style sampling for Lemma 16.3.5:
* primary domain: filtered colimits of smooth and standard smooth commutative ring maps;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfSmooth`, the Chapter 10 source-facing owner for PT
    presentations;
  - `CategoryTheory.MorphismProperty.ind`, the generic owner for filtered-colimit closure of a
    morphism property;
  - `RingHom.toMorphismProperty`, the canonical bridge from a ring-hom property to a
    `CommRingCat` morphism property;
  - `RingHom.IsStandardSmooth`, the canonical owner for standard smoothness of a ring map.
* best owner abstraction: `(toMorphismProperty IsStandardSmooth).ind (ofHom f)`;
* primitive data: standard smoothness of each stage map;
* derived API: any chosen filtered diagram, cocone, and comparison isomorphism witnessing the
  filtered-colimit presentation.

Source/core/bridge triage:
* `source-facing`: the map `R → A` is a filtered colimit of standard smooth `R`-algebras;
* `core/canonical`: `(toMorphismProperty IsStandardSmooth).ind (ofHom f)`;
* `bridge/view`: a particular filtered diagram in `Under (CommRingCat.of R)` presenting `f`.

The previous local `CommRingCat.standardSmooth` abbreviation duplicated mathlib's canonical bridge
`RingHom.toMorphismProperty`, so the file now states the lemma directly at that owner level.
-/

-- Proof sketch: use Lemma `10.127.4` in the standard-smooth variant. Given a finitely presented
-- `R`-algebra mapping to `A`, factor the map through one of the smooth stages of the given
-- filtered colimit presentation, then apply Lemma `16.3.4` to replace that smooth stage by a
-- standard smooth `R`-algebra through which the map still factors.
/-- Lemma 16.3.5: if a ring map `R → A` is a filtered colimit of smooth `R`-algebras, then it is
a filtered colimit of standard smooth `R`-algebras. -/
theorem isFilteredColimitOfStandardSmooth_of_isFilteredColimitOfSmooth
    {f : R →+* A} (h : f.IsFilteredColimitOfSmooth) :
    (toMorphismProperty IsStandardSmooth).ind (ofHom f) := sorry

end

end RingHom
