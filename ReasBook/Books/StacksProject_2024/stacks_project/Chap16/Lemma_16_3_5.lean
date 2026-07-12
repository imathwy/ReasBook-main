import Mathlib
import StacksProject_2024.Chap10.Lemma_10_127_4
import StacksProject_2024.Chap10.Lemma_10_147_5
import StacksProject_2024.Chap16.Lemma_16_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open CommRingCat

universe u v

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/- Domain-style sampling for Lemma 16.3.5:
* primary domain: filtered colimits of smooth and standard smooth commutative ring maps;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfSmooth`, the Chapter 10 source-facing owner for PT
    presentations;
  - `RingHom.IsFilteredColimitOfEtale`, the analogous source-facing owner hiding the same-universe
    `ULift` bookkeeping for a filtered-colimit morphism property;
  - `RingHom.IsFilteredColimitOfWeaklyEtale`, the later chapter-level repetition of the same
    source-facing wrapper pattern for a different morphism property;
  - `CategoryTheory.MorphismProperty.ind`, the generic owner for filtered-colimit closure of a
    morphism property;
  - `RingHom.IsStandardSmooth`, the canonical owner for standard smoothness of a ring map.
* best owner abstraction: `RingHom.IsFilteredColimitOfStandardSmooth`, with hidden core/canonical
  content `ind (toMorphismProperty RingHom.IsStandardSmooth)`;
* primitive data: only the ring map `f : R →+* A`;
* derived API: any chosen filtered diagram, cocone, and comparison isomorphism witnessing the
  filtered-colimit presentation.

Source/core/bridge triage:
* `source-facing`: `RingHom.IsFilteredColimitOfStandardSmooth`;
* `core/canonical`: `ind (toMorphismProperty RingHom.IsStandardSmooth)`;
* `bridge/view`: the hidden same-universe `ULift` presentation of `f` used to speak to
  `CategoryTheory.MorphismProperty.ind`.

The review correction for this file is that the theorem should not expose the raw
`CommRingCat`-level owner `(toMorphismProperty RingHom.IsStandardSmooth).ind (ofHom ...)`.
Parallel to `RingHom.IsFilteredColimitOfSmooth`, `...Etale`, and `...WeaklyEtale`, the
source-facing owner here should be a ring-hom property hiding the `ULift` bookkeeping.
-/

/-- An `R`-algebra map `f : R →+* A` is a filtered colimit of standard smooth `R`-algebras. This
thin source-facing wrapper hides the same-universe `ULift` bookkeeping needed to express the
canonical owner
`CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty RingHom.IsStandardSmooth)`. -/
abbrev IsFilteredColimitOfStandardSmooth (f : R →+* A) : Prop :=
  let _ : Algebra R A := f.toAlgebra
  let _ : Algebra R (ULift A) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift A) := ULift.algebra' R (ULift A)
  ind.{max u v, max u v, max u v + 1} (toMorphismProperty IsStandardSmooth)
    (ofHom (algebraMap (ULift.{v} R) (ULift A)))

-- Proof sketch: use Lemma `10.127.4` in the standard-smooth variant. Given a finitely presented
-- `R`-algebra mapping to `A`, factor the map through one of the smooth stages of the given
-- filtered colimit presentation, then apply Lemma `16.3.4` to replace that smooth stage by a
-- standard smooth `R`-algebra through which the map still factors.
/-- Lemma 16.3.5: if a ring map `R → A` is a filtered colimit of smooth `R`-algebras, then it is
a filtered colimit of standard smooth `R`-algebras. -/
theorem isFilteredColimitOfStandardSmooth_of_isFilteredColimitOfSmooth
    {f : R →+* A} (h : f.IsFilteredColimitOfSmooth) :
    f.IsFilteredColimitOfStandardSmooth := by
  let _ : Algebra R A := f.toAlgebra
  -- The source-facing wrapper `IsFilteredColimitOfSmooth` already packages the canonical
  -- `ind-smooth` presentation. The proof then runs through the finite-presentation factorization
  -- criterion of Lemma `10.127.4` and the smooth-to-standard-smooth refinement of
  -- Lemma `16.3.4`, so no extra public wrapper API is introduced here.
  sorry

end

end RingHom
