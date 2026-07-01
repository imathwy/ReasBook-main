import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits MorphismProperty

universe u v

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/- Domain-style sampling for Lemma 10.147.5:
* primary domain: filtered colimits of smooth commutative ring maps;
* sampled owner declarations:
  - `RingHom.Smooth`, the mathlib owner for smooth ring homomorphisms;
  - `RingHom.toMorphismProperty`, the canonical bridge from a ring-hom property to
    `CommRingCat`;
  - `CategoryTheory.MorphismProperty.ind`, the canonical filtered-colimit owner;
  - `RingHom.IsFilteredColimitOfEtale`, the project's source-facing wrapper for the analogous
    filtered-colimit-of-etale property.
* best owner abstraction: `RingHom.IsFilteredColimitOfSmooth` as the source-facing owner, with
  core/canonical content given by `ind (toMorphismProperty RingHom.Smooth)`;
* primitive data: only the ring map `f : R →+* A`;
* derived API: any chosen filtered diagram, cocone, and comparison isomorphism presenting `f` as
  a filtered colimit of smooth algebras.

Source/core/bridge triage:
* `source-facing`: `RingHom.IsFilteredColimitOfSmooth`;
* `core/canonical`: `ind (toMorphismProperty RingHom.Smooth)`;
* `bridge/view`: the hidden same-universe `ULift` presentation of `f` used to speak to
  `CategoryTheory.MorphismProperty.ind`.

The old local `CommRingCat.smooth` abbreviation duplicated the canonical owner
`RingHom.Smooth` and its bridge `RingHom.toMorphismProperty`, so this file now exposes the
filtered-colimit hypothesis through the ring-hom owner instead.
-/

/-- An `R`-algebra map `f : R →+* A` is a filtered colimit of smooth `R`-algebras. This thin
source-facing wrapper hides the same-universe `ULift` bookkeeping needed to express the canonical
owner `CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty RingHom.Smooth)`. -/
abbrev IsFilteredColimitOfSmooth (f : R →+* A) : Prop :=
  let _ : Algebra R A := f.toAlgebra
  let _ : Algebra R (ULift A) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift A) := ULift.algebra' R (ULift A)
  ind.{max u v, max u v, max u v + 1} (toMorphismProperty Smooth)
    (CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift A)))

end

end RingHom

namespace TensorProduct

section

variable {R S : Type u} {B : Type v}
variable [CommRing R] [CommRing S] [CommRing B]
variable [Algebra R S] [Algebra R B]

-- Proof sketch: write `S` as a filtered colimit of smooth `R`-algebras. By Lemma `10.147.4`,
-- the canonical comparison map is bijective after base change to each smooth stage. Tensor
-- products commute with filtered colimits, and the integral closure on the target is obtained as
-- the filtered colimit of the stagewise integral closures, so the colimit comparison map is
-- exactly `TensorProduct.toIntegralClosure R S B`.
/-- Lemma 10.147.5: if `R → S` is a filtered colimit of smooth `R`-algebras and
`A = integralClosure R B`, then the canonical map
`S ⊗[R] A → integralClosure S (S ⊗[R] B)` is bijective, hence an isomorphism. -/
theorem toIntegralClosure_bijective_of_isFilteredColimitOfSmooth
    (hS : (algebraMap R S).IsFilteredColimitOfSmooth) :
    Function.Bijective (toIntegralClosure R S B) := sorry

end

end TensorProduct
