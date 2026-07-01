import Mathlib
import stacks_project.Chap15.Lemma_15_33_6

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open CategoryTheory MorphismProperty
open CommRingCat
open scoped TensorProduct

universe u v

noncomputable section

namespace RingHom

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling for Lemma 15.33.7:
* primary domain: filtered-colimit presentations of local complete intersection ring maps in
  commutative algebra;
* sampled owner declarations:
  - `RingHom.IsLocalCompleteIntersection` from `Definition_15_33_2`;
  - `RingHom.toMorphismProperty`, the canonical bridge from ring-hom properties to
    `CommRingCat`;
  - `CategoryTheory.MorphismProperty.ind`, the canonical owner for filtered-colimit morphism
    properties;
  - `RingHom.IsFilteredColimitOfSmooth` from `Lemma_10_147_5`, which already uses this owner
    pattern for the analogous smooth case.
* best owner abstraction: the source-facing owner here is
  `RingHom.IsFilteredColimitOfLocalCompleteIntersection`, whose core/canonical content is
  `CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty
  RingHom.IsLocalCompleteIntersection)`;
* primitive data: only the ring map `f : R →+* S`;
* derived API: any chosen filtered diagram, cocone, and comparison isomorphism exhibiting `f` as
  a filtered colimit of local complete intersection `R`-algebras.

Source/core/bridge triage:
* `source-facing`: `RingHom.IsFilteredColimitOfLocalCompleteIntersection`;
* `core/canonical`: `CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty
  RingHom.IsLocalCompleteIntersection)`;
* `bridge/view`: the hidden same-universe `ULift` presentation used to speak to
  `CategoryTheory.MorphismProperty.ind`.
-/
/-- An `R`-algebra map `f : R →+* S` is a filtered colimit of local complete intersection
`R`-algebras. This thin source-facing wrapper hides the same-universe `ULift` bookkeeping needed
to express the canonical owner
`CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty
RingHom.IsLocalCompleteIntersection)`. -/
abbrev IsFilteredColimitOfLocalCompleteIntersection (f : R →+* S) : Prop :=
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R (ULift S) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift S) := ULift.algebra' R (ULift S)
  ind.{max u v, max u v, max u v + 1} (toMorphismProperty IsLocalCompleteIntersection)
    (ofHom (algebraMap (ULift.{v} R) (ULift S)))

end

end RingHom

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable {ι : Type v}

-- Proof sketch: write `B → C` as a filtered colimit of local complete intersection maps. Apply
-- Lemma `15.33.6` to each stage to obtain the left-extended Jacobi-Zariski sequence there, then
-- use Lemma `10.134.9` to identify the direct limit of the stagewise naive cotangent complexes
-- with the naive cotangent complex of `A → B → C`. Exactness of filtered colimits transports the
-- stagewise exactness to the limit sequence.
/-- Lemma 15.33.7: let `A → B → C` be ring maps. If `B → C` is a filtered colimit of local
complete intersection homomorphisms, then for any presentation `P : A[x_s] → B`, the
left-extended Jacobi-Zariski sequence
`0 → H₁(NL_{B/A} ⊗[B] C) → H¹(L_{C/A}) → H¹(L_{C/B}) → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`
is exact, where `H₁(NL_{B/A} ⊗[B] C)` is represented by the kernel of the tensorized differential
attached to `P`. -/
theorem presentation_jacobi_zariski_exact_sequence_with_zero_left_of_isFilteredColimitOfLocalCompleteIntersection
    (P : Generators A B ι)
    (hQ : (algebraMap B C).IsFilteredColimitOfLocalCompleteIntersection) :
    Function.Injective (tensor_presentation_cotangent_h1_to_h1_cotangent C P) ∧
      (presentationJacobiZariskiLeftSequence C P).Exact := sorry

end
