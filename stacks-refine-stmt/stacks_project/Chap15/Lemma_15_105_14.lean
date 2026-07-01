import Mathlib
import stacks_project.Chap10.Lemma_10_154_3
import stacks_project.Chap15.Definition_15_105_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open CommRingCat
open scoped TensorProduct

universe u v

namespace RingHom

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- An `R`-algebra map `f : R →+* S` is a filtered colimit of weakly étale `R`-algebras. This
thin source-facing wrapper hides the same-universe `ULift` bookkeeping needed to express the
canonical owner
`CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty (fun f ↦ Algebra.IsWeaklyEtale _ _))`. -/
abbrev IsFilteredColimitOfWeaklyEtale (f : R →+* S) : Prop :=
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R (ULift S) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift S) := ULift.algebra' R (ULift S)
  ind.{max u v, max u v, max u v + 1}
    (toMorphismProperty fun {R S} [CommRing R] [CommRing S] (f : R →+* S) ↦
      let _ : Algebra R S := f.toAlgebra
      Algebra.IsWeaklyEtale R S)
    (ofHom (algebraMap (ULift.{v} R) (ULift S)))

end

end RingHom

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/- Domain-style sampling for Lemma 15.105.14:
- primary domain: weakly étale commutative algebra and filtered-colimit presentations of ring maps;
- sampled owner declarations:
  `Algebra.IsWeaklyEtale`,
  `CategoryTheory.MorphismProperty.ind`,
  `RingHom.toMorphismProperty`,
  `RingHom.IsFilteredColimitOfWeaklyEtale`,
  `RingHom.algebraMap_isFilteredColimitOfEtale_of_isColimit`;
- best owner abstraction: the filtered-colimit hypothesis is the source-facing ring-hom owner
  `(algebraMap A B).IsFilteredColimitOfWeaklyEtale`, whose hidden core/canonical content is
  `CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty (fun f ↦ Algebra.IsWeaklyEtale _ _))`;
- primitive data: the owner class `Algebra.IsWeaklyEtale` on each stage map;
- derived API: the source-facing closure statement that the colimit map `A → B` is weakly étale.

This file should therefore expose the filtered-colimit hypothesis through the ring-hom owner
`RingHom.IsFilteredColimitOfWeaklyEtale`, rather than through a raw `toMorphismProperty ... .ind`
term in theorem statements.
-/

-- Proof sketch: a localization map is étale by the canonical mathlib instance
-- `Algebra.Etale.of_isLocalizationAway` in the away-localization case, and more generally the
-- Stacks lemma allows one to view localizations as weakly étale directly. The weakly étale
-- statement then follows from the defining flatness properties of localization.
/-- Lemma 15.105.14 (1): if `B` is a localization of `A`, then the ring map `A → B` is weakly
étale. -/
theorem isWeaklyEtale_of_isLocalization (M : Submonoid A) [IsLocalization M B] :
    Algebra.IsWeaklyEtale A B := sorry

/-- Lemma 15.105.14 (2): every étale ring map `A → B` is weakly étale. -/
instance isWeaklyEtale_of_etale [Algebra.Etale A B] :
    Algebra.IsWeaklyEtale A B := sorry

-- Proof sketch: filtered colimits preserve flatness of the structural map `A → B`, and the
-- tensor-square multiplication map of the colimit is the filtered colimit of the corresponding
-- tensor-square multiplication maps of the stages. Since each stage is weakly étale, both
-- flatness conditions pass to the colimit.
/-- Lemma 15.105.14 (3): a filtered colimit of weakly étale `A`-algebras is weakly étale over
`A`. -/
theorem isWeaklyEtale_of_isFilteredColimitOfWeaklyEtale
    (hcolim : (algebraMap A B).IsFilteredColimitOfWeaklyEtale) :
    Algebra.IsWeaklyEtale A B := sorry

/-- If `A → B` is a filtered colimit of étale `A`-algebras, then it is weakly étale. -/
theorem isWeaklyEtale_of_isFilteredColimitOfEtale
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale) :
    Algebra.IsWeaklyEtale A B := sorry

end
