import StacksProject_2024.Chap10.Definition_10_135_5
import StacksProject_2024.Chap10.Definition_10_160_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

namespace RingHom

section

variable {R : Type u} {A : Type u} [CommRing R] [CommRing A]

/-- The map-theoretic condition in a regular-local presentation of `A`: a surjective local ring
homomorphism. The regular-local source hypothesis is carried by
`RingHom.RegularLocalPresentation`. -/
def IsRegularLocalPresentation (π : R →+* A) : Prop :=
  IsLocalHom π ∧ Function.Surjective π

/-- A regular-local presentation map is a local ring homomorphism. -/
theorem IsRegularLocalPresentation.isLocalHom {π : R →+* A}
    (hπ : π.IsRegularLocalPresentation) :
    IsLocalHom π :=
  hπ.1

/-- A regular-local presentation map is surjective. -/
theorem IsRegularLocalPresentation.surjective {π : R →+* A}
    (hπ : π.IsRegularLocalPresentation) :
    Function.Surjective π :=
  hπ.2

end

section

variable (A : Type u) [CommRing A]

/-- A regular-local presentation of `A` is a surjective local map from a regular local ring onto
`A`. This is the source-facing owner for the presentation data used in Definition 23.8.5. -/
structure RegularLocalPresentation where
  ring : Type u
  instCommRing : CommRing ring
  instIsRegularLocalRing : IsRegularLocalRing ring
  hom : ring →+* A
  isRegularLocalPresentation : hom.IsRegularLocalPresentation

attribute [instance] RegularLocalPresentation.instCommRing
attribute [instance] RegularLocalPresentation.instIsRegularLocalRing

namespace RegularLocalPresentation

variable {A : Type u} [CommRing A]

/-- Build a regular-local presentation from a regular local source ring and a map satisfying the
presentation predicate. -/
def ofHom {R : Type u} [CommRing R] [IsRegularLocalRing R] (hom : R →+* A)
    (hhom : hom.IsRegularLocalPresentation) : RegularLocalPresentation A where
  ring := R
  instCommRing := inferInstance
  instIsRegularLocalRing := inferInstance
  hom := hom
  isRegularLocalPresentation := hhom

/-- The structure map of `ofHom hom hhom` is `hom`. -/
@[simp] theorem ofHom_hom {R : Type u} [CommRing R] [IsRegularLocalRing R] (hom : R →+* A)
    (hhom : hom.IsRegularLocalPresentation) :
    (ofHom hom hhom).hom = hom :=
  rfl

/-- The structure map of a regular-local presentation is a local ring homomorphism. -/
instance (P : RegularLocalPresentation A) : IsLocalHom P.hom :=
  P.isRegularLocalPresentation.isLocalHom

/-- The structure map of a regular-local presentation is surjective. -/
theorem surjective (P : RegularLocalPresentation A) :
    Function.Surjective P.hom :=
  P.isRegularLocalPresentation.surjective

/-- Postcomposing the structure map of a regular-local presentation with a ring equivalence
transports the presentation to the equivalent target ring. -/
def postcomposeRingEquiv {B : Type u} [CommRing B] (P : RegularLocalPresentation A)
    (e : A ≃+* B) : RegularLocalPresentation B :=
  ofHom (e.toRingHom.comp P.hom) <| by
    let _ : IsLocalHom e.toRingHom := isLocalHom_toRingHom e
    constructor
    · exact RingHom.isLocalHom_comp e.toRingHom P.hom
    · intro b
      rcases P.surjective (e.symm b) with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      change e (P.hom r) = b
      rw [hr, RingEquiv.apply_symm_apply]

/-- The structure map of `P.postcomposeRingEquiv e` is the composite of `P.hom` with `e`. -/
@[simp] theorem postcomposeRingEquiv_hom {B : Type u} [CommRing B]
    (P : RegularLocalPresentation A) (e : A ≃+* B) :
    (P.postcomposeRingEquiv e).hom = e.toRingHom.comp P.hom :=
  rfl

/-- Pointwise form of `postcomposeRingEquiv_hom`. -/
@[simp] theorem postcomposeRingEquiv_hom_apply {B : Type u} [CommRing B]
    (P : RegularLocalPresentation A) (e : A ≃+* B) (r : P.ring) :
    (P.postcomposeRingEquiv e).hom r = e (P.hom r) :=
  rfl

/-- The kernel condition from Definition 23.8.5, viewed as a property of a fixed regular-local
presentation. -/
abbrev KernelIsGeneratedByRegularSequence (P : RegularLocalPresentation A) : Prop :=
  P.hom.KernelIsGeneratedByRegularSequence

/-- Unfolding the presentation-level kernel condition recovers the map-level condition. -/
@[simp] theorem kernelIsGeneratedByRegularSequence_iff (P : RegularLocalPresentation A) :
    P.KernelIsGeneratedByRegularSequence ↔ P.hom.KernelIsGeneratedByRegularSequence :=
  Iff.rfl

end RegularLocalPresentation

end

