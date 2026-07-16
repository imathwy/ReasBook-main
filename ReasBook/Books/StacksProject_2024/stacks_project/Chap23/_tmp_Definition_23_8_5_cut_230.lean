import StacksProject_2024.stacks_project.Chap10.Definition_10_135_5
import StacksProject_2024.stacks_project.Chap10.Definition_10_160_1

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

end RingHom

section

variable {R : Type u} [CommRing R]

/-
Local analogue check:
* `IsCompleteLocalRing` supplies the complete-local owner for maximal-ideal completions;
* `RingHom.KernelIsGeneratedByRegularSequence` supplies the quotient-by-regular-sequence owner;
* prime-local conditions elsewhere in the repo are stated via `∀ p : PrimeSpectrum R, ...`.
Semantic `lean_leansearch` was not exposed in this run, so the owner choice is based on these
verified local precedents.
-/

/-- Definition 23.8.5: a complete Noetherian local ring is a complete intersection if it is a
quotient of a regular local ring by an ideal generated by a regular sequence. -/
@[stacks 09Q3]
class IsCompleteIntersectionCompleteLocalRing (R : Type u) [CommRing R] : Prop extends
    IsCompleteLocalRing R, IsNoetherianRing R where
  exists_presentation :
    ∃ P : RingHom.RegularLocalPresentation R, P.KernelIsGeneratedByRegularSequence

/-- Unfold Definition 23.8.5 into the complete-local, Noetherian, and presentation conditions. -/
theorem isCompleteIntersectionCompleteLocalRing_iff (R : Type u) [CommRing R] :
    IsCompleteIntersectionCompleteLocalRing R ↔
      IsCompleteLocalRing R ∧ IsNoetherianRing R ∧
        ∃ P : RingHom.RegularLocalPresentation R, P.KernelIsGeneratedByRegularSequence := by
  constructor
  · intro h
    letI : IsCompleteIntersectionCompleteLocalRing R := h
    exact ⟨inferInstance, inferInstance, h.exists_presentation⟩
  · rintro ⟨hComplete, hNoetherian, hExists⟩
    letI : IsCompleteLocalRing R := hComplete
    letI : IsNoetherianRing R := hNoetherian
    exact { exists_presentation := hExists }

namespace IsCompleteIntersectionCompleteLocalRing

/-- Unfold a complete-intersection complete local ring into a regular-local presentation whose
kernel is generated by a regular sequence. -/
theorem presentation (R : Type u) [CommRing R] [IsCompleteIntersectionCompleteLocalRing R] :
    ∃ P : RingHom.RegularLocalPresentation R, P.KernelIsGeneratedByRegularSequence :=
  (inferInstance : IsCompleteIntersectionCompleteLocalRing R).exists_presentation

/-- A complete Noetherian local ring is a complete intersection as soon as it admits a
regular-local presentation whose kernel is generated by a regular sequence. -/
theorem of_exists_regularLocalPresentation
    (R : Type u) [CommRing R] [IsCompleteLocalRing R] [IsNoetherianRing R]
    (hPresentation :
      ∃ P : RingHom.RegularLocalPresentation R, P.KernelIsGeneratedByRegularSequence) :
    IsCompleteIntersectionCompleteLocalRing R :=
  (isCompleteIntersectionCompleteLocalRing_iff R).2
    ⟨inferInstance, inferInstance, hPresentation⟩

end IsCompleteIntersectionCompleteLocalRing

namespace RingHom.RegularLocalPresentation

variable {A : Type u} [CommRing A] [IsCompleteLocalRing A] [IsNoetherianRing A]

/-- A regular-local presentation with regular-sequence kernel exhibits the target complete
Noetherian local ring as a complete intersection. -/
theorem isCompleteIntersectionCompleteLocalRing (P : RingHom.RegularLocalPresentation A)
    (hP : P.KernelIsGeneratedByRegularSequence) :
    IsCompleteIntersectionCompleteLocalRing A :=
  IsCompleteIntersectionCompleteLocalRing.of_exists_regularLocalPresentation A ⟨P, hP⟩

end RingHom.RegularLocalPresentation

/-- Definition 23.8.5 (1): a Noetherian local ring is a complete intersection if its maximal-ideal
adic completion is a complete intersection complete local ring. -/
@[stacks 09Q3 "(1)"]
class IsCompleteIntersectionLocalRing (R : Type u) [CommRing R] : Prop extends
    IsLocalRing R, IsNoetherianRing R where
  completion_isCompleteIntersection :
    IsCompleteIntersectionCompleteLocalRing (AdicCompletion (maximalIdeal R) R)

/-- Unfold Definition 23.8.5 (1) into the Noetherian hypothesis and the completion condition. -/
theorem isCompleteIntersectionLocalRing_iff (R : Type u) [CommRing R] [IsLocalRing R] :
    IsCompleteIntersectionLocalRing R ↔
      IsNoetherianRing R ∧
        IsCompleteIntersectionCompleteLocalRing (AdicCompletion (maximalIdeal R) R) := by
  constructor
  · intro h
    letI : IsCompleteIntersectionLocalRing R := h
    exact ⟨inferInstance, h.completion_isCompleteIntersection⟩
  · rintro ⟨hNoetherian, hCompletion⟩
    letI : IsNoetherianRing R := hNoetherian
    exact { completion_isCompleteIntersection := hCompletion }

namespace IsCompleteIntersectionLocalRing

/-- The maximal-ideal completion of a complete-intersection local ring is a
complete-intersection complete local ring. -/
theorem completion (R : Type u) [CommRing R] [IsCompleteIntersectionLocalRing R] :
    IsCompleteIntersectionCompleteLocalRing (AdicCompletion (maximalIdeal R) R) :=
  (inferInstance : IsCompleteIntersectionLocalRing R).completion_isCompleteIntersection

/-- A Noetherian local ring is a complete intersection once its maximal-ideal completion is a
complete-intersection complete local ring. -/
theorem of_completion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hCompletion :
      IsCompleteIntersectionCompleteLocalRing (AdicCompletion (maximalIdeal R) R)) :
    IsCompleteIntersectionLocalRing R :=
  (isCompleteIntersectionLocalRing_iff R).2
    ⟨inferInstance, hCompletion⟩

end IsCompleteIntersectionLocalRing
