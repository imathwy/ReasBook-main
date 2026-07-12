import Mathlib.Algebra.Homology.ShortComplex.ShortExact

open CategoryTheory

universe u v w x

section

variable {C : Type u} [Category.{v} C]
variable {Graded : Type w} [Category.{x} Graded]

/-- Definition 22.7.1 (1): a homomorphism of differential graded modules is an admissible
monomorphism if the underlying graded-module map is split mono. -/
@[stacks 09JT]
abbrev IsAdmissibleMono (forgetToGraded : C ⥤ Graded) {K L : C} (ι : K ⟶ L) : Prop :=
  IsSplitMono (forgetToGraded.map ι)

/-- The defining criterion for admissibility of a monomorphism after forgetting the differential. -/
theorem isAdmissibleMono_iff_exists_retraction
    (forgetToGraded : C ⥤ Graded) {K L : C} (ι : K ⟶ L) :
    IsAdmissibleMono forgetToGraded ι ↔
      ∃ retraction : forgetToGraded.obj L ⟶ forgetToGraded.obj K,
        forgetToGraded.map ι ≫ retraction = 𝟙 (forgetToGraded.obj K) := by
  constructor
  · intro hι
    letI : IsSplitMono (forgetToGraded.map ι) := hι
    exact ⟨retraction (forgetToGraded.map ι), IsSplitMono.id (forgetToGraded.map ι)⟩
  · rintro ⟨retraction, left_inv⟩
    exact IsSplitMono.mk' ⟨retraction, left_inv⟩

/-- Definition 22.7.1 (2): a homomorphism of differential graded modules is an admissible
epimorphism if the underlying graded-module map is split epi. -/
@[stacks 09JT]
abbrev IsAdmissibleEpi (forgetToGraded : C ⥤ Graded) {L M : C} (π : L ⟶ M) : Prop :=
  IsSplitEpi (forgetToGraded.map π)

/-- The defining criterion for admissibility of an epimorphism after forgetting the differential. -/
theorem isAdmissibleEpi_iff_exists_section
    (forgetToGraded : C ⥤ Graded) {L M : C} (π : L ⟶ M) :
    IsAdmissibleEpi forgetToGraded π ↔
      ∃ gradedSection : forgetToGraded.obj M ⟶ forgetToGraded.obj L,
        gradedSection ≫ forgetToGraded.map π = 𝟙 (forgetToGraded.obj M) := by
  constructor
  · intro hπ
    letI : IsSplitEpi (forgetToGraded.map π) := hπ
    exact ⟨section_ (forgetToGraded.map π), IsSplitEpi.id (forgetToGraded.map π)⟩
  · rintro ⟨gradedSection, right_inv⟩
    exact IsSplitEpi.mk' ⟨gradedSection, right_inv⟩

end

section

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]
variable {Graded : Type w} [Category.{x} Graded]

/-- Definition 22.7.1 (3): a short exact sequence of differential graded modules is an admissible
short exact sequence if it is short exact and its underlying graded-module maps are split. -/
@[stacks 09JT]
class IsAdmissibleShortExact (forgetToGraded : C ⥤ Graded) (S : ShortComplex C) : Prop where
  shortExact : S.ShortExact
  isAdmissibleMono : IsAdmissibleMono forgetToGraded S.f
  isAdmissibleEpi : IsAdmissibleEpi forgetToGraded S.g

attribute [instance] IsAdmissibleShortExact.isAdmissibleMono
attribute [instance] IsAdmissibleShortExact.isAdmissibleEpi

/-- The defining criterion for admissibility of a short exact sequence of differential graded
modules. -/
theorem isAdmissibleShortExact_iff
    (forgetToGraded : C ⥤ Graded) (S : ShortComplex C) :
    IsAdmissibleShortExact forgetToGraded S ↔
      S.ShortExact ∧
        IsAdmissibleMono forgetToGraded S.f ∧
        IsAdmissibleEpi forgetToGraded S.g := by
  constructor
  · intro hS
    exact ⟨hS.shortExact, hS.isAdmissibleMono, hS.isAdmissibleEpi⟩
  · rintro ⟨hShortExact, hMono, hEpi⟩
    exact ⟨hShortExact, hMono, hEpi⟩

/-- Unfold `IsAdmissibleShortExact` into short exactness together with explicit graded splittings
of the underlying monomorphism and epimorphism. -/
theorem isAdmissibleShortExact_iff_exists_retraction_section
    (forgetToGraded : C ⥤ Graded) (S : ShortComplex C) :
    IsAdmissibleShortExact forgetToGraded S ↔
      S.ShortExact ∧
        (∃ retraction : forgetToGraded.obj S.X₂ ⟶ forgetToGraded.obj S.X₁,
          forgetToGraded.map S.f ≫ retraction = 𝟙 (forgetToGraded.obj S.X₁)) ∧
        (∃ gradedSection : forgetToGraded.obj S.X₃ ⟶ forgetToGraded.obj S.X₂,
          gradedSection ≫ forgetToGraded.map S.g = 𝟙 (forgetToGraded.obj S.X₃)) := by
  rw [isAdmissibleShortExact_iff, isAdmissibleMono_iff_exists_retraction,
    isAdmissibleEpi_iff_exists_section]

end
