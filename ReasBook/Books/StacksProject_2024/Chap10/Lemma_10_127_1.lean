import StacksProject_2024.Chap10.Lemma_10_127_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u v

/-- The object property on `Over (CommAlgCat.of R A)` selecting the finitely presented
`R`-algebras over `A`. -/
abbrev finitelyPresentedAlgebrasOverProperty (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] : ObjectProperty (Over (CommAlgCat.of R A)) :=
  fun B : Over (CommAlgCat.of R A) ↦ Algebra.FinitePresentation R B.left

/-- The category of finitely presented `R`-algebras equipped with an `R`-algebra map to `A`. -/
abbrev finitelyPresentedAlgebrasOver (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] :=
  (finitelyPresentedAlgebrasOverProperty R A).FullSubcategory

/-- The canonical cocone from the diagram of finitely presented `R`-algebras over `A` to `A`. -/
abbrev finitelyPresentedAlgebrasOverCocone (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] :=
  selectedAlgebrasOverTargetCocone (finitelyPresentedAlgebrasOverProperty R A)

/-- Lemma 10.127.1: the finitely presented `R`-algebras over `A` form a filtered category, and
their canonical cocone exhibits `A` as the filtered colimit of all finitely presented
`R`-algebras mapping to `A`. -/
theorem finitelyPresentedAlgebrasOver_isFilteredColimit (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] :
    IsFiltered (finitelyPresentedAlgebrasOver R A) ∧
      Nonempty (IsColimit (finitelyPresentedAlgebrasOverCocone R A)) := by
  refine (selectedAlgebrasOverTarget_isFilteredColimit_iff_factorization
    (finitelyPresentedAlgebrasOverProperty R A) ?_).2 ?_
  · intro B hB
    simpa using hB
  · intro B hB
    exact ⟨⟨B, hB⟩, ⟨𝟙 B⟩⟩

/-- The canonical cocone from finitely presented `R`-algebras over `A` exhibits `A` as their
filtered colimit. This witness is canonical because `IsColimit` is a subsingleton. -/
noncomputable def finitelyPresentedAlgebrasOverCoconeIsColimit (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] :
    IsColimit (finitelyPresentedAlgebrasOverCocone R A) :=
  (finitelyPresentedAlgebrasOver_isFilteredColimit R A).2.some

/-- The category of finitely presented `R`-algebras over `A` is filtered. -/
instance finitelyPresentedAlgebrasOver_isFiltered (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] : IsFiltered (finitelyPresentedAlgebrasOver R A) :=
  (finitelyPresentedAlgebrasOver_isFilteredColimit R A).1
