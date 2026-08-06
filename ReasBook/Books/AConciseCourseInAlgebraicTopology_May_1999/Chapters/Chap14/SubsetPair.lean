import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_1_1

open CategoryTheory
open SpacePair

universe u

/-- The pair `(X, A)` regarded as an object of `SpacePair`. -/
abbrev subsetPair (X : TopCat.{u}) (A : Set X) : SpacePair where
  space := X
  subspace := A

/-- The identity-on-ambient-space map `(X, B) ⟶ (X, A)` determined by an inclusion `B ⊆ A`. -/
def subsetPairInclusion {X : TopCat.{u}} {A B : Set X} (hBA : B ⊆ A) :
    subsetPair X B ⟶ subsetPair X A where
  hom := 𝟙 X
  map_subspace' := by
    intro x hx
    exact hBA hx

@[simp] theorem subsetPairInclusion_rfl {X : TopCat.{u}} (A : Set X) :
    subsetPairInclusion Set.Subset.rfl = 𝟙 (subsetPair X A) := by
  apply SpacePair.hom_ext
  ext x
  rfl

@[simp] theorem subsetPairInclusion_comp {X : TopCat.{u}} {A B C : Set X}
    (hAB : B ⊆ A) (hBC : C ⊆ B) :
    subsetPairInclusion (Set.Subset.trans hBC hAB) =
      subsetPairInclusion hBC ≫ subsetPairInclusion hAB := by
  apply SpacePair.hom_ext
  ext x
  rfl

namespace SpacePair

/-- The subset `A ⊆ Y`, regarded as a subset of the subspace `X ⊆ Y`. -/
abbrev restrictedSubset {Y : TopCat.{u}} (X A : Set Y) : Set X :=
  Subtype.val ⁻¹' A

/-- The canonical map from the absolute pair on `A ⊆ Y` to the absolute pair on the
corresponding restricted subset of `X`. -/
def restrictionAbsoluteMap {Y : TopCat.{u}} {X A : Set Y} (hAX : A ⊆ X) :
    absolute (TopCat.of A) ⟶ absolute (TopCat.of (restrictedSubset X A)) :=
  { hom := TopCat.ofHom
      ⟨fun a ↦ ⟨⟨a.1, hAX a.2⟩, a.2⟩,
        (continuous_subtype_val.subtype_mk fun a ↦ hAX a.2).subtype_mk fun a ↦ a.2⟩
    map_subspace' := by
      intro a ha
      cases ha }

/-- The canonical map from the absolute pair on `A ∩ B ⊆ Y` to the common restricted subset of
`X`. -/
def intersectionRestrictionAbsoluteMap {Y : TopCat.{u}} {X A B : Set Y} (hAX : A ⊆ X) :
    subspaceFunctor.obj (subsetPair Y (A ∩ B)) ⟶
      subspaceFunctor.obj
        (subsetPair (TopCat.of X) (restrictedSubset X A ∩ restrictedSubset X B)) :=
  { hom := TopCat.ofHom
      ⟨fun a ↦ ⟨⟨a.1, hAX a.2.1⟩, ⟨a.2.1, a.2.2⟩⟩,
        (continuous_subtype_val.subtype_mk fun a ↦ hAX a.2.1).subtype_mk fun a ↦
          ⟨a.2.1, a.2.2⟩⟩
    map_subspace' := by
      intro a ha
      cases ha }

end SpacePair
