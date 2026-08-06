import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.CWComplex.Classical.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.SpacePair

open CategoryTheory
open SpacePair

universe u

/-- A pair of spaces is a CW pair when its ambient space together with its distinguished subspace
forms a relative CW complex. -/
def IsCWPair (P : SpacePair.{u}) : Prop :=
  Nonempty (Topology.RelCWComplex (Set.univ : Set P.space) P.subspace)

/-- The full subcategory of `SpacePair` on CW pairs. -/
notation "CWPair" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsCWPair

namespace IsCWPair

/-- The underlying pair of spaces of a CW pair. -/
abbrev toSpacePair (P : CWPair) : SpacePair :=
  P.obj

/-- The ambient space of a CW pair `(X, A)`. -/
abbrev space (P : CWPair) : TopCat :=
  (toSpacePair P).space

/-- The distinguished subspace of a CW pair `(X, A)`. -/
abbrev subspace (P : CWPair) : Set (space P) :=
  (toSpacePair P).subspace

/-- The one-point CW pair `(*, ∅)`. -/
def point : CWPair :=
  ⟨SpacePair.point, by
    sorry⟩

/-- The subspace `A` of a CW pair `(X, A)`, regarded canonically as the CW pair `(A, ∅)`. -/
def subspacePair (P : CWPair) : CWPair :=
  ⟨SpacePair.subspaceAbsolute (toSpacePair P), by
    sorry⟩

/-- The ambient space `X` of a CW pair `(X, A)`, regarded canonically as the CW pair `(X, ∅)`. -/
def absolutePair (P : CWPair) : CWPair :=
  ⟨SpacePair.absolute (space P), by
    sorry⟩

/-- The excision pair `(X \ U, A \ U)` attached to a CW pair `(X, A)`. -/
def removeSubsetPair (P : CWPair) (U : Set (space P))
    (hU : closure U ⊆ interior (subspace P)) : CWPair :=
  ⟨SpacePair.removeSubset (toSpacePair P) U, by
    sorry⟩

/-- The coproduct CW pair `∐ i, (Xᵢ, Aᵢ)` with underlying sigma pair. -/
def sigmaPair {ι : Type u} (P : ι → CWPair) : CWPair :=
  ⟨SpacePair.sigmaPair fun i ↦ toSpacePair (P i), by
    sorry⟩

/-- The canonical inclusion `(A, ∅) ⟶ (X, ∅)` attached to a CW pair `(X, A)`. -/
abbrev subspaceInclusion (P : CWPair) : subspacePair P ⟶ absolutePair P :=
  ObjectProperty.homMk (SpacePair.subspaceInclusion (toSpacePair P))

/-- The canonical comparison `(X, ∅) ⟶ (X, A)` attached to a CW pair `(X, A)`. -/
abbrev absoluteToRelative (P : CWPair) : absolutePair P ⟶ P :=
  ObjectProperty.homMk (SpacePair.absoluteToRelative (toSpacePair P))

/-- The canonical excision inclusion `(X \ U, A \ U) ⟶ (X, A)` attached to a CW pair `(X, A)`. -/
abbrev removeSubsetInclusion (P : CWPair) (U : Set (space P))
    (hU : closure U ⊆ interior (subspace P)) :
    removeSubsetPair P U hU ⟶ P :=
  ObjectProperty.homMk (SpacePair.removeSubsetInclusion (toSpacePair P) U)

/-- The endofunctor `(X, A) ↦ (X, ∅)` on `CWPair`. -/
def ambientFunctor : CWPair ⥤ CWPair where
  obj P := absolutePair P
  map f := ObjectProperty.homMk (SpacePair.ambientFunctor.map f.hom)
  map_id := by
    intro P
    apply ObjectProperty.hom_ext
    rfl
  map_comp := by
    intro P Q R f g
    apply ObjectProperty.hom_ext
    rfl

/-- The endofunctor `(X, A) ↦ (A, ∅)` on `CWPair`. -/
def subspaceFunctor : CWPair ⥤ CWPair where
  obj P := subspacePair P
  map f := ObjectProperty.homMk (SpacePair.subspaceFunctor.map f.hom)
  map_id := by
    intro P
    apply ObjectProperty.hom_ext
    rfl
  map_comp := by
    intro P Q R f g
    apply ObjectProperty.hom_ext
    rfl

/-- The natural inclusion `(A, ∅) ⟶ (X, ∅)` over all CW pairs `(X, A)`. -/
def subspaceInclusionNatTrans : subspaceFunctor ⟶ ambientFunctor where
  app P := subspaceInclusion P
  naturality := by
    intro P Q f
    apply ObjectProperty.hom_ext
    apply SpacePair.hom_ext
    ext x
    rfl

/-- The natural comparison `(X, ∅) ⟶ (X, A)` over all CW pairs `(X, A)`. -/
def absoluteToRelativeNatTrans : ambientFunctor ⟶ 𝟭 CWPair where
  app P := absoluteToRelative P
  naturality := by
    intro P Q f
    apply ObjectProperty.hom_ext
    apply SpacePair.hom_ext
    ext x
    rfl

end IsCWPair
