import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_4.Quotient
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.SpacePair

open scoped Topology

universe u

noncomputable section

variable {X : Type u} [TopologicalSpace X]

/-- The inclusion `A ↪ X` of a subspace as a continuous map. -/
abbrev subsetInclusion (A : Set X) : C(A, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The canonical quotient map `X ⟶ X / A` sending each point to its collapse class. -/
def collapseSubsetQuotientMap (A : Set X) : C(X, collapseSubsetType X A) :=
  ⟨fun x ↦ Quotient.mk'' x, continuous_quotient_mk'⟩

/-- A chosen representative of the collapsed point in `X / A`, obtained from a witness that
`A` is nonempty. -/
def collapseSubsetPoint (A : Set X) (hA : A.Nonempty) : collapseSubsetType X A :=
  Quotient.mk'' (Classical.choose hA)

/-- Every point of `A` has the same image in `X / A` as the chosen collapsed point. -/
theorem collapseSubsetQuotientMap_eq_point (A : Set X) (hA : A.Nonempty) (a : A) :
    collapseSubsetQuotientMap A a.1 = collapseSubsetPoint A hA := by
  apply Quotient.sound
  apply Relation.EqvGen.rel
  exact Or.inr ⟨a.2, Classical.choose_spec hA⟩

/-- The canonical pair `(X / A, *)`, where `*` is the collapsed point of `A`. -/
abbrev collapseSubsetPair (A : Set X) (hA : A.Nonempty) : SpacePair where
  space := TopCat.of (collapseSubsetType X A)
  subspace := ({collapseSubsetPoint A hA} : Set (collapseSubsetType X A))

/-- The canonical quotient map sends `A` into the singleton collapsed-point subspace of
`collapseSubsetPair A hA`. -/
theorem collapseSubsetQuotientMap_mapsSubspace (A : Set X) (hA : A.Nonempty) :
    ∀ ⦃x : X⦄, x ∈ A →
      collapseSubsetQuotientMap A x ∈ ({collapseSubsetPoint A hA} : Set (collapseSubsetType X A)) :=
  fun {x} hx ↦ by
    simpa using collapseSubsetQuotientMap_eq_point A hA ⟨x, hx⟩

/-- The canonical quotient map induces a map of pairs `(X, A) ⟶ (X / A, *)`. -/
def collapseSubsetPairMap (A : Set X) (hA : A.Nonempty) :
    SpacePair.Hom ⟨TopCat.of X, A⟩ (collapseSubsetPair A hA) where
  hom := TopCat.ofHom (collapseSubsetQuotientMap A)
  map_subspace' := by
    intro x hx
    exact collapseSubsetQuotientMap_mapsSubspace A hA hx
