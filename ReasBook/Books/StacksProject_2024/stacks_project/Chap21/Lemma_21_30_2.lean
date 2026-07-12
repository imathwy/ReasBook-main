import StacksProject_2024.Chap21.«21_30_0_1»
import StacksProject_2024.Chap21.Situation_21_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C]
variable {τ τ' : GrothendieckTopology C}
variable (P : MorphismProperty C)

/-- The localized comparison subcategory `A_X ⊂ Ab(C_τ / X)` obtained by pulling back `A'_X`
along the topology-comparison direct image `ε_{X,*}`. -/
def comparisonObjectProperty
    (hle : τ' ≤ τ)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u}))
    (X : C) :
    ObjectProperty (Sheaf (τ.over X) AddCommGrpCat.{u}) :=
  (A' X).inverseImage (comparisonTopologyPushforwardAb hle X)

/- Source-facing notation for the pulled-back comparison subcategory `A_X`. -/
scoped notation "A[" hle ", " A' "]_(" X ")" =>
  comparisonObjectProperty hle A' X

open scoped CategoryTheory.GrothendieckTopology

/-- Helper for Lemma 21.30.2: membership in the pulled-back comparison subcategory is exactly
membership after applying the comparison pushforward. -/
@[simp]
theorem comparisonObjectProperty_mem_iff
    (hle : τ' ≤ τ)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u}))
    {X : C} {ℱ : Sheaf (τ.over X) AddCommGrpCat.{u}} :
    A[hle, A']_(X) ℱ ↔ A' X ((comparisonTopologyPushforwardAb hle X).obj ℱ) :=
  Iff.rfl

/-- Lemma 21.30.2: in Situation `21.30.1`, assuming each `A'_X` is closed under isomorphisms,
inverse image along `f_τ^{-1}` sends the pulled-back comparison subcategory `A[hle, A']_(Y)` into
the inverse-image object property of `A[hle, A']_(X)`. This owner-level form is the direct wrapper
around the objectwise pullback statement above. -/
@[stacks 0EZ9]
theorem comparisonObjectProperty_le_inverseImage_overMapPullback
    (hle : τ' ≤ τ)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u}))
    [∀ X : C, ObjectProperty.IsClosedUnderIsomorphisms (A' X)]
    (h : CohomologyComparisonSituation τ τ' P A')
    {X Y : C} (f : X ⟶ Y) :
    A[hle, A']_(Y) ≤
      (A[hle, A']_(X)).inverseImage (τ.overMapPullback AddCommGrpCat.{u} f) := by
  intro ℱ hℱ
  -- View the goal directly on the source-side object properties `A'_Y` and `A'_X`.
  change A' Y ((comparisonTopologyPushforwardAb hle Y).obj ℱ) at hℱ
  change
    A' X
      ((comparisonTopologyPushforwardAb hle X).obj
        ((τ.overMapPullback AddCommGrpCat.{u} f).obj ℱ))
  -- Pull back the source-side membership and transport it across the comparison isomorphism.
  let e :
      (comparisonTopologyPushforwardAb hle X).obj
          ((τ.overMapPullback AddCommGrpCat.{u} f).obj ℱ) ≅
        (τ'.overMapPullback AddCommGrpCat.{u} f).obj
          ((comparisonTopologyPushforwardAb hle Y).obj ℱ) :=
    ((overMapPullbackCompComparisonTopologyPushforward hle f).app ℱ).symm
  exact (A' X).prop_of_iso e (h.inverseImage_mem f hℱ)

end CategoryTheory.GrothendieckTopology
