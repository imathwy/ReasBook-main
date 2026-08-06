import Mathlib.Tactic.Recall
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Construction_14_6_3

open CategoryTheory CategoryTheory.Limits

universe u v

/- Remark 14.6.5: the telescope attached to a sequence `X₀ ⟶ X₁ ⟶ X₂ ⟶ ⋯` is formalized here by
`topologicalTelescope`, while `ContinuousMap.doubleMappingCylinder` gives the analogous parallel
gluing construction. The ordinary categorical coequalizer API records the same parallel-pair
colimit pattern that underlies homotopy coequalizers. -/
recall topologicalTelescope
    {X : ℕ → Type u} [∀ i, TopologicalSpace (X i)]
    (f : ∀ i : ℕ, C(X i, X (i + 1))) : TopCat

recall ContinuousMap.doubleMappingCylinder
    {A B C : Type u} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (i : C(C, A)) (j : C(C, B)) : TopCat

/- The double mapping cylinder is the pushout of its attaching and boundary maps. -/
recall ContinuousMap.doubleMappingCylinder_def
    {A B C : Type u} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (i : C(C, A)) (j : C(C, B)) :
    ContinuousMap.doubleMappingCylinder i j =
      pushout (TopCat.ofHom (ContinuousMap.doubleMappingCylinderAttachMap i j))
        (TopCat.ofHom (ContinuousMap.doubleMappingCylinderBoundaryMap C))

/- The ordinary categorical coequalizer is the colimit of a parallel pair. -/
recall coequalizerIsCoequalizer
    {C : Type u} [Category.{v} C] {X Y : C} (p q : X ⟶ Y) [HasCoequalizer p q] :
    IsColimit (Cofork.ofπ (coequalizer.π p q) (coequalizer.condition p q))
