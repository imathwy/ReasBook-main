import StacksProject_2024.stacks_project.Chap29.Definition_29_49_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` returned only general rational-map/open-immersion API, so the
-- statement owner was fixed from the local project definitions `Birational` and `BirationalOver`
-- in `Definition_29_49_11`.

/-- The open subscheme `U ⊆ X` viewed as an object of `Over S`. -/
abbrev openSubschemeOver
    (S X : Scheme) [X.Over S] (U : X.Opens) : Over S :=
  Over.mk (U.ι ≫ (X ↘ S))

/-- There exist nonempty open subschemes of `X` and `Y` that are isomorphic. -/
def HasIsomorphicNonemptyOpenSubschemes (X Y : Scheme) : Prop :=
  ∃ U : X.Opens, ∃ V : Y.Opens, Nonempty U ∧ Nonempty V ∧ IsIsomorphic U.toScheme V.toScheme

/-- There exist nonempty open subschemes of `X` and `Y` that are isomorphic over `S`. -/
def HasIsomorphicNonemptyOpenSubschemesOver
    (S X Y : Scheme) [X.Over S] [Y.Over S] : Prop :=
  ∃ U : X.Opens, ∃ V : Y.Opens,
    Nonempty U ∧ Nonempty V ∧
      IsIsomorphic (openSubschemeOver S X U) (openSubschemeOver S Y V)

/-- Lemma 29.49.12 (1): irreducible schemes `X` and `Y` are birational if and only if there exist
nonempty opens `U ⊆ X` and `V ⊆ Y` whose associated open subschemes are isomorphic. -/
@[stacks 0BAA]
theorem birational_iff_exists_isomorphic_nonemptyOpens
    (X Y : Scheme) [IrreducibleSpace X] [IrreducibleSpace Y] :
    Birational X Y ↔ HasIsomorphicNonemptyOpenSubschemes X Y := sorry

/-- Lemma 29.49.12 (2): for irreducible schemes over `S`, `X` and `Y` are `S`-birational if and
only if there exist nonempty opens `U ⊆ X` and `V ⊆ Y` whose associated open subschemes are
isomorphic over `S`. -/
@[stacks 0BAA]
theorem birationalOver_iff_exists_isomorphic_nonemptyOpens
    (S X Y : Scheme) [X.Over S] [Y.Over S] [IrreducibleSpace X] [IrreducibleSpace Y] :
    BirationalOver S X Y ↔ HasIsomorphicNonemptyOpenSubschemesOver S X Y := sorry

end AlgebraicGeometry
