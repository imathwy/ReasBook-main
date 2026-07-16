import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap29.Definition_29_49_11
import StacksProject_2024.stacks_project.Chap29.Lemma_29_49_12

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: no `lean_leansearch` tool was available in this runner, so the owner/API
-- choices were verified locally against `BirationalOver` in `Definition_29_49_11`,
-- `birationalOver_iff_exists_isomorphic_nonemptyOpens` in `Lemma_29_49_12`, and the analogous
-- generic-point over-`S` packaging in `Lemma_29_50_6`.

/-- The residue fields of two points of `S`-schemes are isomorphic over `S` when the corresponding
field-valued points of `S` are isomorphic in `Over S`. -/
abbrev GenericPointResidueFieldIsoOver
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S] (x : X) (y : Y) : Prop :=
  Nonempty
    (Over.mk (X.fromSpecResidueField x ≫ (X ↘ S)) ≅
      Over.mk (Y.fromSpecResidueField y ≫ (Y ↘ S)))

/-- Unfold `GenericPointResidueFieldIsoOver` as an isomorphism in `Over S` between the corresponding
field-valued points. -/
theorem genericPointResidueFieldIsoOver_iff
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S] (x : X) (y : Y) :
    GenericPointResidueFieldIsoOver S X Y x y ↔
      Nonempty
        (Over.mk (X.fromSpecResidueField x ≫ (X ↘ S)) ≅
          Over.mk (Y.fromSpecResidueField y ≫ (Y ↘ S))) := sorry

/-- Lemma 29.50.7: let `S` be a scheme, let `X` and `Y` be integral schemes locally of finite type
over `S`, and let `x ∈ X` and `y ∈ Y` be generic points. Then the following are equivalent:
`X` and `Y` are `S`-birational, there exist nonempty opens of `X` and `Y` which are isomorphic
over `S`, and `x` and `y` have isomorphic residue fields over `S` (equivalently, they map to the
same point `s ∈ S` and `κ(x) ≅ κ(y)` as `κ(s)`-extensions). -/
@[stacks 0552]
theorem birationalOver_tfae_of_isIntegral_of_locallyOfFiniteType
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType (X ↘ S)] [LocallyOfFiniteType (Y ↘ S)]
    (x : X) (y : Y)
    (hx : IsGenericPoint x (Set.univ : Set X))
    (hy : IsGenericPoint y (Set.univ : Set Y)) :
    List.TFAE
      [ BirationalOver S X Y
      , HasIsomorphicNonemptyOpenSubschemesOver S X Y
      , GenericPointResidueFieldIsoOver S X Y x y
      ] := sorry
#min_imports
end AlgebraicGeometry
