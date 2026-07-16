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

-- Semantic recall: `lean_leansearch` did not surface a ready-made owner for the generic-point local
-- ring comparison over a base scheme, so the statement keeps the local Chapter 29 owner
-- `BirationalOver` and adds the source-faithful generic-point stalk clause explicitly.

/-- The generic-point local rings of two irreducible `S`-schemes are isomorphic over a common image
point of `S`. -/
abbrev GenericPointLocalRingIsoOver
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S] [IrreducibleSpace X] [IrreducibleSpace Y] : Prop :=
  ∃ (s : S) (hx : (X ↘ S) (genericPoint X) = s) (hy : (Y ↘ S) (genericPoint Y) = s)
    (e : X.presheaf.stalk (genericPoint X) ≅ Y.presheaf.stalk (genericPoint Y)),
      ((S.presheaf.stalkCongr (.of_eq hx.symm)).hom ≫ (X ↘ S).stalkMap (genericPoint X)) ≫ e.hom =
        (S.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫ (Y ↘ S).stalkMap (genericPoint Y)

/-- Lemma 29.50.6: let `S` be a scheme and let `X` and `Y` be irreducible schemes locally of finite
presentation over `S`. Then the following are equivalent: `X` and `Y` are `S`-birational, there
exist nonempty opens of `X` and `Y` which are isomorphic over `S`, and the generic points of `X`
and `Y` have the same image `s : S` while the local rings `𝒪_{X,η_X}` and `𝒪_{Y,η_Y}` are
isomorphic over `𝒪_{S,s}`. -/
@[stacks 0BAD]
theorem birationalOver_tfae_of_locallyOfFinitePresentation
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y]
    [LocallyOfFinitePresentation (X ↘ S)] [LocallyOfFinitePresentation (Y ↘ S)] :
    List.TFAE
      [ BirationalOver S X Y
      , HasIsomorphicNonemptyOpenSubschemesOver S X Y
      , GenericPointLocalRingIsoOver S X Y
      ] := sorry

end AlgebraicGeometry
