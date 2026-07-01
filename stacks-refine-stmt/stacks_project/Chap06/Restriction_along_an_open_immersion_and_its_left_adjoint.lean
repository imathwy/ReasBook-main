import Mathlib

open CategoryTheory TopologicalSpace Opposite
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe u

/-- The functor on open subsets induced by the inclusion of an open subset `U ⊆ X`. -/
private abbrev openSubspaceInclusionFunctor {X : TopCat.{u}} (U : Opens X) :
    Opens ((toTopCat X).obj U) ⥤ Opens X :=
  let h := U.isOpenEmbedding
  h.isOpenMap.functor

/-- Restriction of a presheaf of types on `X` to an open subset `U`, given by precomposition with
the inclusion of opens of `U` into opens of `X`. -/
abbrev presheafRestrictionToOpen {X : TopCat.{u}} (U : Opens X) :
    X.Presheaf (Type u) ⥤ ((toTopCat X).obj U).Presheaf (Type u) :=
  (Functor.whiskeringLeft _ _ (Type u)).obj (openSubspaceInclusionFunctor U).op

-- Proof sketch: an open embedding induces a continuous functor on opens, and precomposing a sheaf
-- with that functor again satisfies the sheaf condition on the smaller space.
/-- The explicit restriction of a sheaf to an open subset is again a sheaf. -/
theorem presheafRestrictionToOpen_isSheaf {X : TopCat.{u}} (U : Opens X)
    (F : X.Sheaf (Type u)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ((toTopCat X).obj U))
      ((presheafRestrictionToOpen U).obj F.1) := sorry

/-- Restriction along an open immersion and its left adjoint: the restriction functor `j^{-1}` for
an open subset `U ⊆ X` is given by precomposing a sheaf on `X` with the inclusion of opens of `U`
into opens of `X`. -/
def sheafRestrictionToOpen {X : TopCat.{u}} (U : Opens X) :
    X.Sheaf (Type u) ⥤ ((toTopCat X).obj U).Sheaf (Type u) where
  obj F := ⟨(presheafRestrictionToOpen U).obj F.1, presheafRestrictionToOpen_isSheaf U F⟩
  map α := ⟨(presheafRestrictionToOpen U).map α.1⟩

-- Proof sketch: the explicit restriction functor is induced by the open-embedding adjunction on
-- opens, and for sheaves of types the corresponding inverse-image functor along an open embedding
-- has a left adjoint given by extension by empty.
/-- Restriction of sheaves of types to an open subset is a right adjoint. -/
theorem sheafRestrictionToOpen_isRightAdjoint {X : TopCat.{u}} (U : Opens X) :
    (sheafRestrictionToOpen U).IsRightAdjoint := sorry

/-- Extension by empty along the inclusion `U ↪ X`, defined as the chosen left adjoint to
`sheafRestrictionToOpen U`. This is the `j_!` functor for sheaves of types. -/
noncomputable abbrev sheafExtensionByEmptyToOpen {X : TopCat.{u}} (U : Opens X) :
    ((toTopCat X).obj U).Sheaf (Type u) ⥤ X.Sheaf (Type u) :=
  letI : (sheafRestrictionToOpen U).IsRightAdjoint := sheafRestrictionToOpen_isRightAdjoint U
  (sheafRestrictionToOpen U).leftAdjoint

/-- The extension-by-empty functor is left adjoint to restriction to the open subset. -/
noncomputable abbrev sheafExtensionByEmptyToOpen_adjunction {X : TopCat.{u}} (U : Opens X) :
    sheafExtensionByEmptyToOpen U ⊣ sheafRestrictionToOpen U :=
  letI : (sheafRestrictionToOpen U).IsRightAdjoint := sheafRestrictionToOpen_isRightAdjoint U
  Adjunction.ofIsRightAdjoint (sheafRestrictionToOpen U)
