import Mathlib.CategoryTheory.Functor.Derived.RightDerived

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

section

variable {C : Type u₁} {D : Type u₂} {DE : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} DE]

-- Semantic recall hits:
-- `Functor.totalRightDerived`, `Functor.totalRightDerivedUnit`, and
-- `Functor.HasRightDerivedFunctor`.
--
-- Source/core/bridge triage:
-- * source-facing: the generic Chapter `22` right-derived-Hom owner `RHom[Q, W](homK)` along a
--   localization `Q`;
-- * core/canonical: `Functor.totalRightDerived`.

/-- Lemma 22.32.1: the Chapter `22` derived-Hom functor `RHom[Q, W](homK)` attached to
`homK : C ⥤ DE` along a
localization functor `Q : C ⥤ D`. This is the source-facing owner built from the canonical total
right derived functor of `homK`. -/
@[stacks 09LK]
abbrev derivedHom (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (homK : C ⥤ DE) [homK.HasRightDerivedFunctor W] :
    D ⥤ DE :=
  homK.totalRightDerived Q W

/- Source notation for the Chapter `22` derived-Hom functor. -/
scoped notation:max "RHom[" Q ", " W "](" homK ")" =>
  CategoryTheory.derivedHom Q W homK

/-- The canonical comparison from `homK` to `RHom[Q, W](homK)`. -/
abbrev derivedHomUnit (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (homK : C ⥤ DE) [homK.HasRightDerivedFunctor W] :
    homK ⟶ Q ⋙ (RHom[Q, W](homK) : D ⥤ DE) :=
  homK.totalRightDerivedUnit Q W

end

end CategoryTheory
