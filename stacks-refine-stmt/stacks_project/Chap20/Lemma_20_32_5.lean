import Mathlib
import stacks_project.Chap20.Lemma_20_32_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/-- The underlying continuous map of a morphism of ringed spaces. -/
abbrev baseMap (f : X ⟶ Y) : X.carrier ⟶ Y.carrier :=
  f.hom.base

/-- The morphism of structure sheaves attached to a morphism of ringed spaces. -/
abbrev structureSheafHom (f : X ⟶ Y) :=
  f.hom.c

/-- The inverse-image open subset `f^{-1}(V)` attached to `V ⊆ Y`. -/
abbrev preimageOpen (f : X ⟶ Y) (V : Opens Y.carrier) : Opens X.carrier :=
  Opens.comap (baseMap f).hom V

/-- The map on section rings over an open subset induced by a morphism of ringed spaces. -/
abbrev sectionsMapOnOpen (f : X ⟶ Y) (V : Opens Y.carrier) :
    sectionsRingOnOpen Y V ⟶ sectionsRingOnOpen X (preimageOpen f V) :=
  (structureSheafHom f).app (Opposite.op V)

/-- Restriction of scalars along the map `Γ(V, \mathcal O_Y) → Γ(f^{-1}(V), \mathcal O_X)`. -/
abbrev moduleSectionsRestrictionFunctor (f : X ⟶ Y) (V : Opens Y.carrier) :
    ModuleCat (sectionsRingOnOpen X (preimageOpen f V)) ⥤
      ModuleCat (sectionsRingOnOpen Y V) :=
  ModuleCat.restrictScalars (sectionsMapOnOpen f V).hom

/-- Restriction of scalars on section modules is additive. -/
instance moduleSectionsRestrictionFunctor_additive (f : X ⟶ Y) (V : Opens Y.carrier) :
    (moduleSectionsRestrictionFunctor f V).Additive := by
  infer_instance

/-- Restriction of scalars on derived categories along the map
`Γ(V, \mathcal O_Y) → Γ(f^{-1}(V), \mathcal O_X)`. -/
abbrev moduleSectionsRestrictionExactFunctor (f : X ⟶ Y) (V : Opens Y.carrier) :
    ModuleCat (sectionsRingOnOpen X (preimageOpen f V)) ⥤ₑ
      ModuleCat (sectionsRingOnOpen Y V) :=
  ExactFunctor.of (moduleSectionsRestrictionFunctor f V)

/-- Restriction of scalars on derived categories along the map
`Γ(V, \mathcal O_Y) → Γ(f^{-1}(V), \mathcal O_X)`. -/
abbrev moduleSectionsRestrictionDerivedFunctor (f : X ⟶ Y) (V : Opens Y.carrier) :
    DerivedCategory (ModuleCat (sectionsRingOnOpen X (preimageOpen f V))) ⥤
      DerivedCategory (ModuleCat (sectionsRingOnOpen Y V)) :=
  let _ : (moduleSectionsRestrictionExactFunctor f V).obj.Additive :=
    moduleSectionsRestrictionFunctor_additive f V
  (moduleSectionsRestrictionExactFunctor f V).obj.mapDerivedCategory

/-- The functor `RΓ(f^{-1}(V), -)` viewed in `D(Γ(V, \mathcal O_Y))` via restriction of
scalars. -/
abbrev moduleDerivedSectionsAtPreimageViaRestriction (f : X ⟶ Y) (V : Opens Y.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (ModuleCat (sectionsRingOnOpen Y V)) :=
  moduleDerivedSectionsAtOpen X (preimageOpen f V) ⋙
    moduleSectionsRestrictionDerivedFunctor f V

-- Proof sketch: first use Lemma `20.32.4` to identify the restriction of `Rf_*` to `V` with the
-- derived pushforward for the restricted morphism `f^{-1}(V) → V`. Then apply Lemma `20.28.2` to
-- compose this restricted derived pushforward with derived global sections on `V`, obtaining the
-- same functor as derived sections on `f^{-1}(V)`, viewed over `Γ(V, \mathcal O_Y)` by
-- restriction of scalars.
/-- Lemma 20.32.5: for a morphism of ringed spaces `f : X ⟶ Y` and an open subset `V ⊆ Y`, with
`U = f^{-1}(V)`, the functor `RΓ(U, -)` viewed in `D(Γ(V, \mathcal O_Y))` via restriction of
scalars is isomorphic to `RΓ(V, -) ∘ Rf_*`. -/
theorem moduleDerivedSectionsAtPreimageViaRestriction_iso_pushforward_comp
    (f : X ⟶ Y) (V : Opens Y.carrier) :
    IsIsomorphic
      (moduleDerivedSectionsAtPreimageViaRestriction f V)
      (moduleDerivedPushforward f ⋙ moduleDerivedSectionsAtOpen Y V) := sorry

-- Proof sketch: specialize
-- `moduleDerivedSectionsAtPreimageViaRestriction_iso_pushforward_comp` to `V = ⊤`, where
-- `Γ(⊤, \mathcal O_Y) = Γ(Y, \mathcal O_Y)` and `f^{-1}(⊤) = X`.
/-- The global-sections case of the preimage comparison, viewed over `Γ(Y, \mathcal O_Y)`. -/
theorem moduleDerivedGlobalSectionsViaRestriction_iso_pushforward_comp
    (f : X ⟶ Y) :
    IsIsomorphic
      (moduleDerivedSectionsAtPreimageViaRestriction f ⊤)
      (moduleDerivedPushforward f ⋙ moduleDerivedGlobalSections Y) := sorry

end AlgebraicGeometry.RingedSpace
