import StacksProject_2024.stacks_project.Chap20.«20_14_1_1»
import StacksProject_2024.stacks_project.Chap20.Sections_on_open

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open scoped RingedSpaceDerivedGlobalSections RingedSpaceDerivedPushforward

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.32.5:
- primary domain: derived sections on inverse-image opens and derived pushforward for sheaves of
  modules on ringed spaces;
- sampled owner declarations:
  `RingedSpace.preimageOpen`,
  `sectionsMapOnOpen`,
  `moduleSectionsRestrictionFunctor`,
  `moduleDerivedSectionsAtOpen`,
  `moduleDerivedPushforward`;
- best owner abstraction:
  `source-facing`: the comparison between `RΓ(f⁻¹(V), -)`, viewed over `Γ(V, 𝒪_Y)` by
    restriction of scalars, and `RΓ(V, -) ∘ Rf_*`;
  `core/canonical`: the chapter owners `moduleSectionsRestrictionFunctor`,
    `moduleDerivedSectionsAtOpen`, and `moduleDerivedPushforward`;
  `bridge/view`: the present functor `moduleDerivedSectionsAtPreimageViaRestriction`, which is the
    source-facing comparison built from those canonical owners;
- primitive data: a morphism `f : X ⟶ Y` and an open subset `V ⊆ Y`;
- derived API: the comparison isomorphisms in this file.

This file should therefore stay at the `bridge/view` layer and reuse the upstream section-ring and
restriction-of-scalars owners from `Sections_on_open` instead of rebuilding parallel local copies.
-/

/-- The functor `RΓ(f⁻¹(V), -)` viewed in `D(Γ(V, 𝒪_Y))` via restriction of scalars. -/
abbrev moduleDerivedSectionsAtPreimageViaRestriction (f : X ⟶ Y) (V : Opens Y.carrier) :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat (sectionsRingOnOpen Y V)) :=
  moduleDerivedSectionsAtOpen X (preimageOpen f V) ⋙ moduleSectionsRestrictionDerived f V

-- Proof sketch: first use Lemma `20.32.4` to identify the restriction of `Rf_*` to `V` with the
-- derived pushforward for the restricted morphism `f⁻¹(V) ⟶ V`. Then apply Lemma `20.28.2` to
-- compose this restricted derived pushforward with derived global sections on `V`, obtaining the
-- same functor as derived sections on `f⁻¹(V)`, viewed over `Γ(V, 𝒪_Y)` by
-- restriction of scalars.
/-- Lemma 20.32.5: for a morphism of ringed spaces `f : X ⟶ Y` and an open subset `V ⊆ Y`, with
`U = f⁻¹(V)`, the functor `RΓ(U, -)` viewed in `D(Γ(V, 𝒪_Y))` via restriction of scalars is
isomorphic to `RΓ(V, -) ∘ Rf_*`. -/
@[stacks 0D5W]
theorem moduleDerivedSectionsAtPreimageViaRestriction_isomorphic_pushforward_comp
    (f : X ⟶ Y) (V : Opens Y.carrier) :
    IsIsomorphic
      (moduleDerivedSectionsAtPreimageViaRestriction f V)
      (R(f)_* ⋙ moduleDerivedSectionsAtOpen Y V) := sorry

-- Proof sketch: specialize
-- `moduleDerivedSectionsAtPreimageViaRestriction_isomorphic_pushforward_comp` to `V = ⊤`, where
-- `Γ(⊤, 𝒪_Y) = Γ(Y, 𝒪_Y)` and `f⁻¹(⊤) = X`.
/-- The global-sections case of the preimage comparison, viewed over `Γ(Y, 𝒪_Y)`. -/
theorem moduleDerivedGlobalSectionsViaRestriction_isomorphic_pushforward_comp
    (f : X ⟶ Y) :
    IsIsomorphic
      (moduleDerivedSectionsAtPreimageViaRestriction f ⊤)
      (R(f)_* ⋙ RΓ(Y)) := by
  simpa using
    moduleDerivedSectionsAtPreimageViaRestriction_isomorphic_pushforward_comp
      f ⊤

end AlgebraicGeometry.RingedSpace
