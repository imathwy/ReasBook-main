import StacksProject_2024.stacks_project.Chap34.Lemma_34_4_17

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced `isCocontinuous_comp`,
-- `Functor.isContinuous_comp`, and the site-theoretic morphism-of-topoi owners. Local Chapter 34
-- precedent in Lemma 34.3.18 fixes the source-facing surface as equality of the bundled big and
-- small morphisms of topoi under `MorphismOfTopoiIn.comp`.

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Lemma 34.4.18 (1): for composable morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`, the
associated big étale morphisms of topoi satisfy `g_big ∘ f_big = (g ∘ f)_big`. -/
@[stacks 021J]
theorem bigEtaleMorphismOfTopoi_comp :
    MorphismOfTopoiIn.comp (bigEtaleMorphismOfTopoi g) (bigEtaleMorphismOfTopoi f) =
      bigEtaleMorphismOfTopoi (f ≫ g) := sorry

/-- Lemma 34.4.18 (2): for composable morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`, the
associated small étale morphisms of topoi satisfy `g_small ∘ f_small = (g ∘ f)_small`. -/
@[stacks 021J]
theorem smallEtaleMorphismOfTopoi_comp :
    MorphismOfTopoiIn.comp (smallEtaleMorphismOfTopoi g) (smallEtaleMorphismOfTopoi f) =
      smallEtaleMorphismOfTopoi (f ≫ g) := sorry

end AlgebraicGeometry.Scheme
