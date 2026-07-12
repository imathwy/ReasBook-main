import Mathlib
import StacksProject_2024.Chap07.Lemma_7_21_1
import StacksProject_2024.Chap34.Lemma_34_7_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped MorphismOfTopoiIn

universe u

noncomputable section

namespace AlgebraicGeometry
namespace Scheme

variable {S T X Y Z : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced `MorphismOfTopoiIn.comp`,
-- `Functor.morphismOfTopoiInOfCocontinuous`, and `Over.mapComp_eq`; local Chapter 34 precedent
-- in the big Zariski and big étale files fixes the source-facing owner as the bundled big-site
-- morphism of topoi attached to `Over.map`.

/-- The big fppf morphism of topoi attached to `f`, presented cocontinuously by `Over.map f`. -/
abbrev bigFppfMorphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn (Scheme.fppfTopology.over S) (Scheme.fppfTopology.over T) :=
  (Over.map f).morphismOfTopoiInOfCocontinuous
    (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S)

@[simp] theorem bigFppfMorphismOfTopoi_pushforward (f : T ⟶ S) :
    (bigFppfMorphismOfTopoi f) _* = bigFppfDirectImage f := by
  simpa [bigFppfDirectImage] using
    (Functor.morphismOfTopoiInOfCocontinuous_pushforward
      (Over.map f) (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S))

/-- Lemma 34.7.13: for composable morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`, the
associated big fppf morphisms of topoi satisfy `g_big ∘ f_big = (g ∘ f)_big`. -/
@[stacks 021X]
theorem bigFppfMorphismOfTopoi_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    MorphismOfTopoiIn.comp (bigFppfMorphismOfTopoi g) (bigFppfMorphismOfTopoi f) =
      bigFppfMorphismOfTopoi (f ≫ g) := sorry

end Scheme
end AlgebraicGeometry
