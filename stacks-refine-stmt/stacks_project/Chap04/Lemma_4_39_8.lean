import stacks_project.Chap04.Definition_4_31_2
import stacks_project.Chap04.Lemma_4_39_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open FibredInSetoidsOver

variable {C : Type u} [Category.{v} C]
variable {X Y Z : FibredInSetoidsOver C}
variable {F : X ⟶ Y} {G : Z ⟶ Y}

/-
Domain-style sampling:
- primary domain: categories fibred in setoids over a fixed base, bicategorical `2`-fibre
  product squares between them, and the presheaves of fiberwise isomorphism classes attached to
  such objects;
- inspected owner-level declarations:
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`,
  `fibredInSetoidsToPresheaf`,
  `FibredInSetoidsOver.hom_isoClasses_equiv_presheafHom`,
  `IsPullback`;
- best owner abstraction: the main statement should live at the canonical presheaf pullback level,
  namely `IsPullback` for the square obtained by applying `fibredInSetoidsToPresheaf` to a chosen
  bicategorical `2`-fibre product square;
- primitive data: the two owner morphisms `F : X ⟶ Y` and `G : Z ⟶ Y`, together with a chosen
  square `P : BicategoricalTwoCommutativeSquare F G`;
- derived API: the projection morphisms of `P` and the induced presheaf morphisms obtained by
  functoriality of `fibredInSetoidsToPresheaf`.

Source/core/bridge triage:
- `source-facing`: the textbook claim that iso-classes of a chosen fibred `2`-fibre product form
  the pullback presheaf;
- `core/canonical`: `Bicategory.IsFinal`, `FibredInSetoidsOver.hom_isoClasses_equiv_presheafHom`,
  and the target owner `IsPullback` in the presheaf category;
- `bridge/view`: the projections of a chosen square `P : BicategoricalTwoCommutativeSquare F G`,
  whose images under `fibredInSetoidsToPresheaf` form the pullback square. -/
namespace FibredInSetoidsOver

-- Proof sketch: identify sections of the presheaf attached to a chosen bicategorical
-- `2`-fibre product square over each `U : C` with compatible pairs of isomorphism classes in the
-- fibers of `X` and `Z` over the common class in the fiber of `Y`; setoidness of the fibers
-- makes the comparison from the invertible `2`-morphism `P.ψ` collapse to equality on
-- isomorphism classes, and the finality of `P` gives the pullback universal property.
/-- Lemma 4.39.8: if `P` is a bicategorical `2`-fibre product square of morphisms of categories
fibred in setoids, then the presheaf of isomorphism classes associated to its apex is the
pullback of the presheaves associated to the two factors over the presheaf associated to the
base. -/
lemma isoClasses_presheaf_isPullback_of_isFinal
    (P : BicategoricalTwoCommutativeSquare F G) (hP : Bicategory.IsFinal P) :
    IsPullback
      (fibredInSetoidsToPresheaf.map P.p)
      (fibredInSetoidsToPresheaf.map P.q)
      (fibredInSetoidsToPresheaf.map F)
      (fibredInSetoidsToPresheaf.map G) := by
  letI := hP
  sorry

end FibredInSetoidsOver

end CategoryTheory
