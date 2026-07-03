import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

/-
Domain-style sampling for Lemma 17.13.3:
- primary domain: finite-type module sheaves on ringed spaces under pushforward along a closed
  embedding;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsFiniteType`,
  `RingedSpace.Hom.pushforward`,
  `RingedSpace.Hom.commRingSheafPushforwardMap`,
  `RingedSpace.IsClosedImmersion`;
- best owner abstraction: the canonical owner predicate `SheafOfModules.IsFiniteType` on the
  direct-image object `(i _*).obj ℱ` inside the owner categories `RingedSpace.Modules Z` and
  `RingedSpace.Modules X`, together with the chapter owner for the structure-sheaf map of `i`;
- primitive data: the morphism `i : Z ⟶ X` and the module sheaf `ℱ`;
- derived API: the source-facing preservation/reflection equivalence for finite type.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that finite type is preserved and reflected by
  pushforward along such a morphism;
- `core/canonical`: `RingedSpace.Modules`, `SheafOfModules.IsFiniteType`, the direct-image
  functor `i _*`, and `RingedSpace.Hom.commRingSheafPushforwardMap`;
- `bridge/view`: the specialization to morphisms whose underlying map is a closed embedding and
  whose structure-sheaf map is locally surjective.

The file should therefore keep the source-facing equivalence, but phrase the closed-immersion
hypothesis using the chapter owner `RingedSpace.IsClosedImmersion` rather than parallel primitive
fields. -/

namespace AlgebraicGeometry

-- Proof sketch: for the forward implication, finite local generators of `ℱ` on opens in `Z`
-- induce finite local generators of `i_* ℱ` on the corresponding opens in `X`, using the closed
-- embedding to identify neighborhoods on the image and the local surjectivity of
-- `𝒪_X ⟶ i_* 𝒪_Z` to lift the module coefficients. For the converse implication, restrict finite
-- local generators of `i_* ℱ` near points of the image back to `Z` and identify stalks along the
-- closed embedding.
/-- Lemma 17.13.3: for a morphism of ringed spaces
`i : (Z, \mathcal O_Z) \to (X, \mathcal O_X)` that is a closed immersion, the pushforward `i_* ℱ`
is of finite type if and only if `ℱ` is of finite type. -/
theorem ringedSpaceModulePushforward_isFiniteType_iff_of_isClosedImmersion
    {X Z : RingedSpace.{u}} (i : Z ⟶ X)
    [RingedSpace.IsClosedImmersion i]
    (ℱ : RingedSpace.Modules Z) :
    ((i _*).obj ℱ).IsFiniteType ↔ ℱ.IsFiniteType := sorry

end AlgebraicGeometry
