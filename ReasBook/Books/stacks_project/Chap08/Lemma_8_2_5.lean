import Mathlib
import stacks_project.Chap04.Lemma_4_32_5
import stacks_project.Chap04.Lemma_4_39_6
import stacks_project.Chap04.Lemma_4_41_1_2_Yoneda_lemma_for_fibred_categories
import stacks_project.Chap08.Definition_8_2_2

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Lemma 8.2.5:
- primary domain: categories fibred in setoids over a slice category, together with the presheaf
  of isomorphism classes attached to a fibred-in-setoids projection;
- inspected owner-level declarations:
  `IsFibredInSetoids`,
  `explicitTwoFibreProductLeftProjection`,
  `sliceTwoFibreProductStructuredArrowToFiber_isEquivalence`,
  `Functor.fiberIsoClassPresheaf`,
  `fiberIsomorphismSubfunctor`;
- best owner abstraction: clause `(1)` is source-facing and should stay a public theorem asserting
  that the explicit slice `2`-fibre-product projection is `IsFibredInSetoids`; the stronger
  Chapter 4 owner theorem `explicitTwoFibreProductLeftProjection_isFibredInGroupoids` is not the
  right main abstraction here because it assumes a fibred-in-groupoids target, stronger than the
  source lemma. Clause `(2)` is the bridge identifying the source-facing presheaf `Isom(x, y)`
  with the canonical owner `fiberIsoClassPresheaf` of that projection;
- primitive data: the fibred category `X`, an object `U : C`, and fiber objects `x y : X.p.Fiber U`;
- derived API: the `IsFibredInSetoids` instance on the projection and the presheaf comparison in
  clause `(2)`.

Source/core/bridge triage:
- `source-facing`: `fiberObjectSliceProjection`,
  `fiberObjectSliceProjection_isFibredInSetoids`;
- `core/canonical`: `IsFibredInSetoids` and `Functor.fiberIsoClassPresheaf`;
- `bridge/view`: `fiberIsomorphismSubfunctor_toFunctor_eq_fiberIsoClassPresheaf`. -/

open Opposite

universe u v uS

namespace CategoryTheory

open CategoryOver
open Functor

variable {C : Type u} [Category.{v} C]

namespace FibredCategoryOver

/-- The canonical slice `2`-fibre-product projection over `C/U` attached to two objects
`x, y ∈ X_U`, obtained as the left projection from the explicit `2`-fibre product of the
pullback-model `2`-Yoneda morphisms `C/U ⟶ X` corresponding to `x` and `y`. -/
noncomputable def fiberObjectSliceProjection
    (X : FibredCategoryOver C) {U : C} (x y : X.p.Fiber U) :
    (explicitTwoFibreProduct
      (((X.yonedaEvaluationFunctor U).asEquivalence.inverse.obj x).toHom)
      (((X.yonedaEvaluationFunctor U).asEquivalence.inverse.obj y).toHom)).obj ⥤ Over U :=
  let Gx : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ X.toBasedCategory :=
    ((X.yonedaEvaluationFunctor U).asEquivalence.inverse.obj x).toHom
  let Gy : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ X.toBasedCategory :=
    ((X.yonedaEvaluationFunctor U).asEquivalence.inverse.obj y).toHom
  show
      (explicitTwoFibreProduct Gx Gy).obj ⥤ Over U from
    (explicitTwoFibreProductLeftProjection Gx Gy).toFunctor

section

variable (X : FibredCategoryOver C) {U : C} (x y : X.p.Fiber U)

-- Proof sketch: over an object `f : V ⟶ U` of the slice category, Lemma `4.42.1` identifies the
-- corresponding fiber with a structured-arrow category whose source fiber in `C/U` is thin. Hence
-- any two morphisms in that fiber agree.
/-- Every standard fiber of the canonical slice `2`-fibre-product projection for `x` and `y` is a
setoid `1`-category. -/
private theorem fiberObjectSliceProjection_fiber_isThin
    (f : Over U) :
    Quiver.IsThin ((X.fiberObjectSliceProjection x y).Fiber f) := by
  sorry

/-- Lemma 8.2.5 (1): for objects `x` and `y` in the fiber `S_U` of a fibred category `p : S ⥤ C`,
the explicit `2`-fibre product over `C/U` of the corresponding pullback-model `2`-Yoneda
morphisms is fibred in setoids over `C/U`. -/
theorem fiberObjectSliceProjection_isFibredInSetoids :
    IsFibredInSetoids (X.fiberObjectSliceProjection x y) := by
  let p := X.fiberObjectSliceProjection x y
  letI : ∀ f : Over U, Quiver.IsThin (p.Fiber f) :=
    fiberObjectSliceProjection_fiber_isThin X x y
  change IsFibredInSetoids p
  letI : IsFibredInGroupoids p := by
    sorry
  infer_instance

instance :
    IsFibredInSetoids (X.fiberObjectSliceProjection x y) :=
  fiberObjectSliceProjection_isFibredInSetoids X x y

/-- Lemma 8.2.5 (2): the underlying presheaf of the canonical subpresheaf `Isom(x, y)` from
Definition `8.2.2` is the presheaf of isomorphism classes attached to the fibred-in-setoids
projection from part `(1)`, after the canonical universe lift from `Type v` to `Type (max u v)`. -/
theorem fiberIsomorphismSubfunctor_toFunctor_eq_fiberIsoClassPresheaf
    :
    (fiberIsomorphismSubfunctor X.p x y).toFunctor ⋙ uliftFunctor.{u, v} =
      (X.fiberObjectSliceProjection x y).fiberIsoClassPresheaf := by
  sorry

end

end FibredCategoryOver

end CategoryTheory
