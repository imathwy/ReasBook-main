import Mathlib
import stacks_project.Chap04.Definition_4_40_1

-- Declarations for this item will be appended below by the statement pipeline.

universe v u₁ u₂

namespace CategoryTheory

open Functor
open Functor.Fiber
open FibredCategoryMor

variable {C : Type u₁} [Category.{v} C]

namespace FibredCategoryOver

variable (X : FibredCategoryOver C)

/- Domain-style sampling for Lemma 4.41.1 (2):
- primary domain: fibred categories over a fixed base and evaluation of the hom-category
  `Mor_{Fib/C}(C/U, X)` at the identity slice object `id_U : U/U`.
- inspected owner-level declarations:
  `CategoryTheory.IsFibredInGroupoids (Over.forget U)`,
  `FibredCategoryOver.ofFunctor`,
  `FibredCategoryMor.toFunctor`,
  `FibredCategoryMor.comm`,
  `Fiber.inducedFunctor`,
  `Fiber.fiberInclusion_comp_eq_const`.
- best owner abstraction: the public owner here is the evaluation functor from the hom-category of
  fibred-category morphisms out of the canonical slice owner
  `FibredCategoryOver.ofFunctor (Over.forget U) inferInstance` to the standard
  fibre `X.p.Fiber U`; its construction should factor through the canonical fiber owner
  `Fiber.inducedFunctor`.
- primitive data: the underlying evaluation functor to the total category `X.S` together with the
  proof that its composite with `X.p` is constant at `U`.
- derived API: the fibre-valued evaluation functor and its equivalence instance.

Source/core/bridge triage:
- `source-facing`: `yonedaEvaluationFunctor` and `yonedaEvaluationFunctor_isEquivalence`.
- `core/canonical`: `FibredCategoryOver.ofFunctor`, the ambient owner homs `X ⟶ Y`, and
  `Fiber.inducedFunctor`.
- `bridge/view`: the fibred-in-groupoids specialization in
  `Lemma_4_41_2_2_Yoneda_lemma`. -/

private noncomputable def yonedaEvaluationToTotal (U : C) :
    (FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X) ⥤ X.S :=
  ((fibredCategoryOverSubTwoCategory C).hom (FibredCategoryOver.ofFunctor (Over.forget U)) X).inclusion ⋙
    BasedNatTrans.forgetful _ _ ⋙ (evaluation (Over U) X.S).obj (Over.mk (𝟙 U))

private theorem yonedaEvaluationToTotal_comp_eq_const (U : C) :
    X.yonedaEvaluationToTotal U ⋙ X.p =
      (Functor.const (FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X)).obj U := by
  let hobj :
      ∀ F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X,
        (X.yonedaEvaluationToTotal U ⋙ X.p).obj F = U :=
    fun F ↦ congrArg (fun q ↦ q.obj (Over.mk (𝟙 U))) (FibredCategoryMor.comm F)
  refine Functor.ext hobj ?_
  intro F G τ
  let _ : X.p.IsHomLift (𝟙 U) ((X.yonedaEvaluationToTotal U).map τ) := by
    change X.p.IsHomLift (𝟙 U) ((τ.hom.hom).toNatTrans.app (Over.mk (𝟙 U)))
    exact fibredCategoryMor_hom_isHomLift_id τ (Over.mk (𝟙 U))
  change X.p.map ((X.yonedaEvaluationToTotal U).map τ) =
      eqToHom (hobj F) ≫ 𝟙 U ≫ eqToHom (hobj G).symm
  simpa using IsHomLift.fac' X.p (𝟙 U) ((X.yonedaEvaluationToTotal U).map τ)

/-- Evaluation at the identity object `id_U : U/U` on morphisms of fibred categories
`C/U ⟶ X` over `C`. -/
noncomputable def yonedaEvaluationFunctor (U : C) :
    (FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X) ⥤ X.p.Fiber U :=
  Fiber.inducedFunctor (X.yonedaEvaluationToTotal_comp_eq_const U)

-- Proof sketch: choose pullbacks for `X.p` as in Definition 4.33.6. For `x : X_U`, send an
-- object `f : V ⟶ U` of `C/U` to the chosen pullback `f^*x`; Lemma 4.33.7 supplies the
-- comparison isomorphisms needed for functoriality. One then checks that this construction is
-- inverse, up to natural isomorphism, to evaluation at `id_U`.
/-- Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the evaluation functor
`Mor_{Fib/C}(C/U, X) ⥤ X_U`, sending `G` to `G(id_U)`, is an equivalence. -/
noncomputable instance yonedaEvaluationFunctor_isEquivalence (U : C) :
    (X.yonedaEvaluationFunctor U).IsEquivalence := sorry

end FibredCategoryOver

end CategoryTheory
