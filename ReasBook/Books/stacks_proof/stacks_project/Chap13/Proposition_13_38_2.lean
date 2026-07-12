import Mathlib
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Triangulated.Yoneda
import StacksProject_2024.Chap13.Lemma_13_38_1
import StacksProject_2024.Chap13.Definition_13_3_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped Pretriangulated.Opposite

noncomputable section

universe v u₁ u₂

namespace CategoryTheory

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v} D] [Category.{v} D']
  [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [IsTriangulated D] [IsTriangulated D']
  [HasCoproducts.{max u₁ v} D]
  (hD : IsCompactlyGenerated D)

/- Domain-style sampling for Proposition 13.38.2:
- primary domain: Brown representability and adjunction criteria for exact functors between
  triangulated categories;
- sampled owner declarations:
  `brown_representability_isRepresentable`,
  `Functor.isLeftAdjoint_of_objwise_hom_isRepresentable`,
  `Adjunction.ofIsLeftAdjoint`,
  `Adjunction.isTriangulated_rightAdjoint`;
- best owner abstraction:
  `F.IsLeftAdjoint` for the left-adjoint existence statement and `F.rightAdjoint.IsTriangulated`
  for the exactness of the chosen right adjoint;
- primitive data: the functor `F`, the compact-generation hypothesis `hD`, exactness
  `[F.IsTriangulated]`, and coproduct preservation;
- derived API: the chosen adjunction `Adjunction.ofIsLeftAdjoint F`, its induced right-adjoint
  shift compatibility, and the resulting exactness instance on `F.rightAdjoint`.

Source/core/bridge triage:
- `source-facing`: the two theorems below, which keep the compact-generation hypothesis explicit;
- `core/canonical`: `brown_representability_isRepresentable`,
  `Functor.isLeftAdjoint_of_objwise_hom_isRepresentable`, and
  `Adjunction.isTriangulated_rightAdjoint`;
- `bridge/view`: the chosen adjunction `Adjunction.ofIsLeftAdjoint F` together with
  `Adjunction.rightAdjointCommShift` and `Adjunction.commShift_of_leftAdjoint`.
-/

-- Proof sketch: for each `Y : D'`, apply the canonical Brown-representability bridge
-- `brown_representability_isRepresentable` to the contravariant cohomological functor
-- `W ↦ Hom(F(W), Y)`. Exactness of `F` makes this functor homological, and preservation of direct
-- sums by `F` turns coproducts in `D` into products in `AddCommGrpCat`. The resulting objectwise
-- representability hypothesis is exactly the input for the owner criterion
-- `F.isLeftAdjoint_of_objwise_hom_isRepresentable`.
/-- Helper for Proposition 13.38.2: for fixed `Y`, the contravariant Hom functor
`W ↦ Hom_D'(F(W), Y)` is cohomological. -/
lemma objwise_hom_functor_rightOp_is_homological
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] (Y : D') :
    ((F.op ⋙ preadditiveYoneda.obj Y).rightOp).IsHomological := by
  -- Route correction: the relevant owner instance lives first on the opposite-valued functor
  -- `F.op ⋙ preadditiveYoneda.obj Y`, and `Definition 13.3.5` then transports it to `rightOp`.
  haveI : (F.op ⋙ preadditiveYoneda.obj Y).IsHomological := by
    infer_instance
  -- The chapter bridge from homologicality on `Dᵒᵖ` to cohomologicality on `D` is now immediate.
  infer_instance

/-- Helper for Proposition 13.38.2: for fixed `Y`, the contravariant Hom functor
`W ↦ Hom_D'(F(W), Y)` sends direct sums in `D` to products. -/
lemma objwise_hom_functor_preserves_discrete_limits
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v), PreservesColimitsOfShape (Discrete J) F]
    (Y : D') (J : Type (max u₁ v)) :
    PreservesLimitsOfShape (Discrete J) (F.op ⋙ preadditiveYoneda.obj Y) := by
  let H : Dᵒᵖ ⥤ AddCommGrpCat.{v} := F.op ⋙ preadditiveYoneda.obj Y
  -- Opposites turn coproduct preservation for `F` into product preservation for `F.op`.
  haveI : PreservesLimitsOfShape (Discrete J) F.op := by
    simpa using (CategoryTheory.Limits.preservesLimitsOfShape_op (J := Discrete J) F)
  haveI : PreservesLimitsOfShape (Discrete J) (H ⋙ forget AddCommGrpCat) := by
    -- After forgetting additivity, the represented functor is just plain Yoneda, which preserves
    -- limits objectwise.
    simpa [H, whiskering_preadditiveYoneda, Functor.assoc] using
      (inferInstance : PreservesLimitsOfShape (Discrete J) (F.op ⋙ yoneda.obj Y))
  -- `forget AddCommGrpCat` reflects limits, so preserving them after forgetting lifts back to the
  -- additive-valued functor itself.
  simpa [H] using
    (CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves
      H (forget AddCommGrpCat) : PreservesLimitsOfShape (Discrete J) H)

/-- Helper for Proposition 13.38.2: for fixed `Y`, Brown representability represents the functor
`W ↦ Hom_D'(F(W), Y)`. -/
lemma objwise_hom_functor_isRepresentable
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v), PreservesColimitsOfShape (Discrete J) F]
    (hD : IsCompactlyGenerated D)
    (Y : D') :
    (F.op ⋙ yoneda.obj Y).IsRepresentable := by
  let H : Dᵒᵖ ⥤ AddCommGrpCat.{v} := F.op ⋙ preadditiveYoneda.obj Y
  -- Brown representability applies to the additive-valued Hom functor once its cohomological and
  -- product-preserving inputs are recorded in the canonical owner form.
  have hH : H.rightOp.IsHomological := by
    simpa [H] using objwise_hom_functor_rightOp_is_homological (F := F) Y
  have hprod : ∀ J : Type (max u₁ v), PreservesLimitsOfShape (Discrete J) H := by
    intro J
    simpa [H] using objwise_hom_functor_preserves_discrete_limits (F := F) Y J
  -- Rewriting through `whiskering_preadditiveYoneda` puts Brown's conclusion into the plain Yoneda
  -- form required by the adjoint criterion.
  simpa [H, whiskering_preadditiveYoneda, Functor.assoc] using
    brown_representability_isRepresentable H hD hH hprod

include hD
/-- Proposition 13.38.2: an exact functor from a compactly generated triangulated category that
preserves arbitrary direct sums is a left adjoint. The companion theorem
`exactFunctor_hasExactRightAdjoint_of_isCompactlyGenerated` records that the chosen
right adjoint is exact. -/
@[stacks 0A8G]
theorem exactFunctor_isLeftAdjoint_of_isCompactlyGenerated
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v), PreservesColimitsOfShape (Discrete J) F]
    : F.IsLeftAdjoint := by
  -- For each target object `Y`, Brown representability produces an object of `D` representing the
  -- Hom functor `W ↦ Hom_D'(F(W), Y)`, which is exactly the owner condition for existence of a
  -- right adjoint.
  rw [F.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top]
  ext Y
  simpa [F.rightAdjointObjIsDefined_iff Y] using
    objwise_hom_functor_isRepresentable (hD := hD) (F := F) Y

-- Proof sketch: apply `exactFunctor_isLeftAdjoint_of_isCompactlyGenerated` to obtain the chosen
-- adjunction `Adjunction.ofIsLeftAdjoint F`. The left adjoint is already exact by hypothesis, so
-- Lemma `13.7.1`, equivalently `Adjunction.isTriangulated_rightAdjoint`, gives that the right
-- adjoint is exact.
/-- The right adjoint produced by Brown representability is exact for an exact
coproduct-preserving functor out of a compactly generated triangulated category. -/
theorem exactFunctor_hasExactRightAdjoint_of_isCompactlyGenerated
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v), PreservesColimitsOfShape (Discrete J) F]
    : letI := exactFunctor_isLeftAdjoint_of_isCompactlyGenerated hD F
      let adj := Adjunction.ofIsLeftAdjoint F
      letI := adj.rightAdjointCommShift ℤ
      F.rightAdjoint.IsTriangulated := by
  letI := exactFunctor_isLeftAdjoint_of_isCompactlyGenerated hD F
  let adj : F ⊣ F.rightAdjoint := Adjunction.ofIsLeftAdjoint F
  letI := adj.rightAdjointCommShift ℤ
  letI := adj.commShift_of_leftAdjoint ℤ
  exact adj.isTriangulated_rightAdjoint

omit hD

end

end CategoryTheory
