import Mathlib
import Mathlib.CategoryTheory.Triangulated.Opposite.Basic
import StacksProject_2024.Chap13.Lemma_13_39_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [IsTriangulated D] [IsTriangulated D']
  [HasCoproducts.{max u₁ v₁} D]

/-
Domain-style sampling for Proposition 13.39.2:
- primary domain: Brown representability and adjunction criteria for exact functors between
  triangulated categories;
- sampled owner declarations:
  `brown_representability_of_detecting_factorization_set_isRepresentable`,
  `Functor.isLeftAdjoint_of_objwise_hom_isRepresentable`,
  `Adjunction.ofIsLeftAdjoint`,
  `Adjunction.isTriangulated_rightAdjoint`;
- best owner abstraction:
  `F.IsLeftAdjoint` for the left-adjoint conclusion, with exactness of the chosen right adjoint
  expressed canonically by `F.rightAdjoint.IsTriangulated`;
- primitive data: the functor `F`, the Brown-representability-set hypothesis `hD`, exactness
  `[F.IsTriangulated]`, and coproduct preservation;
- derived API: the chosen adjunction `Adjunction.ofIsLeftAdjoint F`, its induced right-adjoint
  shift compatibility, and the resulting triangulated structure on `F.rightAdjoint`.

Source/core/bridge triage:
- `source-facing`: the two theorems below, which keep the Brown-representability-set hypothesis
  explicit;
- `core/canonical`: `brown_representability_of_detecting_factorization_set_isRepresentable`,
  `Functor.isLeftAdjoint_of_objwise_hom_isRepresentable`, and
  `Adjunction.isTriangulated_rightAdjoint`;
- `bridge/view`: the chosen adjunction `Adjunction.ofIsLeftAdjoint F` together with
  `Adjunction.rightAdjointCommShift`.
-/

/-- Helper for Proposition 13.39.2: for fixed `Y`, the contravariant Hom functor
`W ↦ Hom_D'(F(W), Y)` is cohomological. -/
lemma objwise_hom_functor_rightOp_is_homological_of_brownSet
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] (Y : D') :
    ((F.op ⋙ preadditiveYoneda.obj Y).rightOp).IsHomological := by
  sorry

/-- Helper for Proposition 13.39.2: for fixed `Y`, the contravariant Hom functor
`W ↦ Hom_D'(F(W), Y)` sends direct sums in `D` to products. -/
lemma objwise_hom_functor_preserves_discrete_limits_of_brownSet
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F]
    (Y : D') (J : Type (max u₁ v₁)) :
    PreservesLimitsOfShape (Discrete J) (F.op ⋙ preadditiveYoneda.obj Y) := by
  let H : Dᵒᵖ ⥤ AddCommGrpCat.{v₂} := F.op ⋙ preadditiveYoneda.obj Y
  -- Opposites turn coproduct preservation for `F` into product preservation for `F.op`.
  letI : PreservesLimitsOfShape (Discrete J) F.op := by
    simpa using (CategoryTheory.Limits.preservesLimitsOfShape_op (J := Discrete J) F)
  letI : PreservesLimitsOfShape (Discrete J) (H ⋙ forget AddCommGrpCat) := by
    -- After forgetting additivity, the represented functor is just plain Yoneda, which preserves
    -- limits objectwise.
    simpa [H, whiskering_preadditiveYoneda, Functor.assoc] using
      (inferInstance : PreservesLimitsOfShape (Discrete J) (F.op ⋙ yoneda.obj Y))
  -- `forget AddCommGrpCat` reflects limits, so preserving them after forgetting lifts back to the
  -- additive-valued functor itself.
  simpa [H] using
    (CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves
      H (forget AddCommGrpCat) : PreservesLimitsOfShape (Discrete J) H)

/-- Helper for Proposition 13.39.2: Brown representability with a detecting factorization set
represents the functor `W ↦ Hom_D'(F(W), Y)`. -/
lemma objwise_hom_functor_isRepresentable_of_brownSet
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F]
    (hD : ∃ S : Set D, IsBrownRepresentabilitySet S) (Y : D') :
    (F.op ⋙ yoneda.obj Y).IsRepresentable := by
  rcases hD with ⟨S, hS⟩
  let H : Dᵒᵖ ⥤ AddCommGrpCat.{v₂} := F.op ⋙ preadditiveYoneda.obj Y
  have hH : H.rightOp.IsHomological := by
    simpa [H] using
      objwise_hom_functor_rightOp_is_homological_of_brownSet (F := F) Y
  have hprod : ∀ J : Type (max u₁ v₁), PreservesLimitsOfShape (Discrete J) H := by
    intro J
    simpa [H] using
      objwise_hom_functor_preserves_discrete_limits_of_brownSet (F := F) Y J
  have hrep :
      ((F.op ⋙ yoneda.obj Y) ⋙ uliftFunctor.{v₁}).IsRepresentable := by
    -- Rewriting through `whiskering_preadditiveYoneda` puts Brown's conclusion into the plain
    -- Yoneda form required by the adjoint criterion.
    simpa [H, whiskering_preadditiveYoneda, Functor.assoc] using
      brown_representability_of_detecting_factorization_set_isRepresentable S hS H hH hprod
  exact Functor.isRepresentable_comp_uliftFunctor_iff.mp hrep

/-- A coproduct-preserving exact functor out of a triangulated category satisfying the Brown
representability-set hypothesis of Lemma 13.39.1 is a left adjoint. -/
theorem exactFunctor_isLeftAdjoint_of_exists_brownRepresentabilitySet
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F]
    (hD : ∃ S : Set D, IsBrownRepresentabilitySet S) :
    F.IsLeftAdjoint := by
  -- Brown representability produces, for each target object `Y`, an object of `D` representing
  -- the Hom functor `W ↦ Hom_D'(F(W), Y)`, which is exactly the owner condition for a right
  -- adjoint.
  rw [F.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top]
  ext Y
  simpa [F.rightAdjointObjIsDefined_iff Y] using
    objwise_hom_functor_isRepresentable_of_brownSet (F := F) hD Y

/-- Proposition 13.39.2: if `D` admits a set of objects satisfying conditions (1) and (2) of
Lemma 13.39.1, then every exact functor `F : D ⥤ D'` of triangulated categories that preserves
arbitrary direct sums has an exact right adjoint. In the canonical API, this is expressed by the
fact that the chosen right adjoint `F.rightAdjoint` is triangulated. -/
@[stacks 0GYH]
theorem exactFunctor_hasExactRightAdjoint_of_exists_brownRepresentabilitySet
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F]
    (hD : ∃ S : Set D, IsBrownRepresentabilitySet S) :
    letI := exactFunctor_isLeftAdjoint_of_exists_brownRepresentabilitySet F hD
    let adj : F ⊣ F.rightAdjoint := Adjunction.ofIsLeftAdjoint F
    letI := adj.rightAdjointCommShift ℤ
    F.rightAdjoint.IsTriangulated := by
  letI := exactFunctor_isLeftAdjoint_of_exists_brownRepresentabilitySet F hD
  let adj : F ⊣ F.rightAdjoint := Adjunction.ofIsLeftAdjoint F
  letI := adj.rightAdjointCommShift ℤ
  letI := adj.commShift_of_leftAdjoint ℤ
  exact adj.isTriangulated_rightAdjoint

end

end CategoryTheory
