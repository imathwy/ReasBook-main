import Mathlib
import stacks_project.Chap13.Lemma_13_39_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

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

-- Proof sketch: unpack the existence of a Brown-representability set `S`. For each `Y : D'`,
-- apply the canonical Brown-representability companion
-- `brown_representability_of_detecting_factorization_set_isRepresentable` to the contravariant
-- functor `W ↦ Hom(F.obj W, Y)`, using exactness of `F` to get a cohomological functor and
-- preservation of direct sums by `F` to turn coproducts in `D` into products in `AddCommGrpCat`.
-- The resulting objectwise representability hypothesis yields `F.IsLeftAdjoint` via the owner
-- criterion `F.isLeftAdjoint_of_objwise_hom_isRepresentable`.
/-- A coproduct-preserving exact functor out of a triangulated category satisfying the Brown
representability-set hypothesis of Lemma 13.39.1 is a left adjoint. -/
theorem exactFunctor_isLeftAdjoint_of_exists_brownRepresentabilitySet
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F]
    (hD : ∃ S : Set D, IsBrownRepresentabilitySet S) :
    F.IsLeftAdjoint := sorry

-- Proof sketch: first apply
-- `exactFunctor_isLeftAdjoint_of_exists_brownRepresentabilitySet` to get the chosen adjunction
-- `Adjunction.ofIsLeftAdjoint F`. Then use the canonical shift-compatibility of right adjoints
-- together with `Adjunction.isTriangulated_rightAdjoint` to conclude that the canonical chosen
-- right adjoint `F.rightAdjoint` is triangulated, hence exact.
/-- Proposition 13.39.2: if `D` admits a set of objects satisfying conditions (1) and (2) of
Lemma 13.39.1, then every exact functor `F : D ⥤ D'` of triangulated categories that preserves
arbitrary direct sums has an exact right adjoint. In the canonical API, this is expressed by the
fact that the chosen right adjoint `F.rightAdjoint` is triangulated. -/
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
