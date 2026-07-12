import Mathlib
import StacksProject_2024.Chap07.Lemma_7_29_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped MorphismOfTopoiIn

universe u₁ u₂ u₃ v₁ v₂ v₃ w

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Remark 7.29.8:
- primary domain: equivalences of sheaf topoi presented by dense-subsite comparison functors to a
  common site;
- sampled owner API:
  `Functor.IsDenseSubsite`,
  `MorphismOfTopoiIn`,
  `MorphismOfTopoiIn.id`,
  `CatCommSq`,
  `Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension`;
- best owner abstraction: the main statement should live directly over the common site, the two
  dense-subsite functors into it, and the factorization square through the identity morphism of
  the common sheaf topos; the pointwise right-Kan-extension witnesses belong only to a separate
  bridge theorem realizing the dense-subsite cocontinuous direct-image functors as equivalences on
  sheaves of sets;
- primitive data: the common site `(C', J')`, the dense-subsite functors from `(C, J)` and
  `(D, K)`, and the comparison square expressing `f` through `MorphismOfTopoiIn.id J'`;
- derived API: the equivalence instances for the two cocontinuous sheaf pushforwards and the
  resulting canonical natural isomorphism
  `f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous ≅
    targetFunctor.sheafPushforwardCocontinuous`;
  the public theorem surfaces should end with `Nonempty` of the square owner or of the comparison
  natural isomorphism, with no extra tautological payload, because those owners already contain the
  relevant comparison data.

Source/core/bridge triage:
- `source-facing`: the existence of a common site presenting an equivalence of topoi;
- `core/canonical`: `Functor.IsDenseSubsite`, `MorphismOfTopoiIn`, `MorphismOfTopoiIn.id`, and
  `CatCommSq`;
- `bridge/view`: the pointwise right Kan extension hypotheses used to realize the two
  dense-subsite cocontinuous direct-image functors as equivalences on set-valued sheaves and turn
  the square through `MorphismOfTopoiIn.id J'` into a canonical natural isomorphism of functors to
  `Sh(C', J')`.
-/

-- Proof sketch: apply Lemma `7.29.6` to `f`, and use the hypothesis that `f` is an equivalence
-- of topoi to replace the lower morphism by the identity morphism of a common site `(C', J')`.
-- The source-facing statement keeps only the common site, the two dense-subsite functors, and the
-- factorization square through `MorphismOfTopoiIn.id J'`; the right-Kan-extension bridge data
-- needed to realize the induced equivalences on sheaves of sets are recorded separately below.
/-- Remark 7.29.8: if the morphism of topoi `f : Sh(J) ⟶ Sh(K)` is an equivalence, then one can
choose a common site `(C', J')` together with special cocontinuous functors
`C ⥤ C'` and `D ⥤ C'` such that the induced equivalences of sheaf topoi identify `f` with the
factorization through the identity morphism of `Sh(C', J')`. -/
theorem exists_special_cocontinuous_common_site_factorization_of_isEquivalence
    (f : MorphismOfTopoiIn K J) [(f⁻¹).IsEquivalence] :
    ∃ (C' : Type u₃) (_ : Category.{v₃} C') (J' : GrothendieckTopology C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J')
      (targetFunctor : D ⥤ C') (_ : targetFunctor.IsDenseSubsite K J'),
      Nonempty
        (CatCommSq
          (targetFunctor.sheafPushforwardContinuous (Type w) K J')
          ((MorphismOfTopoiIn.id J')⁻¹)
          (f⁻¹)
          (sourceFunctor.sheafPushforwardContinuous (Type w) J J')) := by
  sorry

-- Proof sketch: add the pointwise right-Kan-extension bridge data to the source-facing theorem
-- above, so that the two dense-subsite cocontinuous direct-image functors become equivalences on
-- `Type w`-valued sheaves. The factorization square through `MorphismOfTopoiIn.id J'` then
-- identifies the two canonical functors from `Sh(K)` to `Sh(C', J')`,
-- namely `f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous` and
-- `targetFunctor.sheafPushforwardCocontinuous`, by a natural isomorphism.
/-- Bridge companion to Remark 7.29.8: after supplying the pointwise right-Kan-extension
hypotheses needed to realize the dense-subsite cocontinuous direct-image functors as equivalences
on sheaves of sets, the source-facing factorization through `MorphismOfTopoiIn.id J'` yields the
canonical natural isomorphism
`f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous ≅
  targetFunctor.sheafPushforwardCocontinuous`. -/
theorem exists_special_cocontinuous_common_site_factorization_of_isEquivalence_canonical
    (f : MorphismOfTopoiIn K J) [(f⁻¹).IsEquivalence] :
    ∃ (C' : Type u₃) (_ : Category.{v₃} C') (J' : GrothendieckTopology C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J')
      (_ : ∀ P : Cᵒᵖ ⥤ Type w, sourceFunctor.op.HasPointwiseRightKanExtension P)
      (targetFunctor : D ⥤ C') (_ : targetFunctor.IsDenseSubsite K J')
      (_ : ∀ P : Dᵒᵖ ⥤ Type w, targetFunctor.op.HasPointwiseRightKanExtension P),
      Nonempty (
        f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous (Type w) J J' ≅
          targetFunctor.sheafPushforwardCocontinuous (Type w) K J') := by
  sorry

end

end CategoryTheory
