import Mathlib
import StacksProject_2024.Chap04.Lemma_4_35_16
import StacksProject_2024.Chap08.Lemma_8_2_3
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1
import StacksProject_2024.Chap08.Lemma_8_4_8
import StacksProject_2024.Chap08.Lemma_8_5_4
import StacksProject_2024.Chap08.Lemma_8_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open BasedFunctor
open Functor
open Functor.Fiber
open Functor.IsStronglyCartesian
open FibredCategoryOver

universe w v₁ u₁

namespace CategoryTheory

namespace FibredCategoryMor

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}
variable {X Y : FibredCategoryOver C} [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]

/- Domain-style sampling for Lemma 8.11.3:
- primary domain: morphisms of fibred categories over a site, expressed through canonical
  pullback functors on fibers and comparison isomorphisms between `f^*F(x)` and `F(f^*x)`;
- inspected owner-level declarations:
  `BasedFunctor.fiberFunctor`,
  `PullbackChoice.pullbackFunctor`,
  `canonicalPullbackChoice`,
  `Functor.IsStronglyCartesian.domainIsoOfBaseIso`;
- best owner abstraction: the source-facing predicate
  `FibredCategoryMor.LocallyLiftsFiberMorphisms`, stated in the fiber categories using the
  canonical pullback functors and the comparison square they induce;
- primitive data: a morphism `b` in the target fiber over `U`, together with local lifts `a` in
  the pulled-back source fibers over a covering family;
- derived API: the canonical stack-morphism shorthand
  `StackInGroupoidsOver.Hom.LocallyLiftsFiberMorphisms` and the gerbe characterization theorem at
  the end of the file.

Source/core/bridge triage:
- `source-facing`: `FibredCategoryMor.LocallyLiftsFiberMorphisms`;
- `core/canonical`: `BasedFunctor.fiberFunctor`, `canonicalPullbackChoice`,
  `PullbackChoice.pullbackFunctor`, `FibredCategoryMor.pullbackComparison`, and
  `IsStronglyCartesian.domainIsoOfBaseIso`;
- `bridge/view`: `FibredCategoryMor.pullbackComparison`, reused here to express the source
  condition as a commuting square in the pulled-back target fiber. -/

/-- Any morphism between two objects in the image of a fiber is locally lifted after restricting
to a covering family. This is condition `(2)(b)` in Lemma `8.11.3`. -/
def LocallyLiftsFiberMorphisms
    (J : GrothendieckTopology C) (F : FibredCategoryMor X Y) : Prop :=
  let hcX := canonicalPullbackChoice X.p
  let hcY := canonicalPullbackChoice Y.p
  ∀ {U : C} (x x' : X.p.Fiber U)
      (b : (fiberFunctor F U).obj x ⟶ (fiberFunctor F U).obj x'),
      ∃ S : J.Cover U, ∀ I : S.Arrow,
        ∃ a : I.f ^*[hcX] x ⟶ I.f ^*[hcX] x',
          CommSq
            ((hcY.pullbackFunctor I.f).map b)
            (pullbackComparison F I.f x).hom
            (pullbackComparison F I.f x').hom
            ((fiberFunctor F I.Y).map a)

end

end FibredCategoryMor

namespace StackInGroupoidsOver.Hom

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackInGroupoidsOver J}

/-- Owner-level shorthand for the local lifting condition on a `1`-morphism of stacks in
groupoids. -/
abbrev LocallyLiftsFiberMorphisms (F : X ⟶ Y) : Prop :=
  FibredCategoryMor.LocallyLiftsFiberMorphisms J (toFibredCategoryMor F)

end

end StackInGroupoidsOver.Hom

namespace StackInGroupoidsOver.Hom

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver J}

/- Domain-style sampling for the main gerbe characterization in Lemma 8.11.3:
- primary domain: gerbes over morphisms of stacks in groupoids, compared across different
  factorizations of the same morphism through a functor fibred in groupoids over the target;
- inspected owner-level declarations:
  `exists_equivalence_over_target_between_fibred_groupoid_factorizations`,
  `isStackInGroupoids_iff_of_equivalence_over_base`,
  `isGerbe_iff_of_equivalence_over_base`,
  `fibredInGroupoidsFactorizationToTarget`;
- best owner abstraction: the source-facing gerbe predicate
  `IsGerbe (inheritedTopology J Yₛ) F'.toFunctor` on an arbitrary factorization of `F`
  through a functor `F'` fibred in groupoids over `Yₛ`;
- primitive data: a factorization `a ⋙ F' = toBasedFunctor F` with `a` an equivalence over `C`;
- derived API: the canonical explicit-factorization specialization below.

Source/core/bridge triage:
- `source-facing`: the factorization-independent equivalence below for an arbitrary factorization
  `a ⋙ F' = toBasedFunctor F`;
- `core/canonical`: `IsGerbe (inheritedTopology J Yₛ) F'.toFunctor`,
  `exists_equivalence_over_target_between_fibred_groupoid_factorizations`, and the transport
  lemmas `isStackInGroupoids_iff_of_equivalence_over_base` and
  `isGerbe_iff_of_equivalence_over_base`;
- `bridge/view`: the canonical explicit factorization
  `fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)`. -/

-- Proof sketch: compare the given factorization `a ⋙ F' = toBasedFunctor F` with the canonical
-- explicit factorization from Lemma `4.35.16` using Lemma `4.35.17`, which gives an equivalence
-- over the target stack. Transport the inherited-topology stack and gerbe predicates across that
-- equivalence by Lemmas `8.5.4` and `8.11.2`, and then identify the canonical factorization with
-- conditions `(2)(a)` and `(2)(b)` via the specialization below.
/-- Lemma 8.11.3: let `F : Xₛ ⟶ Yₛ` be a morphism of stacks in groupoids over `(C, J)`, and let
`a : Xₛ ⥤ᵇ X'` be an equivalence over `C` such that `a ⋙ F' = toBasedFunctor F`, where
`F' : X' ⟶ Yₛ` is fibred in groupoids over `Yₛ`. Then `F'`, viewed over the topology on `Yₛ`
inherited from `(C, J)`, is a gerbe if and only if `F` is locally essentially surjective on
objects and locally lifts fiber morphisms after passing to a cover. -/
theorem isGerbeOverInheritedTopology_iff_locallyEssentiallySurjective_and_locallyLiftsFiberMorphisms_of_factorization
    (F : Xₛ ⟶ Yₛ)
    {X' : BasedCategory C}
    (a : Xₛ.toBasedCategory ⥤ᵇ X')
    (F' : X' ⥤ᵇ Yₛ.toBasedCategory)
    [IsFibredInGroupoids F'.toFunctor]
    (ha : a.IsEquivalenceOverBase)
    (hfactor : a ⋙ F' = toBasedFunctor F) :
    IsGerbe (inheritedTopology J Yₛ) F'.toFunctor ↔
      LocallyEssentiallySurjectiveOnObjects F ∧
        LocallyLiftsFiberMorphisms F := by
  sorry

-- Proof sketch: apply the main factorization-independent statement to the canonical explicit
-- factorization `X ×_{F,Y,\mathrm{id}} Y ⟶ Y`, where the source comparison
-- `X ⟶ X ×_{F,Y,\mathrm{id}} Y` is an equivalence over `C` by Lemma `4.35.16`.
/-- Canonical specialization of Lemma 8.11.3 to the explicit factorization
`X ×_{F,Y,\mathrm{id}} Y ⟶ Y`. This is the bridge from the source-facing factorization statement
to the chapter's canonical factorization owner. -/
theorem factorizationToTarget_isGerbeOverInheritedTopology_iff_locallyEssentiallySurjective_and_locallyLiftsFiberMorphisms
    (F : Xₛ ⟶ Yₛ) :
    IsGerbe (inheritedTopology J Yₛ)
      (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor ↔
      LocallyEssentiallySurjectiveOnObjects F ∧
        LocallyLiftsFiberMorphisms F := by
  letI :
      IsFibredInGroupoids
        (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor :=
    fibredInGroupoidsFactorizationToTarget_isFibredInGroupoids (toBasedFunctor F)
  exact
    isGerbeOverInheritedTopology_iff_locallyEssentiallySurjective_and_locallyLiftsFiberMorphisms_of_factorization
      F
      (fibredInGroupoidsFactorizationFromSource (toBasedFunctor F))
      (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F))
      (fibredInGroupoidsFactorizationFromSource_isEquivalenceOverBase (toBasedFunctor F))
      (fibredInGroupoidsFactorization_comp (toBasedFunctor F))

end

end StackInGroupoidsOver.Hom

end CategoryTheory
