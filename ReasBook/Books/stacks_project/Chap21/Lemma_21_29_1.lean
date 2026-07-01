import Mathlib
import stacks_project.Chap21.Lemma_21_28_6

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ObjectProperty

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (ε : RingedSite.Hom X Y)

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y

variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [HasSheafify Y.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]

variable [Abelian ModX] [Abelian ModY]
variable [HasInjectiveResolutions ModX]
variable [ε.IsFlat]
variable [ε.modulePushforward.Additive]
variable [ε.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived ε) (ModuleQis X)]

variable (A' : ObjectProperty ModY) (A : ObjectProperty ModX)
variable [IsWeakSerreClass A]

-- Proof sketch: push forward is assumed exact on the source weak Serre full subcategory. Pull back
-- a five-term exact sequence in `A'`, apply weak-Serre closure on `A`, and then use the unit
-- isomorphisms together with exact pushforward to transport the middle term back to `A'`.
/-- Lemma 21.29.1 (1): in the topology-comparison situation, if pullback identifies the target
subcategory `\mathcal A'` with a weak Serre subcategory `\mathcal A` on the source and
pushforward is exact on the source subcategory, then `\mathcal A'` is a weak Serre subcategory
of `\operatorname{Mod}(\mathcal O_{\tau'})`. This formalizes the target-side image of the
textbook subcategory `\mathcal A`. -/
theorem targetWeakSerreSubcategory_of_pullbackEquivalence_of_pushforwardExact
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (ε.modulePullback.obj ℱ'))
    (hpush_mem : ∀ ⦃ℱ : ModX⦄, A ℱ → A' (ε.modulePushforward.obj ℱ))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory ε A' A hpull_mem)]
    (_hexact : CategoryTheory.exactFunctor A.FullSubcategory ModY
      (ObjectProperty.ι A ⋙ ε.modulePushforward))
    (adj : modulePullbackDerivedOfFlat ε ⊣ modulePushforwardDerived ε)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    IsWeakSerreClass A' := sorry

variable [IsWeakSerreClass A']

-- Proof sketch: apply the derived comparison theorem of Lemma `21.28.6` to the comparison
-- morphism `ε`. The bounded-cohomology basis hypotheses provide the local vanishing input, and
-- the unit isomorphisms on degree-zero objects identify the restricted right derived pushforward
-- as the quasi-inverse.
/-- Lemma 21.29.1 (2): assuming the target image subcategory is weak Serre and the local
bounded-cohomology hypotheses needed for the comparison-topology argument, the exact pullback
along `\epsilon` induces the equivalence
`D_{\mathcal A'}(\mathcal O_{\tau'}) \simeq D_{\mathcal A}(\mathcal O_\tau)`, with quasi-inverse
given by the restricted right derived pushforward `R \epsilon_*`. -/
theorem topologyComparisonDerivedPullback_isEquivalence_of_boundedCohomology
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (ε.modulePullback.obj ℱ'))
    [Functor.IsEquivalence
      (modulePullbackOnWeakSerreSubcategory ε A' A hpull_mem)]
    (basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis Y.structureSheaf A')
    (adj : modulePullbackDerivedOfFlat ε ⊣ modulePushforwardDerived ε)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    Functor.IsEquivalence
      (modulePullbackDerivedOfFlatWithCohomologyIn ε A' A hpull_mem) := sorry

end

end RingedSite.Hom
