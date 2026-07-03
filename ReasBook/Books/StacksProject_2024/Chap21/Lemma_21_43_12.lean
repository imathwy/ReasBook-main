import Mathlib
import stacks_project.Chap21.Definition_21_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open Opposite

noncomputable section

universe u v w w'

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- The `RingCat`-valued structure sheaf on a category, viewed through the chaotic topology. -/
abbrev chaoticRingSheaf :
    Sheaf (⊥ : GrothendieckTopology C) RingCat :=
  (sheafCompose (⊥ : GrothendieckTopology C) (forget₂ CommRingCat RingCat)).obj 𝒪

/-- The category `\mathrm{Mod}(\mathcal O)` of module sheaves on a category with the chaotic
topology. -/
abbrev moduleOnCategory :=
  SheafOfModules (chaoticRingSheaf 𝒪)

variable [Abelian (moduleOnCategory 𝒪)]
variable [HasDerivedCategory (moduleOnCategory 𝒪)]

variable
  (RGamma :
    ∀ U : C,
      DerivedCategory (moduleOnCategory 𝒪) ⥤
        DerivedCategory (ModuleCat (𝒪.1.obj (op U))))
  (derivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.1.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.1.obj (op U))))
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

/-- The target-side object property in Lemma `21.43.12`: an object of `D(\mathcal C_\tau,
\mathcal O_\tau)` lies in the relevant full subcategory when its pushforward `Rε_*` belongs to
`QC(\mathcal O)`. -/
abbrev pushforwardQuasiCoherentProperty
    {Dτ : Type w} [Category Dτ]
    (rEpsilonPushforward : Dτ ⥤ DerivedCategory (moduleOnCategory 𝒪)) :
    ObjectProperty Dτ :=
  fun K ↦ isQuasiCoherent 𝒪.1 RGamma derivedRestrict comparison (rEpsilonPushforward.obj K)

-- Proof sketch: this is just the defining expansion of `pushforwardQuasiCoherentProperty`.
/-- Membership in the target subcategory of Lemma `21.43.12` means precisely that the pushed
forward object lies in `QC(\mathcal O)`. -/
theorem mem_pushforwardQuasiCoherentProperty_iff
    {Dτ : Type w} [Category Dτ]
    (rEpsilonPushforward : Dτ ⥤ DerivedCategory (moduleOnCategory 𝒪))
    (K : Dτ) :
    pushforwardQuasiCoherentProperty 𝒪 RGamma derivedRestrict comparison rEpsilonPushforward K ↔
      isQuasiCoherent 𝒪.1 RGamma derivedRestrict comparison (rEpsilonPushforward.obj K) := sorry

/-- The canonical restriction of `Rε_*` from the target full subcategory back to `QC(\mathcal O)`.
-/
abbrev restrictedPushforwardToQC
    {Dτ : Type w} [Category Dτ]
    (rEpsilonPushforward : Dτ ⥤ DerivedCategory (moduleOnCategory 𝒪)) :
    (pushforwardQuasiCoherentProperty 𝒪 RGamma derivedRestrict comparison
      rEpsilonPushforward).FullSubcategory ⥤
        QC 𝒪.1 RGamma derivedRestrict comparison :=
  ObjectProperty.lift
    (isQuasiCoherent 𝒪.1 RGamma derivedRestrict comparison)
    ((pushforwardQuasiCoherentProperty 𝒪 RGamma derivedRestrict comparison
      rEpsilonPushforward).ι ⋙ rEpsilonPushforward)
    (fun K ↦ K.property)

-- Proof sketch: `restrictedPushforwardToQC` is defined by lifting `Rε_*` through the full
-- subcategory cut out by the condition that `Rε_* K` is quasi-coherent.
/-- The restricted pushforward of Lemma `21.43.12` is the lift of `Rε_*` through the defining full
subcategory of objects whose pushforward lies in `QC(\mathcal O)`. -/
abbrev restrictedPushforwardToQC_comp_ι
    {Dτ : Type w} [Category Dτ]
    (rEpsilonPushforward : Dτ ⥤ DerivedCategory (moduleOnCategory 𝒪)) :
    restrictedPushforwardToQC 𝒪 RGamma derivedRestrict comparison rEpsilonPushforward ⋙
        (isQuasiCoherent 𝒪.1 RGamma derivedRestrict comparison).ι ≅
      (pushforwardQuasiCoherentProperty 𝒪 RGamma derivedRestrict comparison
        rEpsilonPushforward).ι ⋙
        rEpsilonPushforward :=
  (isQuasiCoherent 𝒪.1 RGamma derivedRestrict comparison).liftCompιIso
    ((pushforwardQuasiCoherentProperty 𝒪 RGamma derivedRestrict comparison
      rEpsilonPushforward).ι ⋙ rEpsilonPushforward)
    (fun K ↦ K.property)

-- Proof sketch: Section `21.27` provides the adjunction `ε^* ⊣ Rε_*` with `Rε_*` fully faithful,
-- so the counit identifies every object on the target side with one coming from `ε^*`. The
-- K-flat comparison hypothesis computes `Rε_*(ε^* M)` for `M ∈ QC(\mathcal O)` and gives the unit
-- isomorphism on `QC(\mathcal O)`, which upgrades the chosen restriction of `ε^*` and the
-- canonical restricted `Rε_*` to quasi-inverse equivalences.
/-- Lemma 21.43.12: let `ε : (\mathcal C_\tau, \mathcal O_\tau) \to
(\mathcal C_{\tau'}, \mathcal O_{\tau'})` be the topology-change morphism of Section `21.27`, and
assume `τ'` is the chaotic topology on `\mathcal C`. If for every `U ∈ \operatorname{Ob}(\mathcal
C)` and every chosen K-flat complex over `\mathcal O(U)` the comparison map from that complex to
the derived sections of its sheafified tensor with `\mathcal O_U` is a quasi-isomorphism, then the
restriction of `ε^*` to `QC(\mathcal O)` is an equivalence onto the full subcategory of
`D(\mathcal C_\tau, \mathcal O_\tau)` consisting of those `K` with `Rε_* K ∈ QC(\mathcal O)`. The
companion declaration `restrictedPushforwardToQC` is the intended quasi-inverse induced by
`Rε_*`. -/
theorem epsilonPullback_qc_isEquivalence_of_kFlatComparison
    {Dτ : Type w} [Category Dτ]
    (epsilonPullback : DerivedCategory (moduleOnCategory 𝒪) ⥤ Dτ)
    (rEpsilonPushforward : Dτ ⥤ DerivedCategory (moduleOnCategory 𝒪))
    (adj : epsilonPullback ⊣ rEpsilonPushforward)
    [rEpsilonPushforward.Full] [rEpsilonPushforward.Faithful]
    (epsilonPullbackQC :
      QC 𝒪.1 RGamma derivedRestrict comparison ⥤
        (pushforwardQuasiCoherentProperty 𝒪 RGamma derivedRestrict comparison
          rEpsilonPushforward).FullSubcategory)
    (hε :
      epsilonPullbackQC ⋙
          (pushforwardQuasiCoherentProperty 𝒪 RGamma derivedRestrict comparison
            rEpsilonPushforward).ι ≅
        (isQuasiCoherent 𝒪.1 RGamma derivedRestrict comparison).ι ⋙ epsilonPullback)
    {KFlatComplex : C → Type w'} [∀ U : C, Category (KFlatComplex U)]
    (derivedSections : ∀ U : C, KFlatComplex U ⥤ KFlatComplex U)
    (sectionComparison : ∀ U : C, 𝟭 (KFlatComplex U) ⟶ derivedSections U)
    (hKFlat : ∀ U : C, ∀ M : KFlatComplex U, IsIso ((sectionComparison U).app M)) :
    Functor.IsEquivalence epsilonPullbackQC := sorry

end CategoryTheory.ModulesOnCategory
