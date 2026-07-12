import StacksProject_2024.Chap21.Definition_21_46_1_Core
import StacksProject_2024.Chap21.Lemma_21_19_1_core

open CategoryTheory
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

open SheafOfModules.RingedSite

section

/- Domain-style sampling for Lemma 21.46.5:
- primary domain: tor-amplitude in derived categories of module sheaves under unbounded derived
  pullback on ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.modulePullbackDerived`,
  `RingedSite.Hom.modulePullbackToDerived`,
  `RingedSite.Hom.ModuleDerived`,
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`;
- best owner abstraction: the pullback side is canonically owned by the bundled ringed-site
  morphism `f : X ⟶ Y` via `modulePullbackDerived f`, while tor-amplitude is already owned by the
  source-facing predicate `SheafOfModules.RingedSite.HasTorAmplitudeIn` on the ambient ringed
  sites;
- primitive data: the morphism `f`, the derived object `E`, and the interval bounds `a, b`;
- derived API: preservation of tor-amplitude under `L(f)^*`.

Source/core/bridge triage:
- `source-facing`: tor-amplitude preservation under derived pullback;
- `core/canonical`: `modulePullbackDerived` and `HasTorAmplitudeIn`;
- `bridge/view`: site-presented pullback specializations that reuse this owner theorem downstream. -/

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [Abelian (ModuleCat X)]
variable [CategoryWithHomology (ModuleCat X)]
variable [MonoidalCategory (ModuleDerived X)]

variable [Abelian (ModuleCat Y)]
variable [CategoryWithHomology (ModuleCat Y)]
variable [MonoidalCategory (ModuleDerived Y)]

variable [f.modulePushforward.Additive]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} f.structureSheafMap)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

-- Proof sketch: represent `E` by a flat complex concentrated in degrees `[a, b]` using
-- Lemma `21.46.3`, pull that complex back termwise along `F`, and use Lemma `18.39.1` to keep
-- the terms flat after pullback. The pulled-back complex is still concentrated in `[a, b]`, so
-- Lemma `21.46.3` again identifies `Lf^*E` as having tor-amplitude in `[a, b]`.
/-- Lemma 21.46.5: for a morphism `f : X ⟶ Y` of ringed sites, if `E` has tor-amplitude in
`[a, b]`, then its derived pullback `L(f)^*E` also has tor-amplitude in `[a, b]`. -/
@[stacks 08H5]
theorem modulePullbackDerived_hasTorAmplitudeIn
    (E : ModuleDerived Y) (a b : ℤ)
    (hE : HasTorAmplitudeIn E a b) :
    HasTorAmplitudeIn ((L(f)^*).obj E) a b := by
  sorry

end

end RingedSite.Hom
