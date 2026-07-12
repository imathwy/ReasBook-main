import StacksProject_2024.Chap06.Lemma_6_30_10
import StacksProject_2024.Chap06.Lemma_6_30_12
import StacksProject_2024.Chap06.Definition_6_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable {B : Set (Opens X)} (hB : Opens.IsBasis B)

private instance basisOpenInclusion_isContinuous :
    Functor.IsContinuous (basisOpenInclusion B)
      (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X) := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  exact
    Functor.IsCoverDense.isContinuous
      (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)
      (basisOpenInclusion B)
      (Functor.inducedTopology_coverPreserving (basisOpenInclusion B)
        (Opens.grothendieckTopology X))

/- Domain-style sampling for Lemma 6.30.13:
- primary domain: sheaves of modules over ring-valued sheaves on a dense basis subsite;
- sampled owner declarations:
  `(basisOpenInclusion B).sheafPushforwardContinuous`,
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`,
  `SheafOfModules.pushforward`,
  `basisModuleSheafExtension`;
- best owner abstraction: the dense-subsite restriction functor on sheaves, together with the
  induced module-sheaf pushforward along the identity map of the restricted ring sheaf;
- primitive data: the basis inclusion `basisOpenInclusion B`, the induced topology
  `basisGrothendieckTopology B hB`, and the sheaf of rings `𝒪`;
- derived API: restriction of `𝒪`-modules to the basis and the extension construction from
  `Lemma_6_30_12`, expressed through the canonical functor
  `SheafOfModules.pushforward (𝟙 _)`;
- source/core/bridge triage:
  `source-facing`: restriction of `𝒪`-modules to basis opens;
  `core/canonical`: `(basisOpenInclusion B).sheafPushforwardContinuous` and
    `SheafOfModules.pushforward`;
  `bridge/view`: `basisModuleSheafExtension`, which supplies the inverse-direction module
    structure on the extension back to `X`.
-/

variable (𝒪 : TopCat.Sheaf RingCat.{u} X)

/- The restriction functor in Lemma 6.30.13 is not a new owner: it is the canonical module
pushforward functor along the identity map of the restricted ring sheaf on the basis site. On the
source-facing surface, it has type `Mod(𝒪) ⥤ Mod(𝒪|_B)`. -/
#check
  (SheafOfModules.pushforward
      (𝟙 (((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj 𝒪)) :
    Mod(𝒪) ⥤
      Mod((((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj 𝒪)))

-- Proof sketch: use Lemma 6.30.10 for the equivalence between sheaves on `X` and sheaves on the
-- basis site, and Lemma 6.30.12 to equip the extended additive sheaf with the canonical module
-- structure over the extended ring sheaf. Together these identify restriction to the basis as an
-- equivalence on module sheaves.
/-- Lemma 6.30.13: restricting a sheaf of `\mathcal O`-modules on `X` to the members of the basis
`\mathcal B` defines an equivalence between `Mod(\mathcal O)` and
`Mod(\mathcal O|_\mathcal B)`. -/
theorem restrictSheafOfModulesToBasis_isEquivalence
    (𝒪 : TopCat.Sheaf RingCat.{u} X) :
    Functor.IsEquivalence
      (SheafOfModules.pushforward
          (𝟙 (((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
            (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj 𝒪)) :
        Mod(𝒪) ⥤
          Mod((((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
            (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj 𝒪))) := sorry

end
