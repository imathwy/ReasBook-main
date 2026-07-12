import StacksProject_2024.Chap13.Lemma_13_31_9
import StacksProject_2024.Chap21.Lemma_21_19_1_core
import StacksProject_2024.Chap21.Lemma_21_20_1_Owner

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open RingedSite.Hom
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "ModU" => ringedSiteModuleCategory (J.over U) (𝒪.over U)
local notation "X" => RingedSite.ofCommRingSheaf J 𝒪

/- Domain-style sampling for Lemma 21.20.1:
- primary domain: K-injective cochain complexes under localized restriction of module sheaves on a
  ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `ringSheaf`,
  `ringedSiteLocalizedLowerShriek`,
  `SheafOfModules.pushforward`,
  `CochainComplex.IsKInjective`,
  `RingedSite.Hom.localizedRestrictionComplex`,
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`,
  and, for the same localized restriction surface, Chapter 18's
  `ringedSiteLocalizedRestriction`;
- best owner abstraction first: the Chapter 21 lower-shriek owner
  `ringedSiteLocalizedLowerShriek J 𝒪 U`, together with the Chapter 18 localized restriction owner
  `ringedSiteLocalizedRestriction J 𝒪 U`.

Source/core/bridge triage:
- `source-facing`: the specialized statement that restriction to `(𝒞/U, 𝒪_U)` sends
  K-injective complexes of `𝒪`-modules to K-injective complexes;
- `core/canonical`: the generic Chapter 13 owner theorem
  `right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- `bridge/view`: the source-facing complex owner
  `RingedSite.Hom.localizedRestrictionComplex X U`, which specializes the generic owner to
  localized restriction of module sheaves.

Primitive data vs. derived API:
- primitive data here are just the ambient module category
  `ringedSiteModuleCategory J 𝒪`, the localized structure sheaf `ringSheaf J 𝒪`, and the
  canonical lower-shriek / restriction pair
  `ringedSiteLocalizedLowerShriek J 𝒪 U` and `RingedSite.Hom.localizedRestrictionComplex X U`;
- the K-injectivity conclusion is derived API.

Refinement choice:
- the former file kept the exact left adjoint to localized restriction private;
- we publicize the source-facing lower-shriek owner
  `ringedSiteLocalizedLowerShriek J 𝒪 U` together with its adjunction and exactness companions,
  together with the Chapter 21 core restriction-complex owner
  `RingedSite.Hom.localizedRestrictionComplex X U`;
- this keeps the source-facing semantics unchanged while avoiding repeated elaboration of the raw
  identity-pushforward complex functor. -/

-- Proof sketch: the source proof uses the adjunction
-- `SheafOfModules.pullback (𝟙 ((ringSheaf J 𝒪).over U)) ⊣ ringedSiteLocalizedRestriction J 𝒪 U`.
-- Route correction: the exact left adjoint here is the pullback lower-shriek, not the Chapter 18
-- right adjoint `ringedSiteLocalizedExtensionByZero`.
-- The Chapter 13 K-injective owner uses the canonical `[Abelian]` to `[Preadditive]` inference.
-- This file keeps that canonical surface rather than adding local instance scaffolding.

section

variable [HasSheafify (J.over U) AddCommGrpCat.{u}]
variable [hAbelianMod : Abelian Mod] [hAbelianModU : Abelian ModU]

namespace RingedSite.Hom

instance localizedRestriction_additive_ofCommRingSheaf :
    (localizedRestriction X U).Additive := by
  simpa [RingedSite.Hom.localizedRestriction, RingedSite.Hom.ModuleCat] using
    (SheafOfModules.RingedSite.ringedSiteLocalizedRestriction_additive J 𝒪 U :
      (ringedSiteLocalizedRestriction J 𝒪 U).Additive)

-- Lemma 21.20.1: for a ringed site `(𝒞, 𝒪)`, an object `U : 𝒞`, and a K-injective complex of
-- `𝒪`-modules, the restricted complex on the localized ringed site `(𝒞/U, 𝒪_U)` is K-injective.
instance ringedSiteLocalizedRestriction_isKInjective
    (I : CochainComplex Mod ℤ) [I.IsKInjective] :
    ((localizedRestrictionComplex X U).obj I).IsKInjective := by
  simpa [RingedSite.Hom.localizedRestrictionComplex, RingedSite.Hom.localizedRestriction] using
    (right_adjoint_preserves_isKInjective_of_exact_left_adjoint
      (ringedSiteLocalizedRestriction J 𝒪 U)
      (ringedSiteLocalizedLowerShriek J 𝒪 U)
      (ringedSiteLocalizedLowerShriek_adjunction J 𝒪 U)
      (ringedSiteLocalizedLowerShriek_exact J 𝒪 U)
      I)

/-- Lemma 21.20.1: for a ringed site `(𝒞, 𝒪)`, an object `U : 𝒞`, and a K-injective complex of
`𝒪`-modules, the restricted complex on the localized ringed site `(𝒞/U, 𝒪_U)` is K-injective. -/
@[stacks 08FI]
abbrev localizedRestrictionComplex_isKInjective
    (I : CochainComplex Mod ℤ) [I.IsKInjective] :
    ((localizedRestrictionComplex X U).obj I).IsKInjective :=
  inferInstance

end RingedSite.Hom

end

end
