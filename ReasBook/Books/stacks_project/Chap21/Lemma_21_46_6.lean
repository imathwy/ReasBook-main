import Mathlib
import stacks_project.Chap18.Lemma_18_19_2
import stacks_project.Chap21.Definition_21_46_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Lemma 21.46.6:
- primary domain: tor-amplitude in the derived category of modules on a ringed site, viewed as an
  object property with distinguished-triangle closure;
- sampled owner declarations:
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`,
  `CategoryTheory.hasTorAmplitudeIn_obj₃_of_distinguishedTriangle`,
  `CategoryTheory.hasTorAmplitudeIn_obj₂_of_distinguishedTriangle`,
  `CategoryTheory.hasTorAmplitudeIn_obj₁_of_distinguishedTriangle`;
- best owner abstraction: the source-facing owner is `HasTorAmplitudeIn` on
  `DerivedCategory (ringedSiteModuleCategory J 𝒪)`, while this file provides the three
  distinguished-triangle bridge lemmas for that owner in the ringed-site setting;
- primitive data: the ambient derived category `D(\mathcal O)`, a distinguished triangle in it,
  and the tor-amplitude hypotheses on the relevant vertices;
- derived API: the tor-amplitude conclusion for the remaining vertex.

Source/core/bridge triage:
- `source-facing`: the three textbook closure statements for tor-amplitude in a distinguished
  triangle;
- `core/canonical`: the owner predicate `HasTorAmplitudeIn`;
- `bridge/view`: these `obj₁`/`obj₂`/`obj₃_of_distinguishedTriangle` consequences.

The previous version carried `[HasSheafify J AddCommGrpCat]` and
`[J.WEqualsLocallyBijective AddCommGrpCat]` through the public theorem surface even though neither
the ambient category nor the owner predicate depends on them. This refinement removes those
proof-only assumptions from the API.
-/
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (DerivedCategory (ringedSiteModuleCategory J 𝒪))]

variable {a b : ℤ}

-- Proof sketch: apply the derived tensor functor with an arbitrary degree-zero `\mathcal O`-module
-- to the distinguished triangle, use preservation of distinguished triangles, and read off the
-- vanishing range for the third term from the resulting long exact homology sequence.
/-- Lemma 21.46.6 (1): in a distinguished triangle in `D(\mathcal O)`, if the first term has
tor-amplitude in `[a + 1, b + 1]` and the second term has tor-amplitude in `[a, b]`, then the
third term has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_obj₃_of_distinguishedTriangle
    (T : Triangle (DerivedCategory (ringedSiteModuleCategory J 𝒪)))
    (hT : T ∈ distTriang (DerivedCategory (ringedSiteModuleCategory J 𝒪)))
    (h₁ : HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1))
    (h₂ : HasTorAmplitudeIn T.obj₂ a b) :
    HasTorAmplitudeIn T.obj₃ a b := sorry

-- Proof sketch: apply the derived tensor functor with an arbitrary degree-zero `\mathcal O`-module
-- to the distinguished triangle and use the long exact homology sequence together with
-- two-out-of-three for vanishing outside `[a, b]`.
/-- Lemma 21.46.6 (2): in a distinguished triangle in `D(\mathcal O)`, if the first and third
terms have tor-amplitude in `[a, b]`, then the second term has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_obj₂_of_distinguishedTriangle
    (T : Triangle (DerivedCategory (ringedSiteModuleCategory J 𝒪)))
    (hT : T ∈ distTriang (DerivedCategory (ringedSiteModuleCategory J 𝒪)))
    (h₁ : HasTorAmplitudeIn T.obj₁ a b)
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₂ a b := sorry

-- Proof sketch: rotate the distinguished triangle and reduce to the first closure statement,
-- which shifts the tor-amplitude interval on the first vertex by one.
/-- Lemma 21.46.6 (3): in a distinguished triangle in `D(\mathcal O)`, if the second term has
tor-amplitude in `[a + 1, b + 1]` and the third term has tor-amplitude in `[a, b]`, then the
first term has tor-amplitude in `[a + 1, b + 1]`. -/
theorem hasTorAmplitudeIn_obj₁_of_distinguishedTriangle
    (T : Triangle (DerivedCategory (ringedSiteModuleCategory J 𝒪)))
    (hT : T ∈ distTriang (DerivedCategory (ringedSiteModuleCategory J 𝒪)))
    (h₂ : HasTorAmplitudeIn T.obj₂ (a + 1) (b + 1))
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1) := sorry

end

end SheafOfModules.RingedSite
