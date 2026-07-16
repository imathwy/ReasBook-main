import StacksProject_2024.stacks_project.Chap20.Lemma_20_26_12
import StacksProject_2024.stacks_project.Chap20.RingedSpaceModuleHasDerivedCategory
import StacksProject_2024.stacks_project.Chap20.Tor_amplitude_on_opens_ringed_site
import StacksProject_2024.stacks_project.Chap21.Lemma_21_46_2

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]
variable [MonoidalCategory (DerivedCategory (Modules X))]

local notation "ModX" => Modules X
local notation "SiteTermwiseFlat" => IsTermwiseFlat
/- Domain-style sampling for Lemma 20.48.2:
- primary domain: flatness of the cokernel of `d^{a - 1}` for a bounded-above flat complex
  representing a derived object of tor-amplitude in `[a, b]`;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn`,
  `CochainComplex.isTermwiseFlat_iff`,
  `hasTorAmplitudeIn_iff_opensRingedSiteHasTorAmplitudeIn`,
  `SheafOfModules.RingedSite.hasTorAmplitudeIn_iff_hasFlatRepresentativeInRange`,
  `SheafOfModules.RingedSite.isFlat_cokernel_dFrom_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeIn`;
- best owner abstraction:
  `source-facing`: the ringed-space flatness statement below;
  `core/canonical`: the canonical termwise-flat statement in this file together with the Chapter 21
    opens-site tor-amplitude and flat-representative owners;
  `bridge/view`: `CochainComplex.isTermwiseFlat_iff` and
    `hasTorAmplitudeIn_iff_opensRingedSiteHasTorAmplitudeIn`, which convert the source-facing
    degreewise-flat and ringed-space tor-amplitude hypotheses to canonical owner form.
-/

-- Proof sketch: the canonical theorem is the termwise-flat formulation. The tagged source-facing
-- degreewise-flat statement is a direct bridge through `CochainComplex.isTermwiseFlat_iff`, while
-- the termwise-flat theorem itself uses the opens-site tor-amplitude owner from Chapter 21.
/-- Canonical termwise-flat companion to Lemma 20.48.2: if `E^•` is bounded above and termwise
flat in the owner sense `SiteTermwiseFlat E`, and `Q(E)` has tor-amplitude in `[a, b]`, then the
cokernel of the differential `E^{a - 1} ⟶ E^a` is flat. -/
theorem isFlat_cokernel_dFrom_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeIn
    (E : CochainComplex ModX ℤ) (a b : ℤ)
    (hbounded : CochainComplex.minus ModX E)
    (hFlat : SiteTermwiseFlat E)
    (hTor : HasTorAmplitudeIn (DerivedCategory.Q.obj E) a b) :
    (cokernel (E.dFrom (a - 1))).IsFlat := by
  sorry

/-- Lemma 20.48.2: if `E^•` is a bounded above complex of flat `𝒪_X`-modules on a ringed space
`(X, 𝒪_X)` and `Q(E)` has tor-amplitude in `[a, b]`, then the cokernel of the differential
`E^{a - 1} ⟶ E^a` is a flat `𝒪_X`-module. -/
@[stacks 08CH]
theorem isFlat_cokernel_dFrom_of_boundedAbove_of_flat_terms_of_hasTorAmplitudeIn
    (E : CochainComplex ModX ℤ) (a b : ℤ)
    (hbounded : CochainComplex.minus ModX E)
    (hFlat : ∀ n : ℤ, (E.X n).IsFlat)
    (hTor : HasTorAmplitudeIn (DerivedCategory.Q.obj E) a b) :
    (cokernel (E.dFrom (a - 1))).IsFlat := by
  sorry

end

end AlgebraicGeometry.RingedSpace
