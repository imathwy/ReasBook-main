import StacksProject_2024.stacks_project.Chap21.Definition_21_45_1
import StacksProject_2024.stacks_project.Chap21.Definition_21_46_1
import StacksProject_2024.stacks_project.Chap21.Definition_21_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Lemma 21.47.3:
- primary domain: perfection criteria for derived `\mathcal O`-modules on a ringed site via
  tor-amplitude and pseudo-coherence;
- sampled owner declarations:
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`,
  `RingedSite.DerivedCategory.IsMPseudoCoherent`,
  `RingedSite.DerivedCategory.IsPerfect`,
  `RingedSite.Hom.localizedRestrictionDerived`;
- best owner abstraction: the Chapter 21 source-facing owners
  `HasTorAmplitudeIn`, `RingedSite.DerivedCategory.IsMPseudoCoherent`, and the intrinsic
  ringed-site owner `RingedSite.DerivedCategory.IsPerfect`;
- primitive data: the derived object `E`, the interval bounds `a, b`, the tor-amplitude witness
  on `[a, b]`, and the `(a - 1)`-pseudo-coherence witness;
- derived API: the perfection conclusion below.

Source/core/bridge triage:
- `source-facing`: the perfection criterion below;
- `core/canonical`: the Chapter 21 owners `HasTorAmplitudeIn`,
  `RingedSite.DerivedCategory.IsMPseudoCoherent`, and
  `RingedSite.DerivedCategory.IsPerfect`;
- `bridge/view`: none in this file; the previous representative-style local
  `IsMPseudoCoherent` duplicate is deleted in favor of the owner predicate from
  `Definition_21_45_1`. -/

variable {X : RingedSite.{u, v}}

variable [HasBinaryProducts X.carrier]
variable [∀ U : X, (localizedRestriction X U).Additive]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
variable [CategoryWithHomology (ModuleCat X)]
variable [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))]
variable [MonoidalCategory (ModuleDerived X)]

local notation "DMod" => ModuleDerived X

/-- Lemma 21.47.3: let `(𝒞, 𝒪)` be a ringed site, let `E` be an object of
`D(𝒪)`, and let `a, b` be integers. If `E` has tor-amplitude in `[a, b]` and is
`(a - 1)`-pseudo-coherent, then `E` is perfect. -/
@[stacks 08G7]
theorem isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent
    (E : DMod) (a b : ℤ)
    (hE : HasTorAmplitudeIn E a b)
    (hpc : E.IsMPseudoCoherent (a - 1)) :
    E.IsPerfect := by
  rcases hpc with ⟨K, eK, hKpc⟩
  have hKperfect : RingedSite.CochainComplex.IsPerfect K := by
    intro U
    rcases hKpc U with ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro I
    rcases hT I with ⟨P, hP, α, hαiso, hαepi⟩
    -- Route correction: the proof is now reduced to the source-faithful local construction.
    -- Starting from the strict-perfect approximation `α`, use the tor-amplitude hypothesis to
    -- identify the boundary cokernel in degree `a` as flat, replace `P` by the resulting strict-
    -- perfect tail complex on a refined cover, and then strictify the resulting comparison to a
    -- quasi-isomorphism. The source proof works directly on the slice-site derived restriction.
    --
    -- TODO for Lemma 21.47.3: build the local strict-perfect tail complex from `P`, using the
    -- tor-amplitude interval to prove flatness of `cokernel (P.dFrom (a - 1))`. The first open
    -- blocker is upgrading the representative-level normalization to the homotopy/derived
    -- comparison needed to transport `HasTorAmplitudeIn` to the slice site in a way that meshes
    -- with the available local monoidal owner on `D(𝒪_{I.Y})`. Once that transport is available,
    -- the remaining steps are the source-faithful boundary-cokernel and tail-complex
    -- constructions, followed by Lemma `18.29.3`.
    sorry
  -- Proof comment: once the representative complex is locally perfect, package it back into the
  -- derived-category owner.
  exact ⟨K, eK, hKperfect⟩

end

end SheafOfModules.RingedSite
