import StacksProject_2024.Chap13.Lemma_13_31_9
import StacksProject_2024.Chap17.Remark_17_13_5
import StacksProject_2024.Chap20.Lemma_20_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open ClosedSubsetSectionsWithSupport
open scoped RingedSpaceClosedSubsetSectionsWithSupport

/- Domain-style sampling for Lemma 20.34.3:
- primary domain: K-injective cochain complexes of module sheaves on a ringed space under the
  closed-subset pushforward/sections-with-support adjunction;
- sampled owner declarations:
  `closedSubsetModulePushforward`,
  `RingedSpace.ClosedSubsetSectionsWithSupport.pushforwardSectionsWithSupportAdjunction`,
  `closedSubsetModulePushforward_additive`,
  `closedSubsetSectionsWithSupport_additive`,
  `𝓗[hZ]`,
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- best owner abstractions:
  `closedSubsetModulePushforward X Z` and `𝓗[hZ]` for the Chapter 17 closed-subset functors, with
  the Chapter 13 K-injective-preservation theorem as the core owner theorem.

Primitive-vs-derived split:
- primitive data: the ringed space `X`, the closed subset `Z ⊆ X` with hypothesis `hZ`, and the
  K-injective complex `I`;
- derived API: K-injectivity of the image under `𝓗[hZ]`; the exactness and adjunction input
  belongs to the earlier Chapter 17/13 proof route and should not appear as new public data in the
  present file.

Source/core/bridge triage:
- `source-facing`: the sections-with-support functor for the closed subset `Z` sends K-injective
  complexes of `𝒪_X`-modules to K-injective complexes of `𝒪_X|_Z`-modules;
- `core/canonical`: `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- `bridge/view`: this file specializes that owner theorem to the Chapter 20 closed-subset
  functors, keeping the ringed-space data on the public theorem surface. -/

section

variable {X : RingedSpace.{u}} {Z : Set X}

local notation "ModX" => RingedSpace.Modules X
local notation "ModZ" => closedSubsetModuleCategory X Z

-- Proof sketch: this is the closed-subset specialization of the Chapter 13 preservation theorem
-- for a right adjoint to an exact left adjoint. The target file keeps only the source-facing
-- K-injective statement and does not package the intermediate adjunction data as local API.
/-- For a closed subset `Z ⊆ X`, the sections-with-support functor `𝓗[hZ]` sends
K-injective cochain complexes of `𝒪_X`-modules to K-injective cochain complexes of
`𝒪_X|_Z`-modules. -/
instance closedSubsetModuleSectionsWithSupportFunctor_mapHomologicalComplex_isKInjective
    (hZ : IsClosed Z)
    (I : CochainComplex ModX ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective ((𝓗[hZ].mapHomologicalComplex (up ℤ)).obj I) := by
  exact
    right_adjoint_preserves_isKInjective_of_exact_left_adjoint
      𝓗[hZ]
      (closedSubsetModulePushforward X Z)
      (pushforwardSectionsWithSupportAdjunction hZ)
      (closedSubsetModulePushforward_exact X Z hZ)
      I

/-- Lemma 20.34.3: if `X` is a ringed space, `Z ⊆ X` is closed, and `I` is a K-injective complex
of `𝒪_X`-modules, then the complex `𝓗[hZ](I)` is K-injective as a complex of
`𝒪_X|_Z`-modules. -/
@[stacks 0G6Z]
theorem closedSubsetModuleSectionsWithSupportFunctor_isKInjective
    (hZ : IsClosed Z)
    (I : CochainComplex ModX ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective ((𝓗[hZ].mapHomologicalComplex (up ℤ)).obj I) :=
  inferInstance

end

end AlgebraicGeometry.RingedSpace
