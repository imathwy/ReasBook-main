import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap17.Remark_17_13_5

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

open scoped RingedSpaceClosedSubsetSectionsWithSupport

section

open RingedSpace.ClosedSubsetSectionsWithSupport

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)
variable (𝒢 : RingedSpace.closedSubsetModuleCategory X Z)
variable (ℱ : X.Modules)

/- Domain-style sampling for Lemma 17.13.6:
- primary domain: the adjunction between pushforward and sections-with-support for
  `\mathcal O_X`-modules along a closed subset inclusion `Z ↪ X`;
- sampled owner API:
  `RingedSpace.closedSubsetModulePushforward`,
  `RingedSpace.ClosedSubsetSectionsWithSupport.functor`,
  `RingedSpace.ClosedSubsetSectionsWithSupport.pushforwardSectionsWithSupportAdjunction`,
  `Adjunction.homEquiv`,
  `Equiv.bijective`;
- best owner abstraction: the source-facing closed-subset adjunction
  `pushforwardSectionsWithSupportAdjunction hZ :
    RingedSpace.closedSubsetModulePushforward X Z ⊣ 𝓗[hZ]`;
- primitive data: a ringed space `X`, a closed subset `Z ⊆ X`, its closedness proof `hZ`, an
  `\mathcal O_X|_Z`-module `𝒢`, and an `\mathcal O_X`-module `ℱ`;
- derived API: the hom-set equivalence
  `((pushforwardSectionsWithSupportAdjunction hZ).homEquiv 𝒢 ℱ)` and its
  canonical bijectivity theorem.

Source/core/bridge triage:
- `source-facing`: the Stacks bijection
  `\operatorname{Hom}_X(i_* \mathcal G, \mathcal F) \cong
    \operatorname{Hom}_{\mathcal O_X|_Z}(\mathcal G, \mathcal H_Z(\mathcal F))`;
- `core/canonical`: `Adjunction.homEquiv`;
- `bridge/view`: the closed-immersion specialization obtained by pulling this adjunction back
  along an actual closed immersion of ringed spaces.

This item stays at the `source-facing` closed-subset layer by recalling the canonical adjunction
and its hom-set bijection directly, rather than routing the public surface through the
closed-immersion bridge wrapper.
-/

/- Lemma 17.13.6: for a closed subset inclusion `i : Z ↪ X`, pushforward of
`\mathcal O_X|_Z`-modules is left adjoint to the explicit sections-with-support functor
`𝓗[hZ] = \mathcal H_Z`. -/
recall pushforwardSectionsWithSupportAdjunction

/- Lemma 17.13.6 companion: the source bijection on hom-sets is the canonical bijectivity theorem
of the specialized adjunction hom-equivalence. -/
#check ((pushforwardSectionsWithSupportAdjunction hZ).homEquiv 𝒢 ℱ).bijective

end

end AlgebraicGeometry
