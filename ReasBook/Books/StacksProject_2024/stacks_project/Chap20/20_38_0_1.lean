import Mathlib.Tactic.Recall
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap13.Lemma_13_29_3

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for 20.38.0.1:
- primary domain: lower truncation resolution systems of cochain complexes in an abelian category,
  reused in Chapter 20 for complexes of `𝒪_X`-modules on a ringed space;
- sampled owner declarations:
  `CategoryTheory.LowerTruncationResolutionSystem`,
  `CategoryTheory.LowerTruncationResolutionSystem.cone`,
  `CategoryTheory.LowerTruncationResolutionSystem.intoLimit`,
  `CategoryTheory.LowerTruncationResolutionSystem.intoLimit_comp_π`;
- best owner abstraction: the Chapter 13 owner `LowerTruncationResolutionSystem`, whose derived API
  already supplies the canonical cone to the inverse system and the induced morphism to its limit;
- primitive data versus derived API: the primitive data are only the chosen resolution system
  `S`; the cone and the comparison morphism to the inverse limit are derived owner API and should
  not survive as a second Chapter 20 wrapper.

Layer triage:
- `source-facing`: the canonical morphism from `𝓕^•` to the inverse-limit complex attached to a
  chosen lower truncation injective system;
- `core/canonical`: `LowerTruncationResolutionSystem.intoLimit`;
- `bridge/view`: this numbered item is now a direct recall of that owner, specialized to
  the ringed-space chapter context rather than a second local wrapper.
-/

/- 20.38.0.1: the canonical morphism `𝓕^• ⟶ 𝓘^•` into the
inverse-limit complex attached to a chosen lower truncation resolution system is the owner map
`LowerTruncationResolutionSystem.intoLimit`. -/
recall LowerTruncationResolutionSystem.intoLimit

section

variable {X : RingedSpace.{u}}
variable {F : CochainComplex (RingedSpace.Modules X) ℤ}
variable (S : LowerTruncationResolutionSystem (isInjective (RingedSpace.Modules X)) F)
variable [HasLimit S.diagram]

/- Specialized check for the Chapter 20 ringed-space context. -/
#check (S.intoLimit : F ⟶ limit S.diagram)

end

/- Companion recall: composing the canonical map with the `n`th limit projection recovers the
stage comparison map. -/
recall LowerTruncationResolutionSystem.intoLimit_comp_π

end AlgebraicGeometry.RingedSpace
