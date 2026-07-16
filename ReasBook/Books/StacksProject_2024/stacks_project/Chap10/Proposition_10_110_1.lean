import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_72_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_109_10
import StacksProject_2024.stacks_project.Chap10.Lemma_10_109_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-
Domain-style sampling:
* primary domain: projective/global dimension bounds for finite modules over regular local rings;
* sampled owner declarations:
  `HasProjectiveDimensionLE`,
  `HasGlobalDimensionLE`,
  `hasProjectiveDimensionLE_iff_hasFiniteFreeResolutionLengthLE`,
  `moduleDepth`;
* best owner abstraction: the module-wise bound should first be stated through the canonical owner
  `HasProjectiveDimensionLE (ModuleCat.of R M) n`, while the finite-free-resolution theorem is the
  source-facing bridge supplied by Lemma `10.109.7`;
* source/core/bridge triage:
  the projective-dimension theorem below is `core/canonical`,
  Proposition `10.110.1 (1)` remains `source-facing`,
  and `hasProjectiveDimensionLE_iff_hasFiniteFreeResolutionLengthLE` is the `bridge/view`;
* primitive data: the ambient regular-local owner `[IsRegularLocalRing R]`, the finite module `M`,
  and the source-faithful numerical equalities `ringKrullDim R = d` and `moduleDepth R M = e`;
* derived API: the finite free resolution of length at most `d - e`.

The proposition does not need a second free-resolution owner. The chapter owner is projective
dimension, and the finite-free-resolution surface is derived from that owner in the local
Noetherian setting.
-/

-- Proof sketch: regular local rings are Cohen-Macaulay as modules over themselves, so the ring
-- depth equals `ringKrullDim R = d`. The Auslander--Buchsbaum formula then gives projective
-- dimension `d - e` for `M`, hence the corresponding owner bound.
/-- Core/canonical form of Proposition 10.110.1 (1): if `R` is a regular local ring of dimension
`d` and `M` is a finite `R`-module of depth `e`, then `M` has projective dimension at most
`d - e`. -/
theorem hasProjectiveDimensionLE_of_moduleDepth_of_isRegularLocalRing
    {d e : ℕ} (hdim : ringKrullDim R = d) (hdepth : moduleDepth R M = e) :
    HasProjectiveDimensionLE (ModuleCat.of R M) (d - e) := sorry

/-- Proposition 10.110.1 (1): if `R` is a regular local ring of dimension `d` and `M` is a finite
`R`-module of depth `e`, then `M` admits a finite free resolution of length at most `d - e`. -/
theorem hasFiniteFreeResolutionLengthLE_of_moduleDepth_of_isRegularLocalRing
    {d e : ℕ} (hdim : ringKrullDim R = d) (hdepth : moduleDepth R M = e) :
    HasFiniteFreeResolutionLengthLE R M (d - e) := by
  exact
    (hasProjectiveDimensionLE_iff_hasFiniteFreeResolutionLengthLE (d - e)).mp
      (hasProjectiveDimensionLE_of_moduleDepth_of_isRegularLocalRing hdim hdepth)

-- Proof sketch: apply the canonical module-wise bound above to finite modules and then use the
-- finite/cyclic criterion for the owner `HasGlobalDimensionLE R d`.
/-- Proposition 10.110.1 (2): a regular local ring of dimension `d` has global dimension at most
`d`. -/
theorem hasGlobalDimensionLE_of_isRegularLocalRing
    {d : ℕ} (hdim : ringKrullDim R = d) :
    HasGlobalDimensionLE R d := sorry

end
