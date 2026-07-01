import Mathlib
import stacks_project.Chap10.Definition_10_103_8
import stacks_project.Chap10.Proposition_10_110_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain triage:
* primary domain: maximal Cohen-Macaulay modules over regular local rings;
* sampled owner declarations:
  `Module.MaximalCohenMacaulay`,
  `hasFiniteFreeResolutionLengthLE_of_moduleDepth_of_isRegularLocalRing`,
  `hasFiniteFreeResolutionLengthLE_zero_iff`,
  `IsRegularLocalRing.spanFinrank_maximalIdeal`;
* owner abstraction: the ambient owner predicates `Module.MaximalCohenMacaulay R M` and
  `IsRegularLocalRing R`;
* layer: `source-facing`, with the finite-free-resolution owner API providing the canonical bridge
  to freeness.
-/

-- Proof sketch: `IsRegularLocalRing.spanFinrank_maximalIdeal` identifies `ringKrullDim R` with a
-- natural number `d = (maximalIdeal R).spanFinrank`, and the maximal Cohen-Macaulay hypothesis
-- gives the same value for `moduleDepth R M`. Proposition `10.110.1` then yields a finite free
-- resolution of `M` of length at most `d - d = 0`, which is exactly freeness by the owner
-- definition of `HasFiniteFreeResolutionLengthLE`.
/-- Lemma 10.106.6: over a regular local ring `R`, every maximal Cohen-Macaulay `R`-module,
is free. -/
theorem free_of_maximalCohenMacaulay_of_isRegularLocalRing
    (hMCM : Module.MaximalCohenMacaulay R M) :
    Module.Free R M := sorry

end
