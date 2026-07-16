import Mathlib
import Mathlib.Tactic.TFAE
import StacksProject_2024.stacks_project.Chap10.Definition_10_109_2
import StacksProject_2024.stacks_project.Chap10.Definition_10_109_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- 
Domain-style sampling:
* primary domain: homological characterizations of regular local rings for Noetherian local rings;
* sampled owner declarations:
  `projectiveDimension`,
  `projectiveDimension_ne_top_iff`,
  `IsFiniteGlobalDimensionRing`,
  `IsRegularLocalRing.iff_finrank_cotangentSpace`;
* best owner abstraction: the canonical owners are the residue-field invariant
  `projectiveDimension (ModuleCat.of R (ResidueField R))`, the ring-level owner
  `IsFiniteGlobalDimensionRing R`, and the local-regularity owner `IsRegularLocalRing R`;
* primitive data vs. derived API:
  the three owner predicates/invariants above are primitive for this proposition;
  the TFAE statement and the equalities involving `globalDimension R`, `ringKrullDim R`, and the
  cotangent-space finrank are derived API;
* source/core/bridge triage:
  the TFAE theorem is `source-facing`,
  the owner abstractions above are `core/canonical`,
  and the two equality theorems are `bridge/view` consequences.

This file should therefore stay owner-facing and avoid introducing any extra local wrapper for
"finite projective dimension of the residue field" or for regular locality.
-/

-- Proof sketch: use Proposition `10.110.1` to prove that a regular local ring has finite global
-- dimension, the definition of finite global dimension to deduce finite projective dimension for
-- the residue field, and Lemmas `10.110.3` and `10.110.4` together with the characterization of
-- regular local rings from Definition `10.60.10` to recover regularity from finite projective
-- dimension of the residue field.
/-- Proposition 10.110.5: for a Noetherian local ring `R`, the following are equivalent: the
residue field `ResidueField R` has finite projective dimension as an `R`-module, `R` has finite
global dimension, and `R` is a regular local ring. -/
theorem residueField_finiteProjectiveDimension_finiteGlobalDimension_regularLocal_tfae :
    List.TFAE
      [ projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤,
        IsFiniteGlobalDimensionRing R,
        IsRegularLocalRing R ] := sorry

variable [IsFiniteGlobalDimensionRing R]

-- Proof sketch: finite global dimension gives `globalDimension R` as a projective-dimension bound
-- for every module. Apply the main TFAE theorem to obtain regularity, use Proposition `10.110.1`
-- to bound the global dimension above by `ringKrullDim R`, and use the residue-field lower bound
-- from Lemma `10.110.3` together with the dimension bound from Lemma `10.110.4` to get the
-- reverse inequality.
/-- Under finite global dimension, the global dimension of a Noetherian local ring equals its Krull
dimension. -/
theorem globalDimension_eq_ringKrullDim_of_finiteGlobalDimension :
    globalDimension R = ringKrullDim R := sorry

-- Proof sketch: by the previous theorem, `globalDimension R = ringKrullDim R`. The finite-global-
-- dimension hypothesis implies finite projective dimension for the residue field, so Lemmas
-- `10.110.3` and `10.110.4` force `ringKrullDim R` and the cotangent-space dimension to coincide.
/-- Under finite global dimension, the Krull dimension of a Noetherian local ring equals the
dimension of its cotangent space `maximalIdeal R / (maximalIdeal R)^2` over the residue field. -/
theorem ringKrullDim_eq_finrank_cotangentSpace_of_finiteGlobalDimension :
    ringKrullDim R = Module.finrank (ResidueField R) (CotangentSpace R) := sorry

end
