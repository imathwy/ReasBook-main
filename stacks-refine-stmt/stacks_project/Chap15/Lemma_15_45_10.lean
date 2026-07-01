import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap10.Lemma_10_155_1
import stacks_project.Chap10.Lemma_10_155_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain-style sampling:
* primary domain: regular local rings under henselization and strict henselization in local
  commutative algebra;
* sampled owner declarations:
  `IsRegularLocalRing`,
  `isRegularLocalRing_of_flat_localHom_of_regularTarget`,
  `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber`,
  `isRegularLocalRing_closedFiber_of_quotient`;
* best owner abstraction: the source-facing statement should stay directly on the canonical owner
  `IsRegularLocalRing`; the theorem should therefore quantify only over the local ring and the
  chosen henselization / strict-henselization owners, recovering flatness, target Noetherianity,
  and closed-fiber regularity internally instead of exposing parallel auxiliary hypotheses;
* primitive data: the local base ring `R` and the chosen henselization / strict henselization
  owners;
* derived API: faithful flatness of `R → Rh` and `R → Rsh`, Noetherianity of `Rh` and `Rsh`, and
  regularity of the closed fibers through their quotient-field presentations.

Source/core/bridge triage:
* `source-facing`: the three-way `List.TFAE` for `IsRegularLocalRing`;
* `core/canonical`: `IsRegularLocalRing`;
* `bridge/view`: the closed-fiber owner `Ideal.Fiber (maximalIdeal R) S` together with the
  maximal-ideal image equalities for henselization and strict henselization.
-/

-- Proof sketch: for the backward implications, apply the canonical flat-local descent theorem for
-- regular local rings to the faithfully flat henselization and strict-henselization maps. For the
-- forward implications, apply the flat-local ascent theorem with regular closed fiber; the closed
-- fiber is canonically a residue-field quotient because the maximal ideal extends to the maximal
-- ideal of the henselization / strict henselization, hence it is a field and therefore a regular
-- local ring.
/-- Lemma 15.45.10: for a local ring `R`, the following are equivalent: `R` is a
regular local ring, a chosen henselization `Rh` of `R` is a regular local ring, and a chosen
strict henselization `Rsh` of `R` is a regular local ring. -/
theorem isRegularLocalRing_tfae_of_henselization_and_strictHenselization :
    List.TFAE [IsRegularLocalRing R, IsRegularLocalRing Rh, IsRegularLocalRing Rsh] := by
  sorry

end
