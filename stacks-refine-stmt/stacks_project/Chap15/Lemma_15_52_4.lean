import Mathlib
import stacks_project.Chap10.Definition_10_162_1
import stacks_project.Chap10.Lemma_10_162_14
import stacks_project.Chap15.Lemma_15_51_4
import stacks_project.Chap15.Lemma_15_51_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-
Domain-style sampling:
- primary domain: Noetherian local Nagata rings and geometric reducedness of formal fibers;
- sampled owner declarations:
  `NagataRing`,
  `LocalFormalFibersHaveProperty`,
  `IsAnalyticallyUnramified`,
  `Algebra.IsGeometricallyReducedProperty`;
- best owner abstraction: the source-facing local formal-fiber hypothesis should use the Chapter 15
  owner `LocalFormalFibersHaveProperty`, specialized to the canonical bridge
  `Algebra.IsGeometricallyReducedProperty`, while `NagataRing` remains the source-facing owner on
  the ring side;
- primitive data vs. derived API: the primitive data are the Noetherian local ring `A` and the
  formal-fiber property owner. The expanded quantifier over `q : PrimeSpectrum A` and the explicit
  fiber expression are derived API and should not remain the main public surface.

Source/core/bridge triage:
- `source-facing`: the equivalence between the Nagata condition and geometrically reduced formal
  fibers for a Noetherian local ring;
- `core/canonical`: `NagataRing`, `LocalFormalFibersHaveProperty`, `IsAnalyticallyUnramified`, and
  `Algebra.IsGeometricallyReducedProperty`;
- `bridge/view`: Lemma `10.162.14` supplies the analytic-unramified bridge, while
  `LocalFormalFibersHaveProperty` packages the fiberwise condition.
-/

-- Proof sketch: apply Lemma `10.162.14` to identify the Nagata condition for a Noetherian local
-- ring with analytic unramifiedness of finite local domain extensions. For the forward direction,
-- geometrically reduced formal fibers imply the relevant completions are reduced after passing to
-- fraction fields, hence those local extensions are analytically unramified. For the reverse
-- direction, use the Nagata criterion to show that every finite residue-field extension of every
-- prime formal fiber remains reduced.
/-- Lemma 15.52.4: for a Noetherian local ring `A`, being Nagata is equivalent to having
geometrically reduced formal fibers. -/
theorem nagataRing_iff_geometricallyReduced_formalFibers :
    NagataRing A ↔
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyReducedProperty A := sorry

end
