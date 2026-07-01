import Mathlib
import stacks_project.Chap20.Lemma_20_35_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- 
Domain-style sampling for Lemma 21.22.3:
- primary domain: inverse-limit topologies on sequential systems of `A`-modules and their
  comparison with the `I`-adic topology via Noetherian hypotheses over the associated graded ring;
- sampled owner declarations:
  * `idealAssociatedGradedRing`;
  * `Ideal.adicModuleTopology`;
  * `CategoryTheory.inverseLimitTopology`;
  * `CategoryTheory.inverseLimitTopology_eq_adicModuleTopology_of_noetherian_kernelAssociatedGraded`.
- owner choice:
  * `source-facing`: the cohomological direct sum
    `DirectSum ℕ fun n ↦ idealPowerCohomology n`;
  * `core/canonical`: `CategoryTheory.inverseLimitTopology cohomologySystem`;
  * `bridge/view`: the source comparison from the ideal-power cohomology direct sum to the kernel
    associated graded used by the abstract Chapter 20 owner theorem.
- primitive data: the ideal `I`, the inverse system `cohomologySystem`, and the family
  `idealPowerCohomology`;
- derived API: the module and Noetherian structures on
  `DirectSum ℕ fun n ↦ idealPowerCohomology n`, together with the equality of topologies.

The local `inverseLimitTopology` wrapper was duplicating the Chapter 20 owner abstraction, and the
local direct-sum abbreviation was only a one-off type alias. This file therefore reuses the owner
directly and keeps the source-facing direct sum as a bare canonical expression.
-/

-- Proof sketch: apply the source hypothesis to the direct sum of the modules
-- `H^p(\mathcal C, I^n \mathcal F_{n+1})` to obtain finite generation over the associated graded
-- ring `⊕_n I^n / I^{n+1}`. This gives eventual equalities `I F^n = F^{n+1}` for the kernel
-- filtration on `lim_n H^p(\mathcal C, \mathcal F_n)`, so the inverse-limit and `I`-adic
-- neighbourhood bases coincide.
/-- Lemma 21.22.3: for the cohomology inverse system `n ↦ H^p(\mathcal C, \mathcal F_n)` coming
from a system of sheaves with `\mathcal F_n = \mathcal F_{n + 1} / I^n \mathcal F_{n + 1}`, if
the direct sum `⊕_{n \geq 0} H^p(\mathcal C, I^n \mathcal F_{n + 1})` is Noetherian over the
associated graded ring `⊕_{n \geq 0} I^n / I^{n + 1}`, then the inverse-limit topology on
`lim_n H^p(\mathcal C, \mathcal F_n)` equals the `I`-adic topology. -/
lemma cohomology_inverseLimitTopology_eq_adicModuleTopology_of_noetherian_associatedGraded
    {A : Type u} [CommRing A] (I : Ideal A)
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A)
    (idealPowerCohomology : ℕ → ModuleCat A)
    [Module (idealAssociatedGradedRing I)
      (DirectSum ℕ fun n ↦ idealPowerCohomology n)]
    [IsNoetherian (idealAssociatedGradedRing I)
      (DirectSum ℕ fun n ↦ idealPowerCohomology n)] :
    inverseLimitTopology cohomologySystem =
      Ideal.adicModuleTopology I ↥(limit cohomologySystem) := sorry
