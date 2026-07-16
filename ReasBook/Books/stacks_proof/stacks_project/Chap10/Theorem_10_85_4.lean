import stacks_proof.stacks_project.Chap10.Lemma_10_85_1
import stacks_proof.stacks_project.Chap10.Lemma_10_85_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {P : Type v}
variable [CommRing R] [IsLocalRing R]
variable [AddCommGroup P] [Module R P] [Module.Projective R P]

/- Domain triage:
* primary domain: projective modules over local rings;
* sampled owner declarations:
  `allProjectiveModulesFree_iff_allCountablyGeneratedProjectiveModulesFree`,
  `Module.free_of_countablyGenerated_of_hasFiniteFreeComplementSummandProperty`,
  `Module.hasFiniteFreeComplementSummandProperty_of_projective_of_isLocalRing`;
* owner abstraction: `Module.Projective R P`, with the finite-free complement summand property as
  derived chapter API;
* layer: `source-facing`, since this numbered theorem states the local-ring freeness result itself,
  proved by the chapter's canonical reduction and owner-form companion. -/

open Module

-- Proof sketch: by Lemma `10.85.1`, it is enough to treat countably generated projective modules.
-- For a countably generated projective module over a local ring, the owner-form companion to
-- Lemma `10.85.3` gives the finite-free complement summand property, and Lemma `10.85.2` then
-- shows the module is free.
/-- Theorem 10.85.4: if `P` is a projective module over a local ring `R`, then `P` is free. -/
@[stacks 0593]
theorem projective_module_free_of_isLocalRing :
    Module.Free R P := by
  refine
    allProjectiveModulesFree_iff_allCountablyGeneratedProjectiveModulesFree.2 ?_ P
  intro Q _ _ _ hQ
  exact free_of_countablyGenerated_of_hasFiniteFreeComplementSummandProperty hQ
    hasFiniteFreeComplementSummandProperty_of_projective_of_isLocalRing

end
