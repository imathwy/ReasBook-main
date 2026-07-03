import Mathlib
import stacks_project.Chap10.Definition_10_84_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable [Module.FaithfullyFlat R S]

/- Source/core/bridge triage:
* source-facing: descent of the countably generated projective condition along a faithfully flat
  base change;
* core/canonical owners: the chapter owner `Module.CountablyGenerated` from
  `Definition_10_84_1` and the owner predicate `Module.Projective`;
* sampled upstream declarations in this domain:
  `Module.countablyGenerated_iff`,
  `Module.countablyGenerated_of_countablyGenerated_tensorProduct_of_faithfullyFlat`,
  `Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated`;
* bridge/view: the theorem below packages the source statement in terms of these owner
  predicates, so no local duplicate owner for countable generation is needed here.
-/

-- Proof sketch: descend countable generation by Lemma `10.95.2`; for projectivity, use Theorem
-- `10.93.3` on the base-changed module, descend flatness and the Mittag-Leffler property by
-- faithful flatness, and use the countably generated hypothesis to obtain the required
-- countably-generated direct-sum decomposition on the `R`-side.
/-- Lemma 10.95.3: if the faithfully flat base change `S ⊗[R] M` is countably generated and
projective over `S`, then `M` is countably generated and projective over `R`. This is the
canonical Lean form of the textbook statement for `M ⊗_R S`. -/
theorem countablyGenerated_projective_of_countablyGenerated_projective_tensorProduct_of_faithfullyFlat
    [Module.Projective S (S ⊗[R] M)] (hcg : Module.CountablyGenerated S (S ⊗[R] M)) :
    Module.CountablyGenerated R M ∧ Module.Projective R M := sorry

end

end Module
