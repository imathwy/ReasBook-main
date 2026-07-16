import Mathlib
import StacksProject_2024.stacks_project.Chap10.Proposition_10_89_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum

universe u v w

namespace Module

namespace MittagLeffler

section DirectSum

/- Domain-style sampling:
- primary domain: the owner class `Module.MittagLeffler` and its closure properties;
- sampled declarations of the same kind:
  `Module.MittagLeffler` from `Definition_10_88_7`,
  `Module.mittagLeffler_iff_tensorProduct_piRight_injective` from `Proposition_10_89_5`,
  `CategoryTheory.ShortComplex.UniversallyExact.mittagLeffler_X₂` from `Lemma_10_89_7`,
  `Module.mittagLeffler_colimit_of_directedSystem` from `Lemma_10_89_9`,
  together with the owner-shaped mathlib declarations `Module.Flat.directSum_iff`,
  `Module.Flat.directSum`, and the definitional companion `Module.Flat.dfinsupp_iff`.
- best owner abstraction: `Module.MittagLeffler`; the direct-sum statement is derived API of this
  owner, not a separate local wrapper notion.
- layer: `source-facing` theorem stated through the canonical owner.
- primitive data: the family of summands `M`.
- derived API: the direct-sum characterization/instance, with the `Π₀` formulation only as a thin
  definitional companion.
-/

section

variable {R : Type u} [CommRing R]
variable {I : Type v} {M : I → Type w}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

-- Proof sketch: for the forward implication, each summand is a direct summand of the direct sum,
-- so apply Lemma `10.89.7 (1)` to the split universally exact sequence coming from the projection
-- onto the `i`-th summand. For the reverse implication, express `Π₀ i, M i` as the directed
-- colimit of its finite partial sums; each finite partial sum is Mittag-Leffler by repeated use of
-- Lemma `10.89.7 (2)`, and Lemma `10.89.9` finishes the passage to the full direct sum.
/-- Lemma 10.89.10: a direct sum `⨁ i, M i` of `R`-modules is Mittag-Leffler if and only if each
summand `M i` is Mittag-Leffler. -/
theorem directSum_iff :
    Module.MittagLeffler R (⨁ i, M i) ↔ ∀ i, Module.MittagLeffler R (M i) := sorry

/-- The `Π₀` presentation is a definitional companion to `directSum_iff`. -/
theorem dfinsupp_iff :
    Module.MittagLeffler R (Π₀ i, M i) ↔ ∀ i, Module.MittagLeffler R (M i) :=
  directSum_iff ..

/-- A direct sum of Mittag-Leffler `R`-modules is Mittag-Leffler. -/
instance directSum [∀ i, Module.MittagLeffler R (M i)] :
    Module.MittagLeffler R (⨁ i, M i) :=
  directSum_iff.2 ‹_›

instance dfinsupp [∀ i, Module.MittagLeffler R (M i)] :
    Module.MittagLeffler R (Π₀ i, M i) :=
  dfinsupp_iff.2 ‹_›

end

end DirectSum

end MittagLeffler

end Module
