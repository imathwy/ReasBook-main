import Mathlib
import stacks_project.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A] [IsLocalRing A] [IsNoetherianRing A]

/- Domain-style sampling for Lemma 15.38.2:
- primary domain: local commutative algebra relating adic formal smoothness of `k → A` to the
  regular-local owner on `A`;
- sampled owner declarations of the same kind:
  `RingHom.formally_smooth_for_adic`,
  `RingHom.formally_smooth_for_adic_tfae_completion_invariance`,
  `IsRegularLocalRing`,
  `RingHom.IsRegularRingMap.of_comp_of_faithfullyFlat`;
- best owner abstraction: the hypothesis should be stated directly with the chapter owner
  `(algebraMap k A).formally_smooth_for_adic (maximalIdeal A)`, while the conclusion stays on the
  canonical owner `IsRegularLocalRing A`;
- primitive data: the field `k`, the Noetherian local `k`-algebra `A`, and adic formal smoothness
  of the structure map;
- derived API: completion invariance, complete-local presentations, and regularity descent are
  proof inputs only and should not appear as extra wrapper data in the public statement.

Source/core/bridge triage:
- `source-facing`: the implication from maximal-ideal-adic formal smoothness to regularity;
- `core/canonical`: `RingHom.formally_smooth_for_adic` and `IsRegularLocalRing`;
- `bridge/view`: completion and Cohen-structure arguments used internally in the proof.
-/

-- Proof sketch: pass from the given `k`-adic formal smoothness hypothesis to the completion using
-- the completion invariance results from Section `15.37`, reduce to the complete local case, and
-- then apply Cohen structure to identify the completed ring with a quotient of a power series ring.
-- The induced surjection to the power series ring is an isomorphism on `maximalIdeal / maximalIdeal^2`,
-- forcing the dimension of `A` to equal the embedding dimension, which is the definition of
-- regularity for a Noetherian local ring.
/-- Lemma 15.38.2: if `A` is a Noetherian local `k`-algebra and the structure map `k → A` is
formally smooth for the `maximalIdeal A`-adic topology, then `A` is a regular local ring. -/
theorem isRegularLocalRing_of_formallySmooth_for_maximalIdeal_adic
    (hfs : (algebraMap k A).formally_smooth_for_adic (maximalIdeal A)) :
    IsRegularLocalRing A := sorry

end
