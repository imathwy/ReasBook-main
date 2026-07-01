import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain triage:
* primary domain: regular sequences on modules over commutative local rings;
* sampled owner API: `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.isRegular_cons_iff`,
  `IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal`,
  `IsLocalRing.isRegular_of_perm`;
* core/canonical owner: `RingTheory.Sequence.IsRegular M rs`;
* layer split: the regular sequence predicate is primitive owner data, while permutation invariance
  in the local/Noetherian setting is derived API.
-/

/- Lemma 10.68.4 is the canonical owner theorem `IsLocalRing.isRegular_of_perm`: over a local
ring, any permutation of an `M`-regular sequence is again `M`-regular. The textbook Noetherian and
finite hypotheses imply the ambient `IsNoetherian R M` assumption used by mathlib. -/
recall IsLocalRing.isRegular_of_perm
