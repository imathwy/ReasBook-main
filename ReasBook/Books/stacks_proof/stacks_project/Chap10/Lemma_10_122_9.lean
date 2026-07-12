import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain triage:
* primary domain: quasi-finite ring maps and their base-change stability;
* source-facing layer: a base change of a quasi-finite ring map is quasi-finite;
* core/canonical owner: `RingHom.QuasiFinite.isStableUnderBaseChange`;
* derived API: the `Algebra.QuasiFinite` and `Algebra.QuasiFiniteAt` instances used internally by
  mathlib to prove the owner theorem.

Primitive data vs. derived API:
* primitive input: a quasi-finite ring hom together with a base-change square;
* derived layer: primewise/tensor-product reformulations belong to the internal proof of the owner
  theorem, not to this file's public API.
-/

/- Lemma 10.122.9: any base change of a quasi-finite ring map is quasi-finite. This is exactly the
canonical mathlib theorem `RingHom.QuasiFinite.isStableUnderBaseChange`. -/
recall RingHom.QuasiFinite.isStableUnderBaseChange
