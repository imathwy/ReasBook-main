import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.Tactic.Recall

universe u

/-
Source/core/bridge triage:
- `source-facing`: a divided power structure on an ideal `I` of a commutative ring `A`;
- `core/canonical`: the mathlib owner `DividedPowers I`;
- `bridge/view`: none needed here, because the source item is exactly the canonical owner.
-/

/-
Definition 23.2.1 (Tag 07GL): for a ring `A` and an ideal `I` of `A`, a divided power structure
on `I` is the canonical mathlib structure `DividedPowers I`.
-/
recall DividedPowers {A : Type u} [CommSemiring A] (I : Ideal A) : Type u
