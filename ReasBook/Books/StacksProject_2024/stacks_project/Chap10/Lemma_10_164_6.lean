import Mathlib
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_164_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {k : ℕ}

/- Domain-style sampling:
* primary domain: descent of Serre's condition `(R_k)` along faithfully flat maps in commutative
  algebra;
* sampled owner declarations:
  `SerreConditionR`,
  `isNoetherianRing_of_faithfullyFlat`,
  `isRegularLocalRing_of_flat_localHom_of_regularTarget`,
  `serreConditionR_of_flat_of_fiber`;
* best owner abstraction: the chapter owner predicate `SerreConditionR`;
* primitive data vs. derived API: Noetherianity of `R` is derived canonically from faithful
  flatness by `isNoetherianRing_of_faithfullyFlat`, while the only remaining primitive field to
  supply is the primewise localized regularity clause of `SerreConditionR`.

Source/core/bridge triage:
* `source-facing`: `serreConditionR_of_faithfullyFlat`, the textbook faithfully flat descent
  statement for `(R_k)`;
* `core/canonical`: the owner predicate `SerreConditionR` and its field
  `SerreConditionR.isRegularLocalRing_localizationAtPrime`;
* `bridge/view`: local faithful-flat descent tools such as
  `isNoetherianRing_of_faithfullyFlat` and
  `isRegularLocalRing_of_flat_localHom_of_regularTarget`.

This file should therefore keep the source-facing theorem, but build the canonical owner directly
instead of treating the whole class-valued conclusion as opaque proof data.
-/
-- Proof sketch: `SerreConditionR S k` already gives `S` Noetherian, so Lemma `10.164.1` descends
-- Noetherianity to `R`. For a prime `p` of `R` with `height p ≤ k`, choose a prime `q` of `S`
-- lying over `p` that is minimal in the fiber over `p`. Faithful flatness localizes to a flat
-- local map `R_p → S_q` with closed fiber of dimension `0`, so Lemma `10.112.7` gives
-- `dim R_p = dim S_q`. Since `S` satisfies `(R_k)`, the local ring `S_q` is regular; then Lemma
-- `10.110.9` descends regularity along the flat local map, proving that `R_p` is regular.
/-- Lemma 10.164.6: if `f : R →+* S` is faithfully flat and `S` satisfies Serre's condition
`(R_k)`, then `R` satisfies Serre's condition `(R_k)`. Since `SerreConditionR` already includes
Noetherianity, this is exactly the textbook conclusion that `R` is Noetherian and has property
`(R_k)`. -/
theorem serreConditionR_of_faithfullyFlat (f : R →+* S) (hf : f.FaithfullyFlat)
    [SerreConditionR S k] : SerreConditionR R k := by
  let _ : IsNoetherianRing R := isNoetherianRing_of_faithfullyFlat f hf
  refine
    { toIsNoetherian := inferInstance
      isRegularLocalRing_localizationAtPrime := ?_ }
  intro p hp
  sorry

end
