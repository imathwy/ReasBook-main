import Mathlib
import stacks_project.Chap10.Definition_10_157_1
import stacks_project.Chap10.Lemma_10_164_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {k : ℕ}

/- Domain-style sampling:
* primary domain: faithfully flat descent for Serre's condition `(S_k)` in commutative algebra;
* sampled owner declarations:
  `SerreConditionS`,
  `Module.SerreConditionS`,
  `SerreConditionS.moduleDepth_localizationAtPrime_ge_min`,
  `isNoetherianRing_of_faithfullyFlat`;
* best owner abstraction: the chapter owner predicate `SerreConditionS`;
* primitive data vs. derived API: Noetherianity of `R` is canonical derived data from faithful
  flatness, while the only primitive field still to supply for the owner is the localized depth
  inequality.

Source/core/bridge triage:
* `source-facing`: `serreConditionS_of_faithfullyFlat`, the textbook descent statement for
  Serre's condition `(S_k)`;
* `core/canonical`: the owner predicate `SerreConditionS` together with the module owner
  `Module.SerreConditionS R R k`;
* `bridge/view`: the self-module identification
  `Module.supportDim_self_eq_ringKrullDim`, which converts the module owner field into the usual
  ring-theoretic depth inequality.

This file should therefore keep the source-facing theorem directly on `SerreConditionS`, derive
Noetherianity canonically from faithful flatness, and build the owner instance explicitly rather
than treating the whole class-valued conclusion as opaque proof data.
-/
-- Proof sketch: Lemma `10.164.1` gives that `R` is Noetherian. For each prime `p` of `R`, choose
-- a prime `q` of `S` lying over `p` that is minimal in the fiber over `p`. The induced local map
-- `R_p → S_q` is flat local with closed fiber of dimension `0`, so Lemmas `10.112.7` and
-- `10.163.2` identify both the Krull dimension and the depth of `R_p` with those of `S_q`.
-- Since `S` satisfies `(S_k)`, the inequality `depth R_p ≥ min(k, dim R_p)` follows.
/-- Lemma 10.164.5: if `f : R →+* S` is faithfully flat and `S` satisfies Serre's condition
`(S_k)`, then `R` is Noetherian and satisfies `(S_k)`, i.e. `R` satisfies
`SerreConditionS R k`. -/
theorem serreConditionS_of_faithfullyFlat (f : R →+* S) (hf : f.FaithfullyFlat)
    [SerreConditionS S k] : SerreConditionS R k := by
  let _ : IsNoetherianRing R := isNoetherianRing_of_faithfullyFlat f hf
  refine
    { toIsNoetherian := inferInstance
      toSerreConditionS := ?_ }
  refine
    { toFinite := inferInstance
      moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
  intro p
  rw [Module.supportDim_self_eq_ringKrullDim]
  sorry

end
