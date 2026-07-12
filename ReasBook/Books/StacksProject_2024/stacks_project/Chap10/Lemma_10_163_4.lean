import Mathlib
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_112_7
import StacksProject_2024.Chap10.Lemma_10_163_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {k : ℕ}
variable [SerreConditionS R k] [IsNoetherianRing S] [Module.Flat R S]

/-
Domain-style sampling pass:
* primary domain: Serre's condition `(S_k)` in commutative algebra under flat base change and
  fiberwise hypotheses;
* sampled owner declarations:
  - `SerreConditionS`, the chapter owner for the ring-theoretic `(S_k)` condition from
    `Definition_10_157_1.lean`;
  - `SerreConditionS.moduleDepth_localizationAtPrime_ge_min`, the primewise localized depth bound
    already derived from that owner;
  - `depth_target_eq_depth_source_add_depth_closed_fiber`, the local depth-additivity owner from
    `Lemma_10_163_2.lean`;
  - `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown`,
    the local fiber-dimension formula from `Lemma_10_112_7.lean`.

Best owner abstraction:
* the public statement should stay on the canonical ring owner `SerreConditionS`;
* the canonical fiber input is `p.asIdeal.Fiber S`;
* the local ring `fiberLocalRingAt R S q` is supporting bridge data for the proof, not a second
  public owner.

Primitive data vs. derived API:
* primitive data: the flat algebra `R → S`, the owner hypothesis `[SerreConditionS R k]`, the
  Noetherian target hypothesis on `S`, and the fiberwise owner hypothesis `hfiber`;
* derived API: the localized depth inequalities, the closed-fiber depth formula, and the
  local-fiber dimension formula used to verify the defining primewise inequality for
  `SerreConditionS S k`.

Source/core/bridge triage:
* `source-facing`: `serreConditionS_of_flat_of_fiber`, the textbook ascent statement for `(S_k)`;
* `core/canonical`: `SerreConditionS` together with its primewise localized depth theorem;
* `bridge/view`: the local flat map `R_(q ∩ R) → S_q`, its closed fiber, and the canonical local
  fiber ring `fiberLocalRingAt R S q`.
-/
-- Proof sketch: for each `q : PrimeSpectrum S`, set `p = q.asIdeal.under R`. The owner theorem
-- `SerreConditionS.moduleDepth_localizationAtPrime_ge_min` gives the `(S_k)` bound on `R_p`, and
-- the same owner theorem applied to `hfiber p` gives the `(S_k)` bound on the local fiber over
-- `q`. The local depth formula `depth_target_eq_depth_source_add_depth_closed_fiber` for
-- `R_p → S_q` and the local dimension formula
-- `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown`
-- combine these two bounds to yield `depth S_q ≥ min(k, dim S_q)`.
/-- Lemma 10.163.4: for a flat ring map `R → S`, if `R` satisfies Serre's condition `(S_k)`, `S`
is Noetherian, and every fiber ring `κ(𝔭) ⊗[R] S`, formalized as `p.asIdeal.Fiber S`, satisfies
`(S_k)`, then `S` satisfies `(S_k)`. -/
theorem serreConditionS_of_flat_of_fiber
    (hfiber : ∀ p : PrimeSpectrum R, SerreConditionS (p.asIdeal.Fiber S) k) :
    SerreConditionS S k := sorry

end
