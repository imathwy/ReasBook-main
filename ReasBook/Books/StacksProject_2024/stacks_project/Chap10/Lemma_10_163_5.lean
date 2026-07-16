import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_157_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {k : ℕ}
variable [SerreConditionR R k] [IsNoetherianRing S] [Module.Flat R S]

/- Domain sampling pass:
* primary domain: commutative algebra of Serre's condition `(R_k)` under flat ring maps and
  fiberwise regularity;
* sampled owner declarations:
  - `SerreConditionR`, the chapter owner predicate for `(R_k)` from
    `Definition_10_157_1.lean`;
  - `Ideal.Fiber`, the canonical fiber-ring owner `κ(𝔭) ⊗[R] S`;
  - `serreConditionS_of_flat_of_fiber`, the sibling owner-level ascent theorem for `(S_k)` in
    `Lemma_10_163_4.lean`;
  - `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber`, the local regularity transfer
    theorem for flat local maps in `Lemma_10_112_8.lean`.

Source/core/bridge triage:
* source-facing: `serreConditionR_of_flat_of_fiber`, the textbook ascent statement for `(R_k)`;
* core/canonical: the owner predicate `SerreConditionR` together with its primewise localized
  regularity field
  `SerreConditionR.isRegularLocalRing_localizationAtPrime`;
* bridge/view: the canonical fiber presentation `p.asIdeal.Fiber S`.

Primitive data already live in the owner abstraction: `(R_k)` on the base ring and on each fiber.
This file should therefore expose only the source-facing ascent theorem, not a parallel wrapper for
fiberwise regularity or localized regularity data.
-/

-- Proof sketch: to prove `(R_k)` for `S`, fix `q : PrimeSpectrum S` of height at most `k` and let
-- `p = q.asIdeal.under R`. Flatness gives going down, so Lemma `10.112.7` expresses
-- `dim S_q = dim R_p + dim ((κ(p) ⊗[R] S)_(q_fiber))`. The bound on `dim S_q` therefore bounds both
-- summands by `k`. Since `R` satisfies `(R_k)`, the localization `R_p` is regular; since the fiber
-- ring over `p` satisfies `(R_k)`, the corresponding localization of the fiber is regular. Lemma
-- `10.112.8` then upgrades these two regularity statements to regularity of `S_q`.
/-- Lemma 10.163.5: for a flat ring map `R → S`, if `R` satisfies Serre's condition `(R_k)`, `S`
is Noetherian, and every fiber ring `κ(𝔭) ⊗[R] S`, formalized as `p.asIdeal.Fiber S`, satisfies
`(R_k)`, then `S` satisfies `(R_k)`. -/
theorem serreConditionR_of_flat_of_fiber
    (hfiber : ∀ p : PrimeSpectrum R, SerreConditionR (p.asIdeal.Fiber S) k) :
    SerreConditionR S k := sorry

end
