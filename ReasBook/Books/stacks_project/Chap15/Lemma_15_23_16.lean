import stacks_project.Chap15.Lemma_15_23_4
import stacks_project.Chap15.Lemma_15_23_11
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Module
open LocalizedModule (AtPrime)

/-
Domain-style sampling:
- primary domain: reflexive finite modules over commutative Noetherian rings and their Serre condition
  `(S₂)`, with prime-local depth bounds and double-dual linear maps as the local bridge;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.SerreConditionS`,
  `Module.IsReflexive.instSerreConditionSTwo`,
  `moduleDepth`,
  `isReflexive_localization_tfae`,
  `linearMap_serreConditionS_two_of_codomain`;
- best owner abstraction:
  `Module.IsReflexive` is the canonical owner of the source hypothesis and
  `Module.SerreConditionS` is the canonical owner of the conclusion. Clause `(1)` uses the
  localized owner theorem `isReflexive_localization_tfae` together with `moduleDepth` on
  `Localization.AtPrime p.asIdeal`, while clause `(2)` should be implemented as the canonical
  `Module.SerreConditionS` instance `Module.IsReflexive.instSerreConditionSTwo` and recalled
  directly rather than duplicated by a parallel theorem;
- source/core/bridge triage:
  clause `(1)` is `source-facing` local depth input at a single prime localization in the
  Noetherian-ring setting of the canonical owner proof,
  clause `(2)` is the `source-facing` global `(S₂)` theorem expressed in the canonical owner
  predicate `Module.SerreConditionS`.

Primitive data are only the reflexive module and the localized depth comparison. The global `(S₂)`
conclusion is owner-level API, so this file should expose the canonical instance directly, reusing
the chapter owners
`isReflexive_localization_tfae` and `linearMap_serreConditionS_two_of_codomain` rather than
duplicating a local wrapper around double-dual linear maps.
-/

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [IsReflexive R M]
variable (p : PrimeSpectrum R)

open scoped ENat
local notation "Rₚ" => Localization.AtPrime p.asIdeal
local notation "Mₚ" => AtPrime p.asIdeal M

-- Proof sketch: use Lemma `15.23.4` to see that the localized module `Mₚ` is reflexive over the
-- local ring `Localization.AtPrime p.asIdeal`, identify it with its double dual via
-- `Module.evalEquiv`, and apply Lemma `15.23.10 (2)` twice to the local ring
-- `Localization.AtPrime p.asIdeal`.
/-- Lemma 15.23.16 (1): if `R` is a Noetherian ring, `M` is a finite reflexive `R`-module, and
`p` is a prime ideal of `R` such that `depth(Rₚ) ≥ 2`, then `depth(Mₚ) ≥ 2`. -/
theorem moduleDepth_localizationAtPrime_ge_two_of_ringDepth_localizationAtPrime_ge_two
    (hp : (2 : ℕ∞) ≤ moduleDepth Rₚ Rₚ) :
    (2 : ℕ∞) ≤ moduleDepth Rₚ Mₚ := by
  sorry

end

section

variable {R : Type u} [CommRing R] [R ⊧ (S₂)]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [IsReflexive R M]

namespace Module.IsReflexive

instance instSerreConditionSTwo : SerreConditionS R M 2 := by
  sorry

end Module.IsReflexive

end

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma 15.23.16 (2): if `R` satisfies `(S_2)`, then every finite reflexive `R`-module `M`
also satisfies Serre's condition `(S_2)`. This is the canonical owner instance
`Module.IsReflexive.instSerreConditionSTwo`, obtained by applying
`linearMap_serreConditionS_two_of_codomain` to the double dual and transporting along the reflexive
evaluation equivalence. -/
recall Module.IsReflexive.instSerreConditionSTwo

end
