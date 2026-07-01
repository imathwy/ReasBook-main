import stacks_project.Chap10.Definition_10_160_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing Polynomial

universe u

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsCompleteLocalRing A] [Ring.KrullDimLE 1 A]

/- Domain-style sampling:
- primary domain: Henselian local algebra of complete local domains, with source-facing control of
  roots under small coefficient perturbations;
- sampled owner-level declarations of the same kind:
  `Ring.KrullDimLE`,
  `Ring.krullDimLE_one_iff_of_noZeroDivisors`,
  `Ideal.mem_map_C_iff`,
  `HenselianLocalRing.is_henselian`,
  `HenselianRing.is_henselian`,
  `IsAdicComplete.henselianRing`,
  `localRing_henselian_of_isCompleteLocalRing`;
- best owner abstraction: the canonical local lifting owner is `HenselianLocalRing`, obtained here
  from completeness via `localRing_henselian_of_isCompleteLocalRing`; polynomial perturbations with
  coefficients in `𝔪 ^ n` are canonically expressed by membership in `(𝔪 ^ n).map C`,
  congruence modulo powers of the maximal ideal is canonically expressed by `SModEq`, and the
  dimension hypothesis is most canonically carried by the owner instance `[Ring.KrullDimLE 1 A]`;
- primitive data: the complete local domain `A`, the source-facing one-dimensional hypothesis
  encoded canonically by `[Ring.KrullDimLE 1 A]`, the polynomial `P`, the chosen root `α`, the
  nonvanishing derivative value `P.derivative.eval α`, and the target precision `c`;
- derived API: eventual stability of the root under perturbations lying in the polynomial ideal
  `(𝔪 ^ n).map C`.

Layer triage:
- `source-facing`: `exists_root_of_small_polynomial_perturbation`;
- `core/canonical`: `HenselianLocalRing`, `HenselianRing`, `Ideal.map`, and `SModEq`;
- `bridge/view`: `localRing_henselian_of_isCompleteLocalRing`, which upgrades complete-local data
  to the henselian owner used in the background proof strategy.
-/
local notation "𝔪" => maximalIdeal A

-- Proof sketch: use the canonical henselian owner supplied by completeness together with the
-- canonical dimension-at-most-one owner `[Ring.KrullDimLE 1 A]` to compare the nonzero derivative
-- value `P.derivative.eval α` with a sufficiently high power of `𝔪`. For `Q ∈ (𝔪 ^ n).map C`,
-- the values `(P + Q).eval α` and `(P + Q).derivative.eval α` are small perturbations of the
-- corresponding values for `P`; the henselian lifting step then produces a root congruent to `α`
-- modulo `𝔪 ^ c`. The zero-dimensional edge case allowed by `[Ring.KrullDimLE 1 A]` is harmless
-- for this conclusion, so the exact equality `ringKrullDim A = 1` is omitted from the main API.
/-- Lemma 15.114.1 (Krasner's lemma): in a complete local domain of Krull dimension at most `1`,
a simple root `α` of a polynomial `P` persists under sufficiently small perturbations of the
coefficients, with the new root congruent to `α` modulo any prescribed power of the maximal
ideal. This keeps the source mathematics while replacing the redundant exact equality
`ringKrullDim A = 1` by the canonical owner hypothesis `[Ring.KrullDimLE 1 A]`. -/
theorem exists_root_of_small_polynomial_perturbation
    (P : A[X]) {α : A} (hα : P.IsRoot α) (hderiv : P.derivative.eval α ≠ 0) (c : ℕ) :
    ∃ n : ℕ, ∀ Q : A[X], Q ∈ (𝔪 ^ n).map C →
      ∃ β : A, (P + Q).IsRoot β ∧ β ≡ α [SMOD 𝔪 ^ c] := sorry

end
