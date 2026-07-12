import Mathlib
import StacksProject_2024.Chap10.Definition_10_37_11
import StacksProject_2024.Chap10.Definition_10_157_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-
Domain-style sampling:
* primary domain: Serre's criterion for normality in Noetherian commutative algebra;
* sampled owner/bridge declarations:
  `IsNormalRing`,
  `SerreConditionR`,
  `SerreConditionS`,
  `SerreConditionS.moduleDepth_localizationAtPrime_ge_min`;
* best owner abstraction: the ring-level owner predicates `IsNormalRing R`,
  `SerreConditionR R 1`, and `SerreConditionS R 2`;
* primitive data vs derived API: the primitive public objects are the owner predicates above,
  while the primewise domain/integrally-closed and depth inequalities are derived local API
  already exposed by those owners.

Source/core/bridge triage:
* `source-facing`: Serre's criterion identifying normality with `(R_1)` and `(S_2)`;
* `core/canonical`: `IsNormalRing`, `SerreConditionR`, and `SerreConditionS`;
* `bridge/view`: the localized primewise clauses inside those owners.

The previous `List.TFAE` duplicated the owner-level normality and Serre-condition fields by
expanding them back into their local primewise formulations. This file now states the textbook
criterion directly at the owner level.
-/

-- Proof sketch: for `→`, unpack `IsNormalRing R` into normal localizations. Height-`≤ 1`
-- localizations are regular by the one-dimensional normal-local-domain criterion, and the
-- depth bound `S₂` comes from the standard depth estimate for normal local domains. For `←`,
-- use Lemma `10.157.3` to obtain reducedness from `(R₁)` and `(S₂)`, then combine reducedness
-- with `(R₁)` and `(S₂)` to show each localization is an integrally closed domain.
/-- Lemma 10.157.4 (Serre's criterion for normality): for a Noetherian ring `R`, `R` is normal if
and only if it satisfies Serre's conditions `(R_1)` and `(S_2)`. -/
theorem isNormalRing_iff_serreConditionR_one_and_serreConditionS_two :
    IsNormalRing R ↔ R ⊧ (R₁) ∧ R ⊧ (S₂) := by
  sorry

end
