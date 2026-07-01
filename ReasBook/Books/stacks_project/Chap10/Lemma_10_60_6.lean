import stacks_project.Chap10.Proposition_10_60_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-
Domain-style sampling for Lemma 10.60.6:
- primary domain: dimension theory for Noetherian local rings via the Hilbert-Samuel polynomial;
- sampled owner declarations:
  `ringKrullDim`,
  `hilbertSamuelPolynomialDegree`,
  `local_noetherian_ring_dimension_tfae`;
- source/core/bridge triage:
  `source-facing`: the equivalence `dim(R) = 0 ↔ d(R) = 0` for a Noetherian local ring;
  `core/canonical`: the chapter owner theorem `local_noetherian_ring_dimension_tfae 0`;
  `bridge/view`: none beyond specializing clauses `(1)` and `(2)` of that owner theorem at `d = 0`.

This item adds no new local data or API beyond that exact specialization, so the correct
statement-stage surface is a labeled recall-style `#check` of the canonical owner theorem rather
than a new wrapper theorem. -/

/- Lemma 10.60.6: for a Noetherian local ring `R`, the Krull-dimension condition `dim(R) = 0` is
equivalent to the vanishing of the Hilbert-Samuel degree invariant `d(R) = 0`; in the project this
is exactly the specialization at `d = 0` of clauses `(1)` and `(2)` of
`local_noetherian_ring_dimension_tfae`. -/
#check
  ((local_noetherian_ring_dimension_tfae 0).out 0 1 rfl rfl :
    ringKrullDim R = 0 ↔ hilbertSamuelPolynomialDegree R R = 0)

end
