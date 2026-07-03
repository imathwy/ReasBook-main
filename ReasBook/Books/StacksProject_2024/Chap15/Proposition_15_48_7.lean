import Mathlib
import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap15.Definition_15_47_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling:
- primary domain: commutative algebra of the chapter owner `IsJ2Ring`, together with the standard
  complete-local, one-dimensional local, Nagata, Dedekind, and finite-type stability sources for
  the `J-2` property;
- sampled owner declarations of the same kind:
  `IsJ2Ring`,
  `isJ2Ring_iff_forall_finiteType_isJ1`,
  `NagataRing`,
  `IsCompleteLocalRing`;
- best owner abstraction: the public surface should stay on the canonical owner `IsJ2Ring`; pure
  specialization clauses such as the field and integer cases should use direct recall or instance
  inference rather than parallel local wrapper declarations;
- primitive vs. derived: the primitive public data are the ambient ring hypotheses for each source
  clause. The `J-1` conclusions for finite type algebras are derived from `IsJ2Ring`, so this file
  should not introduce any auxiliary data packaging around them.

Source/core/bridge triage:
- `source-facing`: the six proposition clauses listing concrete sources of `IsJ2Ring`;
- `core/canonical`: the chapter owner `IsJ2Ring`;
- `bridge/view`: the Dedekind/Nagata/complete-local specializations and the finite-type stability
  theorem.
-/

section

variable (K : Type u) [Field K]

/- Proposition 15.48.7 (1): fields are `J-2`. -/
#check (inferInstance : IsJ2Ring K)

end

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/-- Proposition 15.48.7 (1): a Noetherian complete local ring is `J-2`. -/
-- Proof sketch: use condition `(3)` of Lemma `15.47.6`. Any finite `R`-algebra is a finite
-- product of Noetherian complete local rings, so by Lemma `15.47.3` it suffices to handle the
-- domain case. That domain case is Lemma `15.48.6`.
instance isJ2Ring_of_noetherian_completeLocalRing : IsJ2Ring R := sorry

end

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Proof sketch: use condition `(3)` of Lemma `15.47.6`. Any finite `R`-algebra has finite
-- spectrum; because the regular locus is stable under generalization, it is open, so every finite
-- `R`-algebra is `J-1`.
/-- Proposition 15.48.7 (3): a Noetherian local ring of Krull dimension `1` is `J-2`. -/
theorem isJ2Ring_of_noetherian_local_ring_dimension_one
    (hdim : ringKrullDim R = 1) : IsJ2Ring R := sorry

end

section

variable (R : Type u) [CommRing R] [NagataRing R]

-- Proof sketch: use condition `(4)` of Lemma `15.47.6`. For a prime `p` and a finite purely
-- inseparable extension of its residue field, if `p` is maximal then the extension ring is finite
-- over a field and hence regular; if `p` is minimal, the Nagata property makes the integral
-- closure finite, and in dimension `1` that normal domain is regular.
/-- Proposition 15.48.7 (4): a Nagata ring of Krull dimension `1` is `J-2`. -/
theorem isJ2Ring_of_nagataRing_dimension_one
    (hdim : ringKrullDim R = 1) : IsJ2Ring R := sorry

end

section

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]

/-- Proposition 15.48.7 (5): a Dedekind domain whose fraction field has characteristic zero is
`J-2`. -/
-- Proof sketch: such a ring is Nagata by Proposition `10.162.16`, and a Dedekind domain has
-- Krull dimension `1`; apply the one-dimensional Nagata case.
instance isJ2Ring_of_isDedekindDomain_of_fractionRing_charZero : IsJ2Ring R := sorry

end

section

/- Proposition 15.48.7 (2): the ring of integers `ℤ` is `J-2`, by the Dedekind-domain
characteristic-zero instance above. -/
#check (inferInstance : IsJ2Ring ℤ)

end

section

variable (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Proposition 15.48.7 (6): finite type ring extensions of `J-2` rings are `J-2`. -/
-- Proof sketch: if `T` is a finite type `S`-algebra, then by transitivity it is a finite type
-- `R`-algebra. Since `R` is `J-2`, the ring `T` is `J-1`, so `S` satisfies the defining `J-2`
-- condition.
theorem isJ2Ring_of_finiteType [IsJ2Ring R] [Algebra.FiniteType R S] :
    IsJ2Ring S := by
  refine ⟨?_⟩
  intro A _ _ _
  sorry

end
