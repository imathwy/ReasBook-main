import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap15.Definition_15_50_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/- Domain triage:
- primary domain: `G`-rings, completed localizations, and geometric regularity of formal fibers in
  commutative algebra;
- sampled owner declarations:
  `CompletedLocalizationAtPrime`,
  `IsGRing`,
  `isGRing_iff_forall_regular_localization_completion`,
  `isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular`;
- best owner abstraction: the chapter owner predicate `IsGRing`, with the completed localization
  owner `R̂_[p]` and the prime-pair criterion from Lemma `15.50.2` only as supporting bridge API;
- primitive data: the ring `R` together with the Noetherian and complete-local hypotheses;
- derived API: the formal-fiber regularity statements used to prove the owner instance below.

Layering:
- this proposition is `source-facing`;
- `IsGRing` is the `core/canonical` owner;
- the prime-pair geometric-regularity criterion is the `bridge/view`.
-/
/-- Proposition 15.50.6: a Noetherian complete local ring is a `G`-ring. -/
-- Proof sketch: by Lemma `15.50.2`, it is enough to check geometric regularity of the formal
-- fibres over minimal primes. Quotient by a minimal prime to reduce to the domain case, choose a
-- regular complete local subring from Cohen structure, descend the `G`-ring property along the
-- resulting finite quasi-finite map using Lemma `15.50.3`, and then handle the regular complete
-- local source by the characteristic-zero regularity argument together with the positive
-- characteristic power-series case from Lemma `15.50.5`.
instance : IsGRing R := sorry

end
