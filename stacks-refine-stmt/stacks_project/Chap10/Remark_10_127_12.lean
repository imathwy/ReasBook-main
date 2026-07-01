import stacks_project.Chap10.Lemma_10_127_10
import stacks_project.Chap10.Lemma_10_127_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open DirectedLocalHomApproximation

/-
Domain sampling:
* Primary domain: directed approximation systems for local homomorphisms of local rings in
  commutative algebra.
* Owner declarations inspected in this domain:
  - `DirectedLocalHomApproximation`
  - `DirectedLocalHomApproximation.HasLocalizationOfQuotientTransitions`
  - `DirectedLocalHomApproximation.HasPrimeLocalizationTransitions`
  - `DirectedLocalHomApproximation.HasFailingPrimeLocalizationTransition`
* Best owner abstraction: `DirectedLocalHomApproximation f`.
* Layer targeted here: `source-facing`. The remark asserts existence of one local essentially
  finitely presented map together with two approximation systems on the same owner object,
  distinguished only by derived transition properties.
* Primitive vs. derived: the directed system, stage rings, local stage maps, colimit
  identifications, and stagewise essential finite-type data are primitive owner data from
  `Lemma_10_127_9`; the good/bad transition conditions are derived properties already owned by
  `Lemma_10_127_10` and `Lemma_10_127_11`, so no extra wrapper predicate is needed here.
-/

variable {R : Type u} {S : Type v} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

-- Proof sketch: use the explicit `k = 𝔽₂` example from the remark. The system with
-- `Sₙ = Rₙ / (z, yₙ²)` gives an approximation of the map `R → R / zR` whose successor base-change
-- maps kill `1 ⊗ y_{n + 1}²`, so some transition is not a localization at a prime ideal. Replacing
-- those targets by `Rₙ / zRₙ` gives another approximation of the same local essentially finite
-- presentation map whose transition maps are localizations at prime ideals.
/-- Remark 10.127.12: there exists a local homomorphism of local rings which is essentially of
finite presentation and admits both a good approximation system whose transition maps are
localizations at prime ideals and a different approximation system whose transition maps are still
localizations of quotients but fail to be localizations at prime ideals. -/
theorem exists_essentially_finitePresentation_local_map_with_wrong_approximation_system :
    ∃ (R : Type u) (S : Type v) (_ : CommRing R) (_ : CommRing S) (_ : IsLocalRing R)
      (_ : IsLocalRing S) (f : R →+* S) (_ : IsLocalHom f)
      (_ : RingHom.EssFinitePresentation f) (goodSystem : DirectedLocalHomApproximation f),
      goodSystem.HasPrimeLocalizationTransitions ∧
        ∃ badSystem : DirectedLocalHomApproximation f,
          badSystem.HasLocalizationOfQuotientTransitions ∧
            badSystem.HasFailingPrimeLocalizationTransition := sorry

end
