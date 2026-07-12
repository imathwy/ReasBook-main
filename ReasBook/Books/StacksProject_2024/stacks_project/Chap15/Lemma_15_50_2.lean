import StacksProject_2024.Chap10.Lemma_10_97_3
import StacksProject_2024.Chap10.Lemma_10_166_6
import StacksProject_2024.Chap15.Lemma_15_51_3
import StacksProject_2024.Chap15.Lemma_15_51_4

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra

universe u

section

variable (R : Type u) [CommRing R]

/- Domain triage:
- primary domain: `G`-rings, completed localizations, and geometric regularity of formal fibers in
  commutative algebra;
- sampled owner declarations:
  `CompletedLocalizationAtPrime`,
  `IsGRing`,
  `IsPRing`,
  `isGRing_iff_forall_regular_localization_completion`,
  `SatisfiesPPrimePairCondition`;
- best owner abstraction: the canonical completion owner `CompletedLocalizationAtPrime`, exposed on
  the theorem surface through the textbook notation `R̂_[p]`, together with the chapter owners
  `IsGRing` and `IsPRing`;
- primitive data: a commutative ring `R`, with Noetherianity supplied by the owner hypotheses
  `IsGRing R` or `IsPRing Algebra.IsGeometricallyRegularProperty R`, and a prime pair `q ≤ p`;
- derived API: geometric regularity of the formal fiber `q.asIdeal.Fiber (R̂_[p])`.

Layering:
- the numbered lemma is `source-facing`;
- `IsGRing`, `IsPRing`, and `CompletedLocalizationAtPrime` are the `core/canonical` owners;
- the prime-pair geometric-regularity criterion is the `bridge/view`.
-/

namespace Algebra

/-- The Chapter 15 `FieldAlgebraProperty` corresponding to geometric regularity. -/
abbrev IsGeometricallyRegularProperty : FieldAlgebraProperty :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ IsGeometricallyRegular k A

instance isGeometricallyRegular_hasPropertyA :
    IsGeometricallyRegularProperty.HasPropertyA where
  baseChange := by
    intro k A K _ _ _ _ _ _ _ hP
    sorry

instance isGeometricallyRegular_hasPropertyB :
    IsGeometricallyRegularProperty.HasPropertyB where
  localizationCriterion := by
    intro k A _ _ _ _
    sorry

/-- Geometric regularity satisfies Chapter 15 axiom `(C)`. -/
instance isGeometricallyRegular_hasPropertyC :
    IsGeometricallyRegularProperty.HasPropertyC where
  regularAscent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hB q
    sorry

/-- Geometric regularity satisfies Chapter 15 axiom `(D)`. -/
instance isGeometricallyRegular_hasPropertyD :
    IsGeometricallyRegularProperty.HasPropertyD where
  closedFiberDescent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBC hC
    sorry

end Algebra

/-- The `G`-ring owner is the `P`-ring owner specialized to geometric regularity of formal fibers. -/
theorem isGRing_iff_isPRing_isGeometricallyRegularProperty :
    IsGRing R ↔ IsPRing Algebra.IsGeometricallyRegularProperty R := by
  constructor
  · intro hR
    letI : IsNoetherianRing R := hR.toIsNoetherian
    refine { satisfiesPFormalFiberCondition := ?_ }
    intro p q
    letI : RingHom.IsRegularRingMap (algebraMap (Localization.AtPrime p.asIdeal) (R̂_[p])) :=
      hR.regular_localization_completion p
    let hreg :
        RingHom.IsRegularRingMap (algebraMap (Localization.AtPrime p.asIdeal) (R̂_[p])) :=
      inferInstance
    simpa [Algebra.IsGeometricallyRegularProperty] using hreg.isGeometricallyRegular_fiber q
  · intro hP
    letI : IsNoetherianRing R := hP.toIsNoetherian
    refine isGRing_iff_forall_regular_localization_completion.2 ?_
    intro p
    exact
      { toFlat :=
          RingHom.flat_algebraMap_iff.mpr <|
            (maximalIdeal_adicCompletion_algebraMap_faithfullyFlat
              (Localization.AtPrime p.asIdeal)).flat
        isGeometricallyRegular_fiber := by
          simpa [Algebra.IsGeometricallyRegularProperty] using
            hP.satisfiesPFormalFiberCondition p }

/-- A Noetherian local ring is a `G`-ring exactly when its formal fibers are geometrically
regular. -/
theorem isGRing_iff_localFormalFibersHaveProperty
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsGRing A ↔ LocalFormalFibersHaveProperty Algebra.IsGeometricallyRegularProperty A := by
  sorry

-- Proof sketch: specialize the generic prime-pair criterion for `P`-rings from Lemma `15.51.1`
-- to geometric regularity, then translate the owner back from `IsPRing` to `IsGRing`.
/-- Lemma 15.50.2: for a Noetherian ring `R`, the `G`-ring condition is equivalent to requiring
that for every inclusion of primes `𝔮 ⊆ 𝔭`, the canonical `κ(𝔮)`-algebra `R̂_𝔭 ⊗[R] κ(𝔮)`,
equivalently
`((R ⧸ 𝔮)_𝔭^ ∧) ⊗[R ⧸ 𝔮] κ(𝔮)`, is geometrically regular over `κ(𝔮)`. -/
theorem isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ p q : PrimeSpectrum R, ∀ _hqp : q.asIdeal ≤ p.asIdeal,
        IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p])) := by
  -- Specialize the generic prime-pair criterion for `P`-rings to geometric regularity.
  have hprimePair :
      IsPRing Algebra.IsGeometricallyRegularProperty R ↔
        SatisfiesPPrimePairCondition Algebra.IsGeometricallyRegularProperty R :=
    isPRing_iff_satisfiesPPrimePairCondition
  -- Translate the source-facing `G`-ring owner to the specialized `P`-ring owner and unfold the
  -- packaged property on the prime-pair side.
  simpa [Algebra.IsGeometricallyRegularProperty, SatisfiesPPrimePairCondition] using
    (isGRing_iff_isPRing_isGeometricallyRegularProperty R).trans hprimePair

end
