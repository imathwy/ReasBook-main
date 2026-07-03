import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum Topology

section

variable {R : Type u} [CommRing R]

private abbrev pieceIdeal (C : BasicConstructibleSetData R) : Ideal R :=
  Ideal.span (Set.range C.g)

private abbrev pieceRing (C : BasicConstructibleSetData R) : Type u :=
  Localization.Away (Ideal.Quotient.mk (pieceIdeal C) C.f)

private instance (C : BasicConstructibleSetData R) :
    Algebra.FinitePresentation R (pieceRing C) := by
  have hI : (pieceIdeal C).FG := by
    dsimp [pieceIdeal]
    simpa using Submodule.fg_span (Set.finite_range C.g)
  letI : Algebra.FinitePresentation R (R ⧸ pieceIdeal C) :=
    Algebra.FinitePresentation.quotient hI
  change Algebra.FinitePresentation R
    (Localization.Away (Ideal.Quotient.mk (pieceIdeal C) C.f))
  infer_instance

private theorem range_comap_pieceRing_eq_toSet (C : BasicConstructibleSetData R) :
    Set.range (comap (algebraMap R (pieceRing C))) = C.toSet := by
  let I := pieceIdeal C
  let f : R ⧸ I := Ideal.Quotient.mk I C.f
  trans comap (Ideal.Quotient.mk I) '' (Set.range (comap (algebraMap (R ⧸ I) (pieceRing C))))
  · rw [← Set.range_comp]
    rfl
  · rw [localization_away_comap_range _ f, ← comap_basicOpen,
      TopologicalSpace.Opens.coe_comap, ContinuousMap.coe_mk, Set.image_preimage_eq_inter_range,
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, BasicConstructibleSetData.toSet,
      Set.diff_eq_compl_inter, basicOpen_eq_zeroLocus_compl, Ideal.mk_ker, zeroLocus_span]

private abbrev constructibleWitnessRing (s : ConstructibleSetData R) : Type u :=
  (C : s) → pieceRing C.1

private theorem range_comap_constructibleWitnessRing_eq_toSet (s : ConstructibleSetData R) :
    Set.range (comap (algebraMap R (constructibleWitnessRing s))) = s.toSet := by
  rw [← iUnion_range_comap_comp_evalRingHom, ConstructibleSetData.toSet]
  simp_rw [← Finset.mem_coe, Set.biUnion_eq_iUnion]
  congr! with _ _ C
  simpa [constructibleWitnessRing] using range_comap_pieceRing_eq_toSet C.1

-- Proof sketch: use Lemma `10.29.3` to write a constructible subset as a finite union of sets of
-- the form `D(f) ∩ V(g₁, ..., gₘ)`. Each such piece is the image of
-- `Spec ((R ⧸ (g₁, ..., gₘ))_f) → Spec(R)` by Lemmas `10.17.6` and `10.17.7`, and finite unions
-- are handled by passing to finite products, whose spectra are disjoint unions by Lemma `10.21.2`.
--
-- This is the source-facing finite-presentation refinement of the owner theorem
-- `PrimeSpectrum.exists_range_eq_of_isConstructible`: it uses the same canonical witness ring built
-- from `PrimeSpectrum.ConstructibleSetData`, and records that each quotient-localization factor is
-- finitely presented over `R`.
/-- Lemma 10.29.4: every constructible subset of `Spec(R)` is the image of `Spec(S)` in `Spec(R)`
for some finitely presented ring map `R → S`. -/
theorem exists_finitePresentation_comap_range_eq_of_isConstructible
    {T : Set (PrimeSpectrum R)} (hT : IsConstructible T) :
    ∃ (S : Type u) (_ : CommRing S) (f : R →+* S),
      f.FinitePresentation ∧ Set.range (comap f) = T := by
  obtain ⟨s, rfl⟩ := exists_constructibleSetData_iff.mpr hT
  refine ⟨
    constructibleWitnessRing s,
    inferInstance, algebraMap R (constructibleWitnessRing s), ?_⟩
  constructor
  · exact RingHom.finitePresentation_algebraMap.2 inferInstance
  · exact range_comap_constructibleWitnessRing_eq_toSet s

end
