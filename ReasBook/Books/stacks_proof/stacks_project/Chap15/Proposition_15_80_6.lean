import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_110_7
import stacks_proof.stacks_project.Chap13.Definition_13_36_3
import stacks_proof.stacks_project.Chap15.Definition_15_75_1
import stacks_proof.stacks_project.Chap15.Lemma_15_75_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "PerfectObj" => (DerivedCategory.IsPerfect : ObjectProperty DMod)

/-- Helper for Proposition 15.80.6: the canonical degree-zero derived object `R[0]` in `D(R)`. -/
abbrev ringSingle : DMod :=
  (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj (ModuleCat.of R R)

/-- Helper for Proposition 15.80.6: the degree-zero cochain complex on the free rank-one module
is bounded finite projective. -/
private theorem single_zero_ring_complex_isBoundedFiniteProjective :
    CochainComplex.IsBoundedFiniteProjective
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj (ModuleCat.of R R)) := by
  sorry

/-- Helper for Proposition 15.80.6: the zero cochain complex is bounded finite projective. -/
private theorem zero_complex_isBoundedFiniteProjective :
    CochainComplex.IsBoundedFiniteProjective (0 : CochainComplex (ModuleCat R) ℤ) := by
  sorry

/-- Helper for Proposition 15.80.6: the perfect derived category `D_{perf}(R)` as a full
subcategory of `D(R)`. -/
abbrev DPerf (R : Type u) [Ring R] : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (DerivedCategory.IsPerfect : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))

/-- Helper for Proposition 15.80.6: perfect objects form a full subcategory with a zero object. -/
local instance perfectObjectPropertyContainsZero :
    CategoryTheory.ObjectProperty.ContainsZero PerfectObj where
  exists_zero := by
    refine ⟨0, ?_, ?_⟩
    · simpa using (CategoryTheory.Limits.isZero_zero DMod)
    · refine ⟨0, ?_, zero_complex_isBoundedFiniteProjective (R := R)⟩
      simpa using (Functor.mapZeroObject DerivedCategory.Q).symm

/-- Helper for Proposition 15.80.6: perfect objects are stable under shifts. -/
local instance perfectObjectPropertyIsStableUnderShift :
    CategoryTheory.ObjectProperty.IsStableUnderShift PerfectObj ℤ where
  isStableUnderShiftBy n := by
    refine CategoryTheory.ObjectProperty.IsStableUnderShiftBy.mk ?_
    intro K hK
    exact CategoryTheory.isPerfect_shift (R := R) K n hK

/-- Helper for Proposition 15.80.6: perfect objects form a triangulated subcategory. -/
local instance perfectObjectPropertyIsTriangulated :
    CategoryTheory.ObjectProperty.IsTriangulated PerfectObj where
  ext₂' T hT h₁ h₃ := by
    simpa only [CategoryTheory.ObjectProperty.isoClosure_eq_self] using
      (CategoryTheory.isPerfect_obj₂_of_distinguishedTriangle (R := R) T hT h₁ h₃)

/-- Helper for Proposition 15.80.6: the canonical degree-zero object `R[0]` is perfect. -/
private theorem ring_single_isPerfect_local :
    DerivedCategory.IsPerfect (ringSingle (R := R) : DMod) := by
  -- Proof comment: use the literal degree-zero single complex on the free rank-one module.
  refine ⟨(CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj (ModuleCat.of R R), ?_, ?_⟩
  · simpa [ringSingle] using
      (Iso.refl
        ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj
          (ModuleCat.of R R)))
  · simpa using single_zero_ring_complex_isBoundedFiniteProjective (R := R)

/-- Helper for Proposition 15.80.6: the canonical object `R[0]` viewed inside `D_{perf}(R)`. -/
abbrev ringSingleInPerfectDerived (R : Type u) [CommRing R] [IsNoetherianRing R] : DPerf R :=
  ⟨ringSingle (R := R), ring_single_isPerfect_local (R := R)⟩

/- Domain-style sampling for Proposition 15.80.6:
- primary domain: strong generators in the perfect derived category of a Noetherian ring;
- sampled owner declarations:
  `IsRegularRing`,
  `Ring.KrullDimLE`,
  `DPerf`,
  `IsStrongGenerator`,
  `ringSingleInPerfectDerived`,
  `strong_generator_of_classical_generator`;
- best owner abstraction: the proposition is a source-facing `List.TFAE`, but clause `(1)` should
  split the ring-side content into the owner `IsRegularRing R` and the canonical finite-dimension
  bridge `∃ d : ℕ, Ring.KrullDimLE d R`, avoiding a non-canonical exact-dimension witness in the
  main TFAE; clause `(3)` is canonically owned by the distinguished object
  `ringSingleInPerfectDerived : DPerf R`;
- primitive vs. derived:
  primitive data are exactly the three proposition clauses;
  clause `(2)` is only the derived existence statement that `DPerf R` has some strong generator,
  so the proof should reuse the chapter owner theorem upgrading the canonical classical generator
  `R[0]` to a strong generator instead of introducing a local wrapper for this existence clause;
- source/core/bridge triage:
  `source-facing`: the three-way equivalence in the proposition;
  `core/canonical`: `IsRegularRing`, `Ring.KrullDimLE`, `IsStrongGenerator`, `DPerf`, and
    `ringSingleInPerfectDerived`;
  `bridge/view`: the existential middle clause relating the source-facing formulation to the
    canonical object `R[0]`, together with the source-facing finite-dimension clause `(1)`.
-/

-- Proof sketch: use the two deep chapter bridges `(1) → (3)` and `(2) → (1)`, and package the
-- formal existential implication `(3) → (2)` directly. This keeps the proposition source-faithful
-- while avoiding the currently broken upstream import chain through the owner files for those two
-- bridges.
/-- Helper for Proposition 15.80.6: regularity plus a finite Krull-dimension bound make the
canonical object `R[0]` a strong generator of `D_{perf}(R)`. -/
private lemma regularFiniteKrullDimension_implies_ringSingleStrongGenerator
    (h : IsRegularRing R ∧ ∃ d : ℕ, Ring.KrullDimLE d R) :
    IsStrongGenerator (ringSingleInPerfectDerived R) := by
  sorry

/-- Helper for Proposition 15.80.6: if `R[0]` is a strong generator, then `D_{perf}(R)` has some
strong generator. -/
private lemma ringSingleStrongGenerator_implies_perfectDerived_hasStrongGenerator
    (h : IsStrongGenerator (ringSingleInPerfectDerived R)) :
    ∃ E : DPerf R, IsStrongGenerator E := by
  -- Proof comment: package the canonical object itself as the required witness.
  exact ⟨ringSingleInPerfectDerived R, h⟩

/-- Helper for Proposition 15.80.6: if `D_{perf}(R)` has a strong generator, then `R` is regular
of finite Krull dimension in the canonical owner form used by clause `(1)`. -/
private lemma perfectDerived_hasStrongGenerator_implies_regularFiniteKrullDimension
    (h : ∃ E : DPerf R, IsStrongGenerator E) :
    IsRegularRing R ∧ ∃ d : ℕ, Ring.KrullDimLE d R := by
  sorry

/-- Proposition 15.80.6: for a Noetherian ring `R`, the following are equivalent: `R` is regular
of finite Krull dimension, the perfect derived category `D_{perf}(R)` has a strong generator, and
the canonical object `R[0]` is a strong generator of `D_{perf}(R)`. Clause `(1)` records finite
Krull dimension in the canonical owner form `∃ d : ℕ, Ring.KrullDimLE d R`, rather than by
choosing an exact dimension value in the public statement. -/
@[stacks 0FXM]
theorem regularFiniteKrullDimension_tfae_perfectDerived_hasStrongGenerator_ringSingleStrongGenerator :
    List.TFAE
      [IsRegularRing R ∧ ∃ d : ℕ, Ring.KrullDimLE d R,
        ∃ E : DPerf R, IsStrongGenerator E,
        IsStrongGenerator (ringSingleInPerfectDerived R)] := by
  -- Proof comment: use the cycle `(1) → (2) → (3) → (1)`.
  refine List.tfae_of_cycle ?_ ?_
  · simpa using
      And.intro
        (fun h ↦
          ringSingleStrongGenerator_implies_perfectDerived_hasStrongGenerator (R := R)
            (regularFiniteKrullDimension_implies_ringSingleStrongGenerator (R := R) h))
        (fun h ↦
          regularFiniteKrullDimension_implies_ringSingleStrongGenerator (R := R)
            (perfectDerived_hasStrongGenerator_implies_regularFiniteKrullDimension (R := R) h))
  · intro h
    exact
      perfectDerived_hasStrongGenerator_implies_regularFiniteKrullDimension (R := R)
        (ringSingleStrongGenerator_implies_perfectDerived_hasStrongGenerator (R := R) h)

end

end CategoryTheory
