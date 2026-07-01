import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap13.Definition_13_36_3
import stacks_project.Chap13.Lemma_13_36_6
import stacks_project.Chap15.Lemma_15_80_2
import stacks_project.Chap15.Lemma_15_80_5
import stacks_project.Chap15.Lemma_15_79_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

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

-- Proof sketch: Lemma `15.80.5` gives `(1) → (3)`. Clause `(3) → (2)` is immediate by taking the
-- exhibited generator. For `(2) → (3)`, combine the classical-generation statement for `R[0]` in
-- `D_{perf}(R)` with Derived Categories, Lemma `13.36.6`, which upgrades any classical generator
-- in a triangulated category admitting a strong generator to a strong generator. Finally, the
-- exact-dimension output of Lemma `15.80.2` is used only as an internal bridge to recover the
-- canonical finite-dimensional clause `(1)` from the canonical object `R[0]`.
/-- Proposition 15.80.6: for a Noetherian ring `R`, the following are equivalent: `R` is regular
of finite Krull dimension, the perfect derived category `D_{perf}(R)` has a strong generator, and
the canonical object `R[0]` is a strong generator of `D_{perf}(R)`. Clause `(1)` records finite
Krull dimension in the canonical owner form `∃ d : ℕ, Ring.KrullDimLE d R`, rather than by
choosing an exact dimension value in the public statement. -/
theorem regularFiniteKrullDimension_tfae_perfectDerived_hasStrongGenerator_ringSingleStrongGenerator :
    List.TFAE
      [IsRegularRing R ∧ ∃ d : ℕ, Ring.KrullDimLE d R,
        ∃ E : DPerf R, IsStrongGenerator E,
        IsStrongGenerator (ringSingleInPerfectDerived R)] := by
  tfae_have 1 → 3 := fun h ↦ by
    rcases h with ⟨hreg, hfinite⟩
    letI : IsRegularRing R := hreg
    exact ringSingleInPerfectDerived_isStrongGenerator hfinite
  tfae_have 3 → 2 := fun h ↦
    ⟨ringSingleInPerfectDerived R, h⟩
  tfae_have 2 → 3 := fun h ↦ by
    rcases h with ⟨E, hE⟩
    exact strong_generator_of_classical_generator
      (ringSingleInPerfectDerived R)
      ⟨E, hE⟩
      ring_single_isClassicalGenerator_in_perfectDerivedCategory
  tfae_have 3 → 1 := fun h ↦ by
    rcases
        exists_regularRing_and_ringKrullDim_eq_of_ringSingleInPerfectDerived_isStrongGenerator h
      with ⟨d, hreg, hdim⟩
    exact ⟨hreg, ⟨d, Ring.krullDimLE_iff.mpr (by simpa [hdim])⟩⟩
  tfae_finish

end

end CategoryTheory
