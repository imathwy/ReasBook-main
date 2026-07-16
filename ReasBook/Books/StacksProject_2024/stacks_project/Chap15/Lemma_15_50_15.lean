import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_166_6
import StacksProject_2024.stacks_project.Chap15.Lemma_15_12_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_12_2
import StacksProject_2024.stacks_project.Chap15.Definition_15_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open RingPairCat

universe u

section

variable {A : Type u} [CommRing A] [IsGRing A]
variable (I : Ideal A)

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

/-- Helper for Lemma 15.50.15: geometric regularity ascends along a separable algebraic
extension of the base field, which is the final residue-field step in the source proof. -/
private theorem isGeometricallyRegular_of_separable_baseField
    {k : Type u} {k' : Type u} {R : Type u}
    [Field k] [Field k'] [CommRing R]
    [Algebra k k'] [Algebra k' R] [Algebra k R] [IsScalarTower k k' R]
    [Algebra.IsSeparable k k']
    (hR : Algebra.IsGeometricallyRegular k R) :
    Algebra.IsGeometricallyRegular k' R := by
  -- The source proof uses this exactly for `κ(q) → κ(q^h)` after isolating one fiber factor.
  exact (Algebra.isGeometricallyRegular_iff_of_isSeparable : _ ↔ _).1 hR

/-- Helper for Lemma 15.50.15: the closed fiber of `A → A^h` is unchanged, using the `n = 1`
quotient comparison from Lemma `15.12.2`. -/
private theorem pair_henselization_closedFiber_bijective :
    Function.Bijective
      (Ideal.quotientMap
        (henselizationIdeal (pairOfIdeal I))
        (toHenselization (pairOfIdeal I))
        (by
          simpa [henselizationIdeal_eq_map (X := pairOfIdeal I)] using
            (Ideal.le_comap_map :
              I ≤
                Ideal.comap (toHenselization (pairOfIdeal I))
                  (Ideal.map (toHenselization (pairOfIdeal I)) I)))) := by
  -- Proof comment: specialize the quotient-power comparison to `n = 1` and simplify the powers.
  simpa [pow_one] using
    (quotientPowToHenselization_bijective (X := pairOfIdeal I) 1)

/-- Helper for Lemma 15.50.15: the canonical map `A → A^h` already provides the Noetherianity,
flatness, and closed-fiber bijectivity needed for the completion-comparison step in the source
proof. -/
private theorem pair_henselization_completion_input :
    IsNoetherianRing (henselizationRing (pairOfIdeal I)) ∧
      Module.Flat A (henselizationRing (pairOfIdeal I)) ∧
      Function.Bijective
        (Ideal.quotientMap
          (henselizationIdeal (pairOfIdeal I))
          (toHenselization (pairOfIdeal I))
          (by
            simpa [henselizationIdeal_eq_map (X := pairOfIdeal I)] using
              (Ideal.le_comap_map :
                I ≤
                  Ideal.comap (toHenselization (pairOfIdeal I))
                    (Ideal.map (toHenselization (pairOfIdeal I)) I)))) := by
  constructor
  · -- Proof comment: this is the remaining owner missing from the current compile-safe import
    -- chain. The source proof needs Noetherianity of `A^h` before local completion comparison.
    -- TODO: restore a compile-safe earlier owner for pair-henselization Noetherianity and replace
    -- this placeholder by that theorem.
    sorry
  constructor
  · -- Proof comment: Lemma `15.12.2` supplies flatness of the structural map `A → A^h`.
    exact RingHom.flat_algebraMap_iff.mp <| by
      simpa using (toHenselization_flat (X := pairOfIdeal I))
  · -- Proof comment: the `n = 1` quotient comparison is exactly the closed-fiber bijection used
    -- in the local completion comparison from the source proof.
    exact pair_henselization_closedFiber_bijective (I := I)

/- Domain triage:
- primary domain: `G`-rings and the canonical pair-henselization owner in Chapter 15;
- sampled owner declarations:
  `IsGRing`,
  `isGRing_iff_isPRing_isGeometricallyRegularProperty`,
  `RingPairCat.henselizationRing`,
  `isPRing_henselizationRing`;
- best owner abstraction: the source-facing `G`-ring statement should reuse the canonical
  `P`-ring permanence theorem `isPRing_henselizationRing`, specialized to
  `Algebra.IsGeometricallyRegularProperty` through its Chapter 15 owner instances, rather than
  carrying a parallel local proof shell;
- primitive data: a commutative ring `A`, an ideal `I`, and the owner hypothesis `[IsGRing A]`;
- derived API: the `G`-ring instance on `henselizationRing (pairOfIdeal I)`.

Source/core/bridge triage:
- `source-facing`: the `G`-ring permanence statement for pair henselizations;
- `core/canonical`: `IsGRing`, `IsPRing`, and the pair-henselization owner
  `henselizationRing (pairOfIdeal I)`;
- `bridge/view`: the equivalence
  `isGRing_iff_isPRing_isGeometricallyRegularProperty` together with the separable-base-field
  invariance `isGeometricallyRegular_iff_of_isSeparable`. -/

/-- Lemma 15.50.15: if `A` is a `G`-ring and `(A^h, I^h)` is the chosen henselization of the pair
`(A, I)`, then the henselization ring `A^h` is a `G`-ring. -/
instance pairHenselization_isGRing :
    IsGRing (henselizationRing (pairOfIdeal I)) := by
  have hcompletionInput := pair_henselization_completion_input (I := I)
  let _ : IsNoetherianRing (henselizationRing (pairOfIdeal I)) := hcompletionInput.1
  let _ : Module.Flat A (henselizationRing (pairOfIdeal I)) := hcompletionInput.2.1
  have hclosedFiber :
      Function.Bijective
        (Ideal.quotientMap
          (henselizationIdeal (pairOfIdeal I))
          (toHenselization (pairOfIdeal I))
          (by
            simpa [henselizationIdeal_eq_map (X := pairOfIdeal I)] using
              (Ideal.le_comap_map :
                I ≤
                  Ideal.comap (toHenselization (pairOfIdeal I))
                    (Ideal.map (toHenselization (pairOfIdeal I)) I)))) :=
    hcompletionInput.2.2
  -- Route correction: the intended source-faithful proof still goes through maximal/local
  -- comparison of completions and formal fibers. The flatness input and the `n = 1` quotient
  -- comparison are now packaged above directly from `15.12.2`; the
  -- remaining missing owners are pair-henselization Noetherianity and the ind-étale /
  -- localization bridge needed to pass from this global input to each maximal localization.
  -- Every compile-safe route to package those remaining bridges is currently blocked by earlier
  -- owner files with missing `.olean`s, notably the Noetherianity owners
  -- `Lemma_15_12_4` and `Lemma_15_45_3`, plus the local-criterion owners
  -- `Lemma_15_50_7` and `Lemma_15_50_2 -> Lemma_15_51_4`.
  -- TODO: repair one of those prerequisite owner chains, then finish either through the packaged
  -- maximal-local criterion or through the textbook maximal-ideal argument already outlined above.
  let _ := hclosedFiber
  sorry

end
