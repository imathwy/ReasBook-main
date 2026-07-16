import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_109_12
import StacksProject_2024.stacks_project.Chap10.Lemma_10_109_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open CategoryTheory

variable {R : Type u} [CommRing R]

/-
Source/core/bridge triage:
- `source-facing`: the local-global criterion saying that a Noetherian ring has finite global
  dimension exactly when its maximal-ideal localizations admit one uniform bound;
- `core/canonical`: the chapter owner abstractions `HasGlobalDimensionLE R n` and
  `IsFiniteGlobalDimensionRing R`;
- `bridge/view`: the localization instance from Lemma `10.109.13`, applied to
  `Localization.AtPrime m.asIdeal`.

Primitive data is the owner bound `HasGlobalDimensionLE R n`. The family of bounds on maximal
localizations is derived API coming from that owner, not a second notion of finite global
dimension.
-/

variable [IsNoetherianRing R]

-- Proof sketch: one direction is localization stability of a global-dimension bound, applied to
-- each maximal localization. For the converse, use Lemma `10.109.12` to reduce
-- `HasGlobalDimensionLE R n` to cyclic quotients `R ⧸ I`, and apply the mathlib local criterion
-- `ModuleCat.hasProjectiveDimensionLE_iff_forall_maximalSpectrum` to each cyclic quotient. The
-- given maximal-localization bounds supply the localized projective-dimension estimates directly.
/-- Lemma 10.110.2: a Noetherian ring has finite global dimension if and only if there is a
uniform integer `n` such that every localization `R_𝔪` at a maximal ideal `𝔪` has global
dimension at most `n`. -/
theorem isFiniteGlobalDimensionRing_iff_exists_uniform_bound_localizationAtMaximal :
    IsFiniteGlobalDimensionRing R ↔
      ∃ n : ℕ, ∀ m : MaximalSpectrum R,
        HasGlobalDimensionLE (Localization.AtPrime m.asIdeal) n := by
  constructor
  · intro _
    exact ⟨globalDimension R, fun _ ↦ inferInstance⟩
  · rintro ⟨n, hn⟩
    have hcyclic : ∀ I : Ideal R, HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) n := by
      intro I
      exact ((ModuleCat.of R (R ⧸ I)).hasProjectiveDimensionLE_iff_forall_maximalSpectrum n).2
        fun m ↦ by
          let _ : HasGlobalDimensionLE (Localization.AtPrime m.asIdeal) n := hn m
          simpa [Localization.AtPrime] using
            (inferInstance : HasProjectiveDimensionLE
              ((ModuleCat.of R (R ⧸ I)).localizedModule m.asIdeal.primeCompl) n)
    have hglobal : HasGlobalDimensionLE R n :=
      ((globalDimensionLE_tfae_finite_and_cyclic_modules n).out 2 0).mp hcyclic
    exact ⟨⟨n, hglobal⟩⟩

end
