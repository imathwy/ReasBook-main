import Mathlib
import StacksProject_2024.Chap10.Lemma_10_110_8
import StacksProject_2024.Chap10.Lemma_10_114_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {k : Type u} [Field k]
variable {n : ℕ}

local notation "A" => MvPolynomial (Fin n) k

/-
Domain-style sampling:
* primary domain: regularity and global dimension of polynomial rings over a field, expressed via
  maximal-local regularity data;
* sampled owner declarations:
  `IsRegularRing`,
  `IsFiniteGlobalDimensionRing`,
  `globalDimension`,
  `finiteGlobalDimension_regularRing_localizations_tfae`;
* best owner abstraction: Proposition `10.114.2` is a `source-facing` specialization of the
  canonical owner theorem `finiteGlobalDimension_regularRing_localizations_tfae`, with the
  maximal-local input supplied by Lemma `10.114.1`;
* primitive data vs. derived API: the primitive input is the family of maximal-local statements
  `IsRegularLocalRing (Localization.AtPrime m.asIdeal)` and
  `ringKrullDim (Localization.AtPrime m.asIdeal) = n`; the regular-ring instance, finite-global-
  dimension instance, and the equality `globalDimension A = n` are derived API owned by the
  chapter declarations above;
* source/core/bridge triage:
  `source-facing`: the three declarations in this file;
  `core/canonical`: `IsRegularRing A`, `IsFiniteGlobalDimensionRing A`, `globalDimension A`;
  `bridge/view`: the maximal-local clause in `finiteGlobalDimension_regularRing_localizations_tfae`.

This file should therefore reuse the owner theorem from `10.110.8` directly instead of keeping a
parallel local regularity/global-dimension proof interface.
-/

private theorem mvPolynomial_finiteGlobalDimension_regularRing_localizations_tfae :
    List.TFAE
      [ ∃ _ : IsFiniteGlobalDimensionRing A, globalDimension A = n
      , IsRegularRing A ∧ ringKrullDim A = n
      , (∀ m : MaximalSpectrum A,
            IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
              ringKrullDim (Localization.AtPrime m.asIdeal) ≤ n) ∧
          ∃ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n
      , (∀ p : PrimeSpectrum A,
            IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
              ringKrullDim (Localization.AtPrime p.asIdeal) ≤ n) ∧
          ∃ p : PrimeSpectrum A, ringKrullDim (Localization.AtPrime p.asIdeal) = n ] :=
  by
    exact
      (@finiteGlobalDimension_regularRing_localizations_tfae A inferInstance inferInstance n inferInstance :
        List.TFAE
          [ ∃ _ : IsFiniteGlobalDimensionRing A, globalDimension A = n
          , IsRegularRing A ∧ ringKrullDim A = n
          , (∀ m : MaximalSpectrum A,
                IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
                  ringKrullDim (Localization.AtPrime m.asIdeal) ≤ n) ∧
              ∃ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n
          , (∀ p : PrimeSpectrum A,
                IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
                  ringKrullDim (Localization.AtPrime p.asIdeal) ≤ n) ∧
              ∃ p : PrimeSpectrum A, ringKrullDim (Localization.AtPrime p.asIdeal) = n ])

private theorem maximalLocalizations_regularLocal_and_dim :
    (∀ m : MaximalSpectrum A,
        IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
          ringKrullDim (Localization.AtPrime m.asIdeal) ≤ n) ∧
      ∃ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n := by
  classical
  refine ⟨?_, ?_⟩
  · intro m
    refine ⟨isRegularLocalRing_localizationAtMaximal_mvPolynomial m, ?_⟩
    simp [ringKrullDim_localizationAtMaximal_mvPolynomial m]
  · let m : MaximalSpectrum A := Classical.choice inferInstance
    exact ⟨m, ringKrullDim_localizationAtMaximal_mvPolynomial m⟩

/-- Proposition 10.114.2 (1): a polynomial ring in `n` variables over a field is a regular ring. -/
@[stacks 00OQ]
instance isRegularRing_mvPolynomial :
    IsRegularRing A := by
  have htfae :
      List.TFAE
        [ ∃ _ : IsFiniteGlobalDimensionRing A, globalDimension A = n
        , IsRegularRing A ∧ ringKrullDim A = n
        , (∀ m : MaximalSpectrum A,
              IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
                ringKrullDim (Localization.AtPrime m.asIdeal) ≤ n) ∧
            ∃ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n
        , (∀ p : PrimeSpectrum A,
              IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
                ringKrullDim (Localization.AtPrime p.asIdeal) ≤ n) ∧
            ∃ p : PrimeSpectrum A, ringKrullDim (Localization.AtPrime p.asIdeal) = n ] :=
    mvPolynomial_finiteGlobalDimension_regularRing_localizations_tfae
  have hlocal :
      (∀ m : MaximalSpectrum A,
          IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
            ringKrullDim (Localization.AtPrime m.asIdeal) ≤ n) ∧
        ∃ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n :=
    maximalLocalizations_regularLocal_and_dim
  rcases (htfae.out 2 1).mp hlocal with
    ⟨hregular, _⟩
  exact hregular

/-- The polynomial ring in `n` variables over a field has finite global dimension. -/
instance isFiniteGlobalDimensionRing_mvPolynomial :
    IsFiniteGlobalDimensionRing A := by
  have htfae :
      List.TFAE
        [ ∃ _ : IsFiniteGlobalDimensionRing A, globalDimension A = n
        , IsRegularRing A ∧ ringKrullDim A = n
        , (∀ m : MaximalSpectrum A,
              IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
                ringKrullDim (Localization.AtPrime m.asIdeal) ≤ n) ∧
            ∃ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n
        , (∀ p : PrimeSpectrum A,
              IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
                ringKrullDim (Localization.AtPrime p.asIdeal) ≤ n) ∧
            ∃ p : PrimeSpectrum A, ringKrullDim (Localization.AtPrime p.asIdeal) = n ] :=
    mvPolynomial_finiteGlobalDimension_regularRing_localizations_tfae
  have hlocal :
      (∀ m : MaximalSpectrum A,
          IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
            ringKrullDim (Localization.AtPrime m.asIdeal) ≤ n) ∧
        ∃ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n :=
    maximalLocalizations_regularLocal_and_dim
  rcases (htfae.out 2 0).mp hlocal with
    ⟨hfgd, _⟩
  exact hfgd

/-- Proposition 10.114.2 (2): a polynomial ring in `n` variables over a field has global
dimension `n`. -/
@[stacks 00OQ]
theorem globalDimension_mvPolynomial_eq :
    globalDimension A = n := by
  have htfae :
      List.TFAE
        [ ∃ _ : IsFiniteGlobalDimensionRing A, globalDimension A = n
        , IsRegularRing A ∧ ringKrullDim A = n
        , (∀ m : MaximalSpectrum A,
              IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
                ringKrullDim (Localization.AtPrime m.asIdeal) ≤ n) ∧
            ∃ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n
        , (∀ p : PrimeSpectrum A,
              IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
                ringKrullDim (Localization.AtPrime p.asIdeal) ≤ n) ∧
            ∃ p : PrimeSpectrum A, ringKrullDim (Localization.AtPrime p.asIdeal) = n ] :=
    mvPolynomial_finiteGlobalDimension_regularRing_localizations_tfae
  have hlocal :
      (∀ m : MaximalSpectrum A,
          IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
            ringKrullDim (Localization.AtPrime m.asIdeal) ≤ n) ∧
        ∃ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n :=
    maximalLocalizations_regularLocal_and_dim
  rcases (htfae.out 2 0).mp hlocal with
    ⟨hfgd, hdim⟩
  let _ : IsFiniteGlobalDimensionRing A := hfgd
  simpa using hdim

end
