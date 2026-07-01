import Mathlib
import stacks_project.Chap10.Definition_10_110_7
import stacks_project.Chap10.Definition_10_161_1
import stacks_project.Chap10.Definition_10_162_9
import stacks_project.Chap10.Example_10_119_5
import stacks_project.Chap10.Lemma_10_161_15
import stacks_project.Chap10.Lemma_10_162_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u}
variable [CommRing R] [IsDomain R]

/- 
Domain-style sampling:
- primary domain: iterative finite overrings of one-dimensional semilocal Noetherian domains
  inside the canonical fraction field `FractionRing R`, together with analytic unramifiedness of
  the maximal-local
  completions that controls whether this process can continue indefinitely;
- sampled owner declarations in the same domain:
  `IsRegularRing`,
  `IsAnalyticallyUnramified`,
  `isN1Ring_of_isAnalyticallyUnramified`,
  `finitePthPowerCoefficientAdjoinSubring_completion_not_reduced`;
- best owner abstraction: each stage of the source construction should be an intermediate
  `Subalgebra R (FractionRing R)`, the whole source-facing chain should be owned by a single
  predicate on such sequences, and each finite extension step should be expressed by the canonical
  inclusion
  `Subalgebra.inclusion hle` between consecutive stages rather than by a parallel packaged ring,
  and the completion hypothesis should use the owner predicate
  `IsAnalyticallyUnramified (Localization.AtPrime m.asIdeal)` instead of a parallel
  completion-reducedness wrapper.

Source/core/bridge triage:
- `source-facing`: the sequence `R = R_0 ⊆ R_1 ⊆ R_2 ⊆ ...` of finite intermediate overrings
  discussed in the remark, the characteristic-`0` and characteristic-`p` counterexamples, and the
  stopping criterion under reduced maximal-local completions;
- `core/canonical`: the stage owner `R_n : Subalgebra R (FractionRing R)` together with the
  sequence predicate `IsFiniteSemilocalDomainOverringSequence`, the regularity owner
  `IsRegularRing (R_n)`, and the completion owner
  `IsAnalyticallyUnramified (Localization.AtPrime m.asIdeal)`;
- `bridge/view`: semilocality and dimension-one statements for each stage, the maximal-local
  regularity data used to construct `IsRegularRing (R_n)`, and the finite strict inclusion
  `Subalgebra.inclusion hle` when the next step is taken, plus the owner-form reformulation of
  Example `10.119.5` from nonreduced completion to `¬ IsAnalyticallyUnramified`.

Primitive data are the stage family `R_n : ℕ → Subalgebra R (FractionRing R)` and the finite step
morphisms between consecutive stages. Noetherianity, domain structure, and the algebra
`R_n → FractionRing R` are canonical derived owner data and should not remain packaged as separate
primitive witnesses in the public API. For the completion side, reducedness of the maximal-ideal
completion is derived bridge API from `IsAnalyticallyUnramified`; the public surface should
therefore use the owner predicate instead of a second primitive notion.
-/

/-- A remark-style sequence of finite semilocal one-dimensional overrings of `R` in its fraction
field. Each step is finite; once a stage is regular, the sequence is constant there, and otherwise
the next step is strict. -/
def IsFiniteSemilocalDomainOverringSequence
    (S : ℕ → Subalgebra R (FractionRing R)) : Prop :=
  S 0 = ⊥ ∧
    ∀ n,
      (Finite (MaximalSpectrum (S n)) ∧ ringKrullDim (S n) = 1) ∧
        ∃ hle : S n ≤ S (n + 1),
          (Subalgebra.inclusion hle).toRingHom.Finite ∧
            (IsRegularRing (S n) → S (n + 1) = S n) ∧
            (IsRegularRing (S n) ∨ S n < S (n + 1))

/-- A remark-style overring chain is already semilocal at the base: the stage condition at `0`
identifies `S 0` with the bottom subalgebra, hence with `R`. -/
theorem finite_maximalSpectrum_of_isFiniteSemilocalDomainOverringSequence
    {R : Type u} [CommRing R] [IsDomain R]
    {S : ℕ → Subalgebra R (FractionRing R)}
    (hS : IsFiniteSemilocalDomainOverringSequence S) :
    Finite (MaximalSpectrum R) := by
  let e : S 0 ≃ₐ[R] R :=
    (Subalgebra.equivOfEq (S 0) ⊥ hS.1).trans
      (Algebra.botEquivOfInjective (IsFractionRing.injective R (FractionRing R)))
  let eMax : MaximalSpectrum R ≃ MaximalSpectrum (S 0) := by
    refine
      { toFun := fun m ↦ ⟨Ideal.comap e.toRingEquiv m.asIdeal, inferInstance⟩
        invFun := fun m ↦ ⟨Ideal.map e.toRingEquiv m.asIdeal, inferInstance⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro m
      apply MaximalSpectrum.ext
      simpa using m.asIdeal.map_comap_of_surjective e.toRingEquiv e.toRingEquiv.surjective
    · intro m
      apply MaximalSpectrum.ext
      simpa using m.asIdeal.comap_map_of_bijective e.toRingEquiv e.toRingEquiv.bijective
  letI : Finite (MaximalSpectrum (S 0)) := (hS.2 0).1.1
  exact Finite.of_equiv (MaximalSpectrum (S 0)) eMax.symm

variable [IsNoetherianRing R] [Finite (MaximalSpectrum R)]

-- Proof sketch: localize `R` at the chosen maximal ideal `m`, note that a one-dimensional
-- nonregular local domain has cotangent-space dimension greater than one, and apply
-- Lemma `10.119.3` to obtain a nontrivial finite local extension. Then view that extension inside
-- the canonical fraction field `FractionRing R`, and use the semilocal and one-dimensional
-- permanence properties of finite extensions of Noetherian domains to globalize the local
-- construction back over `R`. Iterating this step produces the chain of finite intermediate
-- overrings from the source remark; once a stage is regular, keep the chain constant from that
-- point on.
/-- Remark 10.119.6: if `R` is a one-dimensional semilocal Noetherian domain and one maximal
localization `R_m` is not regular, then there exists a sequence of intermediate subalgebras
`R = R_0 ⊆ R_1 ⊆ R_2 ⊆ ...` inside `FractionRing R` such that every stage is again a
one-dimensional semilocal domain, each consecutive inclusion `R_n ⊆ R_{n+1}` is finite, and at
each stage either `R_n` is regular and the chain stabilizes there, or the next inclusion is
strict. The initial stage is the bottom subalgebra
`⊥ : Subalgebra R (FractionRing R)`. -/
theorem exists_finite_semilocal_domain_extension_sequence_of_nonregular_maximalLocalization
    (hdim : ringKrullDim R = 1) (m : MaximalSpectrum R)
    (hreg : ¬ IsRegularLocalRing (Localization.AtPrime m.asIdeal)) :
    ∃ S : ℕ → Subalgebra R (FractionRing R), IsFiniteSemilocalDomainOverringSequence S := sorry

/-- The first-step consequence of Remark 10.119.6: if one maximal localization of `R` is not
regular, then there is already a strict finite first overring in the canonical subalgebra chain
`R = R₀ ⊂ R₁ ⊆ FractionRing R`, and that first stage is again a one-dimensional semilocal
domain. -/
theorem exists_finite_semilocal_domain_extension_of_nonregular_maximalLocalization
    (hdim : ringKrullDim R = 1) (m : MaximalSpectrum R)
    (hreg : ¬ IsRegularLocalRing (Localization.AtPrime m.asIdeal)) :
    ∃ S : Subalgebra R (FractionRing R),
      ∃ hlt : (⊥ : Subalgebra R (FractionRing R)) < S,
        (Subalgebra.inclusion hlt.le).toRingHom.Finite ∧
        Finite (MaximalSpectrum S) ∧
        ringKrullDim S = 1 := sorry

end

noncomputable section

open scoped PthPowerSubfield

section PositiveCharacteristicExample

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]

local notation "A" => finitePthPowerCoefficientSubring k p

/-- Example `10.119.5`, owner-form bridge: if `f ∉ A`, then the corresponding one-dimensional
local domain `A[f]` is not analytically unramified. This is the canonical Chapter `10.162`
reformulation of the nonreduced-completion counterexample used in Remark `10.119.6`. -/
theorem finitePthPowerCoefficientAdjoinSubring_not_isAnalyticallyUnramified
    {f : PowerSeries k} (hf : f ∉ A) :
    ¬ IsAnalyticallyUnramified ↥(finitePthPowerCoefficientAdjoinSubring k p f) := by
  simpa [isAnalyticallyUnramified_iff] using
    finitePthPowerCoefficientAdjoinSubring_completion_not_reduced k p f hf

-- Proof sketch: choose `f ∉ A` using Example `10.119.5`. The corresponding ring `A[f]` is the
-- one-dimensional Noetherian local domain from that example, and the previous theorem identifies
-- its completion as nonreduced. For this explicit source counterexample, the blowup construction
-- from Remark `10.119.6` never reaches a regular stage because blowing up commutes with
-- completion, so reduced completion would force analytic unramifiedness.
/-- Remark `10.119.6`, characteristic-`p` counterexample: whenever `k / k^p` is infinite, Example
`10.119.5` produces a one-dimensional Noetherian local domain of positive characteristic whose
completion is not reduced, equivalently which is not analytically unramified, and hence the
remark-style finite-overring process admits a chain in `Frac(A[f])` that never stabilizes. -/
theorem exists_positiveCharacteristic_nonstabilizing_finite_semilocal_domain_overring_sequence
    (hnfd : ¬ FiniteDimensional (pthPowerSubfield k p) k) :
    ∃ f : PowerSeries k,
      let R := ↥(finitePthPowerCoefficientAdjoinSubring k p f)
      f ∉ A ∧
        IsNoetherianRing R ∧
        ringKrullDim R = 1 ∧
        ¬ IsAnalyticallyUnramified R ∧
        ∃ S : ℕ → Subalgebra R (FractionRing R),
          IsFiniteSemilocalDomainOverringSequence S ∧
            ∀ n, S n < S (n + 1) := sorry

end PositiveCharacteristicExample

section CharacteristicZeroExample

-- Proof sketch: take the characteristic-zero Ferrand-Raynaud type counterexample cited in the
-- source remark. For this explicit one-dimensional Noetherian local domain with nonreduced
-- completion, the blowup construction from Remark `10.119.6` never stabilizes because blowing up
-- commutes with completion.
/-- Remark `10.119.6`, characteristic-`0` counterexample: there exists a one-dimensional
Noetherian local domain whose fraction field has characteristic `0` and which is not analytically
unramified, equivalently whose completion is nonreduced; for this ring, the remark-style finite
overring process in its fraction field never stabilizes. -/
theorem exists_charZero_nonstabilizing_finite_semilocal_domain_overring_sequence :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsDomain A)
      (_ : IsNoetherianRing A) (_ : CharZero (FractionRing A)),
      ringKrullDim A = 1 ∧
        ¬ IsAnalyticallyUnramified A ∧
        ∃ S : ℕ → Subalgebra A (FractionRing A),
          IsFiniteSemilocalDomainOverringSequence S ∧
            ∀ n, S n < S (n + 1) := sorry

end CharacteristicZeroExample

section StoppingCriterion

variable {R : Type u}
variable [CommRing R] [IsDomain R]

section Semilocal

variable [IsNoetherianRing R] [Finite (MaximalSpectrum R)]

-- Proof sketch: choose a nonzero element lying in every maximal ideal of the semilocal
-- one-dimensional domain `R`; after localizing away from it, only the generic point remains, so
-- the localization is a field and hence integrally closed.
/-- In a one-dimensional semilocal Noetherian domain, some nonzero localization is already
integrally closed. This is the bridge needed to pass from maximal-local `N-1` data to the global
`N-1` owner using Lemma `10.161.15`. -/
theorem exists_integrallyClosed_localizationAway_of_ringKrullDim_eq_one
    (hdim : ringKrullDim R = 1) :
    ∃ f : R, f ≠ 0 ∧ IsIntegrallyClosed (Localization.Away f) := sorry

-- Proof sketch: by hypothesis each maximal localization is analytically unramified, hence `N-1`
-- by Lemma `10.162.10 (5)`. Combine these local `N-1` statements with the semilocal
-- one-dimensional bridge above and Lemma `10.161.15 (3)`.
/-- If all maximal localizations of a one-dimensional semilocal Noetherian domain are analytically
unramified, then the domain is `N-1`. This is the canonical owner-level form of the “reduced
completion forces stopping” input in Remark `10.119.6`. -/
theorem isN1Ring_of_forall_maximal_isAnalyticallyUnramified
    (hdim : ringKrullDim R = 1)
    (hanalytic :
      ∀ m : MaximalSpectrum R, IsAnalyticallyUnramified (Localization.AtPrime m.asIdeal)) :
    IsN1Ring R := sorry

end Semilocal

-- Proof sketch: every finite intermediate overring of `R` inside `FractionRing R` lies in the
-- normalization `integralClosure R (FractionRing R)`, which is a finite `R`-module by the `N-1`
-- hypothesis.
-- Hence the corresponding chain of `R`-submodules stabilizes, so there cannot be an infinite
-- strictly increasing chain of such finite intermediate overrings.
/-- An `N-1` domain cannot admit an infinite strictly increasing chain of finite intermediate
overrings inside its fraction field. -/
theorem not_exists_infinite_strict_finite_extension_chain_of_isN1Ring
    (hN1 : IsN1Ring R) :
    ¬ ∃ S : ℕ → Subalgebra R (FractionRing R),
        S 0 = ⊥ ∧
          ∀ n, ∃ hlt : S n < S (n + 1),
            (Subalgebra.inclusion hlt.le).toRingHom.Finite := sorry

section Sequence

variable {S : ℕ → Subalgebra R (FractionRing R)}
variable (hS : IsFiniteSemilocalDomainOverringSequence S)

-- Proof sketch: if no stage were regular, then the chain condition would produce a strict finite
-- extension at every step, contradicting the `N-1` stabilization statement above.
/-- Any remark-style chain of finite semilocal one-dimensional overrings inside a fixed fraction
field reaches a regular stage once the base domain is `N-1`. -/
theorem exists_regular_stage_of_finite_semilocal_domain_extension_sequence
    (hN1 : IsN1Ring R) :
    ∃ n, IsRegularRing (S n) := sorry

variable [IsNoetherianRing R]

-- Proof sketch: first upgrade the completion hypothesis to `IsN1Ring R` via the owner theorem
-- above, then apply the `N-1` stopping theorem for the given chain.
/-- Remark `10.119.6`, stopping criterion: if the maximal-local completions of the initial
one-dimensional semilocal Noetherian domain are reduced, equivalently if every maximal
localization is analytically unramified, then any chain of successive finite overrings of the kind
considered in the remark eventually reaches a regular stage and hence stops. -/
theorem exists_regular_stage_of_finite_semilocal_domain_extension_sequence_of_forall_maximal_isAnalyticallyUnramified
    (hdim : ringKrullDim R = 1)
    (hanalytic :
      ∀ m : MaximalSpectrum R, IsAnalyticallyUnramified (Localization.AtPrime m.asIdeal)) :
    ∃ n, IsRegularRing (S n) := sorry

end Sequence

end StoppingCriterion

end
