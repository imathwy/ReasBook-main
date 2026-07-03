import Mathlib
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_53_1 (from Chap10) -/
universe u

section

variable (R : Type u) [CommRing R]

/-
Definition 10.53.1 is recalled canonically by `IsArtinianRing R`: a commutative ring is Artinian
when it satisfies the descending chain condition for ideals.
-/
recall IsArtinianRing

/-- The textbook descending-chain formulation of an Artinian ring, stated directly for ideals. -/
theorem isArtinianRing_iff_ideal_descending_chain_condition :
    IsArtinianRing R ↔ ∀ (f : ℕ →o (Ideal R)ᵒᵈ),
      ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m := by
  simpa [IsArtinianRing] using
    (show (∀ f : ℕ →o (Ideal R)ᵒᵈ, ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m) ↔ IsArtinian R R from
      monotone_stabilizes_iff_artinian).symm

end

/-! ### Lemma_10_53_2 (from Chap10) -/
universe u v

/- Domain triage:
- primary domain: finite-dimensional algebras and Artinian rings;
- sampled owner declarations: `IsArtinianRing.of_finite`,
  `isArtinian_of_fg_of_artinian`, and `isArtinian_of_tower`;
- best owner abstraction: the canonical owner is the typeclass `IsArtinianRing A`;
- primitive data: the ambient field `k`, the `k`-algebra `A`, and the finite-dimensionality
  hypothesis;
- derived API: the Artinian-ring structure on `A`, obtained from the canonical bridge
  `FiniteDimensional k A → Module.Finite k A`.

Source/core/bridge triage:
- `source-facing`: the field-specialized statement that a finite-dimensional `k`-algebra is
  Artinian;
- `core/canonical`: `IsArtinianRing A`;
- `bridge/view`: the theorem `IsArtinianRing.of_finite`, which promotes finite module structure
  over an Artinian base ring to an Artinian target ring. -/

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/- Lemma 10.53.2: a finite-dimensional algebra over a field is an Artinian ring.

This is exactly the field-specialized source wording of the canonical mathlib theorem
`IsArtinianRing.of_finite`. -/
recall IsArtinianRing.of_finite

/-! ### Lemma_10_53_3 (from Chap10) -/
universe u

variable {R : Type u} [CommRing R] [IsArtinianRing R]

/- Lemma 10.53.3: if `R` is Artinian, then `R` has only finitely many maximal ideals. The owner
abstraction is `IsArtinianRing R`, and the source-facing conclusion is the derived instance
`Finite (MaximalSpectrum R)` provided by `IsArtinianRing.instFiniteMaximalSpectrum`. -/
recall IsArtinianRing.instFiniteMaximalSpectrum

/-! ### Lemma_10_53_4 (from Chap10) -/
universe u

variable {R : Type u} [CommRing R] [IsArtinianRing R]

/- Lemma 10.53.4: if `R` is Artinian, then its Jacobson radical is nilpotent. The owner
declaration is the canonical mathlib theorem `IsArtinianRing.isNilpotent_jacobson_bot`; the source
wording identifies `Ideal.jacobson (⊥ : Ideal R)` with `Ring.jacobson R` via `Ideal.jacobson_bot`.
-/
recall IsArtinianRing.isNilpotent_jacobson_bot

/-! ### Lemma_10_53_5 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R]

-- Under the hypotheses of Lemma `10.53.5`, the prime spectrum is discrete; the numbered parts
-- then become direct consequences of the canonical spectrum-localization API in mathlib. The
-- locally nilpotent Jacobson radical is expressed through the chapter owner abstraction
-- `(Ring.jacobson R).IsLocallyNilpotent`.
instance primeSpectrum_discreteTopology_of_finite_of_jacobson_locallyNilpotent
    (hfin : Finite (MaximalSpectrum R))
    (hjac : (Ring.jacobson R).IsLocallyNilpotent) :
    DiscreteTopology (PrimeSpectrum R) := by
  refine (PrimeSpectrum.discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical).2 ?_
  refine ⟨?_, ?_⟩
  · simpa using (MaximalSpectrum.equivSubtype R).finite_iff.mp hfin
  · simpa [Ideal.IsLocallyNilpotent, Ring.jacobson_eq_sInf_isMaximal] using hjac

-- Proof sketch: finite many maximal ideals together with the locally nilpotent Jacobson radical
-- imply that `Spec R` is discrete, so the canonical map to the product of localizations at the
-- maximal ideals is the canonical equivalence `MaximalSpectrum.toPiLocalizationEquiv`.
/-- Lemma 10.53.5 (1): if `R` has finitely many maximal ideals and its Jacobson radical is locally
nilpotent, then `R` is canonically isomorphic to the product of its localizations at maximal
ideals. -/
noncomputable def maximalSpectrum_toPiLocalizationEquiv_of_finite_of_jacobson_locallyNilpotent
    (hfin : Finite (MaximalSpectrum R))
    (hjac : (Ring.jacobson R).IsLocallyNilpotent) :
    R ≃+* MaximalSpectrum.PiLocalization R :=
  letI := primeSpectrum_discreteTopology_of_finite_of_jacobson_locallyNilpotent hfin hjac
  MaximalSpectrum.toPiLocalizationEquiv R

-- Proof sketch: after installing the discrete-spectrum instance, the definition is exactly the
-- canonical equivalence `MaximalSpectrum.toPiLocalizationEquiv`, whose underlying ring hom is
-- `MaximalSpectrum.toPiLocalization`.
/-- The equivalence of `R` with the product of its localizations at maximal ideals extends the
canonical map to that product. -/
theorem maximalSpectrum_toPiLocalizationEquiv_of_finite_of_jacobson_locallyNilpotent_toRingHom
    (hfin : Finite (MaximalSpectrum R))
    (hjac : (Ring.jacobson R).IsLocallyNilpotent) :
    (maximalSpectrum_toPiLocalizationEquiv_of_finite_of_jacobson_locallyNilpotent hfin hjac).toRingHom =
      MaximalSpectrum.toPiLocalization R := by
  -- Installing the discrete-spectrum instance reduces the wrapper to the owner equivalence.
  unfold maximalSpectrum_toPiLocalizationEquiv_of_finite_of_jacobson_locallyNilpotent
  -- The underlying ring hom of `RingEquiv.ofBijective` is definitionally the original map.
  rfl

-- Proof sketch: the preceding instance makes `Spec R` discrete, so the canonical zero-dimensional
-- consequence `Ring.KrullDimLE 0 R` applies; then every prime ideal is maximal by the owner API
-- `Ring.krullDimLE_zero_iff`.
/-- Lemma 10.53.5 (2): if `R` has finitely many maximal ideals and its Jacobson radical is locally
nilpotent, then every prime ideal of `R` is maximal. -/
theorem isMaximal_of_isPrime_of_finite_of_jacobson_locallyNilpotent
    (hfin : Finite (MaximalSpectrum R))
    (hjac : (Ring.jacobson R).IsLocallyNilpotent)
    {I : Ideal R} (hI : I.IsPrime) :
    I.IsMaximal := by
  letI := primeSpectrum_discreteTopology_of_finite_of_jacobson_locallyNilpotent hfin hjac
  haveI : Ring.KrullDimLE 0 R :=
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).2
  exact hI.isMaximal'

end

/-! ### Lemma_10_53_6 (from Chap10) -/
universe u

section

variable (R : Type u) [CommRing R]

/- Lemma 10.53.6: a commutative ring is Artinian if and only if it has finite length as a module
over itself. This is the canonical theorem `isArtinianRing_iff_isFiniteLength`. -/
recall isArtinianRing_iff_isFiniteLength

section

variable [IsArtinianRing R]

/- An Artinian commutative ring is Noetherian. This is the canonical instance
`instIsNoetherianRingOfIsArtinianRing`. -/
recall instIsNoetherianRingOfIsArtinianRing

/- In an Artinian commutative ring, every prime ideal is maximal. This is the canonical theorem
`IsArtinianRing.isPrime_iff_isMaximal`. -/
recall IsArtinianRing.isPrime_iff_isMaximal

/- An Artinian commutative ring is canonically isomorphic to the finite product of its localizations
at its maximal ideals. This is the canonical equivalence `MaximalSpectrum.toPiLocalizationEquiv`. -/
recall MaximalSpectrum.toPiLocalizationEquiv

end

end
