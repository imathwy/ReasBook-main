import Mathlib
import StacksProject_2024.Chap10.Definition_10_32_1

-- Declarations for this item will be appended below by the statement pipeline.

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
