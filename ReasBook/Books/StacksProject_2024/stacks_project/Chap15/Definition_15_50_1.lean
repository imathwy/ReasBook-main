import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_7
import StacksProject_2024.stacks_project.Chap15.Definition_15_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra IsLocalRing

universe u v

section

/-- The completion of the localization `R_𝔭` at its maximal ideal. -/
abbrev CompletedLocalizationAtPrime (R : Type u) [CommRing R] (p : PrimeSpectrum R) : Type u :=
  AdicCompletion (maximalIdeal (Localization.AtPrime p.asIdeal))
    (Localization.AtPrime p.asIdeal)

notation:max "R̂_[" p "]" => CompletedLocalizationAtPrime _ p

namespace CompletedLocalizationAtPrime

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {R' : Type v} [CommRing R'] [Algebra R R'] [Algebra.FiniteType R R']

/-- The canonical map on completed localizations induced by a prime `p'` of `R'` lying over `p`
in the intrinsic prime-spectrum sense `PrimeSpectrum.comap (algebraMap R R') p' = p`. -/
noncomputable abbrev map (p : PrimeSpectrum R) (p' : PrimeSpectrum R')
    (hp : PrimeSpectrum.comap (algebraMap R R') p' = p) :
    R̂_[p] →+* R̂_[p'] :=
  letI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  maximalIdealCompletionMap
    (Localization.localRingHom p.asIdeal p'.asIdeal (algebraMap R R')
      (by
        simpa [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hp).symm))

end

end CompletedLocalizationAtPrime

/-- Definition 15.50.1: a ring `R` is a `G`-ring if `R` is Noetherian and, for every prime `p`
of `R`, the canonical map from the local ring `R_p` to its maximal-ideal-adic completion is a
regular ring map. -/
class IsGRing (R : Type u) [CommRing R] : Prop extends IsNoetherianRing R where
  /-- For every prime `p`, the completion map from `R_p` to its maximal-ideal-adic completion is
  regular. -/
  regular_localization_completion (p : PrimeSpectrum R) :
    (algebraMap (Localization.AtPrime p.asIdeal) (R̂_[p])).IsRegularRingMap

variable {R : Type u} [CommRing R]

/-- The `G`-ring condition is exactly regularity of the completion map at every prime
localization. -/
theorem isGRing_iff_forall_regular_localization_completion [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ p : PrimeSpectrum R,
        (algebraMap (Localization.AtPrime p.asIdeal) (R̂_[p])).IsRegularRingMap :=
  ⟨fun h p ↦ h.regular_localization_completion p,
    fun h ↦ { regular_localization_completion := h }⟩

section

variable (K : Type u) [Field K]

-- Proof sketch: a field is Noetherian, and for its unique prime the localization is again the
-- field; the completion at the zero maximal ideal identifies with the field, so the completion map
-- is the identity regular morphism.
/-- A field is a `G`-ring. -/
instance : IsGRing K := sorry

end

end
