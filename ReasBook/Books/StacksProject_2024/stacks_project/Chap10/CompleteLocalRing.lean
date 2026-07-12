import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

universe u

open IsLocalRing

section

variable (R : Type u) [CommRing R]

/-- A complete local ring is a local ring that is complete for the adic topology defined by its
maximal ideal. -/
class IsCompleteLocalRing : Prop extends IsLocalRing R, IsAdicComplete (maximalIdeal R) R

variable {R}

/-- Any local ring that is adically complete with respect to its maximal ideal is a complete local
ring. -/
instance [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] : IsCompleteLocalRing R := {}

/-- Complete-local structure transports across ring equivalences. -/
theorem isCompleteLocalRing_of_ringEquiv
    {S T : Type u} [CommRing S] [CommRing T] (e : S ≃+* T)
    [IsCompleteLocalRing T] :
    IsCompleteLocalRing S := by
  letI : IsLocalRing S := RingEquiv.isLocalRing e.symm
  letI : IsAdicComplete (maximalIdeal S) S := by
    have hT : IsAdicComplete (maximalIdeal T) T := inferInstance
    have hS : IsAdicComplete ((maximalIdeal T).map e.symm) S :=
      (IsAdicComplete.congr_ringEquiv (I := maximalIdeal T) e.symm).2 hT
    simpa [IsLocalRing.map_ringEquiv_maximalIdeal] using hS
  infer_instance

end
