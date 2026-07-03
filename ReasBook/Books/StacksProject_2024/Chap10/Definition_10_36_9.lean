import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Definition 10.36.9 (Tag 00GP): for a ring map `R → S`, the canonical `R`-subalgebra
`integralClosure R S` is the integral closure `S'` of `R` in `S`. -/
recall integralClosure

/- The same definition uses the canonical owner predicate `IsIntegrallyClosedIn R S` for the map
`R → S` being integrally closed. -/
recall IsIntegrallyClosedIn {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] :
    Prop

end

section

variable {S : Type u} [CommRing S]

namespace Subring

variable (R : Subring S)

/-- Companion bridge for Definition 10.36.9: a subring `R` of `S` is integrally closed in `S`
exactly when it agrees with the canonical integral-closure subring. -/
theorem isIntegrallyClosedIn_iff_eq_integralClosure :
    IsIntegrallyClosedIn R S ↔ R = (integralClosure R S).toSubring := by
  have hbot : (⊥ : Subalgebra R S).toSubring = R := by
    ext x
    rw [Subalgebra.mem_toSubring, Algebra.mem_bot, Set.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  constructor
  · intro h
    have hc : integralClosure R S = ⊥ :=
      (IsIntegrallyClosedIn.integralClosure_eq_bot_iff S
        (FaithfulSMul.algebraMap_injective R S)).mpr h
    calc
      R = (⊥ : Subalgebra R S).toSubring := hbot.symm
      _ = (integralClosure R S).toSubring := by simp [hc]
  · intro h
    have hc : integralClosure R S = ⊥ := by
      apply Subalgebra.toSubring_injective
      calc
        (integralClosure R S).toSubring = R := h.symm
        _ = (⊥ : Subalgebra R S).toSubring := hbot.symm
    exact (IsIntegrallyClosedIn.integralClosure_eq_bot_iff S
      (FaithfulSMul.algebraMap_injective R S)).mp hc

end Subring

end
