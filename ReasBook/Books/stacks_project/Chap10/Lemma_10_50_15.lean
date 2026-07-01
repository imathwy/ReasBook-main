import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A] [IsDomain A]

/- Lemma 10.50.15: the canonical library-facing formulation is
`ValuationRing.iff_local_bezout_domain`, i.e. a domain is a valuation ring exactly when it is a
local Bézout domain. -/
recall ValuationRing.iff_local_bezout_domain

/-- A textbook-facing reformulation of `ValuationRing.iff_local_bezout_domain` using the explicit
condition that every finitely generated ideal is principal. This is a thin source-facing bridge;
the owner abstraction remains `IsBezout`. -/
lemma valuationRing_iff_isLocalRing_and_fgIdeals_principal :
    ValuationRing A ↔ IsLocalRing A ∧ ∀ I : Ideal A, I.FG → I.IsPrincipal := by
  constructor
  · intro hvaluation
    exact ⟨inferInstance, IsBezout.isPrincipal_of_FG⟩
  · rintro ⟨hlocal, hprincipal⟩
    exact ValuationRing.iff_local_bezout_domain.2 ⟨hlocal, ⟨hprincipal⟩⟩

end
