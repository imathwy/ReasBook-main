import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Domain-style sampling pass for Definition 10.50.1.

Primary domain: valuation theory for local subrings of a field.

Sampled owner declarations:
* `LocalSubring.le_def`;
* `LocalSubring.isMax_iff`;
* `ValuationRing.range_algebraMap_eq`;
* `ValuationRing.iff_isInteger_or_isInteger`.

Owner abstraction: domination is the canonical order on `LocalSubring K`, while valuation-ring
structure is carried by `ValuationRing A` and `ValuationSubring K`. The image of `A` in its
fraction field is derived owner data `LocalSubring.range (algebraMap A (FractionRing A))`, so the
main theorem below stays a source-facing bridge from that image to the owner theorem
`LocalSubring.isMax_iff`.

Layering:
* source-facing: `valuationRing_iff_isMax_range_fractionRing`;
* core/canonical: `LocalSubring K`, `ValuationSubring K`, `ValuationRing A`;
* bridge/view: `LocalSubring.range (algebraMap A (FractionRing A))`.
-/

/- Definition 10.50.1: on local subrings of a field, the domination relation is the canonical
order `≤`; equivalently it is characterized by `LocalSubring.le_def`. -/
recall LocalSubring.le_def

/- Definition 10.50.1: the canonical mathlib notion of a valuation ring is `ValuationRing`. -/
recall ValuationRing

/- Definition 10.50.1: a local subring of a field is a valuation ring exactly when it is maximal
for the domination order. This owner theorem is `LocalSubring.isMax_iff`. -/
recall LocalSubring.isMax_iff

section

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]

local notation "K" => FractionRing A

/-- Definition 10.50.1: a local domain `A` is a valuation ring if and only if its image in its
fraction field is maximal for the domination order on local subrings. -/
theorem valuationRing_iff_isMax_range_fractionRing :
    ValuationRing A ↔ IsMax (LocalSubring.range (algebraMap A K)) := by
  let A0 : LocalSubring K := LocalSubring.range (algebraMap A K)
  change ValuationRing A ↔ IsMax A0
  constructor
  · intro
    let V : ValuationSubring K := (ValuationRing.valuation A K).valuationSubring
    have hV : V.toLocalSubring = A0 := by
      apply LocalSubring.toSubring_injective
      simpa [A0, V] using ValuationRing.range_algebraMap_eq A K
    simpa [hV] using V.isMax_toLocalSubring
  · intro hA
    rw [ValuationRing.iff_isInteger_or_isInteger A K]
    intro x
    obtain ⟨V, hV⟩ := LocalSubring.isMax_iff.mp hA
    have hV' : V.toSubring = A0.toSubring := congrArg LocalSubring.toSubring hV
    rcases V.mem_or_inv_mem x with hx | hx
    · left
      simpa [IsLocalization.IsInteger, RingHom.mem_range, hV'] using (show x ∈ V.toSubring from hx)
    · right
      simpa [IsLocalization.IsInteger, RingHom.mem_range, hV'] using
        (show x⁻¹ ∈ V.toSubring from hx)

end

section

variable {K : Type u} [Field K] (V : ValuationSubring K) (R : Subring K)

/- Definition 10.50.1: the Stacks phrase “`V` is centered on `R`” is exactly the containment
condition `R ≤ V.toSubring`. -/
#check R ≤ V.toSubring

end
