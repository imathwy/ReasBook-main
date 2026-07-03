import Mathlib
import stacks_project.Chap15.Lemma_15_111_2
import stacks_project.Chap15.Lemma_15_111_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]

local notation "RFix" => FixedPoints.subring R G

/- Domain-style sampling for Remark 15.111.5:
- primary domain: invariant-theoretic fixed-point quotients for finite group actions when `|G|` is
  invertible
- sampled owner declarations:
  `fixedSubringQuotientToFixedQuotient`,
  `fixedSubringFixedQuotient`,
  `RingEquiv.ofBijective`,
  `Nat.card`
- best owner abstraction: the source-facing owner is still the canonical map
  `fixedSubringQuotientToFixedQuotient J` from `Lemma_15_111_4`; once bijectivity is proved, the
  canonical derived API is the induced ring equivalence
- primitive data: the ideal `J : Ideal RFix` and the invertibility hypothesis on `|G|`
- derived API: bijectivity of the canonical map and the resulting ring equivalence

Layer triage:
- `source-facing`: bijectivity of the canonical map `(R^G)/J → (R / JR)^G`
- `core/canonical`: `fixedSubringQuotientToFixedQuotient` from `Lemma_15_111_4`
- `bridge/view`: `RingEquiv.ofBijective` packaging that canonical map as an isomorphism

The public finiteness assumption should be `[Finite G]`; the proof may introduce a local
`Fintype` instance, but the theorem statement only depends on `Nat.card G`.
-/

-- Proof sketch: use the averaging operator `|G|⁻¹ ∑ g∈G g` on `R / JR`. When `|G|` is invertible
-- in `R`, averaging projects onto the fixed subring and gives an inverse to the canonical map
-- from `(R^G)/J`.
/-- Remark 15.111.5: if `|G|` is a unit in `R`, then the canonical map
`(R^G)/J → (R / JR)^G` is bijective, hence an isomorphism. -/
theorem fixedSubringQuotientToFixedQuotient_bijective_of_isUnit_card
    (J : Ideal RFix) (h_card : IsUnit (Nat.card G : R)) :
    Function.Bijective (fixedSubringQuotientToFixedQuotient J) := by
  letI := Fintype.ofFinite G
  letI := h_card.invertible
  sorry

/-- Remark 15.111.5, canonical isomorphism form: if `|G|` is a unit in `R`, then the canonical map
`(R^G)/J → (R / JR)^G` is an isomorphism of rings. -/
noncomputable def fixedSubringQuotientToFixedQuotientEquivOfIsUnit_card
    (J : Ideal RFix) (h_card : IsUnit (Nat.card G : R)) :
    RFix ⧸ J ≃+* fixedSubringFixedQuotient J :=
  RingEquiv.ofBijective (fixedSubringQuotientToFixedQuotient J)
    (fixedSubringQuotientToFixedQuotient_bijective_of_isUnit_card J h_card)

end
