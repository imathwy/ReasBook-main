import Mathlib.RingTheory.Valuation.LocalSubring

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (A : Type u) (K : Type v) [CommRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [IsIntegrallyClosed A]

private instance :
    IsIntegrallyClosedIn ((algebraMap A K).range) K := by
  letI : Algebra A ((algebraMap A K).range) := RingHom.toAlgebra (algebraMap A K).rangeRestrict
  letI : IsScalarTower A ((algebraMap A K).range) K := .of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra.IsIntegral A ((algebraMap A K).range) := {
    isIntegral := fun x ↦ by
      rcases x with ⟨x, ⟨a, rfl⟩⟩
      simpa using (isIntegral_algebraMap : IsIntegral A ((algebraMap A ((algebraMap A K).range)) a))
  }
  rw [Subring.isIntegrallyClosedIn_iff]
  intro x hx
  have hx' : IsIntegral A x := isIntegral_trans x hx
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hx'
  exact ⟨a, ha⟩

private instance [IsLocalRing A] :
    IsIntegrallyClosedIn (LocalSubring.range (algebraMap A K)).toSubring K := by
  simpa using (inferInstance : IsIntegrallyClosedIn ((algebraMap A K).range) K)

-- Proof sketch: apply the valuation-subring existence theorem to the subring
-- `(algebraMap A K).range`, using that a normal domain is integrally closed in its fraction field.
/-- Lemma 10.50.11 (1): if `x` is not in the embedded image of a normal domain `A` inside its
fraction field `K`, then there is a valuation subring of `K` containing `A` but not containing
`x`. -/
theorem exists_valuationSubring_not_mem_of_not_mem_range {x : K}
    (hx : x ∉ (algebraMap A K).range) :
    ∃ V : ValuationSubring K, (algebraMap A K).range ≤ V.toSubring ∧ x ∉ V := by
  simpa using Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hx

-- Proof sketch: view the image of the local domain `A` in `K` as a local subring and apply the
-- local valuation-subring existence theorem for integrally closed local subrings of a field.
/-- Lemma 10.50.11 (2): if `A` is local and `x` is not in the embedded image of `A` inside `K`,
then there is a valuation subring of `K` dominating `A` and still excluding `x`. -/
theorem exists_valuationSubring_dominating_not_mem_of_not_mem_range [IsLocalRing A] {x : K}
    (hx : x ∉ (algebraMap A K).range) :
    ∃ V : ValuationSubring K, LocalSubring.range (algebraMap A K) ≤ V.toLocalSubring ∧ x ∉ V := by
  simpa using LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn hx

-- Proof sketch: identify the image of `A` in `K` with an integrally closed subring of the field
-- `K`, then apply the canonical `eq_iInf` theorem for valuation subrings containing that subring.
/-- Lemma 10.50.11 (3): a normal domain is the intersection of the valuation subrings of its
fraction field that contain its embedded image. -/
theorem range_eq_iInf_valuationSubrings :
    (algebraMap A K).range =
      ⨅ V : {V : ValuationSubring K // (algebraMap A K).range ≤ V.toSubring}, V.1.toSubring :=
  by
    simpa using (Subring.eq_iInf_of_isIntegrallyClosedIn :
      (algebraMap A K).range =
        ⨅ V : {V : ValuationSubring K // (algebraMap A K).range ≤ V.toSubring}, V.1.toSubring)

-- Proof sketch: apply the local-subring intersection theorem to the local image of `A` in `K`;
-- the dominating condition is encoded by the order relation on local subrings.
/-- Lemma 10.50.11 (4): if `A` is local, then its embedded image in `K` is the intersection of
the valuation subrings of `K` that dominate `A`. -/
theorem range_eq_iInf_dominating_valuationSubrings [IsLocalRing A] :
    (algebraMap A K).range =
      ⨅ V : {V : ValuationSubring K // LocalSubring.range (algebraMap A K) ≤ V.toLocalSubring},
        V.1.toSubring := by
  simpa using (LocalSubring.eq_iInf_of_isIntegrallyClosedIn :
    (LocalSubring.range (algebraMap A K)).toSubring =
      ⨅ V : {V : ValuationSubring K // LocalSubring.range (algebraMap A K) ≤ V.toLocalSubring},
        V.1.toSubring)

end
