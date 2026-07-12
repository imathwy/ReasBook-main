import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]

omit [ValuationRing A] in
private instance isDomain_localization (S : Submonoid A) [Fact ((0 : A) ∉ S)] :
    IsDomain (Localization S) := by
  exact IsLocalization.isDomain_localization
    (le_nonZeroDivisors_of_noZeroDivisors Fact.out)

omit [IsDomain A] [ValuationRing A] in
private theorem mk'_dvd_mk'_of_mul_eq (S : Submonoid A) [Fact ((0 : A) ∉ S)] {a b c : A}
    (s t : S) (h : a * t * c = b * s) :
    IsLocalization.mk' (Localization S) a s ∣ IsLocalization.mk' (Localization S) b t := by
  have h_one : IsLocalization.mk' (Localization S) c (1 : S) =
      algebraMap A (Localization S) c :=
    IsLocalization.mk'_one (Localization S) c
  have h_mul : IsLocalization.mk' (Localization S) (a * c) (s * 1) =
      IsLocalization.mk' (Localization S) a s * IsLocalization.mk' (Localization S) c 1 :=
    IsLocalization.mk'_mul (Localization S) a c s 1
  refine ⟨algebraMap A (Localization S) c, ?_⟩
  rw [← h_one, ← h_mul]
  exact IsLocalization.mk'_eq_of_eq' (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using h)

/-- Lemma 10.50.9: if `S` is a submonoid of a valuation ring `A` with `0 ∉ S`, then
`Localization S` is again a valuation ring. This is the Lean form of the source statement that any
localization of a valuation ring is again a valuation ring. The owner abstraction is
`ValuationRing.iff_dvd_total`; the proof below is the source-facing localization bridge. -/
@[stacks 088Y]
instance valuationRing_localization (S : Submonoid A) [Fact ((0 : A) ∉ S)] :
    ValuationRing (Localization S) := by
  refine ValuationRing.iff_dvd_total.mpr ⟨fun x y ↦ ?_⟩
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
  obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq S y
  obtain ⟨c, h | h⟩ := ValuationRing.cond (a * t) (b * s)
  · left
    exact mk'_dvd_mk'_of_mul_eq S s t h
  · right
    exact mk'_dvd_mk'_of_mul_eq S t s h

/-- Localization at a prime ideal of a valuation ring is again a valuation ring. -/
instance valuationRing_localization_atPrime (p : Ideal A) [p.IsPrime] :
    ValuationRing (Localization.AtPrime p) := by
  letI : Fact ((0 : A) ∉ p.primeCompl) := ⟨by
    simp [Ideal.primeCompl, Ideal.zero_mem p]⟩
  infer_instance

/-- Quotienting a valuation ring by a prime ideal again yields a valuation ring. This is the exact
owner theorem `Function.Surjective.valuationRing` applied to the quotient map. -/
instance valuationRing_quotient (p : Ideal A) [p.IsPrime] : ValuationRing (A ⧸ p) := by
  simpa using Function.Surjective.valuationRing
    (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

end
