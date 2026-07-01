import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open IsLocalRing

section ResiduePreimageSubring

variable (A' : Type u) [CommRing A'] [IsLocalRing A']
variable (A : Type v) [CommRing A] [Algebra A (ResidueField A')]

/-- The subring of `A'` consisting of elements whose residue class lies in the image of `A` in the
residue field of `A'`. -/
noncomputable def residuePreimageSubring : Subring A' :=
  Subring.comap (residue A') (algebraMap A (ResidueField A')).range

-- Proof sketch: unfold `residuePreimageSubring`; membership in a `Subring.comap` is exactly
-- membership of the image under `residue A'` in the target subring.
/-- An element of `A'` lies in `residuePreimageSubring A' A` exactly when its residue class comes
from `A`. -/
@[simp] theorem mem_residuePreimageSubring_iff (x : A') :
    x ∈ residuePreimageSubring A' A ↔
      residue A' x ∈ (algebraMap A (ResidueField A')).range := by
  rfl

-- Proof sketch: elements of the maximal ideal have zero residue class, and `0` is always in the
-- image of `A` in `ResidueField A'`.
/-- Any element of the maximal ideal of `A'` lies in `residuePreimageSubring A' A`. -/
theorem mem_residuePreimageSubring_of_mem_maximalIdeal {x : A'}
    (hx : x ∈ maximalIdeal A') :
    x ∈ residuePreimageSubring A' A := by
  have hres : residue A' x = 0 := (IsLocalRing.residue_eq_zero_iff x).mpr hx
  rw [mem_residuePreimageSubring_iff, hres]
  exact ⟨0, by simp⟩

end ResiduePreimageSubring

section

variable (A' : Type u) [CommRing A'] [IsDomain A'] [ValuationRing A']
variable (A : Type v) [CommRing A] [IsDomain A] [ValuationRing A]
variable [Algebra A (ResidueField A')] [IsFractionRing A (ResidueField A')]

private theorem mem_residuePreimageSubring_or_exists_mul_eq_one (x : A') :
    x ∈ residuePreimageSubring A' A ∨
      ∃ y : A', y ∈ residuePreimageSubring A' A ∧ x * y = 1 := by
  by_cases hx : residue A' x = 0
  · left
    exact mem_residuePreimageSubring_of_mem_maximalIdeal A' A <|
      (IsLocalRing.residue_eq_zero_iff x).mp hx
  · obtain hxA | hxA :=
      ValuationRing.isInteger_or_isInteger A (residue A' x)
    · left
      rw [mem_residuePreimageSubring_iff]
      simpa [IsLocalization.IsInteger, RingHom.mem_range] using hxA
    · have hxunit : IsUnit x := by
        refine (IsLocalRing.notMem_maximalIdeal).mp ?_
        intro hxmax
        exact hx ((IsLocalRing.residue_eq_zero_iff x).mpr hxmax)
      rcases hxunit with ⟨u, rfl⟩
      refine Or.inr ⟨↑u⁻¹, ?_, by simp⟩
      rw [mem_residuePreimageSubring_iff]
      simpa [IsLocalization.IsInteger, RingHom.mem_range] using hxA

-- Proof sketch: for every `x : A'`, either `residue A' x = 0`, in which case `x` lies in
-- `residuePreimageSubring A' A`, or the residue class of `x` is nonzero in `ResidueField A'`.
-- Since `A` is a valuation ring with fraction field `ResidueField A'`, either that residue class
-- or its inverse comes from `A`; in the inverse case, `x` is a unit and an inverse of `x` lies in
-- `residuePreimageSubring A' A`. Combining this dichotomy with `ValuationRing.cond` for `A'`
-- gives total divisibility on `residuePreimageSubring A' A`, hence a valuation-ring structure.
/-- Lemma 10.50.10: if `A'` is a valuation ring and its residue field is the fraction field of a
valuation ring `A`, then the subring of `A'` whose residue classes come from `A` is a valuation
ring. -/
theorem residuePreimageSubring_isValuationRing :
    ValuationRing (residuePreimageSubring A' A) := by
  rw [ValuationRing.iff_dvd_total]
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨c, hxy | hyx⟩ := ValuationRing.cond (x : A') (y : A')
  · obtain hc | ⟨d, hd, hcd⟩ := mem_residuePreimageSubring_or_exists_mul_eq_one A' A c
    · exact Or.inl ⟨⟨c, hc⟩, Subtype.ext hxy.symm⟩
    · refine Or.inr ⟨⟨d, hd⟩, ?_⟩
      apply Subtype.ext
      calc
        (x : A') = (x : A') * (c * d) := by simp [hcd]
        _ = ((x : A') * c) * d := by simp [mul_assoc]
        _ = y * d := by rw [hxy]
  · obtain hc | ⟨d, hd, hcd⟩ := mem_residuePreimageSubring_or_exists_mul_eq_one A' A c
    · exact Or.inr ⟨⟨c, hc⟩, Subtype.ext hyx.symm⟩
    · refine Or.inl ⟨⟨d, hd⟩, ?_⟩
      apply Subtype.ext
      calc
        (y : A') = (y : A') * (c * d) := by simp [hcd]
        _ = ((y : A') * c) * d := by simp [mul_assoc]
        _ = x * d := by rw [hyx]

end
