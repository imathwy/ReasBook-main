import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Valuation.ValuationRing

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Submodule.IsPrincipal

/-
Domain-style sampling:
- primary domain: commutative algebra of generalized valuation rings and their ideal theory;
- sampled owner declarations:
  `PreValuationRing`,
  `PreValuationRing.iff_dvd_total`,
  `PreValuationRing.iff_ideal_total`,
  `ValuationRing.iff_local_bezout_domain`;
- best owner abstraction: `PreValuationRing R` is the canonical owner for the non-domain
  generalized valuation-ring condition, while `ValuationRing R` remains the domain specialization;
- primitive data vs. derived API:
  primitive data is only the ambient nontrivial commutative ring `R` together with the owner
  predicate `PreValuationRing R`;
  derived API is the source-facing comparison with the local Bézout and ideal-order formulations,
  so the TFAE should reuse the owner instead of restating total divisibility as a separate clause.

Source/core/bridge triage:
- `source-facing`: the three-way equivalence in the Stacks lemma;
- `core/canonical`: `PreValuationRing`, `ValuationRing`, `IsLocalRing`, `IsBezout`, and the ideal
  order on `Ideal R`;
- `bridge/view`: the theorem `generalized_valuation_ring_tfae`, which compares the source-facing
  local Bézout and ideal-order statements to the canonical owner `PreValuationRing R`.
-/

variable {R : Type u} [CommRing R]

theorem isPrincipal_span_finset_of_ideal_total
    (h : @Std.Total (Ideal R) (· ≤ ·)) (s : Finset R) :
    (Ideal.span (s : Set R)).IsPrincipal := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (bot_isPrincipal : (⊥ : Ideal R).IsPrincipal)
  | insert x s _ hs =>
      rcases h.total (Ideal.span ({x} : Set R)) (Ideal.span (s : Set R)) with hxs | hsx
      · simpa [Finset.coe_insert, Ideal.span_insert, sup_eq_right.mpr hxs] using hs
      · simpa [Finset.coe_insert, Ideal.span_insert, sup_eq_left.mpr hsx] using
          (inferInstance : (Ideal.span ({x} : Set R)).IsPrincipal)

theorem isBezout_of_ideal_total (h : @Std.Total (Ideal R) (· ≤ ·)) : IsBezout R := by
  refine ⟨fun I hI ↦ ?_⟩
  rcases hI with ⟨s, rfl⟩
  exact isPrincipal_span_finset_of_ideal_total h s

theorem ideal_eq_span_singleton_of_not_mem_maximalIdeal_mul [IsLocalRing R] {I : Ideal R}
    [I.IsPrincipal] {x : R} (hxI : x ∈ I) (hx : x ∉ IsLocalRing.maximalIdeal R * I) :
    I = Ideal.span ({x} : Set R) := by
  obtain ⟨r, hr⟩ :=
    Ideal.mem_span_singleton'.mp (by
      simpa [Ideal.span_singleton_generator I] using hxI :
        x ∈ Ideal.span ({generator I} : Set R))
  have hr_not_mem : r ∉ IsLocalRing.maximalIdeal R := by
    intro hr_mem
    apply hx
    simpa [hr] using
      (Ideal.mul_mem_mul hr_mem (generator_mem I) :
        r * generator I ∈ IsLocalRing.maximalIdeal R * I)
  have hr_unit : IsUnit r := IsLocalRing.notMem_maximalIdeal.mp hr_not_mem
  rcases hr_unit with ⟨u, rfl⟩
  apply le_antisymm
  · rw [← Ideal.span_singleton_generator I]
    exact (Ideal.span_singleton_le_iff_mem (Ideal.span ({x} : Set R))).2 <|
      Ideal.mem_span_singleton'.2 ⟨↑u⁻¹, by
        calc
          ↑u⁻¹ * x = ↑u⁻¹ * (↑u * generator I) := by rw [hr]
          _ = generator I := by simp⟩
  · exact (Ideal.span_singleton_le_iff_mem I).2 hxI

theorem span_pair_eq_span_left_or_right [IsLocalRing R] [IsBezout R] (a b : R) :
    Ideal.span ({a, b} : Set R) = Ideal.span ({a} : Set R) ∨
      Ideal.span ({a, b} : Set R) = Ideal.span ({b} : Set R) := by
  let I : Ideal R := Ideal.span ({a, b} : Set R)
  letI : I.IsPrincipal := by
    simpa [I] using (inferInstance : (Ideal.span ({a, b} : Set R)).IsPrincipal)
  by_cases hI : I = ⊥
  · left
    have ha : a = 0 := by
      simpa using (show a ∈ (⊥ : Ideal R) by
        simpa [I, hI] using (Ideal.subset_span (by simp : a ∈ ({a, b} : Set R))))
    have hb : b = 0 := by
      simpa using (show b ∈ (⊥ : Ideal R) by
        simpa [I, hI] using (Ideal.subset_span (by simp : b ∈ ({a, b} : Set R))))
    simp [ha, hb]
  have h_not :
      a ∉ IsLocalRing.maximalIdeal R * I ∨ b ∉ IsLocalRing.maximalIdeal R * I := by
    by_contra h
    have ha_mul : a ∈ IsLocalRing.maximalIdeal R * I := by
      by_contra ha
      exact h (Or.inl ha)
    have hb_mul : b ∈ IsLocalRing.maximalIdeal R * I := by
      by_contra hb
      exact h (Or.inr hb)
    have hle : I ≤ IsLocalRing.maximalIdeal R * I := by
      change Ideal.span ({a, b} : Set R) ≤ IsLocalRing.maximalIdeal R * I
      refine Ideal.span_le.2 ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha_mul
      · exact hb_mul
    have hfg : I.FG := (inferInstance : I.IsPrincipal).fg
    exact hI <|
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) I hfg hle
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  rcases h_not with ha | hb
  · left
    exact ideal_eq_span_singleton_of_not_mem_maximalIdeal_mul
      (show a ∈ I by
        change a ∈ Ideal.span ({a, b} : Set R)
        exact Ideal.subset_span (by simp))
      ha
  · right
    exact ideal_eq_span_singleton_of_not_mem_maximalIdeal_mul
      (show b ∈ I by
        change b ∈ Ideal.span ({a, b} : Set R)
        exact Ideal.subset_span (by simp))
      hb

theorem ideal_total_of_isLocalRing_isBezout [IsLocalRing R] [IsBezout R] :
    @Std.Total (Ideal R) (· ≤ ·) := by
  constructor
  intro I J
  classical
  by_cases hIJ : I ≤ J
  · exact Or.inl hIJ
  · right
    by_cases hJI : J ≤ I
    · exact hJI
    · have hIJ' : ∃ a, a ∈ I ∧ a ∉ J := by
        by_contra h
        apply hIJ
        intro a haI
        by_contra haJ
        exact h ⟨a, haI, haJ⟩
      have hJI' : ∃ b, b ∈ J ∧ b ∉ I := by
        by_contra h
        apply hJI
        intro b hbJ
        by_contra hbI
        exact h ⟨b, hbJ, hbI⟩
      obtain ⟨a, haI, haJ⟩ := hIJ'
      obtain ⟨b, hbJ, hbI⟩ := hJI'
      rcases span_pair_eq_span_left_or_right a b with hspan | hspan
      · exfalso
        apply hbI
        have hb_span : b ∈ Ideal.span ({a} : Set R) := by
          simpa [← hspan] using (Ideal.subset_span (by simp : b ∈ ({a, b} : Set R)))
        exact ((Ideal.span_singleton_le_iff_mem I).2 haI) hb_span
      · exfalso
        apply haJ
        have ha_span : a ∈ Ideal.span ({b} : Set R) := by
          simpa [← hspan] using (Ideal.subset_span (by simp : a ∈ ({a, b} : Set R)))
        exact ((Ideal.span_singleton_le_iff_mem J).2 hbJ) ha_span

variable (R : Type u) [CommRing R] [Nontrivial R]

-- Proof sketch: use the canonical owner `PreValuationRing R` for the generalized valuation-ring
-- condition, obtain `IsLocalRing R` from the existing instance, derive `IsBezout R` by showing
-- every two-generated ideal is principal, and compare the first and third clauses using
-- `PreValuationRing.iff_ideal_total`.
/-- Lemma 15.125.2 (Generalized valuation rings): for a nonzero commutative ring `R`, the
following are equivalent: `R` is a generalized valuation ring in the canonical sense
`PreValuationRing R`, `R` is a local Bézout ring, and the ideals of `R` are linearly ordered by
inclusion. -/
theorem generalized_valuation_ring_tfae :
    List.TFAE
      [PreValuationRing R,
        IsLocalRing R ∧ IsBezout R,
        @Std.Total (Ideal R) (· ≤ ·)] := by
  tfae_have 1 ↔ 3 := PreValuationRing.iff_ideal_total
  tfae_have 3 → 2 := by
    intro h
    letI : PreValuationRing R := (PreValuationRing.iff_ideal_total.mpr h)
    exact ⟨inferInstance, isBezout_of_ideal_total h⟩
  tfae_have 2 → 3 := by
    rintro ⟨hlocal, hbezout⟩
    letI : IsLocalRing R := hlocal
    letI : IsBezout R := hbezout
    exact ideal_total_of_isLocalRing_isBezout
  tfae_finish

end
