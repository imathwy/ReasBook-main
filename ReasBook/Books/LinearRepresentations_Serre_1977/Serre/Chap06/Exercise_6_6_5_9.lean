import LinearRepresentations_Serre_1977.Serre.Chap06.Corollary_6_6_5_3
import LinearRepresentations_Serre_1977.Serre.Chap06.Exercise_6_6_5_6
import LinearRepresentations_Serre_1977.Serre.Chap06.Exercise_6_6_5_7
import LinearRepresentations_Serre_1977.Serre.Chap06.Exercise_6_6_5_8
import LinearRepresentations_Serre_1977.Serre.Chap06.Proposition_6_6_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Representation

open scoped BigOperators MonoidAlgebra
open Module.End Polynomial

noncomputable section

section IrreducibleFiniteGroup

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) [ρ.IsIrreducible] (s : G)

-- Source/core/bridge triage:
-- * source-facing: the two exercise statements below.
-- * core/canonical owners for part (1): `conjugacyClassSumInCenter` and
--   `isIntegral_finrank_inv_sum_coeff_mul_character`.
-- * core/canonical owners for part (2): `Finset.all_eq_expect_of_ne_zero` and
--   `character_norm_eq_char_one_iff_exists_smul_id`.
-- Primitive data: the irreducible representation `ρ`, the group element `s`, and the arithmetic
-- hypotheses on the conjugacy-class cardinality and the character value.
-- Derived API: the algebraic-integrality scalar from the central class sum, and the resulting
-- scalar-action conclusion for `ρ s`.
--
-- Proof sketch: apply `isIntegral_finrank_inv_sum_coeff_mul_character` to the canonical central
-- class sum `conjugacyClassSumInCenter (ConjClasses.mk s)`. Its coefficients are `0` or `1`, so
-- the normalized character sum is exactly the class cardinality times `ρ.character s` divided by
-- `Module.finrank ℂ V`.
/-- Exercise 6-6.5-9 (1): for an irreducible finite-dimensional complex representation, the
character value at `s` multiplied by the size of the conjugacy class of `s` and divided by the
degree is an algebraic integer. -/
theorem isIntegral_conjClass_card_div_finrank_mul_character
    : by
        letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
        exact
          IsIntegral ℤ
            (((Nat.card (ConjClasses.mk s).carrier : ℂ) / Module.finrank ℂ V) *
              ρ.character s) := by
  classical
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Fintype G := Fintype.ofFinite G
  let u : Subalgebra.center ℂ (ℂ[G]) := conjugacyClassSumInCenter ℂ (ConjClasses.mk s)
  let T : Finset G := Finset.univ.filter fun t ↦ t ∈ (ConjClasses.mk s).carrier
  have hcoeff : ∀ t : G, IsIntegral ℤ ((u : ℂ[G]) t) := fun t ↦ by
    by_cases ht : ConjClasses.mk t = ConjClasses.mk s
    · simpa [u, conjugacyClassSum_apply, ConjClasses.indicator,
        ConjClasses.mem_carrier_iff_mk_eq, ht] using isIntegral_one
    · simpa [u, conjugacyClassSum_apply, ConjClasses.indicator,
        ConjClasses.mem_carrier_iff_mk_eq, ht] using isIntegral_zero
  have h := isIntegral_finrank_inv_sum_coeff_mul_character ρ u hcoeff
  have hsum_filter :
      ∑ t : G, (u : ℂ[G]) t * ρ.character t = T.sum (fun t ↦ ρ.character t) := by
    rw [show T = Finset.univ.filter (fun t ↦ t ∈ (ConjClasses.mk s).carrier) by rfl,
      Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro t _
    by_cases ht : t ∈ (ConjClasses.mk s).carrier
    · simp [u, conjugacyClassSum_apply, ConjClasses.indicator, ht]
    · simp [u, conjugacyClassSum_apply, ConjClasses.indicator, ht]
  have hsum_subtype :
      T.sum (fun t ↦ ρ.character t) = ∑ t : (ConjClasses.mk s).carrier, ρ.character t := by
    change
      (Finset.univ.filter (fun t : G ↦ t ∈ (ConjClasses.mk s).carrier)).sum
          (fun t ↦ ρ.character t) =
        ∑ t : (ConjClasses.mk s).carrier, ρ.character t
    rw [← Finset.sum_subtype_eq_sum_filter]
    simp
  have hsum_const :
      (∑ t : (ConjClasses.mk s).carrier, ρ.character t) =
        ∑ _ : (ConjClasses.mk s).carrier, ρ.character s := by
    refine Finset.sum_congr rfl ?_
    intro t _
    rcases ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.mem_carrier_iff_mk_eq.mp t.2) with
      ⟨u, hu⟩
    have hconj_eq : (u : G) * t * (u : G)⁻¹ = s := by
      calc
        (u : G) * t * (u : G)⁻¹ = (s * (u : G)) * (u : G)⁻¹ := by rw [hu.eq]
        _ = s := by simp [mul_assoc]
    exact (ρ.char_conj t u).symm.trans <| congrArg (fun g ↦ ρ.character g) hconj_eq
  have hsum_card :
      (∑ _ : (ConjClasses.mk s).carrier, ρ.character s) =
        Nat.card (ConjClasses.mk s).carrier * ρ.character s := by
    simp [Nat.card_eq_fintype_card]
  rw [hsum_filter, hsum_subtype, hsum_const, hsum_card] at h
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- Helper for Exercise 6-6.5-9: coprimality upgrades the class-sum integrality from part (1) to
integrality of the normalized character average `(1 / dim V) * χ(s)`. -/
lemma average_character_isIntegral_of_coprime_conjClass_card
    (hcoprime : by
      letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
      exact Nat.Coprime (Nat.card (ConjClasses.mk s).carrier) (Module.finrank ℂ V)) :
    by
      letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
      exact IsIntegral ℤ (((Module.finrank ℂ V : ℂ)⁻¹) * ρ.character s) := by
  classical
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] V
  let c : ℕ := Nat.card (ConjClasses.mk s).carrier
  let n : ℕ := Module.finrank ℂ V
  have hcoprime_cn : Nat.Coprime c n := by
    simpa [c, n] using hcoprime
  have hclass :
      IsIntegral ℤ (((c : ℂ) / n) * ρ.character s) := by
    simpa [c, n] using isIntegral_conjClass_card_div_finrank_mul_character ρ s
  have hchar : IsIntegral ℤ (ρ.character s) := char_isIntegral ρ s
  have hfinrank_ne : (n : ℂ) ≠ 0 := by
    exact_mod_cast ((Module.finrank_pos : 0 < Module.finrank ℂ V)).ne'
  have hbez : (1 : ℤ) = c * Nat.gcdA c n + n * Nat.gcdB c n := by
    simpa [hcoprime_cn.gcd_eq_one] using Nat.gcd_eq_gcd_ab c n
  have hbezC : (1 : ℂ) = (c : ℂ) * Nat.gcdA c n + (n : ℂ) * Nat.gcdB c n := by
    exact_mod_cast hbez
  have hdecomp :
      ((n : ℂ)⁻¹) * ρ.character s =
        (Nat.gcdA c n : ℂ) * (((c : ℂ) / n) * ρ.character s) +
          (Nat.gcdB c n : ℂ) * ρ.character s := by
    -- Expand the Bézout identity after multiplying by `n⁻¹ * χ(s)`.
    calc
      ((n : ℂ)⁻¹) * ρ.character s
          = (((1 : ℂ) * (n : ℂ)⁻¹) : ℂ) * ρ.character s := by simp
      _ = ((((c : ℂ) * Nat.gcdA c n + (n : ℂ) * Nat.gcdB c n) * (n : ℂ)⁻¹) : ℂ) *
            ρ.character s := by rw [hbezC]
      _ = (Nat.gcdA c n : ℂ) * (((c : ℂ) / n) * ρ.character s) +
            (Nat.gcdB c n : ℂ) * ρ.character s := by
          field_simp [hfinrank_ne]
  -- Each Bézout summand is integral, so their sum is integral as well.
  rw [hdecomp]
  exact
    IsIntegral.add
      (IsIntegral.mul isIntegral_algebraMap hclass)
      (IsIntegral.mul isIntegral_algebraMap hchar)

end IrreducibleFiniteGroup

section IrreducibleFiniteGroup

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) [ρ.IsIrreducible] (s : G)

-- Proof sketch: by part (1), coprimality of the class size and the degree implies that
-- `(Module.finrank ℂ V : ℂ)⁻¹ * ρ.character s` is an algebraic integer. Apply Exercise 6.8 to the
-- characteristic roots of `ρ s`, indexed with multiplicity by the coerced multiset
-- `(ρ s).charpoly.roots`; the nonzero-average hypothesis comes from `hχ`. This shows that the
-- normalized character average has norm `1`, so the Chapter 6 owner
-- `character_norm_eq_char_one_iff_exists_smul_id` closes the scalar-action conclusion.
/-- Exercise 6-6.5-9 (2): if the size of the conjugacy class of `s` is relatively prime to the
degree of an irreducible finite-dimensional complex representation and `χ(s) ≠ 0`, then `ρ s` is
a homothety. -/
theorem exists_smul_id_of_coprime_conjClass_card_of_character_ne_zero
    (hcoprime : by
      letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
      exact Nat.Coprime (Nat.card (ConjClasses.mk s).carrier) (Module.finrank ℂ V))
    (hχ : ρ.character s ≠ 0) :
    ∃ z : ℂ, ρ s = z • 1 := by
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] V
  have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
  let z : ℂ := 𝔼 μ : (ρ s).charpoly.roots, (μ : ℂ)
  have hfinrank_ne : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast ((Module.finrank_pos : 0 < Module.finrank ℂ V)).ne'
  have hz_eq : z = ((Module.finrank ℂ V : ℂ)⁻¹) * ρ.character s := by
    have hcard : Fintype.card ((ρ s).charpoly.roots : Type) = (ρ s).charpoly.roots.card := by
      simp
    rw [show z = 𝔼 μ : (ρ s).charpoly.roots, (μ : ℂ) by rfl, Fintype.expect_eq_sum_div_card,
      ← Multiset.sum_eq_sum_coe ((ρ s).charpoly.roots), hcard, Representation.character,
      trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _),
      ← (IsAlgClosed.splits ((ρ s).charpoly)).natDegree_eq_card_roots,
      LinearMap.charpoly_natDegree]
    simp [div_eq_mul_inv, mul_comm]
  have hz_int : IsIntegral ℤ z := by
    rw [hz_eq]
    exact average_character_isIntegral_of_coprime_conjClass_card ρ s hcoprime
  have hz_ne : z ≠ 0 := by
    rw [hz_eq]
    exact mul_ne_zero (inv_ne_zero hfinrank_ne) hχ
  have hz_norm : ‖z‖ = 1 := by
    exact
      Finset.expect_norm_eq_one_of_ne_zero_of_isIntegral_of_isOfFinOrder
        (Finset.univ : Finset (ρ s).charpoly.roots)
        (fun μ : (ρ s).charpoly.roots ↦ (μ : ℂ))
        (fun μ _ ↦ by
          refine isOfFinOrder_iff_pow_eq_one.2 ⟨orderOf s, hs.orderOf_pos, ?_⟩
          have hμ : (μ : ℂ) ∈ (ρ s).charpoly.roots := by
            simpa using (μ.2 : 0 < ((ρ s).charpoly.roots.count μ))
          simpa using ρ.charpoly_root_pow_orderOf_eq_one s hμ)
        hz_int hz_ne
  have hchar_eq : ρ.character s = (Module.finrank ℂ V : ℂ) * z := by
    calc
      ρ.character s =
          (Module.finrank ℂ V : ℂ) * (((Module.finrank ℂ V : ℂ)⁻¹) * ρ.character s) := by
            field_simp [hfinrank_ne]
      _ = (Module.finrank ℂ V : ℂ) * z := by rw [← hz_eq]
  have hnorm : ‖ρ.character s‖ = Module.finrank ℂ V := by
    rw [hchar_eq]
    simp [hz_norm]
  exact (character_norm_eq_char_one_iff_exists_smul_id ρ s hs).1 hnorm

end IrreducibleFiniteGroup

end

end Representation
