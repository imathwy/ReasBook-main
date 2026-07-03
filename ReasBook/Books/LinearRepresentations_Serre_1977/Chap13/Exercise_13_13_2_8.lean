import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Definition_1_1_4_1
import LinearRepresentations_Serre_1977.Chap02.Corollary_2_2_4_3
import LinearRepresentations_Serre_1977.Chap13.Proposition_13_13_2_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open CategoryTheory

noncomputable section

universe w

namespace Representation

section

variable {G : Type} [Group G] [Finite G]
variable {ι : Type w}
variable (π : ι → FDRep ℂ G)

attribute [local instance] Classical.propDecidable

local instance instNeZeroNatCardComplex : NeZero (Nat.card G : ℂ) := by
  exact ⟨by exact_mod_cast Nat.card_pos.ne'⟩

section PartOne

/-- Helper for Exercise 13-13.2-8: evaluating the degree-weighted irreducible character sum at a
square detects whether that square is the identity. -/
lemma weighted_degree_character_at_square_eq_ite_group_order
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (s : G) :
    let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
    let _ : Fintype ι := Fintype.ofFinite ι
    ∑ i : ι, (Module.finrank ℂ (π i) : ℂ) * (π i).character (s ^ (2 : ℕ)) =
      if s ^ (2 : ℕ) = 1 then Nat.card G else 0 := by
  classical
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype G := Fintype.ofFinite G
  by_cases hs : s ^ (2 : ℕ) = 1
  · -- At the identity, Corollary 2-2.4-3 (1) gives the sum of squared degrees.
    have hsq :=
      sum_sq_degree_eq_card_of_complete_irreducible_family
        (π := π) hπ_complete hπ_pairwise
    have hsqC : ((∑ i : ι, Module.finrank ℂ (π i) ^ 2 : ℕ) : ℂ) = (Nat.card G : ℂ) := by
      exact_mod_cast hsq
    have hsumC :
        ∑ i : ι, (Module.finrank ℂ (π i) : ℂ) * (π i).character (s ^ (2 : ℕ)) =
          (Nat.card G : ℂ) := by
      simpa [hs, Representation.char_one, pow_two, mul_comm] using hsqC
    simpa [hs] using hsumC
  · -- Away from the identity, Corollary 2-2.4-3 (2) forces the weighted character sum to vanish.
    have hzero :
        ∑ i : ι, (Module.finrank ℂ (π i) : ℂ) * (π i).character (s ^ (2 : ℕ)) = (0 : ℂ) := by
      simpa using sum_degree_mul_character_eq_zero_of_ne_one_of_complete_irreducible_family
        (π := π) hπ_complete hπ_pairwise (s ^ (2 : ℕ)) hs
    simpa [hs] using hzero

/-- Helper for Exercise 13-13.2-8: the degree-weighted Frobenius-Schur indicators count the
self-inverse elements of `G`. -/
lemma weighted_frobenius_schur_sum_eq_card_self_inverse
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
    let _ : Fintype ι := Fintype.ofFinite ι
    ∑ i : ι, (Module.finrank ℂ (π i) : ℂ) * frobeniusSchurIndicator (π i).character =
      (Nat.card { s : G // s ^ (2 : ℕ) = 1 } : ℂ) := by
  classical
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype G := Fintype.ofFinite G
  calc
    ∑ i : ι, (Module.finrank ℂ (π i) : ℂ) * frobeniusSchurIndicator (π i).character
      = ∑ i : ι,
          (Module.finrank ℂ (π i) : ℂ) *
            ((Nat.card G : ℂ)⁻¹ * ∑ s : G, (π i).character (s ^ (2 : ℕ))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [frobeniusSchurIndicator_eq_card_inv_sum_sq]
    _ = (Nat.card G : ℂ)⁻¹ *
          ∑ s : G, ∑ i : ι, (Module.finrank ℂ (π i) : ℂ) * (π i).character (s ^ (2 : ℕ)) := by
            calc
              ∑ i : ι,
                  (Module.finrank ℂ (π i) : ℂ) *
                    ((Nat.card G : ℂ)⁻¹ * ∑ s : G, (π i).character (s ^ (2 : ℕ)))
                = ∑ i : ι,
                    (Nat.card G : ℂ)⁻¹ *
                      ((Module.finrank ℂ (π i) : ℂ) * ∑ s : G, (π i).character (s ^ (2 : ℕ))) := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        ring
              _ = (Nat.card G : ℂ)⁻¹ *
                    ∑ i : ι, (Module.finrank ℂ (π i) : ℂ) * ∑ s : G, (π i).character (s ^ (2 : ℕ)) := by
                      rw [← Finset.mul_sum]
              _ = (Nat.card G : ℂ)⁻¹ *
                    ∑ i : ι, ∑ s : G, (Module.finrank ℂ (π i) : ℂ) * (π i).character (s ^ (2 : ℕ)) := by
                      refine congrArg ((Nat.card G : ℂ)⁻¹ * ·) ?_
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      rw [Finset.mul_sum]
              _ = (Nat.card G : ℂ)⁻¹ *
                    Finset.sum Finset.univ
                      (fun s : G => ∑ i : ι, (Module.finrank ℂ (π i) : ℂ) * (π i).character (s ^ (2 : ℕ))) := by
                      refine congrArg ((Nat.card G : ℂ)⁻¹ * ·) ?_
                      rw [Finset.sum_comm]
    _ = (Nat.card G : ℂ)⁻¹ *
          Finset.sum Finset.univ
            (fun s : G => if s ^ (2 : ℕ) = 1 then (Nat.card G : ℂ) else 0) := by
          refine congrArg ((Nat.card G : ℂ)⁻¹ * ·) ?_
          refine Finset.sum_congr rfl ?_
          intro s hs
          simpa using
            weighted_degree_character_at_square_eq_ite_group_order
              (π := π) hπ_pairwise hπ_complete s
    _ = (Nat.card G : ℂ)⁻¹ *
          ((Nat.card { s : G // s ^ (2 : ℕ) = 1 } : ℂ) * (Nat.card G : ℂ)) := by
          have hcount :
              Finset.sum Finset.univ
                (fun s : G => if s ^ (2 : ℕ) = 1 then (Nat.card G : ℂ) else 0) =
                (Nat.card { s : G // s ^ (2 : ℕ) = 1 } : ℂ) * (Nat.card G : ℂ) := by
            -- Counting the surviving summands turns the sum into the cardinality of the
            -- self-inverse locus times the constant value `|G|`.
            calc
              Finset.sum Finset.univ
                (fun s : G => if s ^ (2 : ℕ) = 1 then (Nat.card G : ℂ) else 0)
                = Finset.sum
                    (Finset.univ.filter (fun s : G => s ^ (2 : ℕ) = 1))
                    (fun _ => (Nat.card G : ℂ)) := by
                      simpa using
                        (Fintype.sum_ite_mem
                          (s := Finset.univ.filter (fun s : G => s ^ (2 : ℕ) = 1))
                          (f := fun _ : G => (Nat.card G : ℂ)))
              _ = ((Finset.univ.filter (fun s : G => s ^ (2 : ℕ) = 1)).card : ℂ) *
                    (Nat.card G : ℂ) := by
                      simp
              _ = (Fintype.card { s : G // s ^ (2 : ℕ) = 1 } : ℂ) *
                    (Fintype.card G : ℂ) := by
                      rw [← Fintype.card_subtype (fun s : G => s ^ (2 : ℕ) = 1),
                        Nat.card_eq_fintype_card]
              _ = (Nat.card { s : G // s ^ (2 : ℕ) = 1 } : ℂ) * (Nat.card G : ℂ) := by
                    simp [Nat.card_eq_fintype_card]
          rw [hcount]
    _ = (Nat.card { s : G // s ^ (2 : ℕ) = 1 } : ℂ) := by
          field_simp

/-- Helper for Exercise 13-13.2-8: each irreducible member contributes its degree times the sign of
its Frobenius-Schur indicator. -/
lemma weighted_indicator_value_eq_signed_degree
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι) :
    (Module.finrank ℂ (π i) : ℂ) * frobeniusSchurIndicator (π i).character =
      if IsRealizableOver ℝ (π i).ρ then
        (Module.finrank ℂ (π i) : ℂ)
      else if IsValuedInBaseField ℝ (π i).character then
        -((Module.finrank ℂ (π i) : ℂ))
      else
        0 := by
  letI : Simple (π i) := hπ_complete.isSimple i
  letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
  by_cases htype2 : IsRealizableOver ℝ (π i).ρ
  · -- Type `2` contributes `+χ(1)`.
    have hfs :
        frobeniusSchurIndicator (π i).character = 1 :=
      (isTypeTwo_iff_frobeniusSchurIndicator_eq_one (ρ := (π i).ρ)).1 htype2
    simp [htype2, hfs]
  · by_cases hreal : IsValuedInBaseField ℝ (π i).character
    · -- Type `3` contributes `-χ(1)`.
      have hfs :
          frobeniusSchurIndicator (π i).character = -1 :=
        (isTypeThree_iff_frobeniusSchurIndicator_eq_neg_one (ρ := (π i).ρ)).1
          ⟨hreal, htype2⟩
      simp [htype2, hreal, hfs]
    · -- Type `1` contributes `0`.
      have hfs :
          frobeniusSchurIndicator (π i).character = 0 :=
        (isTypeOne_iff_frobeniusSchurIndicator_eq_zero (ρ := (π i).ρ)).1 hreal
      simp [htype2, hreal, hfs]

/-- Helper for Exercise 13-13.2-8: the cast of the degree difference agrees with the full signed
sum over the whole irreducible family. -/
lemma complex_cast_typeTwo_sub_typeThree_eq_signed_sum
    [Fintype ι]
    (d : ι → ℕ) (p q : ι → Prop) :
    (((∑ i : { i // p i }, (d i : ℤ)) -
        ∑ i : { i // q i ∧ ¬ p i }, (d i : ℤ) : ℤ) : ℂ) =
      ∑ i : ι, if p i then (d i : ℂ) else if q i then -(d i : ℂ) else 0 := by
  classical
  have hp :
      (((∑ i : { i // p i }, (d i : ℤ)) : ℤ) : ℂ) =
        ∑ i : ι, if p i then (d i : ℂ) else 0 := by
    -- Rewrite the subtype sum as a filtered sum, then expand it as an indicator sum over `ι`.
    calc
      (((∑ i : { i // p i }, (d i : ℤ)) : ℤ) : ℂ)
        = Finset.sum (Finset.univ.filter p) (fun i => (d i : ℂ)) := by
            rw [← Finset.sum_subtype_eq_sum_filter]
            simp
      _ = ∑ i : ι, if p i then (d i : ℂ) else 0 := by
            simpa using
              (Fintype.sum_ite_mem (s := Finset.univ.filter p)
                (f := fun i : ι => (d i : ℂ))).symm
  have hq :
      (((∑ i : { i // q i ∧ ¬ p i }, (d i : ℤ)) : ℤ) : ℂ) =
        ∑ i : ι, if q i ∧ ¬ p i then (d i : ℂ) else 0 := by
    -- The same filtered-sum conversion handles the type `3` contribution.
    calc
      (((∑ i : { i // q i ∧ ¬ p i }, (d i : ℤ)) : ℤ) : ℂ)
        = Finset.sum (Finset.univ.filter (fun i : ι => q i ∧ ¬ p i))
            (fun i => (d i : ℂ)) := by
              rw [← Finset.sum_subtype_eq_sum_filter]
              simp
      _ = ∑ i : ι, if q i ∧ ¬ p i then (d i : ℂ) else 0 := by
            simpa using
              (Fintype.sum_ite_mem
                (s := Finset.univ.filter (fun i : ι => q i ∧ ¬ p i))
                (f := fun i : ι => (d i : ℂ))).symm
  calc
    (((∑ i : { i // p i }, (d i : ℤ)) -
        ∑ i : { i // q i ∧ ¬ p i }, (d i : ℤ) : ℤ) : ℂ)
      = (((∑ i : { i // p i }, (d i : ℤ)) : ℤ) : ℂ) -
          (((∑ i : { i // q i ∧ ¬ p i }, (d i : ℤ)) : ℤ) : ℂ) := by
            norm_num
    _ = (∑ i : ι, if p i then (d i : ℂ) else 0) -
          ∑ i : ι, if q i ∧ ¬ p i then (d i : ℂ) else 0 := by
            rw [hp, hq]
    _ = Finset.sum Finset.univ
          (fun i : ι =>
            (if p i then (d i : ℂ) else 0) - (if q i ∧ ¬ p i then (d i : ℂ) else 0)) := by
            rw [← Finset.sum_sub_distrib]
    _ = ∑ i : ι, if p i then (d i : ℂ) else if q i then -(d i : ℂ) else 0 := by
          -- The second branch already contains `¬ p`, so only the three LinearRepresentations_Serre_1977 types remain.
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hp' : p i
          · simp [hp']
          · by_cases hq' : q i
            · simp [hp', hq']
            · simp [hp', hq']

-- Source/core/bridge triage:
-- * source-facing: the exercise compares the degree sums of the type `2` and type `3`
--   irreducible members of a complete family with the number of self-inverse elements in `G`.
-- * core/canonical: `IsCompleteIrreducibleFamily π`, `PairwiseNonisomorphic π`,
--   `frobeniusSchurIndicator`, `IsRealizableOver ℝ`, and `IsValuedInBaseField ℝ`.
-- * bridge/view: Proposition `13-13.2-4` turns the source-level type `2`/`3` predicates into the
--   indicator values `1` and `-1`; Corollary `2-2.4-3` supplies the regular-character expansion.
--
-- Primitive data are only the complete pairwise nonisomorphic family `π`; the finite indexing used
-- to perform the sums is operational and derived from the canonical owner
-- `IsCompleteIrreducibleFamily.finite_index`.
-- Proof sketch: use Proposition `13-13.2-4` to rewrite each Frobenius-Schur indicator as `1`,
-- `0`, or `-1` according to whether the irreducible representation is of type `2`, `1`, or `3`.
-- Summing these values with multiplicity `χ(1)` yields the pairing of the trivial character with
-- `Ψ²` of the regular character. Since the regular character vanishes away from `1`, this pairing
-- counts exactly the elements `s ∈ G` such that `s² = 1`.
/-- Exercise 13-13.2-8 (1): for a complete family of pairwise nonisomorphic irreducible complex
representations of `G`, the sum of the degrees of the type `2` members minus the sum of the
degrees of the type `3` members equals the number of elements `s ∈ G` with `s² = 1`. -/
theorem
    sum_degree_typeTwo_sub_sum_degree_typeThree_eq_card_selfInverse_of_complete_irreducible_family
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    :
    let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
    let _ : Fintype ι := Fintype.ofFinite ι
    (∑ i : { i // IsRealizableOver ℝ (π i).ρ }, (Module.finrank ℂ (π i) : ℤ)) -
      ∑ i : { i // IsValuedInBaseField ℝ (π i).character ∧ ¬ IsRealizableOver ℝ (π i).ρ },
        (Module.finrank ℂ (π i) : ℤ) =
      Nat.card { s : G // s ^ (2 : ℕ) = 1 } :=
  by
    classical
    letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
    letI : Fintype ι := Fintype.ofFinite ι
    -- Rewrite the source integer expression as the full weighted indicator sum.
    have hcast :
        (((∑ i : { i // IsRealizableOver ℝ (π i).ρ }, (Module.finrank ℂ (π i) : ℤ)) -
            ∑ i :
              { i // IsValuedInBaseField ℝ (π i).character ∧ ¬ IsRealizableOver ℝ (π i).ρ },
              (Module.finrank ℂ (π i) : ℤ) : ℤ) : ℂ) =
          ∑ i : ι, (Module.finrank ℂ (π i) : ℂ) * frobeniusSchurIndicator (π i).character := by
      calc
        (((∑ i : { i // IsRealizableOver ℝ (π i).ρ }, (Module.finrank ℂ (π i) : ℤ)) -
            ∑ i :
              { i // IsValuedInBaseField ℝ (π i).character ∧ ¬ IsRealizableOver ℝ (π i).ρ },
              (Module.finrank ℂ (π i) : ℤ) : ℤ) : ℂ)
          = ∑ i : ι,
              if IsRealizableOver ℝ (π i).ρ then
                (Module.finrank ℂ (π i) : ℂ)
              else if IsValuedInBaseField ℝ (π i).character then
                -((Module.finrank ℂ (π i) : ℂ))
              else
                0 := by
                  simpa using
                    complex_cast_typeTwo_sub_typeThree_eq_signed_sum
                      (d := fun i ↦ Module.finrank ℂ (π i))
                      (p := fun i ↦ IsRealizableOver ℝ (π i).ρ)
                      (q := fun i ↦ IsValuedInBaseField ℝ (π i).character)
        _ = ∑ i : ι, (Module.finrank ℂ (π i) : ℂ) * frobeniusSchurIndicator (π i).character := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact (weighted_indicator_value_eq_signed_degree
                (π := π) hπ_complete i).symm
    -- The weighted Frobenius-Schur identity is exactly the counting statement from the source.
    have hweighted :=
      weighted_frobenius_schur_sum_eq_card_self_inverse
        (π := π) hπ_pairwise hπ_complete
    exact_mod_cast (hcast.trans hweighted)

end PartOne

section PartTwo

omit [Finite G] in
/-- Helper for Exercise 13-13.2-8: completeness supplies the index of the trivial representation
inside the chosen irreducible family. -/
lemma trivial_constituent_index_exists
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    ∃ i : ι, Nonempty (FDRep.of (Representation.trivial ℂ G ℂ) ≅ π i) := by
  haveI : (Representation.trivial ℂ G ℂ).IsIrreducible := by
    simpa using
      isIrreducible_of_finrank_eq_one (ρ := Representation.trivial ℂ G ℂ)
        (by simp : Module.finrank ℂ ℂ = 1)
  -- Completeness places the trivial representation among the irreducible family members.
  exact
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := π) hπ_complete (Representation.trivial ℂ G ℂ) inferInstance

/-- Helper for Exercise 13-13.2-8: an even-order finite group has at least two elements whose
square is `1`. -/
lemma card_self_inverse_ge_two_of_even_order
    [Finite G]
    (heven : Even (Nat.card G)) :
    2 ≤ Nat.card { s : G // s ^ (2 : ℕ) = 1 } := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := G) 2 heven.two_dvd
  have hg_sq : g ^ (2 : ℕ) = 1 := by
    rw [← hg_order]
    exact pow_orderOf_eq_one g
  have hg_ne_one : g ≠ 1 := by
    intro hg
    simp [hg] at hg_order
  let s1 : { s : G // s ^ (2 : ℕ) = 1 } := ⟨1, by simp⟩
  let sg : { s : G // s ^ (2 : ℕ) = 1 } := ⟨g, hg_sq⟩
  have hlt :
      1 < Fintype.card { s : G // s ^ (2 : ℕ) = 1 } := by
    rw [Fintype.one_lt_card_iff]
    -- The identity and the Cauchy involution are distinct points of the self-inverse locus.
    refine ⟨s1, sg, ?_⟩
    intro hsg
    exact hg_ne_one (by simpa using (congrArg Subtype.val hsg).symm)
  rw [Nat.card_eq_fintype_card]
  omega

/-- Helper for Exercise 13-13.2-8: the trivial constituent contributes one degree and is of type
`2`. -/
lemma trivial_constituent_is_type_two_and_degree_one
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {i : ι} (hi : Nonempty (FDRep.of (Representation.trivial ℂ G ℂ) ≅ π i)) :
    IsRealizableOver ℝ (π i).ρ ∧ Module.finrank ℂ (π i) = 1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Simple (π i) := hπ_complete.isSimple i
  letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
  rcases hi with ⟨e⟩
  have hchar :
      (π i).character = (Representation.trivial ℂ G ℂ).character := by
    -- Transport the trivial character across the chosen isomorphism.
    simpa using
      (Representation.char_iso
        (Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e))).symm
  have hdeg : Module.finrank ℂ (π i) = 1 := by
    -- Evaluating the character equality at `1` identifies the degree.
    have hvalue := congrArg (fun χ : G → ℂ ↦ χ 1) hchar
    simpa [Representation.char_one, Representation.character, Representation.trivial] using hvalue
  have htriv_fs :
      frobeniusSchurIndicator (Representation.trivial ℂ G ℂ).character = 1 := by
    -- The trivial character is constant `1`, so its indicator is the average of `1`.
    have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
      exact_mod_cast Nat.card_pos.ne'
    rw [frobeniusSchurIndicator_eq_card_inv_sum_sq]
    field_simp [hcard_ne]
    simp [Representation.character, Representation.trivial, Nat.card_eq_fintype_card]
  have hfs : frobeniusSchurIndicator (π i).character = 1 := by
    rw [hchar]
    exact htriv_fs
  exact ⟨(isTypeTwo_iff_frobeniusSchurIndicator_eq_one (ρ := (π i).ρ)).2 hfs, hdeg⟩

-- Proof sketch: if `Nat.card G` is even, Cauchy's theorem gives a nontrivial involution, so the
-- right-hand side of part (1) is at least `2` because it counts both `1` and that involution. The
-- trivial representation is always of type `2`, contributing `1` to the left-hand side. Since the
-- type `3` summands contribute negatively, one more type `2` irreducible is needed.
/-- Exercise 13-13.2-8 (2): if the finite group `G` has even order, then a complete family of
pairwise nonisomorphic irreducible complex representations of `G` contains at least two members of
LinearRepresentations_Serre_1977 type `2`. -/
theorem card_typeTwo_irreducibles_ge_two_of_even_order_of_complete_irreducible_family
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (heven : Even (Nat.card G)) :
    2 ≤ Nat.card { i // IsRealizableOver ℝ (π i).ρ } :=
  by
    classical
    letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
    letI : Fintype ι := Fintype.ofFinite ι
    -- Route correction: package the Cauchy-theorem involution count as a reusable helper before
    -- feeding it into the degree-sum identity from part (1).
    have hselfinv_two :
        2 ≤ Nat.card { s : G // s ^ (2 : ℕ) = 1 } :=
      card_self_inverse_ge_two_of_even_order (G := G) heven
    have hmain :=
      sum_degree_typeTwo_sub_sum_degree_typeThree_eq_card_selfInverse_of_complete_irreducible_family
        (π := π) hπ_pairwise hπ_complete
    have htypeThree_nonneg :
        0 ≤
          ∑ i :
            { i // IsValuedInBaseField ℝ (π i).character ∧ ¬ IsRealizableOver ℝ (π i).ρ },
            (Module.finrank ℂ (π i) : ℤ) := by
      -- Every degree term is a nonnegative integer.
      exact Finset.sum_nonneg fun i hi => Int.natCast_nonneg _
    have htypeTwo_sum_ge_two :
        (2 : ℤ) ≤
          ∑ i : { i // IsRealizableOver ℝ (π i).ρ }, (Module.finrank ℂ (π i) : ℤ) := by
      have hselfinv_two_int : (2 : ℤ) ≤ Nat.card { s : G // s ^ (2 : ℕ) = 1 } := by
        exact_mod_cast hselfinv_two
      linarith
    obtain ⟨i0, hi0⟩ := trivial_constituent_index_exists (π := π) hπ_complete
    obtain ⟨hi0_typeTwo, hi0_deg⟩ :=
      trivial_constituent_is_type_two_and_degree_one (π := π) hπ_complete hi0
    by_contra hcard
    have hcard_le_one : Nat.card { i // IsRealizableOver ℝ (π i).ρ } ≤ 1 := by
      omega
    rw [Nat.card_eq_fintype_card] at hcard_le_one
    have hsub :
        Subsingleton { i // IsRealizableOver ℝ (π i).ρ } :=
      (Fintype.card_le_one_iff_subsingleton).1 hcard_le_one
    let i0' : { i // IsRealizableOver ℝ (π i).ρ } := ⟨i0, hi0_typeTwo⟩
    have htypeTwo_sum_eq_one :
        ∑ i : { i // IsRealizableOver ℝ (π i).ρ }, (Module.finrank ℂ (π i) : ℤ) = 1 := by
      have hcard_one : Fintype.card { i // IsRealizableOver ℝ (π i).ρ } = 1 :=
        Fintype.card_eq_one_iff.mpr ⟨i0', fun j ↦ hsub.elim j i0'⟩
      calc
        ∑ i : { i // IsRealizableOver ℝ (π i).ρ }, (Module.finrank ℂ (π i) : ℤ)
          = ∑ i : { i // IsRealizableOver ℝ (π i).ρ }, (1 : ℤ) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hj_eq : j = i0' := hsub.elim j i0'
              cases hj_eq
              simpa using hi0_deg
        _ = 1 := by
              simp [hcard_one]
    linarith

end PartTwo

end

end Representation
