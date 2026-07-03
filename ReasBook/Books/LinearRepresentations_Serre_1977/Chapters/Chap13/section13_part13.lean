import Mathlib
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_13_13_2_8 (from Chap13) -/
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

/-! ### Exercise_13_13_2_9 (from Chap13) -/
noncomputable section

open CategoryTheory
open Representation
open scoped BigOperators MonoidAlgebra

section

variable {G : Type} [Group G]

-- Source/core/bridge triage:
-- * source-facing: the congruence `|G| ≡ # ConjClasses G (mod 16)` for odd-order finite groups.
-- * core/canonical: a complete irreducible family `π`, the Chapter 2 identities
--   `sum_sq_degree_eq_card_of_complete_irreducible_family` and
--   `card_eq_card_conjClasses_of_complete_irreducible_family`, and the Chapter 6 divisibility
--   theorem `finrank_dvd_card`.
-- * bridge/view: the remaining missing piece is a stable in-file dual-pairing bridge for the
--   public complete-family API in this checkout.

/-- Helper for Exercise 13-13.2-9: an odd degree contributes the same as two indices modulo
`16`. -/
lemma paired_square_degree_modEq_two_of_odd {d : ℕ} (hd : Odd d) :
    2 * d ^ 2 ≡ 2 [MOD 16] := by
  -- Write `d = 2k + 1`; then `2 * (d ^ 2 - 1) = 8 * k * (k + 1)`, and one of `k`, `k + 1`
  -- is even.
  rcases hd with ⟨k, rfl⟩
  have hpos : 0 < 2 * (2 * k + 1) ^ 2 := by
    positivity
  have hle : 2 ≤ 2 * (2 * k + 1) ^ 2 := by
    omega
  exact ((Nat.modEq_iff_dvd' hle).2 <| by
    rcases Nat.even_mul_succ_self k with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hmz : (k : ℤ) * ((k : ℤ) + 1) = m + m := by
      exact_mod_cast hm
    have hz : (2 : ℤ) * (2 * k + 1) ^ 2 - 2 = 16 * m := by
      nlinarith [hmz]
    exact_mod_cast hz).symm

/-- Helper for Exercise 13-13.2-9: the inverse character of a finite-dimensional representation
is a class function. -/
lemma inverse_character_mem_classFunctionSubmodule_local
    {H : Type v} [Group H] {V : Type w} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ H V) :
    (fun s : H ↦ ρ.character s⁻¹) ∈ classFunctionSubmodule ℂ H := by
  -- Conjugate elements have conjugate inverses, so the inverse character stays constant on
  -- conjugacy classes.
  rw [mem_classFunctionSubmodule_iff]
  refine ⟨?_⟩
  intro a b hab
  rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hab) with ⟨g, hg⟩
  calc
    ρ.character a⁻¹ = ρ.character (g * a⁻¹ * g⁻¹) := by
      exact (ρ.char_conj a⁻¹ g).symm
    _ = ρ.character b⁻¹ := by
      have hinv : g * a⁻¹ * g⁻¹ = b⁻¹ := by
        rw [← hg]
        simp [mul_assoc]
      simp [hinv]

/-- Helper for Exercise 13-13.2-9: the self-pairing of an irreducible character equals the order
of the group. -/
lemma character_self_pairing_sum_eq_card_local
    {H : Type v} [Group H] [Finite H] [Fintype H]
    {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) [ρ.IsIrreducible] [Invertible (Nat.card H : ℂ)] :
    ∑ s : H, ρ.character s⁻¹ * ρ.character s = Nat.card H := by
  -- Orthogonality identifies the normalized self-pairing with the rank of the intertwiner space.
  have hpair := Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := ρ) (σ := ρ)
  have hpair' : (Nat.card H : ℂ)⁻¹ * ∑ s : H, ρ.character s⁻¹ * ρ.character s = 1 := by
    simpa [mul_comm, IsIrreducible.finrank_intertwiningMap_self ρ] using hpair
  have hcard : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  -- Clear the normalized factor to recover the unscaled sum.
  field_simp [hcard] at hpair'
  simpa using hpair'

/-- Helper for Exercise 13-13.2-9: if `(m : ℂ) / n` is integral over `ℤ`, then `n` divides `m`.
-/
lemma nat_dvd_of_isIntegral_natCast_div_local {m n : ℕ} (hn : n ≠ 0)
    (h : IsIntegral ℤ ((m : ℂ) / n)) :
    n ∣ m := by
  let q : ℚ := m / n
  have hq : IsIntegral ℤ q := by
    -- Descend integrality from `ℂ` to the rational scalar itself.
    have hqC : IsIntegral ℤ (q : ℂ) := by
      simpa [q] using h
    exact IsIntegral.ratCast_iff.mp hqC
  obtain ⟨z, hz : q = z⟩ := hq.exists_int_iff_exists_rat |>.mp ⟨q, rfl⟩
  have hden : q.den = 1 := by
    rw [hz]
    simp
  exact (Rat.den_div_natCast_eq_one_iff m n hn).mp <| by
    simpa [q] using hden

/-- Helper for Exercise 13-13.2-9: the odd-degree divisibility bridge needed for the nontrivial
character pairing argument. -/
lemma Representation.finrank_dvd_card_local
    {H : Type v} [Group H] [Finite H]
    {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) [ρ.IsIrreducible] :
    Module.finrank ℂ V ∣ Nat.card H := by
  classical
  letI : Module ℂ[H] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[H] V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial ℂ[H] V
  have hfinrank_ne_zero : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt Module.finrank_pos
  letI : NeZero (Module.finrank ℂ V : ℂ) := ⟨hfinrank_ne_zero⟩
  have hcard_ne_zero : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hcard_ne_zero
  letI : Fintype H := Fintype.ofFinite H
  let f : classFunctionSubmodule ℂ H :=
    ⟨fun s ↦ ρ.character s⁻¹, inverse_character_mem_classFunctionSubmodule_local (ρ := ρ)⟩
  let u : Subalgebra.center ℂ (ℂ[H]) :=
    ⟨Finsupp.equivFunOnFinite.symm (f : H → ℂ), mem_center_of_classFunction ℂ f⟩
  have hu : ∀ s : H, ((u : ℂ[H]) s) = ρ.character s⁻¹ := by
    -- The coefficients of the packaged central element are exactly the inverse character values.
    intro s
    simp [u, f]
  have hcoeff : ∀ s : H, IsIntegral ℤ ((u : ℂ[H]) s) := by
    -- Finite-order character values are algebraic integers.
    intro s
    rw [hu s]
    exact char_isIntegral_of_isOfFinOrder ρ (isOfFinOrder_of_finite s⁻¹)
  have hsum : ∑ s : H, ρ.character s⁻¹ * ρ.character s = Nat.card H := by
    exact character_self_pairing_sum_eq_card_local (ρ := ρ)
  have hint : IsIntegral ℤ ((Nat.card H : ℂ) / Module.finrank ℂ V) := by
    have hint_raw :
        IsIntegral ℤ
          ((Module.finrank ℂ V : ℂ)⁻¹ * ∑ s : H, (u : ℂ[H]) s * ρ.character s) := by
      -- The central character sends the integral central element `u` to an algebraic integer.
      by_cases hfinrank : (Module.finrank ℂ V : ℂ) = 0
      · simpa [hfinrank] using (isIntegral_zero : IsIntegral ℤ (0 : ℂ))
      · have hu_center : IsIntegral ℤ u :=
          MonoidAlgebra.isIntegral_center_of_coeff_isIntegral u hcoeff
        simpa [centralCharacter_apply_eq_sum_character ρ u hfinrank] using
          map_isIntegral_int (ω[ρ]) hu_center
    have hsum' :
        (Module.finrank ℂ V : ℂ)⁻¹ * ∑ s : H, (u : ℂ[H]) s * ρ.character s =
          (Nat.card H : ℂ) / Module.finrank ℂ V := by
      -- Rewrite the normalized sum using the explicit coefficients of `u`.
      calc
        (Module.finrank ℂ V : ℂ)⁻¹ * ∑ s : H, (u : ℂ[H]) s * ρ.character s
            = (Module.finrank ℂ V : ℂ)⁻¹ * ∑ s : H, ρ.character s⁻¹ * ρ.character s := by
                simp [hu]
        _ = (Module.finrank ℂ V : ℂ)⁻¹ * Nat.card H := by
              rw [hsum]
        _ = (Nat.card H : ℂ) / Module.finrank ℂ V := by
              simp [div_eq_mul_inv, mul_comm]
    rw [hsum'] at hint_raw
    exact hint_raw
  exact nat_dvd_of_isIntegral_natCast_div_local
    (n := Module.finrank ℂ V) (m := Nat.card H) (Nat.ne_of_gt Module.finrank_pos) hint

/-- Helper for Exercise 13-13.2-9: choose a complete pairwise nonisomorphic irreducible complex
family without using the broken Chapter 6.6.3.3 export. -/
lemma isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card_local
    [Finite G] [NeZero (Nat.card G : ℂ)] {ι : Type} [Fintype ι]
    (π : ι → FDRep ℂ G)
    (hπ_simple : ∀ i, Simple (π i))
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_sum : ∑ i : ι, Module.finrank ℂ (π i) ^ 2 = Nat.card G) :
    IsCompleteIrreducibleFamily π := by
  classical
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Subrepresentation (leftRegular ℂ G)),
        iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
          (⨆ i, (σ i).toSubmodule) = ⊤ ∧
          ∀ i, (σ i).toRepresentation.IsIrreducible := by
    exact exists_isInternal_irreducible_subrepresentations (leftRegular ℂ G)
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let S : ι → Finset κ :=
    fun i ↦ Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π i).ρ)
  let covered : Finset κ := Finset.univ.biUnion S
  let dimσ : κ → Nat := fun j ↦ Module.finrank ℂ (σ j).toSubmodule
  have hS_disjoint : Pairwise fun i i' ↦ Disjoint (S i) (S i') := by
    intro i i' hii
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨e'⟩
    exact hπ_pairwise hii <| ⟨(e.symm.trans e').toFDRepIso⟩
  have hmult (i : ι) :
      Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (π i).ρ) } =
        Module.finrank ℂ (π i) := by
    have hπ_irreducible : Representation.IsIrreducible (π i).ρ := by
      letI : Simple (π i) := hπ_simple i
      exact FDRep.isIrreducible_of_simple (π i)
    letI : Representation.IsIrreducible (π i).ρ := hπ_irreducible
    simpa using
      leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr (π i).ρ
        inferInstance
  have hS_card (i : ι) : (S i).card = Module.finrank ℂ (π i) := by
    have hcard :
        Fintype.card { j // Nonempty ((σ j).toRepresentation.Equiv (π i).ρ) } = (S i).card := by
      rw [show S i =
            Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π i).ρ) by rfl]
      rw [Fintype.card_of_subtype
        (Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π i).ρ))]
      intro j
      simp
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using hmult i
  have hS_sum (i : ι) : Finset.sum (S i) dimσ = Module.finrank ℂ (π i) ^ 2 := by
    calc
      Finset.sum (S i) dimσ = Finset.sum (S i) (fun _j ↦ Module.finrank ℂ (π i)) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        exact e.toLinearEquiv.finrank_eq
      _ = (S i).card * Module.finrank ℂ (π i) := by
            simp
      _ = Module.finrank ℂ (π i) ^ 2 := by
            rw [hS_card, pow_two]
  have hcovered_raw : Finset.sum covered dimσ = ∑ i : ι, Finset.sum (S i) dimσ := by
    rw [show covered = Finset.univ.biUnion S from rfl]
    exact Finset.sum_biUnion fun i _ i' _ hii ↦ hS_disjoint hii
  have hcovered_sum : Finset.sum covered dimσ = ∑ i : ι, Module.finrank ℂ (π i) ^ 2 := by
    calc
      Finset.sum covered dimσ = ∑ i : ι, Finset.sum (S i) dimσ := hcovered_raw
      _ = ∑ i : ι, Module.finrank ℂ (π i) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ ↦ hS_sum i
  have hcovered_eq_card : Finset.sum covered dimσ = Nat.card G := by
    calc
      Finset.sum covered dimσ = ∑ i : ι, Module.finrank ℂ (π i) ^ 2 := hcovered_sum
      _ = Nat.card G := hπ_sum
  have htotal_eq_card : ∑ j : κ, dimσ j = Nat.card G := by
    letI := DirectSum.IsInternal.chooseDecomposition (fun j ↦ (σ j).toSubmodule) hinternal
    let e := (DirectSum.decomposeLinearEquiv (fun j ↦ (σ j).toSubmodule)).symm
    calc
      ∑ j : κ, dimσ j = Module.finrank ℂ (G →₀ ℂ) := by
        symm
        calc
          Module.finrank ℂ (G →₀ ℂ) =
              Module.finrank ℂ (DirectSum κ fun j ↦ (σ j).toSubmodule) := by
                exact e.finrank_eq.symm
          _ = ∑ j : κ, dimσ j := by
                simp [dimσ, Module.finrank_directSum]
      _ = Nat.card G := by
            let _ : Fintype G := Fintype.ofFinite G
            rw [Nat.card_eq_fintype_card]
            exact Module.finrank_finsupp_self ℂ
  refine
    { isSimple := hπ_simple
      exists_iso := ?_ }
  intro τ _
  letI : Nontrivial τ := by
    by_contra hτ
    letI : Subsingleton τ := not_nontrivial_iff_subsingleton.mp hτ
    have hzero : (𝟙 τ : τ ⟶ τ) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    exact CategoryTheory.id_nonzero τ hzero
  let τρ := τ.ρ
  have hτρ_irreducible : Representation.IsIrreducible τρ := by
    exact FDRep.isIrreducible_of_simple τ
  letI : Representation.IsIrreducible τρ := hτρ_irreducible
  have hτ_pos : 0 < Module.finrank ℂ τ := Module.finrank_pos
  have hτ_mult :
      Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv τρ) } = Module.finrank ℂ τ := by
    simpa [τρ] using
      leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr τρ inferInstance
  have hτ_count_pos : 0 < Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv τρ) } := by
    rw [hτ_mult]
    exact hτ_pos
  obtain ⟨⟨j, hjτ⟩⟩ := (Nat.card_pos_iff.mp hτ_count_pos).1
  have hj_mem : j ∈ covered := by
    by_contra hj_not_mem
    have hτ_term : dimσ j = Module.finrank ℂ τ := by
      rcases hjτ with ⟨e⟩
      exact e.toLinearEquiv.finrank_eq
    have hcomp_pos : 0 < Finset.sum (Finset.univ \ covered) dimσ := by
      have hj_mem_compl : j ∈ Finset.univ \ covered := by
        simp [hj_not_mem]
      have hsingle : dimσ j ≤ Finset.sum (Finset.univ \ covered) dimσ := by
        simpa using
          (Finset.single_le_sum (fun x hx ↦ Nat.zero_le (dimσ x)) hj_mem_compl :
            dimσ j ≤ Finset.sum (Finset.univ \ covered) dimσ)
      exact lt_of_lt_of_le (by simpa [hτ_term] using hτ_pos) hsingle
    have hlt : Finset.sum covered dimσ < ∑ j : κ, dimσ j := by
      rw [← Finset.sum_add_sum_compl covered dimσ]
      exact Nat.lt_add_of_pos_right hcomp_pos
    have hcontra : Nat.card G < Nat.card G := by
      calc
        Nat.card G = Finset.sum covered dimσ := hcovered_eq_card.symm
        _ < ∑ j : κ, dimσ j := hlt
        _ = Nat.card G := htotal_eq_card
    exact Nat.lt_irrefl _ hcontra
  rcases Finset.mem_biUnion.mp hj_mem with ⟨i, _, hij⟩
  rcases (Finset.mem_filter.mp hij).2 with ⟨e⟩
  rcases hjτ with ⟨eτ⟩
  exact ⟨i, ⟨(eτ.symm.trans e).toFDRepIso⟩⟩

lemma exists_complete_pairwise_nonisomorphic_irreducible_family
    [Finite G] [NeZero (Nat.card G : ℂ)] :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep ℂ G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := leftRegular ℂ G)
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let r : Setoid κ :=
    { r := fun i j ↦ Nonempty ((σ i).toRepresentation.Equiv (σ j).toRepresentation)
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {i j l} hij hjl ↦ by
            rcases hij with ⟨eij⟩
            rcases hjl with ⟨ejl⟩
            exact ⟨eij.trans ejl⟩⟩ }
  let ι : Type := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : ι)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → FDRep ℂ G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_simple (q : ι) : Simple (π q) := by
    letI : Representation.IsIrreducible (π q).ρ := by
      simpa [π] using hσ_irr (Quotient.out q)
    exact FDRep.simple_of_isIrreducible (π q)
  have hπ_sum : ∑ q : ι, Module.finrank ℂ (π q) ^ 2 = Nat.card G := by
    let S : ι → Finset κ :=
      fun q ↦ Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ)
    let dimσ : κ → Nat := fun j ↦ Module.finrank ℂ (σ j).toSubmodule
    have hS_disjoint : Pairwise fun q q' ↦ Disjoint (S q) (S q') := by
      intro q q' hqq'
      refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
      rcases (Finset.mem_filter.mp hj).2 with ⟨eqj⟩
      rcases (Finset.mem_filter.mp hj').2 with ⟨eqj'⟩
      exact hπ_pairwise hqq' <| ⟨(eqj.symm.trans eqj').toFDRepIso⟩
    have hS_card (q : ι) : (S q).card = Module.finrank ℂ (π q) := by
      have hmult :
          Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) } =
            Module.finrank ℂ (π q) := by
        letI : Representation.IsIrreducible (π q).ρ := by
          exact FDRep.isIrreducible_of_simple (π q)
        simpa using
          leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr (π q).ρ
            inferInstance
      have hcard :
          Fintype.card { j // Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) } = (S q).card := by
        rw [show S q = Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) by
          rfl]
        rw [Fintype.card_of_subtype
          (Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ))]
        intro j
        simp
      exact hcard.symm.trans <| by
        simpa [Nat.card_eq_fintype_card] using hmult
    have hS_sum (q : ι) : Finset.sum (S q) dimσ = Module.finrank ℂ (π q) ^ 2 := by
      calc
        Finset.sum (S q) dimσ = Finset.sum (S q) (fun _j ↦ Module.finrank ℂ (π q)) := by
          refine Finset.sum_congr rfl fun j hj ↦ ?_
          rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
          exact e.toLinearEquiv.finrank_eq
        _ = (S q).card * Module.finrank ℂ (π q) := by
              simp
        _ = Module.finrank ℂ (π q) ^ 2 := by
              rw [hS_card, pow_two]
    have hcover : Finset.univ.biUnion S = (Finset.univ : Finset κ) := by
      apply Finset.ext
      intro j
      constructor
      · intro _
        simp
      · intro hj
        have hj_mem : j ∈ S (⟦j⟧ : ι) := by
          refine Finset.mem_filter.mpr ?_
          constructor
          · simp
          · rcases Quotient.exact (Quotient.out_eq (⟦j⟧ : ι)) with ⟨e⟩
            exact ⟨e.symm⟩
        exact Finset.mem_biUnion.mpr ⟨(⟦j⟧ : ι), Finset.mem_univ _, hj_mem⟩
    have htotal_eq_card : Finset.sum (Finset.univ : Finset κ) dimσ = Nat.card G := by
      letI := DirectSum.IsInternal.chooseDecomposition (fun j ↦ (σ j).toSubmodule) hinternal
      letI : ∀ j : κ, Module.Free ℂ (σ j).toSubmodule :=
        fun j ↦ Module.Free.of_divisionRing ℂ (σ j).toSubmodule
      let e := (DirectSum.decomposeLinearEquiv (fun j ↦ (σ j).toSubmodule)).symm
      calc
        Finset.sum (Finset.univ : Finset κ) dimσ = Module.finrank ℂ (G →₀ ℂ) := by
          symm
          calc
            Module.finrank ℂ (G →₀ ℂ) =
                Module.finrank ℂ (DirectSum κ fun j ↦ (σ j).toSubmodule) := by
                  exact e.finrank_eq.symm
            _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
                  dsimp [dimσ]
                  exact Module.finrank_directSum (R := ℂ) (M := fun j ↦ (σ j).toSubmodule)
        _ = Nat.card G := by
              rw [Nat.card_eq_fintype_card]
              exact Module.finrank_finsupp_self ℂ
    calc
      ∑ q : ι, Module.finrank ℂ (π q) ^ 2 = ∑ q : ι, Finset.sum (S q) dimσ := by
        refine Finset.sum_congr rfl fun q _ ↦ (hS_sum q).symm
      _ = Finset.sum (Finset.univ.biUnion S) dimσ := by
            symm
            exact Finset.sum_biUnion fun q _ q' _ hqq' ↦ hS_disjoint hqq'
      _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
            rw [hcover]
      _ = Nat.card G := htotal_eq_card
  have hπ_complete :
      IsCompleteIrreducibleFamily π := by
    exact
      isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card_local
        π hπ_simple hπ_pairwise hπ_sum
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Exercise 13-13.2-9: a complete pairwise nonisomorphic irreducible complex family
has as many indices as conjugacy classes. -/
lemma Representation.card_eq_card_conjClasses_of_complete_irreducible_family_local
    [Finite G] [NeZero (Nat.card G : ℂ)] {ι : Type*} (π : ι → FDRep ℂ G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Nat.card ι = Nat.card (ConjClasses G) := by
  -- Route correction: the old basis-level bridge depended on a missing Chapter 2 export.
  -- The current checkout already provides the direct counting theorem, so use it as the adapter.
  simpa [PairwiseNonisomorphic] using
    (Representation.card_eq_card_conjClasses_of_complete_irreducible_family
      (π := π) hπ_complete.isSimple hπ_pairwise
      (fun τ hτ ↦ hπ_complete.exists_iso τ hτ))

/-- Helper for Exercise 13-13.2-9: a complete irreducible complex family contains the trivial
constituent. -/
lemma trivial_index_exists
    {ι : Type} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    ∃ i, Nonempty (FDRep.of (Representation.trivial ℂ G ℂ) ≅ FDRep.of (π i).ρ) := by
  -- The trivial representation is irreducible because it has degree `1`.
  haveI : (Representation.trivial ℂ G ℂ).IsIrreducible := by
    simpa using
      isIrreducible_of_finrank_eq_one (ρ := Representation.trivial ℂ G ℂ)
        (by simp : Module.finrank ℂ ℂ = 1)
  -- Completeness now produces the desired index.
  exact
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := fun i ↦ FDRep.of (π i).ρ) hπ_complete (Representation.trivial ℂ G ℂ) inferInstance

/-- Helper for Exercise 13-13.2-9: the distinguished trivial constituent in a complete family has
the trivial character. -/
lemma character_eq_trivial_of_trivial_index
    {ι : Type} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    {i0 : ι}
    (hi0 : Nonempty (FDRep.of (Representation.trivial ℂ G ℂ) ≅ FDRep.of (π i0).ρ)) :
    (π i0).ρ.character = (Representation.trivial ℂ G ℂ).character := by
  -- Transport the trivial constituent along the chosen owner-level isomorphism.
  rcases hi0 with ⟨e0⟩
  simpa using
    (Representation.char_iso
      (Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e0))).symm

/-- Helper for Exercise 13-13.2-9: the distinguished trivial constituent in a complete family has
degree `1`. -/
lemma finrank_eq_one_of_trivial_index
    {ι : Type} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    {i0 : ι}
    (hi0 : Nonempty (FDRep.of (Representation.trivial ℂ G ℂ) ≅ FDRep.of (π i0).ρ)) :
    Module.finrank ℂ (π i0) = 1 := by
  -- Compare the transported trivial character at the identity element.
  have hchar0 : (π i0).ρ.character = (Representation.trivial ℂ G ℂ).character :=
    character_eq_trivial_of_trivial_index π hi0
  have hvalue := congrArg (fun χ : G → ℂ ↦ χ 1) hchar0
  simpa [Representation.char_one, Representation.character, Representation.trivial] using hvalue

/-- Helper for Exercise 13-13.2-9: an irreducible complex representation of an odd-order finite
group has odd degree. -/
lemma Representation.finrank_odd_of_irreducible_of_odd_order
    [Finite G] {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hodd : Odd (Nat.card G)) (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Odd (Module.finrank ℂ V) := by
  -- The Chapter 8 divisibility bridge shows that the degree divides `|G|`, so oddness descends.
  exact hodd.of_dvd_nat (Representation.finrank_dvd_card_local (ρ := ρ))

/-- Helper for Exercise 13-13.2-9: every member of a complete irreducible family over an odd-order
group has odd degree. -/
lemma finrank_odd_of_complete_family_member
    [Finite G] (hodd : Odd (Nat.card G))
    {ι : Type} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (i : ι) :
    Odd (Module.finrank ℂ (π i)) := by
  -- Completeness supplies irreducibility of the chosen family member, so the odd-degree bridge
  -- applies directly.
  letI : (π i).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  exact Representation.finrank_odd_of_irreducible_of_odd_order hodd (π i).ρ

/-- Helper for Exercise 13-13.2-9: equal characters force an equivalence between irreducible
finite-dimensional complex representations. -/
lemma Representation.nonempty_equiv_of_character_eq_of_isIrreducible
    [Finite G]
    {V : Type*} {W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (hχ : ρ.character = σ.character) :
    Nonempty (ρ.Equiv σ) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  -- Evaluating at the identity identifies the underlying dimensions.
  have hdim' : (Module.finrank ℂ V : ℂ) = Module.finrank ℂ W := by
    simpa [Representation.char_one] using congrFun hχ 1
  have hdim : Module.finrank ℂ V = Module.finrank ℂ W := by
    exact Nat.cast_injective (R := ℂ) hdim'
  -- Orthogonality upgrades character equality to a one-dimensional intertwining space.
  have hfinrank : Module.finrank ℂ (ρ.IntertwiningMap σ) = 1 := by
    exact_mod_cast
      calc
        (Module.finrank ℂ (ρ.IntertwiningMap σ) : ℂ) = ⟪ρ.character, σ.character⟫ := by
          symm
          exact
            Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              ℂ ρ σ
        _ = ⟪ρ.character, ρ.character⟫ := by simp [hχ]
        _ = Module.finrank ℂ (ρ.IntertwiningMap ρ) := by
          exact
            Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              ℂ ρ ρ
        _ = 1 := by
          simp [Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := ρ)]
  letI : Nontrivial (ρ.IntertwiningMap σ) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by simp [hfinrank])
  obtain ⟨f, hf_ne⟩ := exists_ne (0 : ρ.IntertwiningMap σ)
  -- A nonzero intertwiner between irreducibles is injective, and equal dimensions make it
  -- surjective.
  have hf_inj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero (ρ := ρ) (σ := σ) f).resolve_right hf_ne
  have hf_surj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf_inj
  exact
    Representation.nonempty_equiv_of_bijective_intertwiningMap
      (ρ1 := ρ) (ρ2 := σ) f ⟨hf_inj, hf_surj⟩

/-- Helper for Exercise 13-13.2-9: the doubled contribution of `(d² - 1)` vanishes in `ZMod 16`
when `d` is odd. -/
lemma paired_square_degree_sub_one_zmod_eq_zero_of_odd {d : ℕ} (hd : Odd d) :
    ((((d ^ 2 : ℕ) : ZMod 16) - 1) + ((((d ^ 2 : ℕ) : ZMod 16) - 1))) = 0 := by
  have hcast : (((2 * d ^ 2 : ℕ) : ZMod 16)) = (2 : ZMod 16) := by
    exact
      (ZMod.natCast_eq_natCast_iff (2 * d ^ 2) 2 16).2
        (paired_square_degree_modEq_two_of_odd hd)
  -- Rewrite the doubled contribution as `(2 * d^2) - 2` and then use the congruence above.
  calc
    ((((d ^ 2 : ℕ) : ZMod 16) - 1) + ((((d ^ 2 : ℕ) : ZMod 16) - 1)))
        = (((d ^ 2 : ℕ) : ZMod 16) * 2 - 2) := by
          ring
    _ = (((2 * d ^ 2 : ℕ) : ZMod 16) - 2) := by
          simp [Nat.cast_mul, mul_comm]
    _ = 0 := by
      rw [hcast]
      norm_num

/-- Helper for Exercise 13-13.2-9: an irreducible finite-dimensional complex representation has
irreducible dual. -/
lemma Representation.isIrreducible_dual_of_isIrreducible
    [Finite G] {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    ρ.dual.IsIrreducible := by
  -- Turn the source irreducibility into nontriviality of the carrier, so the dual space is
  -- nontrivial and the subrepresentation lattice of the dual has distinct `⊥` and `⊤`.
  have hV_nontrivial : Nontrivial V := by
    letI : Nontrivial (Subrepresentation ρ) := inferInstance
    by_contra hV
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      ext x
      simp [Subsingleton.elim x 0]
    exact (show (⊥ : Subrepresentation ρ) ≠ ⊤ from bot_ne_top) hbot_top
  letI : Nontrivial V := hV_nontrivial
  letI : Nontrivial (Module.Dual ℂ V) := (Module.nontrivial_dual_iff ℂ).2 inferInstance
  letI : Nontrivial (Subrepresentation ρ.dual) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro hbot_top
    obtain ⟨f, hf⟩ := exists_ne (0 : Module.Dual ℂ V)
    have htopmem : f ∈ (⊤ : Subrepresentation ρ.dual) := by
      exact show f ∈ (⊤ : Subrepresentation ρ.dual).toSubmodule from Submodule.mem_top
    have hfmem : f ∈ (⊥ : Subrepresentation ρ.dual) := by
      simpa [hbot_top] using htopmem
    exact hf (by simpa using hfmem)
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule.dualCoannihilator
      apply_mem_toSubmodule := by
        -- Stability of the annihilator is exactly the contragredient action identity.
        intro g x hx
        rw [Submodule.mem_dualCoannihilator] at hx ⊢
        intro φ hφ
        have hgphi : ρ.dual g⁻¹ φ ∈ W.toSubmodule := by
          exact W.apply_mem_toSubmodule g⁻¹ hφ
        have hx' := hx (ρ.dual g⁻¹ φ) hgphi
        simpa [Representation.dual_apply, Module.Dual.transpose_apply] using hx' }
  have hW' : W' = ⊥ ∨ W' = ⊤ := by
    exact eq_bot_or_eq_top W'
  rcases hW' with hW' | hW'
  · -- If the annihilator in `V` is zero, finite-dimensional duality forces `W = ⊤`.
    apply Subrepresentation.toSubmodule_injective
    calc
      W.toSubmodule = W.toSubmodule.dualCoannihilator.dualAnnihilator := by
        symm
        exact Subspace.dualCoannihilator_dualAnnihilator_eq (W := W.toSubmodule)
      _ = ⊤ := by
        have hco : W.toSubmodule.dualCoannihilator = ⊥ := by
          simpa using congrArg Subrepresentation.toSubmodule hW'
        simp [hco]
  · -- If the annihilator in `V` is all of `V`, then `W = ⊥`, contradicting `hW`.
    exfalso
    apply hW
    apply Subrepresentation.toSubmodule_injective
    calc
      W.toSubmodule = W.toSubmodule.dualCoannihilator.dualAnnihilator := by
        symm
        exact Subspace.dualCoannihilator_dualAnnihilator_eq (W := W.toSubmodule)
      _ = ⊥ := by
        have hco : W.toSubmodule.dualCoannihilator = ⊤ := by
          simpa using congrArg Subrepresentation.toSubmodule hW'
        simp [hco]

/-- Helper for Exercise 13-13.2-9: completeness supplies an index for the dual of any member of a
complete irreducible family. -/
lemma exists_iso_conjugateIndex
    [Finite G] {ι : Type} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (i : ι) :
    ∃ j, Nonempty (FDRep.of ((π i).ρ.dual) ≅ FDRep.of (π j).ρ) := by
  -- The new dual-irreducibility bridge puts the dual representation back inside the complete
  -- family owner.
  letI : (π i).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  letI : ((π i).ρ.dual).IsIrreducible :=
    Representation.isIrreducible_dual_of_isIrreducible (ρ := (π i).ρ)
  exact
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := fun j ↦ FDRep.of (π j).ρ) hπ_complete ((π i).ρ.dual) inferInstance

/-- Helper for Exercise 13-13.2-9: the complete family index paired with `i` is the index of the
dual representation. -/
noncomputable def conjugateIndex
    [Finite G] {ι : Type} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (i : ι) : ι :=
  Classical.choose (exists_iso_conjugateIndex π hπ_complete i)

/-- Helper for Exercise 13-13.2-9: the character at the dual index is the complex conjugate of the
original character. -/
lemma conjugateIndex_character
    [Finite G] {ι : Type} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (i : ι) :
    (π (conjugateIndex π hπ_complete i)).ρ.character =
      fun g ↦ star ((π i).ρ.character g) := by
  -- Recover the chosen owner-level isomorphism for the dual member.
  rcases Classical.choose_spec (exists_iso_conjugateIndex π hπ_complete i) with ⟨e⟩
  have hchar_iso :
      ((π i).ρ.dual).character = (π (conjugateIndex π hπ_complete i)).ρ.character := by
    simpa [conjugateIndex] using
      Representation.char_iso
        (Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e))
  -- The dual character is pointwise complex conjugation of the original one.
  ext g
  rw [← hchar_iso, Representation.char_dual_eq_star]

/-- Helper for Exercise 13-13.2-9: the dual partner preserves irreducible degree. -/
lemma finrank_conjugateIndex_eq
    [Finite G] {ι : Type} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (i : ι) :
    Module.finrank ℂ (π (conjugateIndex π hπ_complete i)) = Module.finrank ℂ (π i) := by
  -- Evaluate the conjugate-character identity at `1`.
  have hvalue := congrFun (conjugateIndex_character π hπ_complete i) 1
  simpa [Representation.char_one] using hvalue

/-- Helper for Exercise 13-13.2-9: a nontrivial irreducible character is orthogonal to the trivial
character. -/
lemma groupFunctionPairing_trivial_character_eq_zero_of_not_trivial
    [Finite G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (hnottrivial : ¬ Nonempty (FDRep.of (Representation.trivial ℂ G ℂ) ≅ FDRep.of ρ)) :
    ⟪1, ρ.character⟫ = 0 := by
  letI : Fintype G := Fintype.ofFinite G
  letI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  haveI : (Representation.trivial ℂ G ℂ).IsIrreducible := by
    simpa using
      isIrreducible_of_finrank_eq_one (ρ := Representation.trivial ℂ G ℂ)
        (by simp : Module.finrank ℂ ℂ = 1)
  have hnottrivial_rep : ¬ Nonempty ((Representation.trivial ℂ G ℂ).Equiv ρ) := by
    intro hEq
    rcases hEq with ⟨e⟩
    exact hnottrivial ⟨by simpa using e.toFDRepIso⟩
  -- Orthogonality against a nonisomorphic irreducible collapses the pairing to zero.
  have hpair :
      ⟪(Representation.trivial ℂ G ℂ).character, ρ.character⟫ = 0 :=
    Representation.groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
      ℂ (Representation.trivial ℂ G ℂ) ρ hnottrivial_rep
  have htrivchar : (Representation.trivial ℂ G ℂ).character = 1 := by
    ext g
    simp [Representation.character, Representation.trivial]
  simpa [htrivchar] using hpair

/-- Helper for Exercise 13-13.2-9: in odd order, the Frobenius-Schur indicator equals the pairing
with the trivial character. -/
lemma frobenius_schur_indicator_eq_pairing_trivial_of_odd_order
    [Finite G] (hodd : Odd (Nat.card G)) (χ : G → ℂ) :
    Representation.frobeniusSchurIndicator χ = ⟪1, χ⟫ := by
  letI : Fintype G := Fintype.ofFinite G
  let e : G ≃ G :=
    Equiv.ofBijective (fun g : G ↦ g ^ (2 : ℕ))
      (Nat.Coprime.pow_left_bijective (G := G) (n := 2) (Odd.coprime_two_right hodd))
  -- Reindex the square-sum defining the indicator along the bijection `g ↦ g^2`.
  rw [Representation.frobeniusSchurIndicator_eq_card_inv_sum_sq]
  have hsum : ∑ s : G, χ (s ^ 2) = ∑ s : G, χ s := by
    simpa [e] using (Equiv.sum_comp e χ)
  rw [hsum]
  simp [Representation.groupFunctionPairingOverField, Nat.card_eq_fintype_card]

/-- Helper for Exercise 13-13.2-9: the dual-index map on a complete pairwise nonisomorphic family
is an involution. -/
lemma conjugateIndex_involution
    [Finite G] {ι : Type} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_pairwise : PairwiseNonisomorphic π)
    (i : ι) :
    conjugateIndex π hπ_complete (conjugateIndex π hπ_complete i) = i := by
  let j := conjugateIndex π hπ_complete (conjugateIndex π hπ_complete i)
  letI : (π i).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  letI : (π j).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete j
  -- The dual-character identity applied twice gives back the original character.
  have hchar : (π j).ρ.character = (π i).ρ.character := by
    ext g
    calc
      (π j).ρ.character g =
          star ((π (conjugateIndex π hπ_complete i)).ρ.character g) := by
            exact congrFun (conjugateIndex_character π hπ_complete (conjugateIndex π hπ_complete i)) g
      _ = star (star ((π i).ρ.character g)) := by
            rw [congrFun (conjugateIndex_character π hπ_complete i) g]
      _ = (π i).ρ.character g := by simp
  rcases
      Representation.nonempty_equiv_of_character_eq_of_isIrreducible
        (ρ := (π j).ρ) (σ := (π i).ρ) hchar with
    ⟨e⟩
  have hπ_pairwise_fdrep := pairwiseNonisomorphic_fdrep_of_rep π hπ_pairwise
  by_contra hji
  exact hπ_pairwise_fdrep hji ⟨e.toFDRepIso⟩

/-- Helper for Exercise 13-13.2-9: the trivial constituent is fixed by the dual-index map. -/
lemma conjugateIndex_trivial_index_eq
    [Finite G] {ι : Type} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_pairwise : PairwiseNonisomorphic π)
    {i0 : ι}
    (hi0 : Nonempty (FDRep.of (Representation.trivial ℂ G ℂ) ≅ FDRep.of (π i0).ρ)) :
    conjugateIndex π hπ_complete i0 = i0 := by
  let j := conjugateIndex π hπ_complete i0
  letI : (π i0).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i0
  letI : (π j).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete j
  have hchar0 :
      (π i0).ρ.character = (Representation.trivial ℂ G ℂ).character :=
    character_eq_trivial_of_trivial_index π hi0
  -- The trivial character is fixed by complex conjugation, so its dual partner is itself.
  have hchar : (π j).ρ.character = (π i0).ρ.character := by
    ext g
    calc
      (π j).ρ.character g = star ((π i0).ρ.character g) := by
        exact congrFun (conjugateIndex_character π hπ_complete i0) g
      _ = star ((Representation.trivial ℂ G ℂ).character g) := by rw [hchar0]
      _ = (Representation.trivial ℂ G ℂ).character g := by
            simp [Representation.character, Representation.trivial]
      _ = (π i0).ρ.character g := by rw [hchar0]
  rcases
      Representation.nonempty_equiv_of_character_eq_of_isIrreducible
        (ρ := (π j).ρ) (σ := (π i0).ρ) hchar with
    ⟨e⟩
  have hπ_pairwise_fdrep := pairwiseNonisomorphic_fdrep_of_rep π hπ_pairwise
  by_contra hji
  exact hπ_pairwise_fdrep hji ⟨e.toFDRepIso⟩

/-- Helper for Exercise 13-13.2-9: away from the trivial constituent, the dual-index involution
has no fixed points for an odd-order group. -/
lemma conjugateIndex_fixed_eq_trivial_index_of_odd_order
    [Finite G] (hodd : Odd (Nat.card G))
    {ι : Type} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_pairwise : PairwiseNonisomorphic π)
    {i0 i : ι}
    (hi0 : Nonempty (FDRep.of (Representation.trivial ℂ G ℂ) ≅ FDRep.of (π i0).ρ))
    (hfix : conjugateIndex π hπ_complete i = i) :
    i = i0 := by
  letI : (π i).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  -- Route correction: convert the fixed point into self-duality, then contradict the odd-order
  -- Frobenius-Schur vanishing criterion unless the character is trivial.
  have hselfdual_fd : Nonempty (FDRep.of ((π i).ρ.dual) ≅ FDRep.of (π i).ρ) := by
    have hspec :
        Nonempty (FDRep.of ((π i).ρ.dual) ≅
          FDRep.of (π (conjugateIndex π hπ_complete i)).ρ) := by
      simpa [conjugateIndex] using
        (Classical.choose_spec (exists_iso_conjugateIndex π hπ_complete i))
    rw [hfix] at hspec
    exact hspec
  have hselfdual : Nonempty ((π i).ρ.Equiv (π i).ρ.dual) := by
    rcases hselfdual_fd with ⟨e⟩
    exact
      ⟨(Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)).symm⟩
  have hreal : IsValuedInBaseField ℝ (π i).ρ.character :=
    (Representation.hasRealValuedCharacter_iff_nonempty_equiv_dual (ρ := (π i).ρ)).2 hselfdual
  have htrivial_iso :
      Nonempty (FDRep.of (Representation.trivial ℂ G ℂ) ≅ FDRep.of (π i).ρ) := by
    by_contra hnottrivial
    have hpair_zero :
        ⟪1, (π i).ρ.character⟫ = 0 :=
      groupFunctionPairing_trivial_character_eq_zero_of_not_trivial (ρ := (π i).ρ) hnottrivial
    have hindicator_zero : Representation.frobeniusSchurIndicator (π i).ρ.character = 0 := by
      rw [frobenius_schur_indicator_eq_pairing_trivial_of_odd_order hodd]
      exact hpair_zero
    have hnot_real :
        ¬ IsValuedInBaseField ℝ (π i).ρ.character :=
      (Representation.isTypeOne_iff_frobeniusSchurIndicator_eq_zero (ρ := (π i).ρ)).2
        hindicator_zero
    exact hnot_real hreal
  haveI : (Representation.trivial ℂ G ℂ).IsIrreducible := by
    simpa using
      isIrreducible_of_finrank_eq_one (ρ := Representation.trivial ℂ G ℂ)
        (by simp : Module.finrank ℂ ℂ = 1)
  have hπ_pairwise_fdrep := pairwiseNonisomorphic_fdrep_of_rep π hπ_pairwise
  by_contra hii0
  exact hπ_pairwise_fdrep hii0 ⟨(Classical.choice htrivial_iso).symm.trans (Classical.choice hi0)⟩

/-- Helper for Exercise 13-13.2-9: after removing the trivial constituent, the sum of squared
degrees is congruent modulo `16` to the number of remaining indices. -/
lemma sum_sq_degree_erase_modEq_card_erase
    [Finite G] {ι : Type} [Fintype ι] [DecidableEq ι]
    (hodd : Odd (Nat.card G))
    (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_pairwise : PairwiseNonisomorphic π)
    {i0 : ι}
    (hi0 : Nonempty (FDRep.of (Representation.trivial ℂ G ℂ) ≅ FDRep.of (π i0).ρ)) :
    ((Finset.univ.erase i0).sum fun i ↦ Module.finrank ℂ (π i) ^ 2) ≡
      (Finset.univ.erase i0).card [MOD 16] := by
  let f : ι → ZMod 16 := fun i ↦ (((Module.finrank ℂ (π i) ^ 2 : ℕ) : ZMod 16) - 1)
  have hsum_zero :
      (Finset.univ.erase i0).sum f = 0 := by
    -- Pair the nontrivial irreducibles by duality; each 2-cycle contributes zero in `ZMod 16`.
    refine
      Finset.sum_involution
        (s := Finset.univ.erase i0)
        (f := f)
        (g := fun i _ ↦ conjugateIndex π hπ_complete i)
        ?_ ?_ ?_ ?_
    · intro i hi
      dsimp [f]
      rw [finrank_conjugateIndex_eq π hπ_complete i]
      exact
        paired_square_degree_sub_one_zmod_eq_zero_of_odd
          (finrank_odd_of_complete_family_member hodd π hπ_complete i)
    · intro i hi _ hfix
      exact (Finset.mem_erase.mp hi).1 <|
        conjugateIndex_fixed_eq_trivial_index_of_odd_order
          hodd π hπ_complete hπ_pairwise hi0 hfix
    · intro i hi
      refine Finset.mem_erase.mpr ?_
      constructor
      · intro hci0
        have hci0' : conjugateIndex π hπ_complete i = i0 := by
          simpa using hci0
        have hi_eq : i = i0 := by
          calc
            i = conjugateIndex π hπ_complete (conjugateIndex π hπ_complete i) := by
              symm
              exact conjugateIndex_involution π hπ_complete hπ_pairwise i
            _ = conjugateIndex π hπ_complete i0 := by
                  exact congrArg (conjugateIndex π hπ_complete) hci0'
            _ = i0 := conjugateIndex_trivial_index_eq π hπ_complete hπ_pairwise hi0
        exact (Finset.mem_erase.mp hi).1 hi_eq
      · exact Finset.mem_univ _
    · intro i hi
      exact conjugateIndex_involution π hπ_complete hπ_pairwise i
  have hcast :
      (((Finset.univ.erase i0).sum fun i ↦ Module.finrank ℂ (π i) ^ 2 : ℕ) : ZMod 16) =
        ((Finset.univ.erase i0).card : ZMod 16) := by
    -- Expand the zero sum of `(d_i^2 - 1)` into the desired equality of casts.
    apply sub_eq_zero.mp
    simpa [f, Finset.sum_sub_distrib]
      using hsum_zero
  exact (ZMod.natCast_eq_natCast_iff _ _ 16).1 hcast

-- Proof sketch: rewrite `Nat.card G` as the sum of the squared irreducible degrees, and rewrite
-- `Nat.card (ConjClasses G)` as the number of indices in a complete irreducible family. The
-- arithmetic helper above already shows that each dual pair of odd degree contributes the same as
-- two indices modulo `16`; the remaining blocker is the exact dual-family bridge needed to package
-- that pairing argument against the currently importable owner declarations in this checkout.
/-- Exercise 13-13.2-9: if `G` has odd order, then the order of `G` is congruent modulo `16` to
the number of conjugacy classes of `G`. -/
theorem group_order_modEq_card_conjClasses_of_odd_order (hodd : Odd (Nat.card G)) :
    Nat.card G ≡ Nat.card (ConjClasses G) [MOD 16] := by
  classical
  letI : Finite G := by
    by_cases hfin : Finite G
    · exact hfin
    · exfalso
      letI : Infinite G := not_finite_iff_infinite.mp hfin
      simp at hodd
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  obtain ⟨ι, _, πfd, hπfd_pairwise, hπfd_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family (G := G)
  letI : Finite ι := Finite.of_fintype ι
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → Rep ℂ G := fun i ↦ Rep.of (πfd i).ρ
  have hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ) := by
    simpa [π] using hπfd_complete
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro i j hij hij_iso
    apply hπfd_pairwise hij
    rcases hij_iso with ⟨e⟩
    simpa [π] using ⟨(Representation.equivOfIso e).toFDRepIso⟩
  obtain ⟨i0, hi0⟩ := trivial_index_exists π hπ_complete
  letI : DecidableEq ι := Classical.decEq ι
  have htail :
      ((Finset.univ.erase i0).sum fun i ↦ Module.finrank ℂ (π i) ^ 2) ≡
        (Finset.univ.erase i0).card [MOD 16] :=
    sum_sq_degree_erase_modEq_card_erase hodd π hπ_complete hπ_pairwise hi0
  have hsum_total :
      ∑ i : ι, Module.finrank ℂ (π i) ^ 2 = Nat.card G := by
    simpa [π] using
      (Representation.sum_sq_degree_eq_card_of_complete_irreducible_family
        (π := πfd) hπfd_complete hπfd_pairwise)
  have hcard_total : Nat.card ι = Nat.card (ConjClasses G) := by
    exact
      Representation.card_eq_card_conjClasses_of_complete_irreducible_family_local
        (π := πfd) hπfd_pairwise hπfd_complete
  have hdeg0 : Module.finrank ℂ (π i0) ^ 2 = 1 := by
    rw [finrank_eq_one_of_trivial_index π hi0]
    norm_num
  have hsum_split :
      Nat.card G = 1 + ((Finset.univ.erase i0).sum fun i ↦ Module.finrank ℂ (π i) ^ 2) := by
    have hsum_univ :
        Module.finrank ℂ (π i0) ^ 2
          + ((Finset.univ.erase i0).sum fun i ↦ Module.finrank ℂ (π i) ^ 2) =
            ∑ i : ι, Module.finrank ℂ (π i) ^ 2 := by
      simpa [add_comm] using
        (Finset.sum_erase_add
          (s := Finset.univ) (a := i0)
          (f := fun i ↦ Module.finrank ℂ (π i) ^ 2) (by simp))
    calc
      Nat.card G = ∑ i : ι, Module.finrank ℂ (π i) ^ 2 := hsum_total.symm
      _ = Module.finrank ℂ (π i0) ^ 2
            + ((Finset.univ.erase i0).sum fun i ↦ Module.finrank ℂ (π i) ^ 2) := hsum_univ.symm
      _ = 1 + ((Finset.univ.erase i0).sum fun i ↦ Module.finrank ℂ (π i) ^ 2) := by
            rw [hdeg0]
  have hcard_split :
      Nat.card (ConjClasses G) = 1 + (Finset.univ.erase i0).card := by
    have hcard_univ : (Finset.univ.erase i0).card + 1 = Fintype.card ι := by
      simpa using (Finset.card_erase_add_one (s := Finset.univ) (a := i0) (by simp))
    calc
      Nat.card (ConjClasses G) = Nat.card ι := hcard_total.symm
      _ = Fintype.card ι := Nat.card_eq_fintype_card
      _ = 1 + (Finset.univ.erase i0).card := by
            simpa [Nat.add_comm] using hcard_univ.symm
  -- Split off the trivial constituent and add `1` to the congruence on the remaining indices.
  rw [hsum_split, hcard_split]
  exact htail.add_left 1

end
