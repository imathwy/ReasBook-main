import Mathlib
import Serre.Chap02.Proposition_2_2_1_1
import Serre.Chap02.Proposition_2_2_2_1
import Serre.Chap02.Theorem_2_2_3_5
import Serre.Chap06.Exercise_6_6_5_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Representation

section

open scoped BigOperators
open IntertwiningMap

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (ρ : Representation k G V) [ρ.IsIrreducible]

-- Source/core/bridge triage: this item is `source-facing`. The primitive data are the
-- irreducible finite-dimensional representation `ρ` and the central element `s`. The owner
-- abstraction is the canonical intertwining endomorphism `centralMul ρ s hs`; Schur's lemma from
-- Chapter 2 is the `core/canonical` input, and forgetting the intertwining map back to the
-- underlying endomorphism is the only `bridge/view` step.
-- Proof sketch: `IntertwiningMap.centralMul s hs` is the canonical intertwining endomorphism
-- attached to the central action of `s`; then apply the Chapter 2 owner theorem
-- `Representation.intertwiningMap_eq_smul_id` and forget back to the underlying endomorphism.
/-- Exercise 3-3.1-4 (1): in an irreducible finite-dimensional representation over an
algebraically closed field, every central element acts by a homothety. -/
theorem exists_smul_id_of_mem_center (s : G) (hs : s ∈ Submonoid.center G) :
    ∃ z : k, ρ s = z • 1 := by
  obtain ⟨z, hz⟩ := intertwiningMap_eq_smul_id ρ (centralMul ρ s hs)
  exact ⟨z, by simpa using congrArg toLinearMap hz⟩

end

section

variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (ρ : Representation ℂ G V) [ρ.IsIrreducible]

-- Source/core/bridge triage: this item is `source-facing`. The primitive data are again `ρ`, the
-- central finite-order element `s`, and its order hypothesis. The scalar-action owner remains
-- `centralMul ρ s hs` together with Chapter 2 Schur; `Representation.character` and
-- `Representation.char_one` provide the canonical character-level bridge from scalar action to the
-- stated norm identity.
-- Proof sketch: use `centralMul ρ s hs` and `intertwiningMap_eq_smul_id` to write
-- `ρ s = z • 1`; then `ρ.character s = z * Module.finrank ℂ V`. If `s` has finite order, then so
-- does `ρ s`, hence the scalar `z` has norm `1`; taking norms yields the claimed equality.
/-- Exercise 3-3.1-4 (2): if `s` is a central finite-order element, then the norm of the character
value `χ(s)` equals the degree of the irreducible representation. -/
theorem norm_character_eq_finrank_of_mem_center (s : G) (hs : s ∈ Submonoid.center G)
    (hsfin : IsOfFinOrder s) :
    ‖ρ.character s‖ = (Module.finrank ℂ V : ℝ) :=
  (character_norm_eq_char_one_iff_exists_smul_id ρ s hsfin).2 <|
    exists_smul_id_of_mem_center ρ s hs

end

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

-- Source/core/bridge triage: this item is `source-facing`. Its primitive data are the irreducible
-- complex representation `ρ`; the square bound is the textbook statement proved directly from
-- character orthogonality. The later Chapter 6 theorem `finrank_dvd_center_index` is a
-- complementary divisibility sharpening, but it does not replace this earlier square-inequality
-- statement.
-- Proof sketch: derive the finite-dimensionality of `V` from the owner theorem
-- `IsIrreducible.finiteDimensional_of_finite`, then start from the orthogonality relation
-- `Representation.card_inv_mul_sum_char_mul_char_eq_finrank` specialized to `ρ = σ`, so the sum
-- of `‖ρ.character s‖ ^ 2` over `G` is `Nat.card G`; then apply
-- `norm_character_eq_finrank_of_mem_center` to each central element using
-- `isOfFinOrder_of_finite s` and compare the contribution of the center with the canonical index
-- `(Subgroup.center G).index = [G : Z(G)]`.
/-- Exercise 3-3.1-4 (3): the square of the degree of an irreducible complex representation is at
most the index of the center. -/
theorem finrank_sq_le_center_index (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Module.finrank ℂ V ^ 2 ≤ (Subgroup.center G).index := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
  have hsum :
      ∑ s : G, Complex.normSq (ρ.character s) = Nat.card G := by
    have hterm :
        Finset.univ.sum (fun s : G ↦ (Complex.normSq (ρ.character s) : ℂ)) =
          Finset.univ.sum (fun s : G ↦ ρ.character s * ρ.character s⁻¹) := by
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [ρ.char_inv_eq_star_of_isOfFinOrder s (isOfFinOrder_of_finite s)]
      simpa [Complex.normSq_eq_norm_sq] using (Complex.mul_conj' (ρ.character s)).symm
    apply Complex.ofReal_injective
    calc
      ((∑ s : G, Complex.normSq (ρ.character s) : ℝ) : ℂ)
          = ∑ s : G, ρ.character s * ρ.character s⁻¹ := by
              simpa using hterm
      _ = Nat.card G := by
            have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
              exact_mod_cast Nat.card_pos.ne'
            letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
            have hortho :
                (Nat.card G : ℂ)⁻¹ * ∑ s : G, ρ.character s * ρ.character s⁻¹ = 1 := by
              rw [ρ.card_inv_mul_sum_char_mul_char_eq_finrank,
                Representation.IsIrreducible.finrank_intertwiningMap_self ρ]
              norm_num
            apply_fun (fun z : ℂ ↦ z * (Nat.card G : ℂ)) at hortho
            simpa [hcard_ne, mul_comm, mul_left_comm, mul_assoc] using hortho
  have hcenter_sum :
      ∑ s : Subgroup.center G, Complex.normSq (ρ.character s) =
        Nat.card (Subgroup.center G) * Module.finrank ℂ V ^ 2 := by
    have hcenter_term (s : Subgroup.center G) :
        Complex.normSq (ρ.character s) = Module.finrank ℂ V ^ 2 := by
      rw [Complex.normSq_eq_norm_sq,
        norm_character_eq_finrank_of_mem_center ρ s
          (show (s : G) ∈ Submonoid.center G from by
            simpa [Subgroup.center_toSubmonoid] using s.2)
          (show IsOfFinOrder (s : G) from by
            let t : G := s
            have ht : IsOfFinOrder t := isOfFinOrder_of_finite t
            simpa [t] using ht)]
    calc
      ∑ s : Subgroup.center G, Complex.normSq (ρ.character s)
          = ∑ _ : Subgroup.center G, Module.finrank ℂ V ^ 2 := by
              simp [hcenter_term]
      _ = Fintype.card (Subgroup.center G) * Module.finrank ℂ V ^ 2 := by
            simp [mul_comm]
      _ = Nat.card (Subgroup.center G) * Module.finrank ℂ V ^ 2 := by
            rw [Nat.card_eq_fintype_card]
  have hcenter_le :
      (Nat.card (Subgroup.center G) * Module.finrank ℂ V ^ 2 : ℝ) ≤ Nat.card G := by
    have hnonneg :
        0 ≤ (Finset.univ.filter (fun s : G ↦ s ∉ Subgroup.center G)).sum
          (fun s ↦ Complex.normSq (ρ.character s)) := by
      exact Finset.sum_nonneg fun s _ ↦ Complex.normSq_nonneg (ρ.character s)
    calc
      (Nat.card (Subgroup.center G) * Module.finrank ℂ V ^ 2 : ℝ)
          = (Finset.univ.filter (fun s : G ↦ s ∈ Subgroup.center G)).sum
              (fun s ↦ Complex.normSq (ρ.character s)) := by
                rw [← Finset.sum_subtype_eq_sum_filter]
                simpa using hcenter_sum.symm
      _ ≤
          (Finset.univ.filter (fun s : G ↦ s ∈ Subgroup.center G)).sum
              (fun s ↦ Complex.normSq (ρ.character s)) +
            (Finset.univ.filter (fun s : G ↦ s ∉ Subgroup.center G)).sum
              (fun s ↦ Complex.normSq (ρ.character s)) := by
            exact le_add_of_nonneg_right hnonneg
      _ = ∑ s : G, Complex.normSq (ρ.character s) := by
            simpa using
              (Finset.univ.sum_filter_add_sum_filter_not
                (fun s : G ↦ s ∈ Subgroup.center G)
                (fun s ↦ Complex.normSq (ρ.character s)))
      _ = Nat.card G := hsum
  have hcenter_le_nat :
      Nat.card (Subgroup.center G) * Module.finrank ℂ V ^ 2 ≤ Nat.card G := by
    exact_mod_cast hcenter_le
  have hmul :
      Nat.card (Subgroup.center G) * Module.finrank ℂ V ^ 2 ≤
        Nat.card (Subgroup.center G) * (Subgroup.center G).index := by
    rw [Subgroup.card_mul_index]
    exact hcenter_le_nat
  exact Nat.le_of_mul_le_mul_left hmul Nat.card_pos

end

section

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) [ρ.IsIrreducible]

-- Proof sketch: first derive `FiniteDimensional k V` from
-- `IsIrreducible.finiteDimensional_of_finite ρ`. For `s ∈ Subgroup.center G`,
-- `exists_smul_id_of_mem_center ρ s hs` writes `ρ s` as `z • 1`; faithfulness identifies `s` with
-- the scalar `z`, so `Subgroup.center G` injects into `kˣ`. The canonical owner theorem
-- `isCyclic_of_injective_ringHom` then implies that this finite subgroup of the unit group of the
-- commutative field `k` is cyclic.
/-- Exercise 3-3.1-4 (4): the center of a finite group admitting a faithful irreducible
representation over an algebraically closed field is cyclic. -/
theorem center_isCyclic_of_faithful (hfaithful : Function.Injective ρ) :
    IsCyclic (Subgroup.center G) := by
  classical
  by_cases hV : Subsingleton V
  · have hG : Subsingleton G := by
      refine ⟨fun g h ↦ hfaithful ?_⟩
      ext x
      exact hV.elim _ _
    infer_instance
  · letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
    letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
    let v : V := Classical.choose (exists_ne (0 : V))
    have hv : v ≠ 0 := Classical.choose_spec (exists_ne (0 : V))
    have hsmul_injective : Function.Injective fun z : k ↦ z • (1 : Module.End k V) := by
      intro z w hzw
      have hvw : z • v = w • v := by
        simpa using congrArg (fun f : Module.End k V ↦ f v) hzw
      have hsub : (z - w) • v = 0 := by
        rw [sub_smul, hvw, sub_self]
      rcases smul_eq_zero.mp hsub with hzero | hzero
      · exact sub_eq_zero.mp hzero
      · exact (hv hzero).elim
    let scalar : Subgroup.center G → k := fun s ↦
      Classical.choose <|
        exists_smul_id_of_mem_center ρ (s : G)
          (show (s : G) ∈ Submonoid.center G from by
            simpa [Subgroup.center_toSubmonoid] using s.2)
    have hscalar (s : Subgroup.center G) :
        ρ (s : G) = scalar s • (1 : Module.End k V) := by
      simpa [scalar] using
        (Classical.choose_spec <|
          exists_smul_id_of_mem_center ρ (s : G)
            (show (s : G) ∈ Submonoid.center G from by
              simpa [Subgroup.center_toSubmonoid] using s.2))
    let φ : Subgroup.center G →* k :=
      { toFun := scalar
        map_one' := by
          apply hsmul_injective
          calc
            scalar 1 • (1 : Module.End k V) = ρ (1 : G) := (hscalar 1).symm
            _ = (1 : k) • (1 : Module.End k V) := by simp
        map_mul' := by
          intro s t
          apply hsmul_injective
          calc
            scalar (s * t) • (1 : Module.End k V) = ρ (s * t : G) := (hscalar (s * t)).symm
            _ = ρ (s : G) * ρ (t : G) := by simp
            _ = (scalar s * scalar t) • (1 : Module.End k V) := by
                  rw [hscalar s, hscalar t]
                  ext x
                  simp [smul_smul, mul_comm] }
    have hφ_injective : Function.Injective φ := by
      intro s t hst
      apply Subtype.ext
      apply hfaithful
      calc
        ρ (s : G) = scalar s • (1 : Module.End k V) := hscalar s
        _ = φ t • (1 : Module.End k V) := by simpa [hst]
        _ = ρ (t : G) := (hscalar t).symm
    exact isCyclic_of_injective_ringHom φ hφ_injective

end

end Representation
