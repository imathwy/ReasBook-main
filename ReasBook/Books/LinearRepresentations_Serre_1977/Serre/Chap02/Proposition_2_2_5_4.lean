import LinearRepresentations_Serre_1977.Chap02.Corollary_2_2_4_3
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open CategoryTheory

noncomputable section

universe u v

namespace Representation

section

variable {G : Type} [Group G] [Finite G] [NeZero (Nat.card G)]
variable {ι : Type v}
variable (π : ι → FDRep ℂ G)

section CompleteFamily

/-- Helper for Proposition 2-2.5-4: pairing the conjugacy-class indicator with an irreducible
character returns the coefficient from the source proof. -/
private theorem indicator_pairing_with_irreducible_character
    (s : G) (i : ι) :
    Representation.groupFunctionPairingOverField ℂ
        ((ConjClasses.mk s).indicatorClassFunction : G → ℂ)
        (π i).character =
      ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
        star ((π i).character s) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let carrier : Set G := (ConjClasses.mk s).carrier
  let S : Finset G := Finset.univ.filter (fun t : G ↦ t ∈ carrier)
  -- Rewrite the normalized pairing as an explicit finite sum over the group.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  calc
    (↑(Nat.card G))⁻¹ *
        (∑ t : G, ((ConjClasses.mk s).indicator t : ℂ) * (π i).character t⁻¹) =
      (↑(Nat.card G))⁻¹ * Finset.sum S (fun t ↦ (π i).character t⁻¹) := by
        congr 1
        simp [ConjClasses.indicator, carrier, S, Set.indicator, Finset.sum_filter, mul_comm]
    _ = (↑(Nat.card G))⁻¹ * (S.card * star ((π i).character s)) := by
        congr 1
        -- Every term on the conjugacy class contributes the same value `χ_i(s)^*`.
        calc
          Finset.sum S (fun t ↦ (π i).character t⁻¹) =
              Finset.sum S (fun _ ↦ star ((π i).character s)) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            have ht' : t ∈ carrier := by
              simpa [S] using (Finset.mem_filter.mp ht).2
            have hconj : IsConj t s := by
              exact ConjClasses.mk_eq_mk_iff_isConj.mp
                ((ConjClasses.mem_carrier_iff_mk_eq).mp ht')
            have hconj_inv : IsConj t⁻¹ s⁻¹ := by
              rcases isConj_iff.mp hconj with ⟨a, ha⟩
              refine isConj_iff.mpr ⟨a, ?_⟩
              calc
                a * t⁻¹ * a⁻¹ = (a * t * a⁻¹)⁻¹ := by simp [mul_assoc]
                _ = s⁻¹ := by simp [ha]
            calc
              (π i).character t⁻¹ = (π i).character s⁻¹ := by
                simpa using Representation.char_eq_of_isConj (ρ := (π i).ρ) hconj_inv
              _ = star ((π i).character s) := by
                simpa using Representation.char_inv_eq_star_of_isOfFinOrder
                  (ρ := (π i).ρ) s (isOfFinOrder_of_finite s)
          _ = S.card * star ((π i).character s) := by
            simp [nsmul_eq_mul]
    _ = ((Nat.card carrier : ℂ) / Nat.card G) * star ((π i).character s) := by
        have hcard : S.card = Nat.card carrier := by
          let _ : Fintype carrier := Fintype.ofFinite carrier
          rw [Nat.card_eq_fintype_card]
          symm
          exact Fintype.card_of_subtype S (fun t ↦ by simp [S, carrier])
        rw [hcard]
        simp [div_eq_mul_inv, mul_assoc, mul_comm]

/-- Helper for Proposition 2-2.5-4: the coordinate of a class function in the irreducible
character basis is its pairing with the corresponding irreducible character. -/
private theorem repr_complete_family_basis_eq_pairing
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    [Finite ι]
    (x : classFunctionSubmodule ℂ G) (i : ι) :
    (irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
        π hπ_pairwise hπ_complete).repr x i =
      Representation.groupFunctionPairingOverField ℂ (x : G → ℂ) (π i).character := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  let b := irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    π hπ_pairwise hπ_complete
  let coordLinear : classFunctionSubmodule ℂ G →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦ b.repr y i
      map_add' := by
        intro y z
        simp
      map_smul' := by
        intro a y
        simp }
  let pairLinear : classFunctionSubmodule ℂ G →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦
        Representation.groupFunctionPairingOverField ℂ (y : G → ℂ) (π i).character
      map_add' := by
        intro y z
        simpa using Representation.groupFunctionPairing_add_left
          (y : G → ℂ) (z : G → ℂ) (π i).character
      map_smul' := by
        intro a y
        simpa using Representation.groupFunctionPairing_smul_left
          a (y : G → ℂ) (π i).character }
  have hmaps : coordLinear = pairLinear := by
    -- Compare the two linear functionals on the character basis itself.
    apply b.ext
    intro j
    have hcoord_j : coordLinear (b j) = if i = j then 1 else 0 := by
      simpa [eq_comm] using
        (show coordLinear (b j) = if j = i then 1 else 0 by
          simp [coordLinear, b, Module.Basis.repr_self, Finsupp.single_apply])
    have hpair_j : pairLinear (b j) = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst j
        letI : Simple (π i) := hπ_complete.isSimple i
        have hself_iso : Nonempty (π i ≅ π i) := ⟨Iso.refl _⟩
        calc
          pairLinear (b i) =
              Representation.groupFunctionPairingOverField ℂ
                (π i).character (π i).character := by
            simp [pairLinear, b,
              irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
          _ = 1 := by
            simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
              hself_iso] using
              (FDRep.char_orthonormal (π i) (π i))
          _ = if i = i then 1 else 0 := by simp
      · have hji : j ≠ i := fun h ↦ hij h.symm
        letI : Simple (π j) := hπ_complete.isSimple j
        letI : Simple (π i) := hπ_complete.isSimple i
        have hnot : ¬ Nonempty (π j ≅ π i) := hπ_pairwise hji
        calc
          pairLinear (b j) =
              Representation.groupFunctionPairingOverField ℂ
                (π j).character (π i).character := by
            simp [pairLinear, b,
              irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
          _ = 0 := by
            simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
              hnot] using
              (FDRep.char_orthonormal (π j) (π i))
          _ = if i = j then 1 else 0 := by simp [hij]
    exact hcoord_j.trans hpair_j.symm
  -- Apply the equality of functionals to the chosen class function.
  have hmaps_apply := congrArg
    (fun f : classFunctionSubmodule ℂ G →ₗ[ℂ] ℂ ↦ f x) hmaps
  simpa [coordLinear, pairLinear] using hmaps_apply

-- Proof sketch: apply the character-basis expansion from the preceding results to the conjugacy
-- class indicator function `(ConjClasses.mk s).indicator`, then rearrange the resulting equality
-- of class functions.
/-- Proposition 2-2.5-4: for a complete set of pairwise nonisomorphic irreducible complex
representations, the scalar-weighted sum of their character functions is `(g / c(s))` times the
indicator of the conjugacy class of `s`, so parts (a) and (b) are its evaluations at `t = s` and
at `t` not conjugate to `s`. -/
theorem sum_star_character_mul_character_eq_conjClassIndicator_mk_of_complete_family
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (s : G) :
    ∑' i : ι, star ((π i).character s) • (π i).character =
      ((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) •
        Set.indicator ((ConjClasses.mk s).carrier) (fun _ ↦ (1 : ℂ)) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hg_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  let _ : NeZero (Nat.card G : ℂ) := ⟨hg_ne⟩
  let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  let _ : Fintype ι := Fintype.ofFinite ι
  let b := irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    π hπ_pairwise hπ_complete
  let x : classFunctionSubmodule ℂ G := (ConjClasses.mk s).indicatorClassFunction
  have hcoeff :
      ∀ i, b.repr x i =
        ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
          star ((π i).character s) := by
    intro i
    -- The basis coefficient is exactly the pairing computed above.
    rw [repr_complete_family_basis_eq_pairing (π := π) hπ_pairwise hπ_complete x i]
    simpa [x] using indicator_pairing_with_irreducible_character (π := π) s i
  have hsum :
      ∑ i,
          (((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
              star ((π i).character s)) • (π i).character =
        (x : G → ℂ) := by
    -- Evaluate the basis expansion pointwise after substituting the coefficient formula.
    funext t
    have hsum_t := congrArg
      (fun z : classFunctionSubmodule ℂ G ↦ (z : G → ℂ) t) (b.sum_repr x)
    simpa [b, x, hcoeff,
      irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply,
      smul_eq_mul] using hsum_t
  have hscaled :
      ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) •
        (∑ i, star ((π i).character s) • (π i).character) =
      (x : G → ℂ) := by
    -- Factor the common scalar `(c(s) / g)` out of the finite basis expansion.
    rw [Finset.smul_sum]
    simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using hsum
  have hcarrier_ne : (Nat.card ((ConjClasses.mk s).carrier) : ℂ) ≠ 0 := by
    let _ : Nonempty ((ConjClasses.mk s).carrier) :=
      ⟨⟨s, ConjClasses.mem_carrier_iff_mk_eq.mpr rfl⟩⟩
    exact_mod_cast Nat.card_pos.ne'
  have hcoeff_ne :
      ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) ≠ 0 := by
    exact div_ne_zero hcarrier_ne hg_ne
  have hcancel :
      (((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
          ((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier))) = 1 := by
    field_simp [hcarrier_ne, hg_ne]
  have hfinal :
      ∑ i, star ((π i).character s) • (π i).character =
        ((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) • (x : G → ℂ) := by
    -- Scalar multiplication by `(c(s) / g)` is injective, so it suffices to compare after
    -- multiplying both sides by that nonzero scalar.
    apply (smul_right_injective (G → ℂ) hcoeff_ne)
    calc
      ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) •
          (∑ i, star ((π i).character s) • (π i).character) =
        (x : G → ℂ) := hscaled
      _ =
        ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) •
          (((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) •
            (x : G → ℂ)) := by
        calc
          (x : G → ℂ) = (1 : ℂ) • (x : G → ℂ) := by simp
          _ =
            ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) •
              (((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) •
                (x : G → ℂ)) := by
            rw [smul_smul, hcancel]
  simpa [x, ConjClasses.indicator, Set.indicator, tsum_fintype] using hfinal

-- Proof sketch: evaluate
-- `sum_star_character_mul_character_eq_conjClassIndicator_mk_of_complete_family` at `t = s` and
-- use `conjClassIndicator_mk_self`.
/-- Evaluating the character-row orthogonality formula at `s` gives `g / c(s)`. -/
theorem sum_star_character_mul_character_self_eq_card_div_conjClass_card_of_complete_family
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (s : G) :
    ∑' i : ι, star ((π i).character s) * (π i).character s =
      (Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier) := by
  classical
  let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  let _ : Fintype ι := Fintype.ofFinite ι
  -- Evaluate the class-function identity at the element `s` itself.
  have hmain :=
    sum_star_character_mul_character_eq_conjClassIndicator_mk_of_complete_family
      (π := π) hπ_pairwise hπ_complete s
  simpa [tsum_fintype, Pi.smul_apply, Set.indicator,
    ConjClasses.mem_carrier_iff_mk_eq] using congrFun hmain s

-- Proof sketch: evaluate
-- `sum_star_character_mul_character_eq_conjClassIndicator_mk_of_complete_family` at `t` and use
-- `conjClassIndicator_mk_eq_zero_of_not_isConj`.
/-- If `t` is not conjugate to `s`, the same irreducible-character sum vanishes. -/
theorem sum_star_character_mul_character_eq_zero_of_not_isConj_of_complete_family
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {s t : G} (hst : ¬ IsConj t s) :
    ∑' i : ι, star ((π i).character s) * (π i).character t = 0 := by
  classical
  let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  let _ : Fintype ι := Fintype.ofFinite ι
  -- Evaluate the same class-function identity away from the conjugacy class of `s`.
  have hmain :=
    sum_star_character_mul_character_eq_conjClassIndicator_mk_of_complete_family
      (π := π) hπ_pairwise hπ_complete s
  have htnot : ConjClasses.mk t ≠ ConjClasses.mk s := by
    intro hmk
    exact hst (ConjClasses.mk_eq_mk_iff_isConj.mp hmk)
  simpa [tsum_fintype, Pi.smul_apply, Set.indicator,
    ConjClasses.mem_carrier_iff_mk_eq, htnot] using
    congrFun hmain t

end CompleteFamily

end

end Representation
