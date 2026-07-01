import Mathlib
import Serre.GroupTheory.ConjClassesPower
import Serre.Chap01.Definition_1_1_4_1
import Serre.Chap02.Corollary_2_2_4_3
import Serre.Chap02.Theorem_2_2_5_3
import Serre.Chap13.Proposition_13_13_2_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open Representation
open scoped BigOperators

universe u v w

namespace ConjClasses

section

variable {G : Type} [Group G]

/-- A conjugacy class is even when it is fixed by inversion. -/
def IsEven (c : ConjClasses G) : Prop :=
  c⁻¹ = c

/-- The class of `g` is even exactly when `g` is conjugate to `g⁻¹`. -/
theorem isEven_mk_iff (g : G) :
    (ConjClasses.mk g).IsEven ↔ IsConj g g⁻¹ := by
  rw [IsEven, inv_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_comm]

end

end ConjClasses

section

variable {G : Type}

/-- Helper for Exercise 13-13.2-6: a complex class function valued in `ℝ` is fixed by complex
conjugation pointwise. -/
private theorem star_eq_of_isValuedInBaseField
    {χ : G → ℂ} (hχ : IsValuedInBaseField ℝ χ) (g : G) :
    star (χ g) = χ g := by
  -- Rewrite the source-valuedness hypothesis as a lift through `ℝ`, then evaluate at `g`.
  rw [Representation.isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range] at hχ
  rcases hχ with ⟨χR, hχR⟩
  rw [← congrFun hχR g]
  simp

end

section

variable {G : Type} [Group G] [Finite G]
variable {ι : Type v}

local instance : Fintype G := Fintype.ofFinite G
local instance : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
local instance : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

/-- Helper for Exercise 13-13.2-6: a complex character is a class function. -/
private theorem character_isClassFunction_local
    {V : Type w} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    _root_.IsClassFunction ρ.character := by
  -- Characters are constant on conjugacy classes.
  refine ⟨fun {x y} hxy ↦ ?_⟩
  exact Representation.char_eq_of_isConj (ρ := ρ) (ConjClasses.mk_eq_mk_iff_isConj.mp hxy)

/-- Helper for Exercise 13-13.2-6: bundle a complex character as an element of the class-function
submodule. -/
private abbrev characterClassFunction_local
    {V : Type w} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    classFunctionSubmodule ℂ G :=
  ⟨ρ.character, (mem_classFunctionSubmodule_iff ℂ _).2
    (character_isClassFunction_local (G := G) ρ)⟩

/-- Helper for Exercise 13-13.2-6: the pairing `⟪1, χ²⟫` is the pairing of the dual character
with `χ`. -/
private theorem pairing_trivial_square_eq_dual_pairing
    (ρ : FDRep ℂ G) :
    ⟪(1 : G → ℂ), ρ.character ^ 2⟫ =
      ⟪(fun s : G ↦ ρ.character s⁻¹), ρ.character⟫ := by
  -- Unfold the normalized pairing and use the dual-character identity at `s⁻¹`.
  rw [Representation.groupFunctionPairingOverField, Representation.groupFunctionPairingOverField]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  simp [pow_two]

/-- Helper for Exercise 13-13.2-6: if an irreducible character is real-valued, then `⟪1, χ²⟫ = 1`.
-/
private theorem pairing_trivial_character_sq_eq_one_of_real
    (ρ : FDRep ℂ G) [Simple ρ]
    (hreal : IsValuedInBaseField ℝ ρ.character) :
    ⟪(1 : G → ℂ), ρ.character ^ 2⟫ = 1 := by
  classical
  letI : Representation.IsIrreducible (ρ := ρ.ρ) := FDRep.isIrreducible_of_simple ρ
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  -- Real-valuedness turns `χ(s⁻¹)` into `χ(s)`, so the square-pairing becomes `⟪χ, χ⟫ = 1`.
  have hchar_inv : ∀ s : G, ρ.character s⁻¹ = ρ.character s := by
    intro s
    calc
      ρ.character s⁻¹ = (Representation.dual ρ.ρ).character s := by
        exact (Representation.char_dual (ρ := ρ.ρ) s).symm
      _ = star (ρ.character s) := by
        simpa using (Representation.char_dual_eq_star (ρ := ρ.ρ) s)
      _ = ρ.character s := star_eq_of_isValuedInBaseField hreal s
  have hpair_rewrite : ⟪(1 : G → ℂ), ρ.character ^ 2⟫ = ⟪ρ.character, ρ.character⟫ := by
    -- Compare the two pairings termwise after replacing `χ(s⁻¹)` by `χ(s)`.
    rw [Representation.groupFunctionPairingOverField, Representation.groupFunctionPairingOverField]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    simp [pow_two, hchar_inv s]
  rw [hpair_rewrite]
  calc
    ⟪ρ.character, ρ.character⟫ = Module.finrank ℂ (Representation.IntertwiningMap ρ.ρ ρ.ρ) :=
      Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        ℂ ρ.ρ ρ.ρ
    _ = 1 := by
      simp [Representation.IsIrreducible.finrank_intertwiningMap_self]

/-- Helper for Exercise 13-13.2-6: if an irreducible character is not real-valued, then
`⟪1, χ²⟫ = 0`. -/
private theorem pairing_trivial_character_sq_eq_zero_of_not_real
    (ρ : FDRep ℂ G) [Simple ρ]
    (hnot : ¬ IsValuedInBaseField ℝ ρ.character) :
    ⟪(1 : G → ℂ), ρ.character ^ 2⟫ = 0 := by
  let ρ' : Representation ℂ G ρ.V := ρ.ρ
  letI : Representation.IsIrreducible (ρ := ρ.ρ) := FDRep.isIrreducible_of_simple ρ
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have hnot_selfdual : ¬ Nonempty (ρ'.Equiv ρ'.dual) := by
    intro hselfdual
    exact hnot ((Representation.hasRealValuedCharacter_iff_nonempty_equiv_dual
      (ρ := ρ')).2 hselfdual)
  have hfinrank_zero : Module.finrank ℂ (ρ'.IntertwiningMap ρ'.dual) = 0 := by
    by_contra hzero
    letI : Nontrivial (ρ'.IntertwiningMap ρ'.dual) :=
      Module.nontrivial_of_finrank_pos (R := ℂ) (Nat.pos_of_ne_zero hzero)
    obtain ⟨f, hf_ne⟩ := exists_ne (0 : ρ'.IntertwiningMap ρ'.dual)
    -- A nonzero intertwiner from an irreducible representation is injective.
    have hf_or_zero : Function.Injective f ∨ f = 0 :=
      Representation.IsIrreducible.injective_or_eq_zero (ρ := ρ') (σ := ρ'.dual) (f := f)
    have hf_inj : Function.Injective f :=
      hf_or_zero.resolve_right hf_ne
    have hfinrank :
        Module.finrank ℂ ρ.V = Module.finrank ℂ (Module.Dual ℂ ρ.V) := by
      exact (Subspace.dual_finrank_eq (K := ℂ) (V := ρ.V)).symm
    have hf_surj : Function.Surjective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).mp hf_inj
    exact hnot_selfdual
      (Representation.nonempty_equiv_of_bijective_intertwiningMap
        (ρ1 := ρ') (ρ2 := ρ'.dual) f ⟨hf_inj, hf_surj⟩)
  -- Commute the pairing so that Schur orthogonality reads it as `Hom_G(ρ, ρᵛ)`.
  calc
    ⟪(1 : G → ℂ), ρ.character ^ 2⟫
        = ⟪ρ.character, ρ'.dual.character⟫ := by
          rw [pairing_trivial_square_eq_dual_pairing, Representation.groupFunctionPairing_comm]
          congr 1
          ext s
          exact (Representation.char_dual (ρ := ρ') s).symm
    _ = Module.finrank ℂ (ρ'.IntertwiningMap ρ'.dual) := by
          exact
            Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              ℂ ρ' ρ'.dual
    _ = 0 := by simp [hfinrank_zero]

/-- Helper for Exercise 13-13.2-6: every conjugacy class has nonzero cardinality. -/
private theorem conjClass_carrier_card_ne_zero
    (c : ConjClasses G) :
    (Nat.card c.carrier : ℂ) ≠ 0 := by
  -- Every conjugacy class contains a representative, so its carrier is nonempty.
  letI : Fintype c.carrier := Fintype.ofFinite c.carrier
  letI : Nonempty c.carrier := by
    obtain ⟨g, hg⟩ := ConjClasses.mk_surjective c
    subst hg
    exact ⟨⟨g, by simp [ConjClasses.mem_carrier_iff_mk_eq]⟩⟩
  rw [Nat.card_eq_fintype_card]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- Helper for Exercise 13-13.2-6: the irreducible-character coefficient of a conjugacy-class
indicator is the expected normalized class size times the starred character value. -/
private theorem indicator_pairing_with_irreducible_character
    (π : ι → FDRep ℂ G)
    (s : G) (i : ι) :
    ⟪(π i).character, (ConjClasses.mk s).indicatorClassFunction⟫ =
      ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) * star ((π i).character s) := by
  classical
  let T : Finset G := Finset.univ.filter fun t ↦ t ∈ (ConjClasses.mk s).carrier
  -- Collapse the pairing to the conjugacy class of `s`.
  have hsum_filter :
      ∑ t : G, (π i).character t⁻¹ * ((ConjClasses.mk s).indicatorClassFunction : G → ℂ) t =
        T.sum (fun t ↦ (π i).character t⁻¹) := by
    rw [show T = Finset.univ.filter (fun t ↦ t ∈ (ConjClasses.mk s).carrier) by rfl,
      Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro t _
    by_cases ht : t ∈ (ConjClasses.mk s).carrier
    · simp [ConjClasses.indicator, ht]
    · simp [ConjClasses.indicator, ht]
  have hsum_subtype :
      T.sum (fun t ↦ (π i).character t⁻¹) =
        ∑ t : (ConjClasses.mk s).carrier, (π i).character t.1⁻¹ := by
    change
      (Finset.univ.filter (fun t : G ↦ t ∈ (ConjClasses.mk s).carrier)).sum
          (fun t ↦ (π i).character t⁻¹) =
        ∑ t : (ConjClasses.mk s).carrier, (π i).character t.1⁻¹
    rw [← Finset.sum_subtype_eq_sum_filter]
    simp
  have hsum_const :
      (∑ t : (ConjClasses.mk s).carrier, (π i).character t.1⁻¹) =
        ∑ _ : (ConjClasses.mk s).carrier, star ((π i).character s) := by
    refine Finset.sum_congr rfl ?_
    intro t _
    have htconj : IsConj t.1 s :=
      (ConjClasses.mk_eq_mk_iff_isConj).1 <|
        ConjClasses.mem_carrier_iff_mk_eq.mp t.2
    calc
      (π i).character t.1⁻¹ = (Representation.dual (π i).ρ).character t.1 := by
        symm
        exact Representation.char_dual (ρ := (π i).ρ) t.1
      _ = (Representation.dual (π i).ρ).character s := by
        exact Representation.char_eq_of_isConj (ρ := (Representation.dual (π i).ρ)) htconj
      _ = star ((π i).character s) := by
        simpa using (Representation.char_dual_eq_star (ρ := (π i).ρ) s)
  have hsum_card :
      (∑ _ : (ConjClasses.mk s).carrier, star ((π i).character s)) =
        (Nat.card ((ConjClasses.mk s).carrier) : ℂ) * star ((π i).character s) := by
    simp [Nat.card_eq_fintype_card]
  -- Rewrite the normalized pairing as the average of this constant sum.
  calc
    ⟪(π i).character, (ConjClasses.mk s).indicatorClassFunction⟫
        = (Nat.card G : ℂ)⁻¹ *
            ∑ t : G, (π i).character t⁻¹ *
              ((ConjClasses.mk s).indicatorClassFunction : G → ℂ) t := by
            rw [Representation.groupFunctionPairingOverField, Nat.card_eq_fintype_card]
    _ = (Nat.card G : ℂ)⁻¹ * T.sum (fun t ↦ (π i).character t⁻¹) := by
          rw [hsum_filter]
    _ = (Nat.card G : ℂ)⁻¹ * ∑ t : (ConjClasses.mk s).carrier, (π i).character t.1⁻¹ := by
          rw [hsum_subtype]
    _ = (Nat.card G : ℂ)⁻¹ * ∑ _ : (ConjClasses.mk s).carrier, star ((π i).character s) := by
          rw [hsum_const]
    _ = (Nat.card G : ℂ)⁻¹ *
          ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) * star ((π i).character s)) := by
          rw [hsum_card]
    _ = ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
          star ((π i).character s) := by
          rw [div_eq_mul_inv]
          ring

/-- Helper for Exercise 13-13.2-6: the row-orthogonality formula for a conjugacy-class indicator,
rederived locally inside the current file. -/
private theorem groupFunctionPairing_sum_smul_left_local
    (s : Finset ι) (a : ι → ℂ) (φ : ι → G → ℂ) (ψ : G → ℂ) :
    Representation.groupFunctionPairingOverField ℂ (Finset.sum s fun i ↦ a i • φ i) ψ =
      Finset.sum s fun i ↦ a i * Representation.groupFunctionPairingOverField ℂ (φ i) ψ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum contributes nothing to the pairing.
      simp [Representation.groupFunctionPairingOverField]
  | @insert i s hi ih =>
      -- Pairing distributes over the inserted term and the remaining finite sum.
      rw [Finset.sum_insert hi, Representation.groupFunctionPairing_add_left,
        Representation.groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Exercise 13-13.2-6: evaluating a finite sum of bundled class functions distributes
over the sum and scalar multiplication. -/
private theorem classFunctionSubmodule_sum_smul_apply
    (s : Finset ι) (a : ι → ℂ) (φ : ι → classFunctionSubmodule ℂ G) (g : G) :
    ((((Finset.sum s fun i ↦ a i • φ i : classFunctionSubmodule ℂ G) : classFunctionSubmodule ℂ G) :
        G → ℂ) g) =
      Finset.sum s fun i ↦ a i * φ i g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s hi ih =>
      simp [Finset.sum_insert, hi, ih, Pi.smul_apply, smul_eq_mul, add_comm, add_left_comm,
        add_assoc]

/-- Helper for Exercise 13-13.2-6: the irreducible characters in a complete pairwise
nonisomorphic family are linearly independent in the class-function space. -/
private theorem complete_family_classFunction_linearIndependent_local
    (π : ι → FDRep ℂ G)
    [Fintype ι]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    LinearIndependent ℂ (fun i ↦ characterClassFunction_local (G := G) (π i).ρ) := by
  let v : ι → classFunctionSubmodule ℂ G := fun i ↦ characterClassFunction_local (π i).ρ
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  -- Pair a finite vanishing linear combination with one irreducible character to isolate its
  -- coefficient by orthogonality.
  rw [linearIndependent_iff']
  intro s a hsum i hi
  have hsum_fun :
      ∑ j ∈ s, a j • (π j).character = (0 : G → ℂ) := by
    have hsum' := congrArg (fun z : classFunctionSubmodule ℂ G ↦ (z : G → ℂ)) hsum
    simpa [v] using hsum'
  have hpair' :=
    congrArg (fun ψ : G → ℂ ↦ ⟪ψ, (π i).character⟫) hsum_fun
  have hpair :
      ⟪∑ j ∈ s, a j • (π j).character, (π i).character⟫ = (0 : ℂ) := by
    simpa [Representation.groupFunctionPairingOverField] using hpair'
  rw [groupFunctionPairing_sum_smul_left_local
    (s := s) (a := a) (φ := fun j ↦ (π j).character) (ψ := (π i).character)] at hpair
  rw [Finset.sum_eq_single i] at hpair
  · letI : Simple (π i) := hπ_complete.isSimple i
    have hself : ⟪(π i).character, (π i).character⟫ = (1 : ℂ) := by
      have hself_iso : Nonempty (π i ≅ π i) := ⟨Iso.refl _⟩
      simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hself_iso]
        using (FDRep.char_orthonormal (π i) (π i))
    simpa [hself] using hpair
  · intro j _ hji
    letI : Simple (π j) := hπ_complete.isSimple j
    letI : Simple (π i) := hπ_complete.isSimple i
    have hnot : ¬ Nonempty (π j ≅ π i) := hπ_pairwise hji
    have hij_pair : ⟪(π j).character, (π i).character⟫ = (0 : ℂ) := by
      simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hnot] using
        (FDRep.char_orthonormal (π j) (π i))
    rw [hij_pair, mul_zero]
  · intro hnot_mem
    exact (hnot_mem hi).elim

/-- Helper for Exercise 13-13.2-6: the index set of a complete pairwise nonisomorphic
irreducible family has the same cardinality as the class-function space dimension. -/
private theorem complete_family_classFunction_card_eq_finrank_local
    (π : ι → FDRep ℂ G)
    [Fintype ι]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Fintype.card ι = Module.finrank ℂ (classFunctionSubmodule ℂ G) := by
  have hcard :
      Fintype.card ι = Module.finrank ℂ (classFunctionSubmodule ℂ G) := by
    have hnat :
        Nat.card ι = Nat.card (ConjClasses G) := by
      simpa [PairwiseNonisomorphic] using
        (Representation.card_eq_card_conjClasses_of_complete_irreducible_family
          (π := π) hπ_complete.isSimple hπ_pairwise
          (fun τ hτ ↦ hπ_complete.exists_iso τ hτ))
    calc
      Fintype.card ι = Fintype.card (ConjClasses G) := by
        simpa [Nat.card_eq_fintype_card] using hnat
      _ = Module.finrank ℂ (ConjClasses G → ℂ) := by
        symm
        exact Module.finrank_fintype_fun_eq_card ℂ
      _ = Module.finrank ℂ (classFunctionSubmodule ℂ G) := by
        symm
        exact (classFunctionSubmodule.equivFun ℂ G).finrank_eq
  exact hcard

/-- Helper for Exercise 13-13.2-6: the irreducible characters in a complete pairwise
nonisomorphic family span the whole class-function space. -/
private theorem complete_family_classFunction_span_eq_top_local
    (π : ι → FDRep ℂ G)
    [Fintype ι]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Submodule.span ℂ (Set.range fun i ↦ characterClassFunction_local (G := G) (π i).ρ) = ⊤ := by
  -- The number of linearly independent characters matches the ambient dimension.
  exact
    LinearIndependent.span_eq_top_of_card_eq_finrank'
      (complete_family_classFunction_linearIndependent_local (π := π) hπ_pairwise hπ_complete)
      (complete_family_classFunction_card_eq_finrank_local (π := π) hπ_pairwise hπ_complete)

/-- Helper for Exercise 13-13.2-6: a complete pairwise nonisomorphic irreducible family gives a
basis of the complex class-function space. -/
private noncomputable def complete_family_classFunction_basis_local
    (π : ι → FDRep ℂ G)
    [Fintype ι]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Module.Basis ι ℂ (classFunctionSubmodule ℂ G) :=
  Module.Basis.mk
    (complete_family_classFunction_linearIndependent_local (π := π) hπ_pairwise hπ_complete)
    (complete_family_classFunction_span_eq_top_local (π := π) hπ_pairwise hπ_complete).ge

/-- Helper for Exercise 13-13.2-6: evaluating the complete-family basis returns the corresponding
irreducible character. -/
@[simp] private theorem complete_family_classFunction_basis_local_apply
    (π : ι → FDRep ℂ G)
    [Fintype ι]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι) :
    ((complete_family_classFunction_basis_local (π := π) hπ_pairwise hπ_complete i :
        classFunctionSubmodule ℂ G) : G → ℂ) =
      (π i).character := by
  -- The basis was built directly from the character family.
  ext g
  simp [complete_family_classFunction_basis_local, characterClassFunction_local, Module.Basis.mk_apply]
  rfl

/-- Helper for Exercise 13-13.2-6: the row-orthogonality formula for a conjugacy-class indicator,
rederived locally inside the current file. -/
private theorem sum_star_character_mul_character_eq_conjClassIndicator_mk_of_complete_family_local
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (s : G) :
    ∑' i : ι, star ((π i).character s) • (π i).character =
      ((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) •
        ((ConjClasses.mk s).indicator : G → ℂ) := by
  classical
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  let b :=
    complete_family_classFunction_basis_local (π := π)
      hπ_pairwise hπ_complete
  let x : classFunctionSubmodule ℂ G :=
    (ConjClasses.mk s).indicatorClassFunctionSubmodule (R := ℂ)
  have hb_apply (j : ι) :
      ((b j : classFunctionSubmodule ℂ G) : G → ℂ) = (π j).character := by
    simpa [b] using
      (complete_family_classFunction_basis_local_apply
        (π := π) hπ_pairwise hπ_complete j)
  have hcoeff (i : ι) :
      b.repr x i =
        ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
          star ((π i).character s) := by
    have hxsum :
        ∑ j : ι, b.repr x j • (π j).character = (x : G → ℂ) := by
      -- Expand the indicator class function in the irreducible-character basis and coerce to
      -- ordinary functions.
      have hxsum_basis :
          (((∑ j : ι, b.repr x j • b j : classFunctionSubmodule ℂ G) : classFunctionSubmodule ℂ G) :
              G → ℂ) =
            (x : G → ℂ) := by
        exact congrArg Subtype.val (b.sum_repr x)
      ext g
      have hpoint0 :
          ((((∑ j : ι, b.repr x j • b j : classFunctionSubmodule ℂ G) :
                classFunctionSubmodule ℂ G) : G → ℂ) g) =
            x g := by
        exact congrFun hxsum_basis g
      have hpoint :
          ∑ j : ι, b.repr x j * ((b j : classFunctionSubmodule ℂ G) g) = x g := by
        calc
          ∑ j : ι, b.repr x j * ((b j : classFunctionSubmodule ℂ G) g)
              = ((((∑ j : ι, b.repr x j • b j : classFunctionSubmodule ℂ G) :
                    classFunctionSubmodule ℂ G) : G → ℂ) g) := by
                  symm
                  simpa using
                    (classFunctionSubmodule_sum_smul_apply (G := G) (s := Finset.univ)
                      (a := fun j ↦ b.repr x j) (φ := fun j ↦ b j) g)
          _ = x g := hpoint0
      simpa [x, hb_apply] using hpoint
    have hdiag (j : ι) :
        ⟪(π j).character, (π j).character⟫ = (1 : ℂ) := by
      letI : Simple (π j) := hπ_complete.isSimple j
      have hself : Nonempty (π j ≅ π j) := ⟨Iso.refl _⟩
      simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hself] using
        (FDRep.char_orthonormal (π j) (π j))
    have horth {j k : ι} (hjk : j ≠ k) :
        ⟪(π j).character, (π k).character⟫ = (0 : ℂ) := by
      letI : Simple (π j) := hπ_complete.isSimple j
      letI : Simple (π k) := hπ_complete.isSimple k
      have hnot : ¬ Nonempty (π j ≅ π k) := hπ_pairwise hjk
      simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hnot] using
        (FDRep.char_orthonormal (π j) (π k))
    have hrepr_pairing : ⟪(x : G → ℂ), (π i).character⟫ = b.repr x i := by
      -- Pair the basis expansion with the `i`-th character and use orthogonality to isolate the
      -- `i`-th coefficient.
      calc
        ⟪(x : G → ℂ), (π i).character⟫
            = ⟪∑ j : ι, b.repr x j • (π j).character, (π i).character⟫ := by
                rw [hxsum]
        _ = ∑ j : ι, b.repr x j * ⟪(π j).character, (π i).character⟫ := by
              simpa using
                groupFunctionPairing_sum_smul_left_local
                  (s := Finset.univ) (a := fun j ↦ b.repr x j)
                  (φ := fun j ↦ (π j).character) (ψ := (π i).character)
        _ = b.repr x i * ⟪(π i).character, (π i).character⟫ := by
              refine Finset.sum_eq_single i ?_ ?_
              · intro j _ hji
                rw [horth hji, mul_zero]
              · intro hi
                exact (hi (Finset.mem_univ i)).elim
        _ = b.repr x i := by
              simp [hdiag i]
    -- The coefficient of the conjugacy-class indicator is the pairing with the corresponding
    -- irreducible character, which the previous lemma computes directly.
    calc
      b.repr x i = ⟪(x : G → ℂ), (π i).character⟫ := hrepr_pairing.symm
      _ = ⟪(π i).character, x⟫ := by
            rw [Representation.groupFunctionPairing_comm]
      _ = ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
            star ((π i).character s) := by
            simpa [x] using
              (indicator_pairing_with_irreducible_character
                (π := π) (s := s) (i := i))
  have hx :
      ∑ i : ι,
          (((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
              star ((π i).character s)) •
            (π i).character =
        ((ConjClasses.mk s).indicator : G → ℂ) := by
    have hsum :
        ∑ i : ι, b.repr x i • (π i).character =
          ((ConjClasses.mk s).indicator : G → ℂ) := by
      -- Expand the indicator class function in the irreducible-character basis and coerce to
      -- ordinary functions.
      have hsum_basis :
          (((∑ i : ι, b.repr x i • b i : classFunctionSubmodule ℂ G) : classFunctionSubmodule ℂ G) :
              G → ℂ) =
            ((ConjClasses.mk s).indicator : G → ℂ) := by
        exact congrArg Subtype.val (b.sum_repr x)
      ext g
      have hpoint0 :
          ((((∑ i : ι, b.repr x i • b i : classFunctionSubmodule ℂ G) :
                classFunctionSubmodule ℂ G) : G → ℂ) g) =
            ((ConjClasses.mk s).indicator : G → ℂ) g := by
        exact congrFun hsum_basis g
      have hpoint :
          ∑ i : ι, b.repr x i * ((b i : classFunctionSubmodule ℂ G) g) =
            ((ConjClasses.mk s).indicator : G → ℂ) g := by
        calc
          ∑ i : ι, b.repr x i * ((b i : classFunctionSubmodule ℂ G) g)
              = ((((∑ i : ι, b.repr x i • b i : classFunctionSubmodule ℂ G) :
                    classFunctionSubmodule ℂ G) : G → ℂ) g) := by
                  symm
                  simpa using
                    (classFunctionSubmodule_sum_smul_apply (G := G) (s := Finset.univ)
                      (a := fun i ↦ b.repr x i) (φ := fun i ↦ b i) g)
          _ = ((ConjClasses.mk s).indicator : G → ℂ) g := hpoint0
      simpa [hb_apply] using hpoint
    simpa [hcoeff] using hsum
  have hcarrier_ne : (Nat.card ((ConjClasses.mk s).carrier) : ℂ) ≠ 0 :=
    conjClass_carrier_card_ne_zero (G := G) (ConjClasses.mk s)
  have hcancel :
      ((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) *
          (((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G)) =
        1 := by
    field_simp [hcarrier_ne, Nat.cast_ne_zero.mpr Nat.card_pos.ne']
  -- Scale the basis expansion pointwise by the reciprocal coefficient to recover the standard
  -- row sum.
  ext t
  have hxt :
      ∑ i : ι,
          (((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
              star ((π i).character s)) *
            (π i).character t =
        (ConjClasses.mk s).indicator t := by
    simpa [Pi.smul_apply] using congrFun hx t
  have hsum_cancel :
      ((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) *
          (∑ i : ι,
            (((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
                star ((π i).character s)) *
              (π i).character t) =
        ∑ i : ι, star ((π i).character s) * (π i).character t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    calc
      ((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) *
          ((((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
              star ((π i).character s)) *
            (π i).character t)
          = ((((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) *
                (((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G))) *
              star ((π i).character s)) *
            (π i).character t := by
              ring
      _ = star ((π i).character s) * (π i).character t := by
            rw [hcancel]
            ring
  calc
    (∑' i : ι, star ((π i).character s) • (π i).character) t
        = ∑ i : ι, star ((π i).character s) * (π i).character t := by
            simp [Pi.smul_apply]
    _ = ((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) *
          ((ConjClasses.mk s).indicator t) := by
            rw [← hsum_cancel, hxt]
    _ = (((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) •
          ((ConjClasses.mk s).indicator : G → ℂ)) t := by
            simp [Pi.smul_apply]

/-- Helper for Exercise 13-13.2-6: on an even conjugacy class, every irreducible character value
is fixed by complex conjugation. -/
private theorem star_character_eq_self_of_isEven_conjClass
    (π : ι → FDRep ℂ G)
    (i : ι) (s : G) (hs : (ConjClasses.mk s).IsEven) :
    star ((π i).character s) = (π i).character s := by
  have hsconj : IsConj s s⁻¹ := (ConjClasses.isEven_mk_iff s).1 hs
  -- Evenness identifies `s` with `s⁻¹`, so `χ(s)` equals its dual/conjugate value.
  calc
    star ((π i).character s) = (Representation.dual (π i).ρ).character s := by
      symm
      simpa using (Representation.char_dual_eq_star (ρ := (π i).ρ) s)
    _ = (π i).character s⁻¹ := by
      exact Representation.char_dual (ρ := (π i).ρ) s
    _ = (π i).character s := by
      exact Representation.char_eq_of_isConj (ρ := (π i).ρ) hsconj.symm

/-- Helper for Exercise 13-13.2-6: on an even class, the sum `∑ χ_i(s)^2` has the expected
character-table value. -/
private theorem sum_character_sq_eq_card_div_conjClass_card_of_isEven
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (s : G) (hs : (ConjClasses.mk s).IsEven) :
    ∑' i : ι, (π i).character s * (π i).character s =
      (Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier) := by
  classical
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  have hindicator : ((ConjClasses.mk s).indicator : G → ℂ) s = 1 := by
    simp [ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq]
  have heval :
      ∑ i : ι, star ((π i).character s) * (π i).character s =
        (Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier) := by
    simpa [Pi.smul_apply, smul_eq_mul, hindicator, mul_assoc] using
      congrFun
        (sum_star_character_mul_character_eq_conjClassIndicator_mk_of_complete_family_local
          π hπ_pairwise hπ_complete s)
        s
  -- Evaluate the local row-orthogonality identity at the diagonal point `s`.
  calc
    ∑' i : ι, (π i).character s * (π i).character s
        = ∑ i : ι, (π i).character s * (π i).character s := by
            simp
    _ = ∑ i : ι, star ((π i).character s) * (π i).character s := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [star_character_eq_self_of_isEven_conjClass π i s hs]
    _ = (Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier) := heval

/-- Helper for Exercise 13-13.2-6: off an even class, the sum `∑ χ_i(s)^2` vanishes. -/
private theorem sum_character_sq_eq_zero_of_not_isEven
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (s : G) (hs : ¬ (ConjClasses.mk s).IsEven) :
    ∑' i : ι, (π i).character s * (π i).character s = 0 := by
  classical
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  have hmk_ne : ConjClasses.mk s ≠ ConjClasses.mk s⁻¹ := by
    intro hmk
    exact hs <| by
      rw [ConjClasses.IsEven, ConjClasses.inv_mk]
      simpa using hmk.symm
  have hindicator : ((ConjClasses.mk s⁻¹).indicator : G → ℂ) s = 0 := by
    simp [ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq, hmk_ne]
  have hstar_inv (i : ι) : star ((π i).character s⁻¹) = (π i).character s := by
    -- The source point `s⁻¹` turns the starred row coefficient back into `χ(s)`.
    calc
      star ((π i).character s⁻¹) = (Representation.dual (π i).ρ).character s⁻¹ := by
        symm
        simpa using (Representation.char_dual_eq_star (ρ := (π i).ρ) s⁻¹)
      _ = (π i).character (s⁻¹)⁻¹ := by
        exact Representation.char_dual (ρ := (π i).ρ) s⁻¹
      _ = (π i).character s := by
        simp
  have heval :
      ∑ i : ι, star ((π i).character s⁻¹) * (π i).character s = (0 : ℂ) := by
    simpa [Pi.smul_apply, smul_eq_mul, hindicator, mul_assoc] using
      congrFun
        (sum_star_character_mul_character_eq_conjClassIndicator_mk_of_complete_family_local
          π hπ_pairwise hπ_complete s⁻¹)
        s
  -- Evaluate the same row-orthogonality identity at a point outside the source conjugacy class.
  calc
    ∑' i : ι, (π i).character s * (π i).character s
        = ∑ i : ι, (π i).character s * (π i).character s := by
            simp
    _ = ∑ i : ι, star ((π i).character s⁻¹) * (π i).character s := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hstar_inv i]
    _ = 0 := heval

/-- Helper for Exercise 13-13.2-6: summing a function constant on conjugacy classes over `G`
equals summing it over conjugacy classes weighted by class size. -/
private theorem sum_over_group_eq_sum_over_conjClasses
    (a : ConjClasses G → ℂ) :
    ∑ x : G, a (ConjClasses.mk x) =
      ∑ c : ConjClasses G, (Nat.card c.carrier : ℂ) * a c := by
  classical
  let F : G → ConjClasses G := ConjClasses.mk
  have himage : (Finset.univ : Finset G).image F = (Finset.univ : Finset (ConjClasses G)) := by
    ext c
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      exact Finset.mem_image.mpr ⟨g, by simp [F]⟩
  have hfiberwise :
      ∑ c ∈ (Finset.univ : Finset G).image F,
          ∑ x ∈ (Finset.univ : Finset G) with F x = c, a (F x)
        =
      ∑ x : G, a (F x) := by
    simpa [F] using
      (Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset G))
        (t := (Finset.univ : Finset G).image F)
        (g := F)
        (fun x hx ↦ Finset.mem_image_of_mem F hx)
        (fun x : G ↦ a (F x)))
  have hcoeff (c : ConjClasses G) :
      ∑ x ∈ (Finset.univ : Finset G) with F x = c, a (F x) =
        (Nat.card c.carrier : ℂ) * a c := by
    let fiber : Finset G := (Finset.univ : Finset G).filter (fun x ↦ F x = c)
    have hfiber_mem : ∀ x : G, x ∈ fiber ↔ x ∈ c.carrier := by
      intro x
      simp [fiber, F, ConjClasses.mem_carrier_iff_mk_eq]
    have hsum_const :
        ∑ x ∈ fiber, a (F x) = (fiber.card : ℂ) * a c := by
      calc
        ∑ x ∈ fiber, a (F x) = ∑ x ∈ fiber, a c := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hx' : F x = c := by
            simpa [F, ConjClasses.mem_carrier_iff_mk_eq] using (hfiber_mem x).1 hx
          simp [hx']
        _ = fiber.card • a c := by
          rw [Finset.sum_const]
        _ = (fiber.card : ℂ) * a c := by
          rw [nsmul_eq_mul]
    have hcard :
        fiber.card = Nat.card c.carrier := by
      let _ : Fintype c.carrier := Fintype.ofFinset fiber (hfiber_mem ·)
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_ofFinset fiber (hfiber_mem ·)).symm
    calc
      ∑ x ∈ (Finset.univ : Finset G) with F x = c, a (F x) = ∑ x ∈ fiber, a (F x) := by
        rfl
      _ = (fiber.card : ℂ) * a c := hsum_const
      _ = (Nat.card c.carrier : ℂ) * a c := by
        rw [hcard]
  -- Partition `G` by the fibers of `ConjClasses.mk`, i.e. by its conjugacy classes.
  calc
    ∑ x : G, a (ConjClasses.mk x)
        = ∑ c ∈ (Finset.univ : Finset G).image F,
            ∑ x ∈ (Finset.univ : Finset G) with F x = c, a (F x) := by
          simpa [F] using hfiberwise.symm
    _ = ∑ c : ConjClasses G, (Nat.card c.carrier : ℂ) * a c := by
          rw [himage]
          refine Finset.sum_congr rfl ?_
          intro c hc
          exact hcoeff c

-- Proof sketch: the intended route is to study the inversion endomorphism of the class-function
-- space, compute its trace in the irreducible-character basis, and compute the same trace in the
-- conjugacy-class-indicator basis.
/-- Exercise 13-13.2-6 (1): for a complete family of pairwise nonisomorphic irreducible complex
representations of `G`, the number of indices whose character is real-valued equals the number of
even conjugacy classes of `G`. -/
theorem card_realValued_irreducible_characters_eq_card_even_conjClasses
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Nat.card { i // IsValuedInBaseField ℝ (π i).character } =
      Nat.card { c : ConjClasses G // c.IsEven } := by
  classical
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- Route correction: the earlier quotient-by-centralizer route was invalid because centralizers
  -- of singletons need not be normal. The stable route here is the source-faithful orthogonality
  -- argument: identify `⟪1, χ_i^2⟫` with the real-valued indicator on irreducibles, then rewrite
  -- the same total by the row orthogonality formula evaluated at `(s⁻¹, s)`.
  have hreal_count :
      ((Nat.card { i // IsValuedInBaseField ℝ (π i).character } : ℕ) : ℂ) =
        ∑ i : ι, ⟪(1 : G → ℂ), (π i).character ^ 2⟫ := by
    -- Sum the per-character indicator `⟪1, χ_i^2⟫ = 1` or `0`.
    calc
      ((Nat.card { i // IsValuedInBaseField ℝ (π i).character } : ℕ) : ℂ) =
          ∑ i : ι, if IsValuedInBaseField ℝ (π i).character then (1 : ℂ) else 0 := by
            rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
            simp
      _ = ∑ i : ι, ⟪(1 : G → ℂ), (π i).character ^ 2⟫ := by
            apply Fintype.sum_congr
            intro i
            letI : Simple (π i) := hπ_complete.isSimple i
            by_cases hreal : IsValuedInBaseField ℝ (π i).character
            · rw [if_pos hreal]
              symm
              exact pairing_trivial_character_sq_eq_one_of_real (ρ := π i) hreal
            · rw [if_neg hreal]
              symm
              exact pairing_trivial_character_sq_eq_zero_of_not_real (ρ := π i) hreal
  let a : ConjClasses G → ℂ := fun c ↦
    if c.IsEven then (Nat.card G : ℂ) / Nat.card c.carrier else 0
  have hrow_sums :
      ∑ x : G, ∑ i : ι, (π i).character x * (π i).character x =
        ∑ x : G, a (ConjClasses.mk x) := by
    -- Replace each inner character sum by the even/non-even row-orthogonality value.
    apply Fintype.sum_congr
    intro x
    by_cases hx : (ConjClasses.mk x).IsEven
    · simpa [a, hx] using
        (sum_character_sq_eq_card_div_conjClass_card_of_isEven
          π hπ_pairwise hπ_complete x hx)
    · simpa [a, hx] using
        (sum_character_sq_eq_zero_of_not_isEven
          π hπ_pairwise hπ_complete x hx)
  have hclass_side :
      ((Nat.card { i // IsValuedInBaseField ℝ (π i).character } : ℕ) : ℂ) =
        (Nat.card G : ℂ)⁻¹ * ∑ x : G, a (ConjClasses.mk x) := by
    -- Rewrite the total Frobenius-Schur count as a sum over group elements.
    calc
      ((Nat.card { i // IsValuedInBaseField ℝ (π i).character } : ℕ) : ℂ)
          = ∑ i : ι, ⟪(1 : G → ℂ), (π i).character ^ 2⟫ := hreal_count
      _ = ∑ i : ι,
            ((Nat.card G : ℂ)⁻¹ *
              ∑ x : G, (π i).character x * (π i).character x) := by
            apply Fintype.sum_congr
            intro i
            rw [Representation.groupFunctionPairingOverField]
            simp [pow_two]
      _ = (Nat.card G : ℂ)⁻¹ *
            ∑ i : ι, ∑ x : G, (π i).character x * (π i).character x := by
            rw [← Finset.mul_sum]
      _ = (Nat.card G : ℂ)⁻¹ *
            ∑ x : G, ∑ i : ι, (π i).character x * (π i).character x := by
            rw [Finset.sum_comm]
      _ = (Nat.card G : ℂ)⁻¹ * ∑ x : G, a (ConjClasses.mk x) := by
            rw [hrow_sums]
  have hcard_even_complex :
      ((Nat.card { i // IsValuedInBaseField ℝ (π i).character } : ℕ) : ℂ) =
        (Nat.card { c : ConjClasses G // c.IsEven } : ℂ) := by
    calc
      ((Nat.card { i // IsValuedInBaseField ℝ (π i).character } : ℕ) : ℂ)
          = (Nat.card G : ℂ)⁻¹ * ∑ x : G, a (ConjClasses.mk x) := hclass_side
      _ = (Nat.card G : ℂ)⁻¹ *
            ∑ c : ConjClasses G, (Nat.card c.carrier : ℂ) * a c := by
            rw [sum_over_group_eq_sum_over_conjClasses]
      _ = ∑ c : ConjClasses G, if c.IsEven then (1 : ℂ) else 0 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro c hc
            by_cases hceven : c.IsEven
            · have hc_ne : (Nat.card c.carrier : ℂ) ≠ 0 :=
                conjClass_carrier_card_ne_zero (G := G) c
              have hc_ne' : ((Fintype.card c.carrier : ℂ)) ≠ 0 := by
                simpa [Nat.card_eq_fintype_card] using hc_ne
              have hcancel :
                  ((Fintype.card c.carrier : ℂ) * (Fintype.card c.carrier : ℂ)⁻¹) = (1 : ℂ) := by
                exact mul_inv_cancel₀ hc_ne'
              simp [a, hceven, div_eq_mul_inv, mul_left_comm]
              exact hcancel
            · simp [a, hceven]
      _ = (Nat.card { c : ConjClasses G // c.IsEven } : ℂ) := by
            rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
            simp
  exact_mod_cast hcard_even_complex

end

section

variable {G : Type} [Group G]

/-- Helper for Exercise 13-13.2-6: inversion preserves the carrier of an even conjugacy class. -/
private theorem inv_mem_carrier_of_isEven
    {c : ConjClasses G} (hc : c.IsEven) {x : G} (hx : x ∈ c.carrier) :
    x⁻¹ ∈ c.carrier := by
  -- Rewrite membership in terms of equality of conjugacy classes, then invert that equality.
  apply ConjClasses.mem_carrier_iff_mk_eq.mpr
  calc
    ConjClasses.mk x⁻¹ = (ConjClasses.mk x)⁻¹ := by simp [ConjClasses.inv_mk]
    _ = c⁻¹ := by rw [ConjClasses.mem_carrier_iff_mk_eq.mp hx]
    _ = c := hc

/-- Helper for Exercise 13-13.2-6: inversion defines a permutation of the carrier of an even
conjugacy class. -/
private theorem carrier_inv_bijective_of_even_class
    {c : ConjClasses G} (hc : c.IsEven) :
    Function.Bijective
      (fun x : c.carrier ↦
        ((⟨x.1⁻¹, inv_mem_carrier_of_isEven hc x.2⟩ : c.carrier))) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hval : x.1⁻¹ = y.1⁻¹ := congrArg Subtype.val hxy
    simpa using congrArg Inv.inv hval
  · intro x
    refine ⟨((⟨x.1⁻¹, inv_mem_carrier_of_isEven hc x.2⟩ : c.carrier)), ?_⟩
    apply Subtype.ext
    simp

/-- Helper for Exercise 13-13.2-6: inversion defines a permutation of the carrier of an even
conjugacy class. -/
private noncomputable def carrier_inv_perm_of_even_class
    {c : ConjClasses G} (hc : c.IsEven) :
    Equiv.Perm c.carrier :=
  Equiv.ofBijective
    (fun x : c.carrier ↦ ((⟨x.1⁻¹, inv_mem_carrier_of_isEven hc x.2⟩ : c.carrier)))
    (carrier_inv_bijective_of_even_class hc)

/-- Helper for Exercise 13-13.2-6: in odd order, the Frobenius-Schur indicator is the pairing
with the trivial character. -/
private theorem frobenius_schur_indicator_eq_pairing_trivial_of_odd_order
    [Finite G] (hodd : Odd (Nat.card G)) (χ : G → ℂ) :
    Representation.frobeniusSchurIndicator χ = ⟪1, χ⟫ := by
  letI : Fintype G := Fintype.ofFinite G
  let e : G ≃ G :=
    Equiv.ofBijective (fun g : G ↦ g ^ (2 : ℕ))
      (Nat.Coprime.pow_left_bijective (G := G) (n := 2) (Odd.coprime_two_right hodd))
  -- Reindex the square-sum along the bijection `g ↦ g ^ 2`.
  rw [Representation.frobeniusSchurIndicator_eq_card_inv_sum_sq]
  have hsum : ∑ s : G, χ (s ^ 2) = ∑ s : G, χ s := by
    simpa [e] using (Equiv.sum_comp e χ)
  rw [hsum]
  simp [Representation.groupFunctionPairingOverField, Nat.card_eq_fintype_card]

/-- Helper for Exercise 13-13.2-6: a nontrivial irreducible character is orthogonal to the
trivial character. -/
private theorem groupFunctionPairing_trivial_character_eq_zero_of_not_trivial
    [Finite G] (ρ : FDRep ℂ G) [Simple ρ]
    (hnottrivial : ¬ Nonempty (FDRep.of (Representation.trivial ℂ G ℂ) ≅ ρ)) :
    ⟪1, ρ.character⟫ = 0 := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Representation.IsIrreducible ρ.ρ := FDRep.isIrreducible_of_simple ρ
  letI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  haveI : (Representation.trivial ℂ G ℂ).IsIrreducible := by
    simpa using
      isIrreducible_of_finrank_eq_one (ρ := Representation.trivial ℂ G ℂ)
        (by simp : Module.finrank ℂ ℂ = 1)
  have hnottrivial_rep : ¬ Nonempty ((Representation.trivial ℂ G ℂ).Equiv ρ.ρ) := by
    intro hEq
    rcases hEq with ⟨e⟩
    exact hnottrivial ⟨by simpa using e.toFDRepIso⟩
  -- Orthogonality identifies the pairing with the zero intertwining-space dimension.
  have hpair :
      ⟪(Representation.trivial ℂ G ℂ).character, ρ.character⟫ = 0 :=
    Representation.groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
      (K := ℂ) (Representation.trivial ℂ G ℂ) ρ.ρ hnottrivial_rep
  have htrivchar : (Representation.trivial ℂ G ℂ).character = 1 := by
    ext g
    simp [Representation.character, Representation.trivial]
  simpa [htrivchar] using hpair

/-- Helper for Exercise 13-13.2-6: in an odd-order finite group, squaring is injective, so the
only element with square `1` is `1`. -/
theorem eq_one_of_sq_eq_one_of_odd_order
    [Finite G] (hodd : Odd (Nat.card G)) {x : G} (hx : x ^ (2 : ℕ) = 1) :
    x = 1 := by
  -- The squaring map is bijective because `2` is coprime to `|G|`.
  let e : G ≃ G :=
    Equiv.ofBijective (fun g : G ↦ g ^ (2 : ℕ))
      (Nat.Coprime.pow_left_bijective (G := G) (n := 2) (Odd.coprime_two_right hodd))
  have hx' : e x = e 1 := by
    simp [e, hx]
  exact e.injective hx'

-- Proof sketch: choose an odd-order-compatible route from the evenness of the class to a
-- self-inverse representative, then apply `eq_one_of_sq_eq_one_of_odd_order`.
/-- Exercise 13-13.2-6 (2): if `G` has odd order, then the only even conjugacy class is the class
of the identity. -/
theorem isEven_conjClass_eq_one_of_odd_order
    (hodd : Odd (Nat.card G)) {c : ConjClasses G} (hc : c.IsEven) :
    c = 1 := by
  letI : Finite G := by
    classical
    by_cases hfin : Finite G
    · exact hfin
    · exfalso
      letI : Infinite G := not_finite_iff_infinite.mp hfin
      simp at hodd
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype c.carrier := Fintype.ofFinite c.carrier
  have hc_card_dvd : Nat.card c.carrier ∣ Nat.card G := by
    obtain ⟨g, hg⟩ := ConjClasses.mk_surjective c
    subst hg
    letI : Fintype (ConjClasses.mk g).carrier := Fintype.ofFinite (ConjClasses.mk g).carrier
    letI : Fintype (MulAction.stabilizer (ConjAct G) g) :=
      Fintype.ofFinite (MulAction.stabilizer (ConjAct G) g)
    have hstabilizer_dvd : Nat.card (MulAction.stabilizer (ConjAct G) g) ∣ Nat.card G := by
      simpa using
        (Subgroup.card_subgroup_dvd_card (MulAction.stabilizer (ConjAct G) g))
    refine ⟨Nat.card (MulAction.stabilizer (ConjAct G) g), ?_⟩
    have hcarrier :
        Nat.card (ConjClasses.mk g).carrier =
          Nat.card G / Nat.card (MulAction.stabilizer (ConjAct G) g) := by
      calc
        Nat.card (ConjClasses.mk g).carrier
            = Fintype.card (ConjClasses.mk g).carrier := Nat.card_eq_fintype_card
        _ = Fintype.card G / Fintype.card (MulAction.stabilizer (ConjAct G) g) := by
              simpa using (ConjClasses.card_carrier (G := G) g)
        _ = Fintype.card G / Nat.card (MulAction.stabilizer (ConjAct G) g) := by
              rw [Nat.card_eq_fintype_card]
        _ = Nat.card G / Nat.card (MulAction.stabilizer (ConjAct G) g) := by
              rw [← Nat.card_eq_fintype_card]
    rw [hcarrier]
    exact (Nat.div_mul_cancel hstabilizer_dvd).symm
  have hc_odd : Odd (Nat.card c.carrier) :=
    hodd.of_dvd_nat hc_card_dvd
  let σ : Equiv.Perm c.carrier := carrier_inv_perm_of_even_class hc
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hσ_eval (x : c.carrier) : σ (σ x) = x := by
    apply Subtype.ext
    simp [σ, carrier_inv_perm_of_even_class]
  have hσ : σ ^ 2 = 1 := by
    ext x
    -- Inversion is an involution on the carrier.
    simpa [pow_two] using congrArg Subtype.val (hσ_eval x)
  obtain ⟨x, hxfix⟩ :=
    Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1)
      (by
        simpa [Nat.card_eq_fintype_card] using hc_odd.not_two_dvd_nat)
      (by simpa using hσ)
  have hx_inv : x.1⁻¹ = x.1 := by
    simpa [σ, carrier_inv_perm_of_even_class] using congrArg Subtype.val hxfix
  have hx_sq : x.1 ^ (2 : ℕ) = 1 := by
    calc
      x.1 ^ (2 : ℕ) = x.1 * x.1 := by rw [pow_two]
      _ = x.1⁻¹ * x.1 := by rw [hx_inv]
      _ = 1 := by simp
  have hx_one : x.1 = 1 := eq_one_of_sq_eq_one_of_odd_order hodd hx_sq
  have hx_class : ConjClasses.mk x.1 = c :=
    ConjClasses.mem_carrier_iff_mk_eq.mp x.2
  -- The fixed point is the identity, so the whole class is the identity class.
  have : c = ConjClasses.mk (1 : G) := by
    simpa [hx_one] using hx_class.symm
  simpa using this

-- Proof sketch: rewrite the Frobenius-Schur indicator as the pairing with the trivial character in
-- odd order, then combine Proposition `13-13.2-4` with orthogonality against the trivial
-- character.
/-- Exercise 13-13.2-6 (3): if `G` has odd order, then an irreducible complex character of `G` is
real-valued exactly when it is the unit character (Burnside). -/
theorem hasRealValuedCharacter_iff_character_eq_trivial_of_odd_order
    (hodd : Odd (Nat.card G))
    (ρ : FDRep ℂ G) [Simple ρ] :
    IsValuedInBaseField ℝ ρ.character ↔
      ρ.character = (trivial ℂ G ℂ).character := by
  letI : Finite G := by
    classical
    by_cases hfin : Finite G
    · exact hfin
    · exfalso
      letI : Infinite G := not_finite_iff_infinite.mp hfin
      simp at hodd
  letI : Representation.IsIrreducible ρ.ρ := FDRep.isIrreducible_of_simple ρ
  constructor
  · intro hreal
    by_contra hneq
    have hnottrivial : ¬ Nonempty (FDRep.of (Representation.trivial ℂ G ℂ) ≅ ρ) := by
      intro htriv
      rcases htriv with ⟨e⟩
      exact hneq (by simpa using (FDRep.char_iso e).symm)
    have hpair_zero :
        ⟪1, ρ.character⟫ = 0 :=
      groupFunctionPairing_trivial_character_eq_zero_of_not_trivial (ρ := ρ) hnottrivial
    have hindicator_zero :
        Representation.frobeniusSchurIndicator ρ.character = 0 := by
      rw [frobenius_schur_indicator_eq_pairing_trivial_of_odd_order hodd]
      exact hpair_zero
    have hnot_real :
        ¬ IsValuedInBaseField ℝ ρ.character :=
      (Representation.isTypeOne_iff_frobeniusSchurIndicator_eq_zero (ρ := ρ.ρ)).2 hindicator_zero
    exact hnot_real hreal
  · intro htriv
    rw [htriv, Representation.isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range]
    refine ⟨1, ?_⟩
    ext g
    simp [Representation.character, Representation.trivial]

end
