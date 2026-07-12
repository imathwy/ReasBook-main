import Mathlib
import LinearRepresentations_Serre_1977.Chap09.Corollary_9_9_2_2
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_6_4
import LinearRepresentations_Serre_1977.Chap13.Corollary_13_13_1_2
import LinearRepresentations_Serre_1977.Chap13.Theorem_13_13_1_3

open scoped BigOperators

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace Representation

open scoped Representation

section

variable {G : Type} [Group G] [Finite G]

local instance instFintypeG_Theorem_13_13_1_7 : Fintype G := Fintype.ofFinite G

local instance anonInstP_Theorem_13_13_1_7_1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

omit [Finite G] in
/-- Helper for Theorem 13-13.1-7: restriction of a rational virtual character to a subgroup
remains a rational virtual character. -/
lemma restrict_mem_characterRingOverField
    (H : Subgroup G) {χ : G → ℚ} (hχ : χ ∈ R[ℚ](G)) :
    (fun h : H ↦ χ h) ∈ R[ℚ](H) := by
  -- Bundle the ambient function so the existing restriction theorem applies directly.
  let χR : R[ℚ](G) := ⟨χ, hχ⟩
  simpa [χR] using Subgroup.restrict_mem_characterRingOverField ℚ H χR

/-- Helper for Theorem 13-13.1-7: a rational virtual character takes the same value on elements
that generate the same cyclic subgroup. -/
private lemma eq_of_zpowers_eq_of_mem_rational_character_ring
    {θ : R[ℚ](G)} {x y : G} (hxy : Subgroup.zpowers x = Subgroup.zpowers y) :
    θ x = θ y := by
  -- Rational characters are class functions, so conjugate elements have the same value.
  have hθClass : _root_.IsClassFunction (θ : G → ℚ) := by
    simpa using
      Representation.isClassFunction_of_mem_characterRingOverField (θ : G → ℚ) θ.property
  let θQ : ℚ ⊗R[ℚ](G) :=
    ⟨(θ : G → ℚ),
      Representation.mem_characterRingOverFieldScalarExtension_of_mem_characterRingOverField
        θ.property⟩
  -- The Chapter 13 criterion upgrades this to invariance under the `Γ_ℚ` power action.
  have hθpow :
      ∀ s (t : Γ_ℚ(G)), (θ : G → ℚ) s = (θ : G → ℚ) (s ^ t) :=
    (rational_valued_classFunction_mem_rational_character_ring_iff_power_invariant
      (θ : G → ℚ) hθClass).1 θQ.property
  have hzpowConj : (Subgroup.zpowers x).IsConj (Subgroup.zpowers y) := by
    simpa [hxy] using Subgroup.IsConj.refl (Subgroup.zpowers x)
  rcases (gammaRat_conjugate_iff_conjugate_zpowers x y).2 hzpowConj with ⟨t, hxt⟩
  calc
    (θ : G → ℚ) x = (θ : G → ℚ) (y ^ t) := by
      exact hθClass.eq_of_isConj hxt
    _ = (θ : G → ℚ) y := by
      symm
      exact hθpow y t

/-- Helper for Theorem 13-13.1-7: summing a restricted function over an internal subgroup agrees
with summing the ambient function over the corresponding mapped subgroup. -/
private lemma subgroup_sum_restrict_eq_sum_map_subtype
    (C : Subgroup G) (J : Subgroup C) (f : G → ℚ) :
    (∑ s : J, f s) = ∑ t : J.map C.subtype, f t := by
  classical
  -- Reindex the finite sum along the canonical equivalence `J ≃ J.map C.subtype`.
  simpa using
    (Fintype.sum_equiv (J.equivMapOfInjective C.subtype C.subtype_injective)
      (fun s : J ↦ f s) (fun t : J.map C.subtype ↦ f t) (fun s ↦ rfl))

/-- Helper for Theorem 13-13.1-7: a proper subgroup of a finite group has strictly smaller
cardinality. -/
private lemma proper_subgroup_natCard_lt {A : Type} [Group A] [Finite A] (J : Subgroup A)
    (hJ : J ≠ ⊤) : Nat.card J < Nat.card A := by
  let _ : Fintype A := Fintype.ofFinite A
  let _ : Fintype J := Fintype.ofFinite J
  -- A proper subgroup omits some element, so the subtype cardinality is strictly smaller.
  have hex : ∃ a : A, a ∉ J := by
    by_cases hall : ∀ a : A, a ∈ J
    · exact False.elim (hJ (by
        ext a
        simp [hall a]))
    · exact not_forall.mp hall
  rcases hex with ⟨a, ha⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simpa using (Fintype.card_subtype_lt (p := fun b : A ↦ b ∈ J) ha)

/-- Helper for Theorem 13-13.1-7: summing over the top subgroup is the same as summing over the
ambient finite group. -/
lemma sum_top_subgroup_eq_sum {A : Type} [Group A] [Finite A] (f : A → ℚ) :
    (∑ s : (⊤ : Subgroup A), f s) = ∑ a : A, f a := by
  let _ : Fintype A := Fintype.ofFinite A
  -- Reindex along the canonical equivalence between `⊤` and the ambient group.
  exact
    Fintype.sum_equiv (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv
      (fun s : (⊤ : Subgroup A) ↦ f s)
      (fun a : A ↦ f a) (fun s ↦ rfl)

/-- Helper for Theorem 13-13.1-7: on a finite cyclic group, vanishing subgroup sums force a
rational virtual character to be zero. -/
private lemma cyclic_rat_character_eq_zero_of_zero_subgroup_sums
    {A : Type} [Group A] [Finite A] [IsCyclic A]
    (θ : R[ℚ](A))
    (hsum : ∀ J : Subgroup A, ∑ s : J, θ s = 0) :
    θ = 0 := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (B : Type) (_ : Group B) (_ : Finite B) (_ : IsCyclic B),
      Nat.card B = n →
      ∀ ψ : R[ℚ](B),
        (∀ J : Subgroup B, ∑ s : J, ψ s = 0) → ψ = 0
  have hstrong : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih B _ _ _ hBcard ψ hsumψ
    -- First restrict to each proper cyclic subgroup generated by a nongenerator.
    have hzero_nongenerator :
        ∀ b : B, Subgroup.zpowers b ≠ (⊤ : Subgroup B) → ψ b = 0 := by
      intro b hb
      let J : Subgroup B := Subgroup.zpowers b
      have hlt : Nat.card J < n := by
        rw [← hBcard]
        exact proper_subgroup_natCard_lt J hb
      let ψJ : R[ℚ](J) :=
        ⟨fun j : J ↦ ψ j, restrict_mem_characterRingOverField J ψ.property⟩
      have hsumJ : ∀ K : Subgroup J, ∑ s : K, ψJ s = 0 := by
        intro K
        -- Transport the internal subgroup sum to the corresponding subgroup of `B`.
        calc
          ∑ s : K, ψJ s = ∑ t : K.map J.subtype, ψ t := by
            exact subgroup_sum_restrict_eq_sum_map_subtype J K (ψ : B → ℚ)
          _ = 0 := hsumψ (K.map J.subtype)
      have hψJ_zero : ψJ = 0 := by
        simpa using
          ih (Nat.card J) hlt J inferInstance inferInstance inferInstance rfl ψJ hsumJ
      have hb_mem : b ∈ J := Subgroup.mem_zpowers b
      have hvalue : ψJ ⟨b, hb_mem⟩ = 0 := by
        simp [hψJ_zero]
      simpa [ψJ] using hvalue
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic B)
    let gen : B → Prop := fun b ↦ Subgroup.zpowers b = (⊤ : Subgroup B)
    have hgenerator_value :
        ∀ b : B, gen b → ψ b = ψ g := by
      intro b hb
      have hzpow : Subgroup.zpowers b = Subgroup.zpowers g := by
        rw [hb, hg]
      simpa using
        eq_of_zpowers_eq_of_mem_rational_character_ring (θ := ψ) (x := b) (y := g) hzpow
    have hsum_all : ∑ b : B, ψ b = 0 := by
      have htop : ∑ s : (⊤ : Subgroup B), ψ s = 0 := hsumψ ⊤
      -- Convert the hypothesis on `⊤` into the total sum over the ambient cyclic group.
      have htop_sum : ∑ s : (⊤ : Subgroup B), ψ s = ∑ b : B, ψ b :=
        sum_top_subgroup_eq_sum (ψ : B → ℚ)
      exact htop_sum.symm ▸ htop
    have hsum_nongenerators :
        Finset.sum (Finset.univ.filter (fun b : B ↦ ¬ gen b)) (fun b ↦ ψ b) = 0 := by
      -- Every nongenerator vanishes after restricting to the proper subgroup it generates.
      refine Finset.sum_eq_zero ?_
      intro b hb
      exact hzero_nongenerator b (Finset.mem_filter.mp hb).2
    have hsum_generators :
        Finset.sum (Finset.univ.filter gen) (fun b ↦ ψ b) =
          ((Finset.univ.filter gen).card : ℚ) * ψ g := by
      -- All generators carry the same value, so the filtered sum is constant.
      calc
        Finset.sum (Finset.univ.filter gen) (fun b ↦ ψ b)
            = Finset.sum (Finset.univ.filter gen) (fun _ ↦ ψ g) := by
                refine Finset.sum_congr rfl ?_
                intro b hb
                exact hgenerator_value b (Finset.mem_filter.mp hb).2
        _ = ((Finset.univ.filter gen).card : ℚ) * ψ g := by
              simp [nsmul_eq_mul]
    have hfiltered_zero :
        Finset.sum (Finset.univ.filter gen) (fun b ↦ ψ b) = 0 := by
      -- Split the total sum into generators and nongenerators.
      have hsplit :=
        Finset.sum_filter_add_sum_filter_not Finset.univ gen (fun b : B ↦ ψ b)
      rw [hsum_nongenerators, add_zero, hsum_all] at hsplit
      exact hsplit
    have hcard_generators_ne_zero :
        ((Finset.univ.filter gen).card : ℚ) ≠ 0 := by
      apply Nat.cast_ne_zero.mpr
      refine Finset.card_ne_zero.mpr ?_
      exact ⟨g, by simp [gen, hg]⟩
    have hg_zero : ψ g = 0 := by
      have hprod_zero : ((Finset.univ.filter gen).card : ℚ) * ψ g = 0 := by
        rw [← hsum_generators]
        exact hfiltered_zero
      rcases mul_eq_zero.mp hprod_zero with hcard_zero | hvalue_zero
      · exact False.elim (hcard_generators_ne_zero hcard_zero)
      · exact hvalue_zero
    -- Every element is either a generator, hence equal to the common zero value, or a nongenerator.
    apply Subtype.ext
    ext b
    by_cases hb : gen b
    · simp [hgenerator_value b hb, hg_zero]
    · simp [hzero_nongenerator b hb]
  simpa using hstrong (Nat.card A) A inferInstance inferInstance inferInstance rfl θ hsum

-- Route correction: the pairing-wrapper proof route imported Theorem `13-13.1-6`, which already
-- occupied the public basename needed here. This file instead follows Serre's direct restriction
-- to `⟨g⟩` and cyclic-induction argument at the source owner `R[ℚ](G)`.
/-- Theorem 13-13.1-7: if a rational virtual character has sum `0` on every cyclic subgroup of
`G`, then it is the zero element of `R[ℚ](G)`. -/
private theorem rat_character_eq_zero_of_sum_eq_zero_on_cyclic_subgroups
    (θ : R[ℚ](G))
    (hsum : ∀ H : Subgroup.cyclicSubgroups G, ∑ s : H.1, θ s = 0) :
    θ = 0 := by
  -- Restrict to the cyclic subgroup generated by each element and apply the cyclic lemma there.
  apply Subtype.ext
  ext g
  let C : Subgroup G := Subgroup.zpowers g
  let θC : R[ℚ](C) :=
    ⟨fun c : C ↦ θ c, restrict_mem_characterRingOverField C θ.property⟩
  have hsumC : ∀ J : Subgroup C, ∑ s : J, θC s = 0 := by
    intro J
    have hmap_cyclic : IsCyclic (J.map C.subtype) := by
      exact ((J.equivMapOfInjective C.subtype C.subtype_injective).isCyclic).1 inferInstance
    -- Reindex the internal subgroup sum to the corresponding cyclic subgroup of `G`.
    calc
      ∑ s : J, θC s = ∑ t : J.map C.subtype, θ t := by
        exact subgroup_sum_restrict_eq_sum_map_subtype C J (θ : G → ℚ)
      _ = 0 := hsum ⟨J.map C.subtype, Subgroup.mem_cyclicSubgroups.2 hmap_cyclic⟩
  have hθC_zero : θC = 0 :=
    cyclic_rat_character_eq_zero_of_zero_subgroup_sums θC hsumC
  have hg_mem : g ∈ C := Subgroup.mem_zpowers g
  -- Evaluate the restricted vanishing theorem at the distinguished element `g ∈ ⟨g⟩`.
  have hvalue : θC ⟨g, hg_mem⟩ = 0 := by
    simp [hθC_zero]
  simpa [θC] using hvalue

end

end Representation
