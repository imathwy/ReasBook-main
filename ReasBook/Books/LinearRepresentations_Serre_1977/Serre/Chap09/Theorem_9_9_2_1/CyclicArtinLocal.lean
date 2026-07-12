import Mathlib
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension

open scoped BigOperators Pointwise Representation SubgroupInduction
open Representation

noncomputable section

namespace Subgroup

section

variable {G : Type} [Group G] [Finite G]

/-- Helper for Exercise 9-9.4-3: the finite family of cyclic subgroups of a finite group. -/
abbrev theorem9921CyclicSubgroups (G : Type) [Group G] [Finite G] : Finset (Subgroup G) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  exact Finset.univ.filter fun H : Subgroup G ↦ IsCyclic H

/-- Helper for Exercise 9-9.4-3: membership in `theorem9921CyclicSubgroups G` is exactly cyclicity. -/
@[simp] theorem mem_theorem9921CyclicSubgroups {H : Subgroup G} :
    H ∈ theorem9921CyclicSubgroups G ↔ IsCyclic H := by
  classical
  simp [theorem9921CyclicSubgroups]

end

end Subgroup

namespace Representation

section

variable {K : Type} [Zero K] [NatCast K]
variable (A : Type) [Group A] [Finite A]

open Classical in
/-- Helper for Exercise 9-9.4-3: Serre's auxiliary function `θ_A`, supported on the generators of
`A` and equal to `|A|` on each generator. -/
def theorem9921CyclicGroupTheta : A → K :=
  fun a ↦ if Subgroup.zpowers a = (⊤ : Subgroup A) then Nat.card A else 0

end

end Representation

section

variable {G : Type} [Group G]

/-- Helper for Exercise 9-9.4-3: an element of a subgroup generates that subgroup internally
exactly when its ambient cyclic subgroup is the whole subgroup. -/
lemma theorem9921_subgroup_zpowers_eq_top_iff (H : Subgroup G) (a : H) :
    Subgroup.zpowers a = ⊤ ↔ Subgroup.zpowers (a : G) = H := by
  -- Map the internal cyclic subgroup along the subtype map to compare it with the ambient one.
  rw [← Subgroup.map_subtype_inj]
  rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, H.range_subtype]
  simp

end

section

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Semifield K]

attribute [local instance] Fintype.ofFinite

/-- Helper for Exercise 9-9.4-3: the induction scalar attached to `orderOf x` is absorbed by
`|G|`. -/
lemma theorem9921_natCard_mul_inv_orderOf_mul_orderOf (x : G) :
    (Nat.card G : K) * (((orderOf x : K)⁻¹) * (orderOf x : K)) = (Nat.card G : K) := by
  -- Rewrite `|G|` as a multiple of `orderOf x`, then split according to whether that cast
  -- vanishes in `K`.
  obtain ⟨m, hm⟩ := orderOf_dvd_natCard x
  have hcard : (Nat.card G : K) = (orderOf x : K) * (m : K) := by
    simpa [Nat.cast_mul] using congrArg (fun n : ℕ => (n : K)) hm
  by_cases hx : (orderOf x : K) = 0
  · rw [hcard]
    simp [hx]
  · calc
      (Nat.card G : K) * (((orderOf x : K)⁻¹) * (orderOf x : K))
          = ((orderOf x : K) * (m : K)) * (((orderOf x : K)⁻¹) * (orderOf x : K)) := by
              rw [hcard]
      _ = ((orderOf x : K) * (orderOf x : K)⁻¹) * ((m : K) * (orderOf x : K)) := by
            ac_rfl
      _ = (m : K) * (orderOf x : K) := by
            simp [hx]
      _ = (orderOf x : K) * (m : K) := by
            ac_rfl
      _ = (Nat.card G : K) := by
            rw [hcard]

/-- Helper for Exercise 9-9.4-3: the cyclic-subgroup sum of the auxiliary functions `(theorem9921CyclicGroupTheta H)`
recovers the constant function with value `|G|`. -/
theorem theorem9921_sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one :
    ∑ H ∈ Subgroup.theorem9921CyclicSubgroups G, Ind[H]((theorem9921CyclicGroupTheta H)) = (Nat.card G : K) • (1 : G → K) := by
  classical
  ext x
  simp [Pi.smul_apply, Nat.card_eq_fintype_card]
  let F : Subgroup G → G → K := fun H y ↦
    if Subgroup.zpowers (y⁻¹ * x * y) = H then ((Nat.card H : K)⁻¹ * (Nat.card H : K)) else 0
  have hInd (H : Subgroup G) : Ind[H]((theorem9921CyclicGroupTheta H)) x = ∑ y : G, F H y := by
    -- Unfold the induced class function and rewrite the `(theorem9921CyclicGroupTheta H)` value using whether the conjugate
    -- generates `H`.
    change ((Nat.card H : K)⁻¹) *
        Finset.univ.sum (fun y : G =>
          if hy : y⁻¹ * x * y ∈ H then (theorem9921CyclicGroupTheta H) ⟨y⁻¹ * x * y, hy⟩ else 0) = _
    rw [Finset.mul_sum]
    change Finset.univ.sum (fun y : G =>
        ((Nat.card H : K)⁻¹) *
          (if hy : y⁻¹ * x * y ∈ H then (theorem9921CyclicGroupTheta H) ⟨y⁻¹ * x * y, hy⟩ else 0)) = _
    refine Finset.sum_congr rfl ?_
    intro y hyuniv
    by_cases hgen : Subgroup.zpowers (y⁻¹ * x * y) = H
    · have hy : y⁻¹ * x * y ∈ H := by
        rw [← hgen]
        exact Subgroup.mem_zpowers _
      have hleft :
          ((Nat.card H : K)⁻¹) *
              (if hy' : y⁻¹ * x * y ∈ H then (theorem9921CyclicGroupTheta H) ⟨y⁻¹ * x * y, hy'⟩ else 0)
            = ((Nat.card H : K)⁻¹) * ((theorem9921CyclicGroupTheta H) : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) := by
        simp [hy]
      have htheta : ((theorem9921CyclicGroupTheta H) : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) = (Nat.card H : K) := by
        simp [Representation.theorem9921CyclicGroupTheta, theorem9921_subgroup_zpowers_eq_top_iff, hgen]
      calc
        ((Nat.card H : K)⁻¹) *
            (if hy' : y⁻¹ * x * y ∈ H then (theorem9921CyclicGroupTheta H) ⟨y⁻¹ * x * y, hy'⟩ else 0)
            = ((Nat.card H : K)⁻¹) * ((theorem9921CyclicGroupTheta H) : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) := hleft
        _ = ((Nat.card H : K)⁻¹) * (Nat.card H : K) := by
              exact congrArg (fun z : K => ((Nat.card H : K)⁻¹) * z) htheta
        _ = F H y := by
              dsimp [F]
              rw [if_pos hgen]
    · by_cases hy : y⁻¹ * x * y ∈ H
      · have hleft :
            ((Nat.card H : K)⁻¹) *
                (if hy' : y⁻¹ * x * y ∈ H then (theorem9921CyclicGroupTheta H) ⟨y⁻¹ * x * y, hy'⟩ else 0)
              = ((Nat.card H : K)⁻¹) * ((theorem9921CyclicGroupTheta H) : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) := by
          simp [hy]
        have htheta : ((theorem9921CyclicGroupTheta H) : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) = 0 := by
          simp [Representation.theorem9921CyclicGroupTheta, theorem9921_subgroup_zpowers_eq_top_iff, hgen]
        have hmul : ((Nat.card H : K)⁻¹) * ((theorem9921CyclicGroupTheta H) : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) = 0 := by
          simpa using congrArg (fun z : K => ((Nat.card H : K)⁻¹) * z) htheta
        calc
          ((Nat.card H : K)⁻¹) *
              (if hy' : y⁻¹ * x * y ∈ H then (theorem9921CyclicGroupTheta H) ⟨y⁻¹ * x * y, hy'⟩ else 0)
              = ((Nat.card H : K)⁻¹) * ((theorem9921CyclicGroupTheta H) : H → K) (⟨y⁻¹ * x * y, hy⟩ : H) := hleft
          _ = 0 := hmul
          _ = F H y := by
                dsimp [F]
                rw [if_neg hgen]
      · have hleft :
            ((Nat.card H : K)⁻¹) *
                (if hy' : y⁻¹ * x * y ∈ H then (theorem9921CyclicGroupTheta H) ⟨y⁻¹ * x * y, hy'⟩ else 0) = 0 := by
          simp [hy]
        calc
          ((Nat.card H : K)⁻¹) *
              (if hy' : y⁻¹ * x * y ∈ H then (theorem9921CyclicGroupTheta H) ⟨y⁻¹ * x * y, hy'⟩ else 0) = 0 := hleft
          _ = F H y := by
                dsimp [F]
                rw [if_neg hgen]
  have hCollapse (a : G) :
      ((Subgroup.theorem9921CyclicSubgroups G).sum fun H ↦ F H a) =
        ((Nat.card (Subgroup.zpowers (a⁻¹ * x * a)) : K)⁻¹ *
          (Nat.card (Subgroup.zpowers (a⁻¹ * x * a)) : K)) := by
    -- Only the subgroup generated by `a⁻¹ * x * a` contributes to the subgroup sum.
    have ha : Subgroup.zpowers (a⁻¹ * x * a) ∈ Subgroup.theorem9921CyclicSubgroups G := by
      simpa using (Subgroup.mem_theorem9921CyclicSubgroups :
        Subgroup.zpowers (a⁻¹ * x * a) ∈ Subgroup.theorem9921CyclicSubgroups G ↔
          IsCyclic (Subgroup.zpowers (a⁻¹ * x * a))).2 inferInstance
    dsimp [F]
    rw [Finset.sum_eq_single (Subgroup.zpowers (a⁻¹ * x * a))]
    · simp
    · intro H hH hne
      have hne' : Subgroup.zpowers (a⁻¹ * x * a) ≠ H := by
        simpa [eq_comm] using hne
      simp [hne']
    · intro hnot
      exact False.elim (hnot ha)
  -- Swap the subgroup sum with the ambient group sum and collapse the unique contributing term.
  calc
    ∑ H ∈ Subgroup.theorem9921CyclicSubgroups G, Ind[H]((theorem9921CyclicGroupTheta H)) x
        = (Subgroup.theorem9921CyclicSubgroups G).sum fun H ↦ ∑ y : G, F H y := by
            refine Finset.sum_congr rfl ?_
            intro H hH
            exact hInd H
    _ = (Subgroup.theorem9921CyclicSubgroups G).sum fun H ↦ Finset.univ.sum (F H) := by
          rfl
    _ = Finset.univ.sum fun y : G ↦ (Subgroup.theorem9921CyclicSubgroups G).sum fun H ↦ F H y := by
          rw [Finset.sum_comm]
    _ = ∑ y : G,
          ((Nat.card (Subgroup.zpowers (y⁻¹ * x * y)) : K)⁻¹ *
            (Nat.card (Subgroup.zpowers (y⁻¹ * x * y)) : K)) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          simpa using hCollapse y
    _ = ∑ y : G, (((orderOf x : K)⁻¹) * (orderOf x : K)) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [Nat.card_zpowers]
          have horder : orderOf (y⁻¹ * x * y) = orderOf x := by
            simpa using ((SemiconjBy.conj_mk y⁻¹ x).orderOf_eq y⁻¹).symm
          rw [horder]
    _ = (Fintype.card G : K) * (((orderOf x : K)⁻¹) * (orderOf x : K)) := by
          simp
    _ = (Nat.card G : K) * (((orderOf x : K)⁻¹) * (orderOf x : K)) := by
          rw [Nat.card_eq_fintype_card]
    _ = (Nat.card G : K) := by
          simpa using theorem9921_natCard_mul_inv_orderOf_mul_orderOf (K := K) x
    _ = (Fintype.card G : K) := by
          rw [Nat.card_eq_fintype_card]

end

namespace Representation

section

variable (A : Type) [Group A] [Finite A]

attribute [local instance] Fintype.ofFinite

/-- Helper for Exercise 9-9.4-3: a proper subgroup of a finite group has strictly smaller
cardinality. -/
private lemma theorem9921_subgroup_natCard_lt_of_ne_top {B : Type} [Group B] [Finite B] (H : Subgroup B)
    (hH : H ≠ ⊤) : Nat.card H < Nat.card B := by
  let _ : Fintype B := Fintype.ofFinite B
  let _ : Fintype H := Fintype.ofFinite H
  -- A proper subgroup omits some ambient element, so the inclusion on carriers is not surjective.
  have hex : ∃ x : B, x ∉ H := by
    by_cases hforall : ∀ x : B, x ∈ H
    · exact False.elim (hH (by
        ext x
        simp [hforall x]))
    · exact not_forall.mp hforall
  rcases hex with ⟨x, hx⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simpa using (Fintype.card_subtype_lt (p := fun y : B ↦ y ∈ H) hx)

/-- Helper for Exercise 9-9.4-3: on the top subgroup, the subgroup version of `θ` agrees with
the ambient one after forgetting the trivial membership proof. -/
private lemma theorem9921_top_cyclicGroupTheta_eq {B : Type} [Group B] [Finite B] :
    (fun g : B ↦ (((theorem9921CyclicGroupTheta (⊤ : Subgroup B)) : (⊤ : Subgroup B) → ℂ) ⟨g, by simp⟩)) =
      ((theorem9921CyclicGroupTheta B) : B → ℂ) := by
  let _ : Fintype B := Fintype.ofFinite B
  let _ : Fintype (⊤ : Subgroup B) := Fintype.ofFinite _
  ext g
  have hsub :
      Subgroup.zpowers (⟨g, by simp⟩ : (⊤ : Subgroup B)) = ⊤ ↔
        Subgroup.zpowers g = (⊤ : Subgroup B) := by
    -- Compare the internal cyclic subgroup with its image in the ambient group.
    rw [← Subgroup.map_subtype_inj]
    rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, (⊤ : Subgroup B).range_subtype]
    simp
  by_cases hg : Subgroup.zpowers g = (⊤ : Subgroup B)
  · have hg' : Subgroup.zpowers (⟨g, by simp⟩ : (⊤ : Subgroup B)) = ⊤ := hsub.mpr hg
    simp [Representation.theorem9921CyclicGroupTheta, hg, hg', Nat.card_eq_fintype_card]
  · have hg' : Subgroup.zpowers (⟨g, by simp⟩ : (⊤ : Subgroup B)) ≠ ⊤ := by
      intro h
      exact hg (hsub.mp h)
    simp [Representation.theorem9921CyclicGroupTheta, hg, hg']

/-- Helper for Exercise 9-9.4-3: in a finite commutative group, the `H = ⊤` summand in Serre's
induction formula is exactly the original auxiliary function `θ`. -/
private lemma theorem9921_top_induced_cyclicGroupTheta_eq {B : Type} [CommGroup B] [Finite B] :
    Ind[(⊤ : Subgroup B)](((theorem9921CyclicGroupTheta (⊤ : Subgroup B)) : (⊤ : Subgroup B) → ℂ)) = ((theorem9921CyclicGroupTheta B) : B → ℂ) := by
  classical
  let _ : Fintype B := Fintype.ofFinite B
  have hcardF : (Fintype.card B : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard : (Nat.card B : ℂ) ≠ 0 := by
    simpa [Nat.card_eq_fintype_card] using hcardF
  ext g
  -- In a commutative group every conjugate of `g` is `g`, so the induction sum is constant.
  calc
    Ind[(⊤ : Subgroup B)](((theorem9921CyclicGroupTheta (⊤ : Subgroup B)) : (⊤ : Subgroup B) → ℂ)) g
        = ((Nat.card (⊤ : Subgroup B) : ℂ)⁻¹) *
            ∑ s : B,
              if hs : s⁻¹ * g * s ∈ (⊤ : Subgroup B) then
                (((theorem9921CyclicGroupTheta (⊤ : Subgroup B)) : (⊤ : Subgroup B) → ℂ) ⟨s⁻¹ * g * s, hs⟩)
              else 0 := by
            rfl
    _ = (Nat.card B : ℂ)⁻¹ *
            ∑ s : B,
              if hs : s⁻¹ * g * s ∈ (⊤ : Subgroup B) then
                (((theorem9921CyclicGroupTheta (⊤ : Subgroup B)) : (⊤ : Subgroup B) → ℂ) ⟨s⁻¹ * g * s, hs⟩)
              else 0 := by
            simp [Nat.card_eq_fintype_card]
    _ = (Nat.card B : ℂ)⁻¹ *
            ∑ _s : B, (((theorem9921CyclicGroupTheta (⊤ : Subgroup B)) : (⊤ : Subgroup B) → ℂ) ⟨g, by simp⟩) := by
            refine congrArg ((Nat.card B : ℂ)⁻¹ * ·) ?_
            refine Fintype.sum_congr
              (fun s : B ↦
                if hs : s⁻¹ * g * s ∈ (⊤ : Subgroup B) then
                  (((theorem9921CyclicGroupTheta (⊤ : Subgroup B)) : (⊤ : Subgroup B) → ℂ) ⟨s⁻¹ * g * s, hs⟩)
                else 0)
              (fun _s : B ↦ (((theorem9921CyclicGroupTheta (⊤ : Subgroup B)) : (⊤ : Subgroup B) → ℂ) ⟨g, by simp⟩))
              ?_
            intro s
            have hs : s⁻¹ * g * s = g := by
              calc
                s⁻¹ * g * s = s⁻¹ * s * g := by
                  ac_rfl
                _ = g := by
                  simp
            have hsub :
                (⟨s⁻¹ * g * s, by simp⟩ : (⊤ : Subgroup B)) = ⟨g, by simp⟩ := by
              apply Subtype.ext
              simp [hs]
            simp [hs, hsub]
    _ = (Nat.card B : ℂ)⁻¹ *
          ((Nat.card B : ℂ) * (((theorem9921CyclicGroupTheta (⊤ : Subgroup B)) : (⊤ : Subgroup B) → ℂ) ⟨g, by simp⟩)) := by
          simp [Finset.sum_const, Nat.card_eq_fintype_card, nsmul_eq_mul]
    _ = (((Nat.card B : ℂ)⁻¹ * (Nat.card B : ℂ)) *
          (((theorem9921CyclicGroupTheta (⊤ : Subgroup B)) : (⊤ : Subgroup B) → ℂ) ⟨g, by simp⟩)) := by
          rw [mul_assoc]
    _ = (((theorem9921CyclicGroupTheta (⊤ : Subgroup B)) : (⊤ : Subgroup B) → ℂ) ⟨g, by simp⟩) := by
          rw [inv_mul_cancel₀ hcard, one_mul]
    _ = ((theorem9921CyclicGroupTheta B) : B → ℂ) g := by
          simpa using congrFun (theorem9921_top_cyclicGroupTheta_eq (B := B)) g

/-- Helper for Exercise 9-9.4-3: if `A` is cyclic, then Serre's auxiliary function `(theorem9921CyclicGroupTheta A)`
belongs to the character ring `R(A)`. -/
theorem theorem9921_cyclicGroupTheta_mem_characterRing [IsCyclic A] :
    (theorem9921CyclicGroupTheta A : A → ℂ) ∈ (R[ℂ](A) : Set (A → ℂ)) := by
  classical
  let _ : CommGroup A := IsCyclic.commGroup
  let P : ℕ → Prop := fun n ↦
    ∀ (G : Type) (_ : Group G) (_ : Finite G) (_ : IsCyclic G),
      Nat.card G = n → (theorem9921CyclicGroupTheta G : G → ℂ) ∈ (R[ℂ](G) : Set (G → ℂ))
  have hstrong : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih
    intro G _ _ _ hGcard
    let _ : CommGroup G := IsCyclic.commGroup
    let _ : Fintype G := Fintype.ofFinite G
    let S : Finset (Subgroup G) := Subgroup.theorem9921CyclicSubgroups G
    have htop : (⊤ : Subgroup G) ∈ S := by
      simpa [S] using (Subgroup.mem_theorem9921CyclicSubgroups.2 inferInstance :
        (⊤ : Subgroup G) ∈ Subgroup.theorem9921CyclicSubgroups G)
    -- Split the cyclic-subgroup sum into the top subgroup and the proper cyclic subgroups.
    have hsplit :
        Finset.sum S (fun H ↦ Ind[H](((theorem9921CyclicGroupTheta H) : H → ℂ))) =
          Ind[(⊤ : Subgroup G)](((theorem9921CyclicGroupTheta (⊤ : Subgroup G)) : (⊤ : Subgroup G) → ℂ)) +
            Finset.sum (S.erase ⊤) (fun H ↦ Ind[H](((theorem9921CyclicGroupTheta H) : H → ℂ))) := by
      rw [← Finset.insert_erase htop]
      simp
    have hsum :
        Ind[(⊤ : Subgroup G)](((theorem9921CyclicGroupTheta (⊤ : Subgroup G)) : (⊤ : Subgroup G) → ℂ)) +
            Finset.sum (S.erase ⊤) (fun H ↦ Ind[H](((theorem9921CyclicGroupTheta H) : H → ℂ))) =
          (Nat.card G : ℂ) • (1 : G → ℂ) := by
      exact hsplit.symm.trans (theorem9921_sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one (G := G) (K := ℂ))
    -- The proper subgroup terms lie in `R(G)` by strong induction and induction on character
    -- rings over `ℂ`.
    have hproper :
        Finset.sum (S.erase ⊤) (fun H ↦ Ind[H](((theorem9921CyclicGroupTheta H) : H → ℂ))) ∈ R[ℂ](G) := by
      refine (R[ℂ](G)).sum_mem ?_
      intro H hH
      have hHne : H ≠ ⊤ := (Finset.mem_erase.mp hH).1
      have hthetaH : (theorem9921CyclicGroupTheta H : H → ℂ) ∈ (R[ℂ](H) : Set (H → ℂ)) := by
        have hlt : Nat.card H < n := by
          rw [← hGcard]
          exact theorem9921_subgroup_natCard_lt_of_ne_top H hHne
        simpa using ih (Nat.card H) hlt H inferInstance inferInstance inferInstance rfl
      exact Subgroup.inducedClassFunction_mem_characterRingOverField (K := ℂ) H ⟨((theorem9921CyclicGroupTheta H) : H → ℂ), hthetaH⟩
    -- The constant term is an integral multiple of the trivial character, hence lies in `R(G)`.
    have hconst : (Nat.card G : ℂ) • (1 : G → ℂ) ∈ R[ℂ](G) := by
      convert ((((Fintype.card G : ℤ) • (1 : R[ℂ](G))) : R[ℂ](G)) : R[ℂ](G)).property using 1
      ext g
      simp [Nat.card_eq_fintype_card, zsmul_eq_mul]
    -- Route correction: rewrite the cyclic-subgroup identity as
    -- `(theorem9921CyclicGroupTheta G) = |G| • 1 - (proper subgroup sum)` and then use closure of `R(G)` under subtraction.
    have htheta_eq :
        ((theorem9921CyclicGroupTheta G) : G → ℂ) =
          (Nat.card G : ℂ) • (1 : G → ℂ) -
            Finset.sum (S.erase ⊤) (fun H ↦ Ind[H](((theorem9921CyclicGroupTheta H) : H → ℂ))) := by
      rw [← theorem9921_top_induced_cyclicGroupTheta_eq (B := G)]
      exact eq_sub_iff_add_eq.2 hsum
    exact htheta_eq.symm ▸ (R[ℂ](G)).sub_mem hconst hproper
  have hA : P (Nat.card A) := hstrong (Nat.card A)
  simpa using hA A inferInstance inferInstance inferInstance rfl

end

end Representation

section

variable {G : Type} [Group G] [Finite G]

attribute [local instance] Fintype.ofFinite

/-- Local transport lemma for Theorem 9-9.2-1: induction is unchanged after conjugating the
source subgroup and transporting the source function along the conjugation isomorphism. -/
theorem Subgroup.theorem9921_inducedClassFunction_conjugate_eq
    (H : Subgroup G) (s : G) (f : H → ℂ) :
    Subgroup.inducedClassFunction (MulAut.conj s • H : Subgroup G)
      (fun x : (MulAut.conj s • H : Subgroup G) =>
        f (((MulAut.conj s).subgroupMap H).symm x)) =
      Subgroup.inducedClassFunction H f := by
  classical
  let _ : DecidablePred fun z : G => z ∈ H := Classical.decPred _
  let _ : DecidablePred fun z : G => z ∈ (MulAut.conj s • H : Subgroup G) :=
    Classical.decPred _
  ext g
  have hcard : Nat.card (MulAut.conj s • H : Subgroup G) = Nat.card H := by
    exact Nat.card_congr (((MulAut.conj s).subgroupMap H).symm.toEquiv)
  rw [Subgroup.inducedClassFunction, Subgroup.inducedClassFunction, hcard]
  let e : G ≃ G := Equiv.mulRight s
  exact congrArg (fun t : ℂ => (↑(Nat.card ↥H) : ℂ)⁻¹ * t) <|
    Fintype.sum_equiv e
      (fun x : G =>
        if hxs : x⁻¹ * g * x ∈ (MulAut.conj s • H : Subgroup G) then
          f (((MulAut.conj s).subgroupMap H).symm ⟨x⁻¹ * g * x, hxs⟩)
        else
          0)
      (fun x : G =>
        if hxH : x⁻¹ * g * x ∈ H then
          f ⟨x⁻¹ * g * x, hxH⟩
        else
          0)
      (fun x => by
        change
          (if hxs : x⁻¹ * g * x ∈ (MulAut.conj s • H : Subgroup G) then
            f (((MulAut.conj s).subgroupMap H).symm ⟨x⁻¹ * g * x, hxs⟩)
          else
            0) =
          if hxH : (x * s)⁻¹ * g * (x * s) ∈ H then
            f ⟨(x * s)⁻¹ * g * (x * s), hxH⟩
          else
            0
        by_cases hxs : x⁻¹ * g * x ∈ (MulAut.conj s • H : Subgroup G)
        · have hxH : ((x * s) : G)⁻¹ * g * (x * s) ∈ H := by
            change x⁻¹ * g * x ∈ H.map (MulAut.conj s).toMonoidHom at hxs
            simpa [mul_assoc] using
              (Subgroup.mem_map_equiv (f := MulAut.conj s) (K := H)).1 hxs
          have hsub :
              (((MulAut.conj s).subgroupMap H).symm ⟨x⁻¹ * g * x, hxs⟩ : H) =
                ⟨(x * s)⁻¹ * g * (x * s), hxH⟩ := by
            apply Subtype.ext
            simp [MulEquiv.subgroupMap_symm_apply, mul_assoc]
          rw [dif_pos hxs, dif_pos hxH]
          simpa using congrArg (fun z : H => f z) hsub
        · have hxH : ¬ ((x * s) : G)⁻¹ * g * (x * s) ∈ H := by
            intro hxH
            apply hxs
            change x⁻¹ * g * x ∈ H.map (MulAut.conj s).toMonoidHom
            exact (Subgroup.mem_map_equiv (f := MulAut.conj s) (K := H)).2 <|
              by simpa [mul_assoc] using hxH
          rw [dif_neg hxs, dif_neg hxH])

/-- Local transport lemma for Theorem 9-9.2-1: if `L ≤ H ≤ G`, inducing first from `L` to
`H` and then from `H` to `G` agrees with direct induction from `L` to `G`. -/
theorem Subgroup.theorem9921_inducedClassFunction_subgroupOf_induction_in_stages
    (H L : Subgroup G) (hL : L ≤ H) (f : L → ℂ) :
    Subgroup.inducedClassFunction H
      (Subgroup.inducedClassFunction (L.subgroupOf H)
        (fun x : L.subgroupOf H => f ((Subgroup.subgroupOfEquivOfLe hL) x))) =
      Subgroup.inducedClassFunction L f := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype L := Fintype.ofFinite L
  letI : Fintype (L.subgroupOf H) := Fintype.ofFinite (L.subgroupOf H)
  let _ : DecidablePred fun z : G => z ∈ H := Classical.decPred _
  let _ : DecidablePred fun z : G => z ∈ L := Classical.decPred _
  let _ : DecidablePred fun z : H => z ∈ L.subgroupOf H := Classical.decPred _
  ext g
  have hcard : Nat.card (L.subgroupOf H) = Nat.card L := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL).toEquiv
  let φ : G → ℂ := fun s =>
    if hs : s⁻¹ * g * s ∈ L then
      f ⟨s⁻¹ * g * s, hs⟩
    else
      0
  have hinner :
      ∀ x : G,
        (if hsg : x⁻¹ * g * x ∈ H then
          (↑(Nat.card ↥L) : ℂ)⁻¹ *
            ∑ y : H,
              if hsg_1 : y⁻¹ * ⟨x⁻¹ * g * x, hsg⟩ * y ∈ L.subgroupOf H then
                f ((Subgroup.subgroupOfEquivOfLe hL)
                  ⟨y⁻¹ * ⟨x⁻¹ * g * x, hsg⟩ * y, hsg_1⟩)
              else
                0
        else
          0) =
        (↑(Nat.card ↥L) : ℂ)⁻¹ * ∑ y : H, φ (x * y) := by
    intro x
    by_cases hx : x⁻¹ * g * x ∈ H
    · rw [dif_pos hx]
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      have hmul :
          (((y : H) : G)⁻¹) * (x⁻¹ * g * x) * ((y : H) : G) =
            (x * y : G)⁻¹ * g * (x * y : G) := by
        group
      dsimp [φ]
      by_cases hxy : (x * y : G)⁻¹ * g * (x * y : G) ∈ L
      · have hsub : ((y : H)⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y) ∈ L.subgroupOf H := by
          change (((y : H) : G)⁻¹ * (x⁻¹ * g * x) * (y : H)) ∈ L
          simpa [hmul] using hxy
        rw [dif_pos hsub, dif_pos hxy]
        congr 1
        apply Subtype.ext
        simp [Subgroup.subgroupOfEquivOfLe, hmul]
      · have hsub : ¬ ((y : H)⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y) ∈ L.subgroupOf H := by
          change ¬ ((((y : H) : G)⁻¹ * (x⁻¹ * g * x) * (y : H)) ∈ L)
          simpa [hmul] using hxy
        rw [dif_neg hsub, dif_neg hxy]
    · have hall : ∀ y : H, φ (x * y) = 0 := by
        intro y
        dsimp [φ]
        by_cases hxy : (x * y : G)⁻¹ * g * (x * y : G) ∈ L
        · exfalso
          apply hx
          have hxyH : (x * y : G)⁻¹ * g * (x * y : G) ∈ H := hL hxy
          simpa [mul_assoc] using
            H.mul_mem (H.mul_mem y.2 hxyH) (H.inv_mem y.2)
        · rw [dif_neg hxy]
      rw [dif_neg hx]
      simp [hall]
  calc
    Subgroup.inducedClassFunction H
        (Subgroup.inducedClassFunction (L.subgroupOf H)
          (fun x : L.subgroupOf H => f ((Subgroup.subgroupOfEquivOfLe hL) x))) g =
      ((↑(Nat.card ↥H) : ℂ)⁻¹) * ∑ x : G,
        ((↑(Nat.card ↥L) : ℂ)⁻¹) * ∑ y : H, φ (x * y) := by
      change ((↑(Nat.card ↥H) : ℂ)⁻¹) *
          ∑ s : G,
            (if hsg : s⁻¹ * g * s ∈ H then
              Subgroup.inducedClassFunction (L.subgroupOf H)
                (fun x : L.subgroupOf H => f ((Subgroup.subgroupOfEquivOfLe hL) x))
                ⟨s⁻¹ * g * s, hsg⟩
            else
              0) = _
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      rw [Subgroup.inducedClassFunction, hcard]
      simpa using hinner x
    _ = ((↑(Nat.card ↥H) : ℂ)⁻¹) *
        (((↑(Nat.card ↥L) : ℂ)⁻¹) * ∑ x : G, ∑ y : H, φ (x * y)) := by
      simp [Finset.mul_sum]
    _ = ((↑(Nat.card ↥H) : ℂ)⁻¹) *
        (((↑(Nat.card ↥L) : ℂ)⁻¹) * ∑ p : G × H, φ p.1) := by
      congr 2
      calc
        ∑ x : G, ∑ y : H, φ (x * y) = ∑ p : G × H, φ (p.1 * p.2) := by
          rw [Fintype.sum_prod_type]
        _ = ∑ p : G × H, φ p.1 := by
          let e : G × H ≃ G × H :=
            { toFun := fun p => (p.1 * p.2, p.2)
              invFun := fun p => (p.1 * p.2⁻¹, p.2)
              left_inv := by
                intro p
                ext <;> simp [mul_assoc]
              right_inv := by
                intro p
                ext <;> simp [mul_assoc] }
          exact Fintype.sum_equiv e
            (fun p : G × H => φ (p.1 * p.2))
            (fun p : G × H => φ p.1)
            (fun p => rfl)
    _ = ((↑(Nat.card ↥H) : ℂ)⁻¹) *
        (((↑(Nat.card ↥L) : ℂ)⁻¹) * ((↑(Nat.card ↥H) : ℂ) * ∑ z : G, φ z)) := by
      congr 2
      calc
        ∑ p : G × H, φ p.1 = ∑ z : G, ∑ y : H, φ z := by
          rw [Fintype.sum_prod_type]
        _ = ∑ z : G, (↑(Nat.card ↥H) : ℂ) * φ z := by
          simp
        _ = (↑(Nat.card ↥H) : ℂ) * ∑ z : G, φ z := by
          rw [Finset.mul_sum]
    _ = (↑(Nat.card ↥L) : ℂ)⁻¹ * ∑ z : G, φ z := by
      have hH0 : (↑(Nat.card ↥H) : ℂ) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      field_simp [hH0, mul_assoc]
    _ = Ind[L](f) g := by
      simp [Subgroup.inducedClassFunction, φ]

end

namespace Representation

section

variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B]

attribute [local instance] Fintype.ofFinite

/-- Local transport lemma for Theorem 9-9.2-1: Serre's cyclic theta function is natural under
group isomorphisms. -/
theorem theorem9921_cyclicGroupTheta_comp_equiv_symm
    {K : Type} [Zero K] [NatCast K] (e : A ≃* B) :
    (fun b : B => (theorem9921CyclicGroupTheta A : A → K) (e.symm b)) =
      (theorem9921CyclicGroupTheta B : B → K) := by
  classical
  ext b
  have hcard : Nat.card A = Nat.card B := Nat.card_congr e.toEquiv
  have hcardK : (Fintype.card A : K) = (Fintype.card B : K) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact congrArg (fun n : ℕ => (n : K)) hcard
  have hgen : Subgroup.zpowers (e.symm b) = (⊤ : Subgroup A) ↔
      Subgroup.zpowers b = (⊤ : Subgroup B) := by
    constructor
    · intro h
      have hmap := congrArg (fun H : Subgroup A => H.map e.toMonoidHom) h
      simpa [MonoidHom.map_zpowers, hcard] using hmap
    · intro h
      have hmap := congrArg (fun H : Subgroup B => H.map e.symm.toMonoidHom) h
      simpa [MonoidHom.map_zpowers, hcard] using hmap
  by_cases hb : Subgroup.zpowers b = (⊤ : Subgroup B)
  · have ha : Subgroup.zpowers (e.symm b) = (⊤ : Subgroup A) := hgen.mpr hb
    simp [theorem9921CyclicGroupTheta, ha, hb, hcardK]
  · have ha : Subgroup.zpowers (e.symm b) ≠ (⊤ : Subgroup A) := by
      intro ha
      exact hb (hgen.mp ha)
    simp [theorem9921CyclicGroupTheta, ha, hb]

end

end Representation

end
