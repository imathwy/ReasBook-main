import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_9_9_4_2 (from Chap09) -/
noncomputable section

universe u

namespace Representation

section

variable (A : Type u) [Group A] [Finite A]

private local instance : Fintype A := Fintype.ofFinite A

open scoped BigOperators Representation SubgroupInduction

/-- Helper for Proposition 9-9.4-2: a proper subgroup of a finite group has strictly smaller
cardinality. -/
lemma subgroup_natCard_lt_of_ne_top {G : Type u} [Group G] [Finite G] (H : Subgroup G)
    (hH : H ≠ ⊤) : Nat.card H < Nat.card G := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype H := Fintype.ofFinite H
  -- A proper subgroup omits some ambient element, so the inclusion on carriers is not surjective.
  have hex : ∃ x : G, x ∉ H := by
    by_cases hforall : ∀ x : G, x ∈ H
    · exact False.elim (hH (by
        ext x
        simp [hforall x]))
    · exact not_forall.mp hforall
  rcases hex with ⟨x, hx⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simpa using (Fintype.card_subtype_lt (p := fun y : G ↦ y ∈ H) hx)

/-- Helper for Proposition 9-9.4-2: on the top subgroup, the subgroup version of `θ` agrees with
the ambient one after forgetting the trivial membership proof. -/
lemma top_cyclicGroupTheta_eq {G : Type u} [Group G] [Finite G] :
    (fun g : G ↦ ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ) ⟨g, by simp⟩)) =
      (θ[G] : G → ℂ) := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype (⊤ : Subgroup G) := Fintype.ofFinite _
  ext g
  have hsub :
      Subgroup.zpowers (⟨g, by simp⟩ : (⊤ : Subgroup G)) = ⊤ ↔
        Subgroup.zpowers g = (⊤ : Subgroup G) := by
    -- Compare the internal cyclic subgroup with its image in the ambient group.
    rw [← Subgroup.map_subtype_inj]
    rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, (⊤ : Subgroup G).range_subtype]
    simp
  by_cases hg : Subgroup.zpowers g = (⊤ : Subgroup G)
  · have hg' : Subgroup.zpowers (⟨g, by simp⟩ : (⊤ : Subgroup G)) = ⊤ := hsub.mpr hg
    simp [Representation.cyclicGroupTheta, hg, hg', Nat.card_eq_fintype_card]
  · have hg' : Subgroup.zpowers (⟨g, by simp⟩ : (⊤ : Subgroup G)) ≠ ⊤ := by
      intro h
      exact hg (hsub.mp h)
    simp [Representation.cyclicGroupTheta, hg, hg']

/-- Helper for Proposition 9-9.4-2: in a finite commutative group, the `H = ⊤` summand in LinearRepresentations_Serre_1977's
induction formula is exactly the original auxiliary function `θ`. -/
lemma top_induced_cyclicGroupTheta_eq {G : Type u} [CommGroup G] [Finite G] :
    Ind[(⊤ : Subgroup G)]((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ)) = (θ[G] : G → ℂ) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hcardF : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact hcardF
  ext g
  -- In a commutative group every conjugate of `g` is `g`, so the induction sum is constant.
  calc
    Ind[(⊤ : Subgroup G)]((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ)) g
        = ((Nat.card (⊤ : Subgroup G) : ℂ)⁻¹) *
            ∑ s : G,
              if hs : s⁻¹ * g * s ∈ (⊤ : Subgroup G) then
                ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ) ⟨s⁻¹ * g * s, hs⟩)
              else 0 := by
            rfl
    _ = (Nat.card G : ℂ)⁻¹ *
            ∑ s : G,
              if hs : s⁻¹ * g * s ∈ (⊤ : Subgroup G) then
                ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ) ⟨s⁻¹ * g * s, hs⟩)
              else 0 := by
            simp [Nat.card_eq_fintype_card]
    _ = (Nat.card G : ℂ)⁻¹ *
            ∑ _s : G, ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ) ⟨g, by simp⟩) := by
            refine congrArg ((Nat.card G : ℂ)⁻¹ * ·) ?_
            refine Fintype.sum_congr
              (fun s : G ↦
                if hs : s⁻¹ * g * s ∈ (⊤ : Subgroup G) then
                  ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ) ⟨s⁻¹ * g * s, hs⟩)
                else 0)
              (fun _s : G ↦ ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ) ⟨g, by simp⟩))
              ?_
            intro s
            have hs : s⁻¹ * g * s = g := by
              calc
                s⁻¹ * g * s = s⁻¹ * s * g := by
                  ac_rfl
                _ = g := by
                  simp
            simp [hs]
    _ = (Nat.card G : ℂ)⁻¹ *
          ((Nat.card G : ℂ) * ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ) ⟨g, by simp⟩)) := by
          simp [Finset.sum_const, Nat.card_eq_fintype_card, nsmul_eq_mul]
    _ = (((Nat.card G : ℂ)⁻¹ * (Nat.card G : ℂ)) *
          ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ) ⟨g, by simp⟩)) := by
          rw [mul_assoc]
    _ = ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ) ⟨g, by simp⟩) := by
          rw [inv_mul_cancel₀ hcard, one_mul]
    _ = (θ[G] : G → ℂ) g := by
          simpa using congrFun (top_cyclicGroupTheta_eq (G := G)) g

/-- Helper for Proposition 9-9.4-2: under the strong induction hypothesis on group order, the sum
of the induced `θ`-terms over the proper cyclic subgroups of `G` already lies in `R(G)`. -/
lemma proper_cyclic_subgroup_sum_mem_characterRing
    {n : ℕ} {G : Type u} [Group G] [Finite G] [DecidableEq (Subgroup G)]
    (ih : ∀ m : ℕ, m < n →
      ∀ (H : Type u) (_ : Group H) (_ : Finite H) (_ : IsCyclic H),
        Nat.card H = m → θ[H] ∈ R(H))
    (hGcard : Nat.card G = n) :
    Finset.sum ((Subgroup.cyclicSubgroups G).erase ⊤) (fun H ↦ Ind[H]((θ[H] : H → ℂ))) ∈ R(G) := by
  -- Each proper cyclic subgroup has smaller order, so the strong induction hypothesis applies to
  -- its `θ`-function before induction carries it back to `R(G)`.
  refine (R(G)).sum_mem ?_
  intro H hH
  have hHne : H ≠ ⊤ := (Finset.mem_erase.mp hH).1
  have hcycH : IsCyclic H := by
    exact Subgroup.mem_cyclicSubgroups.mp (Finset.mem_erase.mp hH).2
  have hthetaH : θ[H] ∈ R(H) := by
    have hlt : Nat.card H < n := by
      rw [← hGcard]
      exact subgroup_natCard_lt_of_ne_top H hHne
    simpa using ih (Nat.card H) hlt H inferInstance inferInstance hcycH rfl
  -- The owner-level induction theorem moves each subgroup character-ring element into `R(G)`.
  let χH : R(H) := ⟨(θ[H] : H → ℂ), hthetaH⟩
  simpa using Subgroup.inducedClassFunction_mem_characterRingOverField (K := ℂ) H χH

-- Source/core/bridge triage:
-- * source-facing: LinearRepresentations_Serre_1977's auxiliary class function `θ[A]` on a cyclic finite group.
-- * core/canonical: the character ring owner `R(A)`.
-- * bridge/view: for this owner-membership statement, the relevant derived API is the theorem
--   `Subgroup.inducedClassFunction_mem_characterRing`; the linear map
--   `Subgroup.characterRingInduction` from `9-9.2-1` is companion API, not the public center of
--   gravity here.
--
-- Proof sketch: proceed by induction on `Nat.card A`. Proposition `9-9.4-1` rewrites the
-- source-facing function `θ[A]` as the constant character `|A| • 1` minus the induced
-- contributions from the proper cyclic subgroups of `A`; the induction hypothesis places each
-- `θ[B]` in `R(B)`, and `Subgroup.inducedClassFunction_mem_characterRing` moves those induced
-- terms into `R(A)`.
/-- Proposition 9-9.4-2: if `A` is a cyclic finite group, then LinearRepresentations_Serre_1977's auxiliary function `θ_A`
belongs to the character ring `R(A)`. -/
theorem cyclicGroupTheta_mem_characterRing [IsCyclic A] :
    θ[A] ∈ R(A) := by
  classical
  let _ : CommGroup A := IsCyclic.commGroup
  let P : ℕ → Prop := fun n ↦
    ∀ (G : Type u) (_ : Group G) (_ : Finite G) (_ : IsCyclic G),
      Nat.card G = n → θ[G] ∈ R(G)
  have hstrong : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih G _ _ _ hGcard
    let _ : CommGroup G := IsCyclic.commGroup
    let _ : Fintype G := Fintype.ofFinite G
    let S : Finset (Subgroup G) := Subgroup.cyclicSubgroups G
    have htop : (⊤ : Subgroup G) ∈ S := by
      simpa [S] using (Subgroup.mem_cyclicSubgroups.2 inferInstance :
        (⊤ : Subgroup G) ∈ Subgroup.cyclicSubgroups G)
    -- Split Proposition 9-9.4-1 into the top subgroup term and the sum over proper cyclic
    -- subgroups.
    have hsplit :
        Finset.sum S (fun H ↦ Ind[H]((θ[H] : H → ℂ))) =
          Ind[(⊤ : Subgroup G)]((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ)) +
            Finset.sum (S.erase ⊤) (fun H ↦ Ind[H]((θ[H] : H → ℂ))) := by
      rw [← Finset.insert_erase htop]
      simp
    have hsum :
        Ind[(⊤ : Subgroup G)]((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → ℂ)) +
            Finset.sum (S.erase ⊤) (fun H ↦ Ind[H]((θ[H] : H → ℂ))) =
          (Nat.card G : ℂ) • (1 : G → ℂ) := by
      exact hsplit.symm.trans
        (sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one (G := G) (K := ℂ))
    -- Each proper cyclic subgroup term lands in the owner `R(G)` by the strong induction
    -- hypothesis followed by subgroup induction on character rings.
    have hproper :
        Finset.sum (S.erase ⊤) (fun H ↦ Ind[H]((θ[H] : H → ℂ))) ∈ R(G) := by
      simpa [S] using proper_cyclic_subgroup_sum_mem_characterRing (ih := ih) (hGcard := hGcard)
    -- The constant term is an integral multiple of the trivial character, hence also belongs to
    -- the character ring.
    have hconst : (Nat.card G : ℂ) • (1 : G → ℂ) ∈ R(G) := by
      convert ((((Fintype.card G : ℤ) • (1 : R(G))) : R(G)) : R(G)).property using 1
      ext g
      simp [Nat.card_eq_fintype_card, zsmul_eq_mul]
    -- Route correction: instead of recursive proof-script unfolding, isolate the `H = ⊤` term and
    -- rewrite LinearRepresentations_Serre_1977's identity as `θ[G] = |G| • 1 - (proper subgroup sum)`.
    have htheta_eq :
        (θ[G] : G → ℂ) =
          (Nat.card G : ℂ) • (1 : G → ℂ) -
            Finset.sum (S.erase ⊤) (fun H ↦ Ind[H]((θ[H] : H → ℂ))) := by
      rw [← top_induced_cyclicGroupTheta_eq (G := G)]
      exact eq_sub_iff_add_eq.2 hsum
    exact htheta_eq.symm ▸ (R(G)).sub_mem hconst hproper
  have hA : P (Nat.card A) := hstrong (Nat.card A)
  simpa using hA A inferInstance inferInstance inferInstance rfl

end

end Representation
