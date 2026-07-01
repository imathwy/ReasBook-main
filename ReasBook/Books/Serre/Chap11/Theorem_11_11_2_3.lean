import Serre.Chap10.Definition_10_10_1_3
import Serre.Chap10.Theorem_10_10_5_2
import Serre.Chap02.Theorem_2_2_5_2
import Serre.Chap03.Theorem_3_3_2_1
import Serre.Chap11.Theorem_11_11_2_2
import Serre.Chap01.Definition_1_1_2_1
import Serre.GroupTheory.ConjClassesPower
import Serre.RepresentationTheory.GroupFunctionPairing
import Serre.Chap06.Proposition_6_6_5_1
import Serre.Chap06.Corollary_6_6_5_3
import Serre.Chap06.Exercise_6_6_5_6
import Serre.Chap11.Theorem_11_11_2_3.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped MonoidAlgebra
open scoped Representation
open scoped SubgroupInduction

namespace Representation

section FrobeniusTheorem

variable {G : Type} [Group G] [Finite G]
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

local instance theorem_11_11_2_3_target_fintype : Fintype G := Fintype.ofFinite G

/-- A subgroup of a finite group is finite. -/
local instance theorem_11_11_2_3_target_subgroup_fintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

local instance theorem_11_11_2_3_target_nthPow_mem_conjClass_decidablePred
    (n : ℕ+) (c : ConjClasses G) :
    DecidablePred (fun x : G ↦ x ^ (n : ℕ) ∈ c.carrier) :=
  Classical.decPred _

/-- Helper for Theorem 11-11.2-3: after transporting the subgroup root-fiber sum through an
elementary decomposition `H ≃ C × P`, the degree-`1` character factors through the two product
coordinates. -/
private theorem elementary_rootfiber_sum_reindex_with_factored_character_local
    (n : ℕ+) (c : ConjClasses G) (H : Subgroup G) (χ : H →* ℂˣ)
    {p : ℕ} {C P : Subgroup H} (hCP : IsPElementaryDecomposition p C P) :
    let e := hCP.isComplement.prodMulEquiv hCP.commute
    let χe : C × P →* ℂˣ := χ.comp e.toMonoidHom
    Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
        (fun h ↦ (χ h : ℂ)) =
      Finset.sum (Finset.univ.filter fun y : C × P ↦
          (((e y : H) : G) ^ (n : ℕ) ∈ c.carrier))
        (fun y ↦
          ((χe.comp (MonoidHom.inl C P) y.1 : ℂˣ) : ℂ) *
            ((χe.comp (MonoidHom.inr C P) y.2 : ℂˣ) : ℂ)) := by
  let e := hCP.isComplement.prodMulEquiv hCP.commute
  let χe : C × P →* ℂˣ := χ.comp e.toMonoidHom
  -- First reindex the filtered sum along the elementary product decomposition.
  rw [filtered_rootFiber_sum_eq_sum_over_elementary_product (G := G) (n := n) (c := c)
    (H := H) (χ := χ) hCP]
  -- Then factor the transported linear character through the two coordinate inclusions.
  refine Finset.sum_congr rfl ?_
  intro y hy
  simpa [e, χe] using
    congrArg (fun z : ℂˣ ↦ (z : ℂ))
      (linearCharacter_on_prod_apply_eq_mul (χ := χe) y.1 y.2)

/-- Helper for Theorem 11-11.2-3: once the target denominator is rewritten through
`Nat.gcd (Nat.card H, n)`, the remaining elementary-subgroup arithmetic is the subgroup-gcd
normalized root-fiber sum. -/
lemma elementary_subgroup_gcd_normalized_rootfiber_sum_mem_range_integralClosure_local
    (n : ℕ+) (c : ConjClasses G)
    (H : Subgroup G) (hH : IsElementary H) (χ : H →* ℂˣ) :
    (((Nat.gcd (Nat.card H) (n : ℕ) : ℂ)⁻¹) *
        Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
          fun h ↦ (χ h : ℂ)) ∈
      Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  classical
  by_cases hroot : ∃ h : H, (h : G) ^ (n : ℕ) ∈ c.carrier
  · -- Route correction: instead of the stalled `C × P` transport, pair the already available
    -- weighted inverse owner with the subgroup character and clear the remaining denominator
    -- by the natural divisibility `orderOf (h0 ^ n) * gcd(|H|, n) ∣ |H|`.
    let _ := hH
    obtain ⟨h0, hh0⟩ := hroot
    let g0 : c.carrier := ⟨(h0 : G) ^ (n : ℕ), hh0⟩
    let S : ℂ :=
      Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
        fun h ↦ (χ h : ℂ)
    let η : G → ℂ := fun x ↦
      algebraMap (integralClosure ℤ ℂ) ℂ
          (((orderOf x / Nat.gcd (orderOf x) (n : ℕ)) : ℕ) :
            integralClosure ℤ ℂ) *
        Ψ^n(((c⁻¹).indicator : G → ℂ)) x
    have hη :
        η ∈ characterRingScalarExtension (integralClosure ℤ ℂ) G := by
      -- The weighted inverse conjugacy-class owner is already realized over the integral closure.
      simpa [η] using
        weighted_inverse_conjClass_mem_characterRingScalarExtension_integralClosure
          (G := G) n c
    have hηH :
        (fun h : H ↦ η h) ∈ characterRingScalarExtension (integralClosure ℤ ℂ) H := by
      -- Restrict the ambient scalar-extended owner to the subgroup.
      simpa [Subgroup.classFunctionRestriction_apply] using
        classFunctionRestriction_mem_characterRingScalarExtension_local
          (A := integralClosure ℤ ℂ) (G := G) H hη
    have hpair_range :
        ⟪(fun h : H ↦ η h), χ.toRepresentation.character⟫ ∈
          Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
      -- Repeat the scalar-extension span induction on the subgroup restriction.
      rw [characterRingScalarExtension] at hηH
      refine
        Submodule.span_induction
          (s := (R(H) : Set (H → ℂ)))
          (p := fun ψ _ ↦
            ⟪ψ, χ.toRepresentation.character⟫ ∈
              Set.range (algebraMap (integralClosure ℤ ℂ) ℂ))
          ?_ ?_ ?_ ?_ hηH
      · intro ψ hψ
        let ηR : R(H) := ⟨ψ, hψ⟩
        have hIntegral : IsIntegral ℤ ⟪ψ, χ.toRepresentation.character⟫ :=
          characterRing_pairing_isIntegral_with_rep_character ηR χ.toRepresentation
        exact
          (IsIntegralClosure.isIntegral_iff
            (A := integralClosure ℤ ℂ) (R := ℤ) (B := ℂ)).1 hIntegral
      · change groupFunctionPairingOverField ℂ (0 : H → ℂ) χ.toRepresentation.character ∈
            Set.range (algebraMap (integralClosure ℤ ℂ) ℂ)
        exact ⟨0, by simp [Representation.groupFunctionPairingOverField]⟩
      · intro ψ ξ _ _ hψ hξ
        simpa [Representation.groupFunctionPairing_add_left] using
          range_algebraMap_add_integralClosure hψ hξ
      · intro a ψ _ hψ
        have hsmul :
            ⟪a • ψ, χ.toRepresentation.character⟫ =
              algebraMap (integralClosure ℤ ℂ) ℂ a *
                ⟪ψ, χ.toRepresentation.character⟫ := by
          simpa using
            (Representation.groupFunctionPairing_smul_left
              (a := algebraMap (integralClosure ℤ ℂ) ℂ a)
              (φ := ψ) (ψ := χ.toRepresentation.character))
        rw [hsmul]
        exact range_algebraMap_mul_integralClosure ⟨a, rfl⟩ hψ
    have hweighted_range :
        (((Nat.card H : ℂ)⁻¹) * ((orderOf (g0 : G) : ℂ) * S)) ∈
          Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
      -- Evaluate the restricted weighted owner against the linear character.
      have hpair_eq :
          groupFunctionPairingOverField ℂ (fun h : H ↦ η h) χ.toRepresentation.character =
            ((Nat.card H : ℂ)⁻¹) * ((orderOf (g0 : G) : ℂ) * S) := by
        simpa [η, S] using
          (weighted_inverse_conjClass_restricted_pairing_eq
            (G := G) (n := n) (c := c) (g := g0) (H := H) (χ := χ))
      rw [hpair_eq] at hpair_range
      exact hpair_range
    have horder_dvd_card : orderOf (h0 : G) ∣ Nat.card H := by
      -- The chosen root lies in the finite subgroup `H`, so its order divides `|H|`.
      simpa [Subgroup.orderOf_mk] using (orderOf_dvd_natCard h0)
    have horder_g0 :
        orderOf (g0 : G) =
          orderOf (h0 : G) / Nat.gcd (orderOf (h0 : G)) (n : ℕ) := by
      -- The order of the `n`th power is the usual quotient by the gcd.
      simpa [g0] using (orderOf_pow (n := (n : ℕ)) (h0 : G))
    obtain ⟨k, hk⟩ := horder_dvd_card
    have hgcd_dvd :
        Nat.gcd (Nat.card H) (n : ℕ) ∣ Nat.gcd (orderOf (h0 : G)) (n : ℕ) * k := by
      -- Compare `gcd(|H|, n)` with `gcd(orderOf h0, n)` using `|H| = orderOf h0 * k`.
      rw [hk]
      have h₁ :
          Nat.gcd (n : ℕ) (orderOf (h0 : G) * k) ∣
            Nat.gcd (n : ℕ) (orderOf (h0 : G)) * Nat.gcd (n : ℕ) k := by
        simpa [Nat.mul_comm] using
          (gcd_mul_dvd_mul_gcd (n : ℕ) (orderOf (h0 : G)) k)
      have h₂ :
          Nat.gcd (n : ℕ) (orderOf (h0 : G)) * Nat.gcd (n : ℕ) k ∣
            Nat.gcd (n : ℕ) (orderOf (h0 : G)) * k := by
        exact Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_right (n : ℕ) k)
      simpa [Nat.gcd_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        dvd_trans h₁ h₂
    have hprod_dvd :
        orderOf (g0 : G) * Nat.gcd (Nat.card H) (n : ℕ) ∣ Nat.card H := by
      -- Clearing the common factor `gcd(orderOf h0, n)` leaves the desired product divisor.
      have hleft :
          orderOf (g0 : G) * Nat.gcd (Nat.card H) (n : ℕ) ∣
            orderOf (g0 : G) * (Nat.gcd (orderOf (h0 : G)) (n : ℕ) * k) := by
        exact Nat.mul_dvd_mul_left _ hgcd_dvd
      have hright :
          orderOf (g0 : G) * (Nat.gcd (orderOf (h0 : G)) (n : ℕ) * k) = Nat.card H := by
        calc
          orderOf (g0 : G) * (Nat.gcd (orderOf (h0 : G)) (n : ℕ) * k)
              = (orderOf (h0 : G) / Nat.gcd (orderOf (h0 : G)) (n : ℕ)) *
                  (Nat.gcd (orderOf (h0 : G)) (n : ℕ) * k) := by
                    rw [horder_g0]
          _ = ((orderOf (h0 : G) / Nat.gcd (orderOf (h0 : G)) (n : ℕ)) *
                Nat.gcd (orderOf (h0 : G)) (n : ℕ)) * k := by
                  ring
          _ = orderOf (h0 : G) * k := by
                rw [Nat.div_mul_cancel (Nat.gcd_dvd_left (orderOf (h0 : G)) (n : ℕ))]
          _ = Nat.card H := hk.symm
      exact hright ▸ hleft
    obtain ⟨q, hq⟩ := hprod_dvd
    have hq_order :
        q * orderOf (g0 : G) = Nat.card H / Nat.gcd (Nat.card H) (n : ℕ) := by
      -- Re-express the quotient `|H| / gcd(|H|, n)` using the divisor extracted above.
      apply Nat.eq_of_mul_eq_mul_right (Nat.gcd_pos_of_pos_right _ n.pos)
      calc
        (q * orderOf (g0 : G)) * Nat.gcd (Nat.card H) (n : ℕ)
            = orderOf (g0 : G) * Nat.gcd (Nat.card H) (n : ℕ) * q := by
                ring
        _ = Nat.card H := by
              simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hq.symm
        _ = (Nat.card H / Nat.gcd (Nat.card H) (n : ℕ)) *
              Nat.gcd (Nat.card H) (n : ℕ) := by
              rw [Nat.div_mul_cancel (Nat.gcd_dvd_left (Nat.card H) (n : ℕ))]
    have hnormalize :
        (((Nat.gcd (Nat.card H) (n : ℕ) : ℂ)⁻¹) * S) =
          algebraMap (integralClosure ℤ ℂ) ℂ (q : integralClosure ℤ ℂ) *
            (((Nat.card H : ℂ)⁻¹) * ((orderOf (g0 : G) : ℂ) * S)) := by
      have hcard_ne_zero : (Nat.card H : ℂ) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      have hgcd_ne_zero : ((Nat.gcd (Nat.card H) (n : ℕ) : ℕ) : ℂ) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr (Nat.gcd_ne_zero_right n.ne_zero)
      have hq_cast :
          ((q * orderOf (g0 : G) : ℕ) : ℂ) =
            ((Nat.card H / Nat.gcd (Nat.card H) (n : ℕ) : ℕ) : ℂ) := by
        exact_mod_cast hq_order
      have hquotient :
          (((Nat.card H / Nat.gcd (Nat.card H) (n : ℕ) : ℕ) : ℂ) *
              (Nat.card H : ℂ)⁻¹) =
            ((Nat.gcd (Nat.card H) (n : ℕ) : ℂ)⁻¹) := by
        rw [Nat.cast_div (Nat.gcd_dvd_left (Nat.card H) (n : ℕ))]
        · field_simp [hcard_ne_zero, hgcd_ne_zero]
        · exact hgcd_ne_zero
      calc
        ((Nat.gcd (Nat.card H) (n : ℕ) : ℂ)⁻¹) * S
            = ((((Nat.card H / Nat.gcd (Nat.card H) (n : ℕ) : ℕ) : ℂ) *
                (Nat.card H : ℂ)⁻¹) * S) := by
                  rw [hquotient]
        _ = ((((q : ℕ) : ℂ) * (orderOf (g0 : G) : ℂ)) *
              (Nat.card H : ℂ)⁻¹ * S) := by
              rw [← hq_cast]
              simp [Nat.cast_mul, mul_assoc]
        _ = algebraMap (integralClosure ℤ ℂ) ℂ (q : integralClosure ℤ ℂ) *
              (((Nat.card H : ℂ)⁻¹) * ((orderOf (g0 : G) : ℂ) * S)) := by
              simp [mul_assoc, mul_left_comm, mul_comm]
    -- Multiply the weighted range statement by the integral quotient `q`.
    rw [hnormalize]
    exact
      range_algebraMap_mul_integralClosure
        ⟨(q : integralClosure ℤ ℂ), rfl⟩ hweighted_range
  · -- If the subgroup root fiber is empty, then the filtered sum itself vanishes.
    have hsum :
        Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
            (fun h ↦ (χ h : ℂ)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro h hh
      exfalso
      exact hroot ⟨h, by simpa using hh⟩
    rw [hsum]
    exact ⟨0, by simp⟩

/-- Helper for Theorem 11-11.2-3: on an elementary subgroup, the normalized root-fiber sum of a
degree-`1` character lies in the image of the integral closure. -/
lemma elementary_linearCharacter_normalized_rootfiber_sum_mem_range_integralClosure
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier)
    (H : Subgroup G) (hH : IsElementary H) (χ : H →* ℂˣ) :
    (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
        Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
          fun h ↦ (χ h : ℂ)) ∈
      Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  classical
  by_cases hroot : ∃ h : H, (h : G) ^ (n : ℕ) ∈ c.carrier
  · -- Route correction: the weighted-owner comparison cannot supply this normalized denominator.
    -- The only remaining arithmetic is the subgroup-gcd-normalized sum, after rewriting the
    -- class-order denominator through `Nat.gcd (Nat.card H) n`.
    have hrewrite :
        (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
            Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
              fun h ↦ (χ h : ℂ)) =
          algebraMap (integralClosure ℤ ℂ) ℂ
              (((Nat.gcd (Nat.card H) (n : ℕ) /
                    Nat.gcd (orderOf (g : G)) (n : ℕ) : ℕ) :
                  integralClosure ℤ ℂ)) *
            ((((Nat.gcd (Nat.card H) (n : ℕ) : ℂ)⁻¹) *
                Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
                  fun h ↦ (χ h : ℂ))) := by
      rw [inv_classOrder_gcd_eq_integral_scalar_mul_inv_subgroup_gcd_of_exists_root
        (G := G) n c g H hroot]
      ring
    rw [hrewrite]
    exact
      range_algebraMap_mul_integralClosure
        ⟨((Nat.gcd (Nat.card H) (n : ℕ) /
              Nat.gcd (orderOf (g : G)) (n : ℕ) : ℕ) :
            integralClosure ℤ ℂ), rfl⟩
        (elementary_subgroup_gcd_normalized_rootfiber_sum_mem_range_integralClosure_local
          (G := G) n c H hH χ)
  · -- If there are no subgroup roots landing in `c`, then the filtered sum itself is zero.
    rw [normalized_rootfiber_sum_eq_zero_of_no_subgroup_root (G := G) n c g H χ hroot]
    exact ⟨0, by simp⟩

/-- Helper for Theorem 11-11.2-3: the restricted pairing with the normalized inverse root owner
is the subgroup index times the normalized subgroup root-fiber sum. -/
lemma linearCharacter_pairing_restrict_normalizedInverseNthRootIndicator_eq
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier)
    (H : Subgroup G) (χ : H →* ℂˣ) :
    ⟪χ.toCharacterRing,
        Subgroup.classFunctionRestriction H
          ⟨normalizedInverseNthRootIndicator n c g,
            normalizedInverseNthRootIndicator_mem_classFunctionSubmodule (G := G) n c g⟩⟫ =
      (((Nat.card H : ℂ)⁻¹) * (Nat.card G : ℂ)) *
        (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
          Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
            fun h ↦ (χ h : ℂ)) := by
  -- Repackage the already-proved raw subgroup pairing identity in the bundled restriction
  -- notation expected by Theorem `11-11.1-4`.
  simpa [Subgroup.classFunctionRestriction_apply, MonoidHom.toCharacterRing_apply] using
    linearCharacter_pairing_normalizedInverseNthRootIndicator_eq
      (G := G) n c g H χ

/-- Helper for Theorem 11-11.2-3: every elementary-subgroup linear-character pairing with the
normalized inverse root owner lands in the image of the integral closure. -/
lemma normalizedInverseNthRootIndicator_pairing_mem_range_on_elementary_linearCharacters
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier)
    (H : Subgroup G) (hH : IsElementary H) (χ : H →* ℂˣ) :
    ⟪χ.toCharacterRing,
        Subgroup.classFunctionRestriction H
          (normalizedInverseNthRootIndicatorClassFunction (G := G) n c g)⟫ ∈
      Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  have hindex :
      (((Nat.card H : ℂ)⁻¹) * (Nat.card G : ℂ)) ∈
        Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) :=
    subgroup_index_scalar_mem_range_integralClosure (G := G) H
  have hroot :
      (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
          Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
            fun h ↦ (χ h : ℂ)) ∈
        Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) :=
    elementary_linearCharacter_normalized_rootfiber_sum_mem_range_integralClosure
      (G := G) n c g H hH χ
  have hpair_eq :
      ⟪χ.toCharacterRing,
          Subgroup.classFunctionRestriction H
            (normalizedInverseNthRootIndicatorClassFunction (G := G) n c g)⟫ =
        (((Nat.card H : ℂ)⁻¹) * (Nat.card G : ℂ)) *
          (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
            Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
              fun h ↦ (χ h : ℂ)) := by
    -- Unfold the bundled owner back to the literal class-function restriction formula.
    simpa [normalizedInverseNthRootIndicatorClassFunction] using
      linearCharacter_pairing_restrict_normalizedInverseNthRootIndicator_eq
        (G := G) n c g H χ
  -- Multiply the subgroup-index factor with the normalized root-fiber factor inside the
  -- integral-closure image, then rewrite back to the pairing formula.
  rw [hpair_eq]
  exact range_algebraMap_mul_integralClosure hindex hroot

/-- Helper for Theorem 11-11.2-3: the bundled inverse-root owner satisfies the exact elementary
pairing hypothesis required by Chapter `11.1.4`. -/
lemma normalizedInverseNthRootIndicator_pairing_hypothesis
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) :
    ∀ (H : Subgroup G) (_ : IsElementary H) (χ : H →* ℂˣ),
      ⟪χ.toCharacterRing,
          Subgroup.classFunctionRestriction H
            (normalizedInverseNthRootIndicatorClassFunction (G := G) n c g)⟫ ∈
        Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  intro H hH χ
  -- This is exactly the previously established subgroup pairing statement, repackaged as a
  -- single hypothesis for the downstream descent theorem.
  exact
    normalizedInverseNthRootIndicator_pairing_mem_range_on_elementary_linearCharacters
      (G := G) n c g H hH χ

/-- Helper for Theorem 11-11.2-3: pairing a realized integral-closure scalar-extension class
function on a subgroup with a genuine subgroup character stays inside the integral-closure image. -/
lemma scalarExtension_pairing_mem_range_with_rep_character_local
    {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (η : H → ℂ)
    (hη : η ∈ characterRingScalarExtension (integralClosure ℤ ℂ) H)
    (ρ : Representation ℂ H W) :
    ⟪η, ρ.character⟫ ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  -- Repeat the scalar-extension span induction locally so the subgroup pairing argument can use
  -- it before the global helper theorem is introduced later in the file.
  rw [characterRingScalarExtension] at hη
  refine
    Submodule.span_induction
      (s := (R(H) : Set (H → ℂ)))
      (p := fun ψ _ ↦
        ⟪ψ, ρ.character⟫ ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ))
      ?_ ?_ ?_ ?_ hη
  · intro ψ hψ
    let ηR : R(H) := ⟨ψ, hψ⟩
    have hIntegral : IsIntegral ℤ ⟪ψ, ρ.character⟫ :=
      characterRing_pairing_isIntegral_with_rep_character ηR ρ
    exact
      (IsIntegralClosure.isIntegral_iff
        (A := integralClosure ℤ ℂ) (R := ℤ) (B := ℂ)).1 hIntegral
  · change groupFunctionPairingOverField ℂ (0 : H → ℂ) ρ.character ∈
        Set.range (algebraMap (integralClosure ℤ ℂ) ℂ)
    exact ⟨0, by simp [Representation.groupFunctionPairingOverField]⟩
  · intro ψ ξ _ _ hψ hξ
    simpa [Representation.groupFunctionPairing_add_left] using
      range_algebraMap_add_integralClosure hψ hξ
  · intro a ψ _ hψ
    have hsmul :
        ⟪a • ψ, ρ.character⟫ =
          algebraMap (integralClosure ℤ ℂ) ℂ a * ⟪ψ, ρ.character⟫ := by
      simpa using
        (Representation.groupFunctionPairing_smul_left
          (a := algebraMap (integralClosure ℤ ℂ) ℂ a)
          (φ := ψ) (ψ := ρ.character))
    rw [hsmul]
    exact range_algebraMap_mul_integralClosure ⟨a, rfl⟩ hψ

/-- Helper for Theorem 11-11.2-3: multiplying an induced class function by the ambient owner is
the same as inducing the product with the subgroup restriction. -/
private theorem induced_mul_eq_induced_mul_classFunctionRestriction_local
    (H : Subgroup G) (ψ : H → ℂ) (φ : classFunctionSubmodule ℂ G) :
    Ind[H](ψ) * (φ : G → ℂ) =
      Ind[H](fun h : H ↦ ψ h * (H.classFunctionRestriction φ : H → ℂ) h) := by
  -- Reuse the Chapter `11.1.4` induction-product compatibility verbatim.
  simpa using induced_mul_eq_induced_mul_classFunctionRestriction (H := H) (ψ := ψ) (φ := φ)

/-- Helper for Theorem 11-11.2-3: every realized scalar-extension element comes from an actual
tensor character over the integral closure. -/
private theorem tensorCharacter_exists_of_mem_characterRingScalarExtension_local
    {f : G → ℂ}
    (hf : f ∈ characterRingScalarExtension (integralClosure ℤ ℂ) G) :
    ∃ χ : (integralClosure ℤ ℂ) ⊗R(G), (χ : G → ℂ) = f := by
  -- This is exactly the realized-span-to-tensor bridge from Chapter `11.1.4`.
  simpa using
    tensorCharacter_exists_of_mem_characterRingScalarExtension (A := integralClosure ℤ ℂ) hf

/-- Helper for Theorem 11-11.2-3: the unit character acts trivially on class functions by
pointwise multiplication. -/
private theorem one_character_mul_classFunction_local
    {G' : Type} [Group G']
    (φ : classFunctionSubmodule ℂ G') :
    ((1 : R(G')) : G' → ℂ) * (φ : G' → ℂ) = (φ : G' → ℂ) := by
  -- Evaluate pointwise: the unit character has constant value `1`.
  ext x
  simp

/-- Helper for Theorem 11-11.2-3: Frobenius reciprocity identifies the pairing of an induced
linear character with the corresponding subgroup restriction. -/
private theorem groupFunctionPairing_induced_linearCharacter_eq_restriction_local
    {H : Type} [Group H] [Finite H]
    (K : Subgroup H) (α : K →* ℂˣ) (x : classFunctionSubmodule ℂ H) :
    ⟪Ind[K](α.toRepresentation.character), (x : H → ℂ)⟫ =
      ⟪α.toCharacterRing, Subgroup.classFunctionRestriction K x⟫ := by
  classical
  let _ : NeZero (Nat.card H : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  let _ : NeZero (Nat.card K : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  let _ : Invertible (Nat.card H : ℂ) := invertibleOfNonzero <| by
    exact NeZero.ne (Nat.card H : ℂ)
  let _ : Invertible (Nat.card K : ℂ) := invertibleOfNonzero <| by
    exact NeZero.ne (Nat.card K : ℂ)
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    FDRep.exists_complete_pairwise_nonisomorphic_simple_family (k := ℂ) (G := H)
  let b := irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    π hπ_pairwise hπ_complete
  let inducedPairing : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦ ⟪Ind[K](α.toRepresentation.character), (y : H → ℂ)⟫
      map_add' := by
        intro y z
        simpa using
          Representation.groupFunctionPairing_add_right
            (Ind[K](α.toRepresentation.character)) (y : H → ℂ) (z : H → ℂ)
      map_smul' := by
        intro a y
        simpa using
          Representation.groupFunctionPairing_smul_right
            (a := a) (φ := Ind[K](α.toRepresentation.character)) (ψ := (y : H → ℂ)) }
  let restrictedPairing : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦ ⟪α.toCharacterRing, Subgroup.classFunctionRestriction K y⟫
      map_add' := by
        intro y z
        simp [Representation.groupFunctionPairing_add_right]
      map_smul' := by
        intro a y
        simp [Representation.groupFunctionPairing_smul_right] }
  have hmaps : inducedPairing = restrictedPairing := by
    -- Compare the two pairing functionals on the irreducible-character basis of `H`.
    apply b.ext
    intro i
    have hind :
        Ind[K](α.toRepresentation.character) =
          (Representation.ind K.subtype α.toRepresentation).character := by
      simpa using
        (Subgroup.inducedClassFunction_eq_character_ind (H := K) (θ := α.toRepresentation))
    have hrestrict :
        ((Subgroup.classFunctionRestriction K (b i) : classFunctionSubmodule ℂ K) : K → ℂ) =
          Representation.character ((π i).ρ.comp K.subtype) := by
      ext k
      simp [b, irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply,
        Subgroup.classFunctionRestriction_apply, FDRep.character, Representation.character]
    -- Frobenius reciprocity on characters gives the equality on each basis vector.
    calc
      inducedPairing (b i)
          = ⟪(Representation.ind K.subtype α.toRepresentation).character,
              (π i).character⟫ := by
              simp [inducedPairing, hind, b,
                irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
      _ = ⟪α.toRepresentation.character,
              Representation.character ((π i).ρ.comp K.subtype)⟫ := by
            simpa using
              (groupFunctionPairing_character_comp_eq_character_ind_local
                (α := K.subtype) (E := (π i).ρ) (θ := α.toRepresentation)).symm
      _ = restrictedPairing (b i) := by
            simp [restrictedPairing, hrestrict]
  -- Apply the equality of linear functionals to the target class function.
  have hmaps_apply := congrArg
    (fun f : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ ↦ f x) hmaps
  simpa [inducedPairing, restrictedPairing] using hmaps_apply

/-- Helper for Theorem 11-11.2-3: once the degree-`1` pairing criterion holds on every
elementary subgroup, it extends by linearity to every character in the monomial-character span of
an elementary subgroup. -/
private theorem pairing_mem_range_of_mem_monomialCharacterSpan_on_elementary_restriction_local_u
    (φ : classFunctionSubmodule ℂ G)
    (hpair : ∀ (H : Subgroup G) (_ : IsElementary H) (χ : H →* ℂˣ),
      ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction H φ⟫ ∈
        Set.range (algebraMap (integralClosure ℤ ℂ) ℂ))
    (H : Subgroup G) (hH : IsElementary H)
    {η : R(H)} (hη : η ∈ monomialCharacterSpan ↥H) :
    ⟪(η : H → ℂ), Subgroup.classFunctionRestriction H φ⟫ ∈
      Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  rw [Representation.monomialCharacterSpan] at hη
  induction hη using Submodule.span_induction with
  | mem ξ hξ =>
      rcases hξ with ⟨K, α, hα⟩
      rw [← hα]
      rw [groupFunctionPairing_induced_linearCharacter_eq_restriction_local]
      exact
        pairing_mem_range_on_nested_elementary_linear_character_local
          (A := integralClosure ℤ ℂ) φ hpair H hH K α
  | zero =>
      refine ⟨0, ?_⟩
      simp [Representation.groupFunctionPairingOverField]
  | add ξ ζ _ _ hξ hζ =>
      rcases hξ with ⟨a, ha⟩
      rcases hζ with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      simp [Representation.groupFunctionPairing_add_left, ha, hb, map_add]
  | smul n ξ _ hξ =>
      rcases hξ with ⟨a, ha⟩
      refine ⟨(n : integralClosure ℤ ℂ) * a, ?_⟩
      have hsmul :
          ⟪((n : ℤ) • (ξ : H → ℂ)), Subgroup.classFunctionRestriction H φ⟫ =
            (n : ℂ) * ⟪(ξ : H → ℂ), Subgroup.classFunctionRestriction H φ⟫ := by
        simpa using
          (Representation.groupFunctionPairing_smul_left
            (a := (n : ℂ)) (φ := (ξ : H → ℂ))
            (ψ := Subgroup.classFunctionRestriction H φ))
      change algebraMap (integralClosure ℤ ℂ) ℂ ((n : integralClosure ℤ ℂ) * a) =
        ⟪((n • ξ : R(H)) : H → ℂ), Subgroup.classFunctionRestriction H φ⟫
      calc
        algebraMap (integralClosure ℤ ℂ) ℂ ((n : integralClosure ℤ ℂ) * a) =
            (n : ℂ) * ⟪(ξ : H → ℂ), Subgroup.classFunctionRestriction H φ⟫ := by
              simp [ha, map_mul]
        _ = ⟪((n : ℤ) • (ξ : H → ℂ)), Subgroup.classFunctionRestriction H φ⟫ := hsmul.symm
        _ = ⟪((n • ξ : R(H)) : H → ℂ), Subgroup.classFunctionRestriction H φ⟫ := by
              rfl

/-- Helper for Theorem 11-11.2-3: the degree-`1` pairing hypothesis forces every elementary
subgroup restriction to lie in the corresponding integral-closure scalar extension. -/
private theorem elementary_restriction_mem_characterRingScalarExtension_of_pairing_mem_range_local_u
    (φ : classFunctionSubmodule ℂ G)
    (hpair : ∀ (H : Subgroup G) (_ : IsElementary H) (χ : H →* ℂˣ),
      ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction H φ⟫ ∈
        Set.range (algebraMap (integralClosure ℤ ℂ) ℂ))
    (H : Subgroup G) (hH : IsElementary H) :
    (Subgroup.classFunctionRestriction H φ : H → ℂ) ∈
      characterRingScalarExtension (integralClosure ℤ ℂ) H := by
  classical
  let _ : NeZero (Nat.card H : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    FDRep.exists_complete_pairwise_nonisomorphic_simple_family (k := ℂ) (G := ↥H)
  let b := irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    π hπ_pairwise hπ_complete
  let x : classFunctionSubmodule ℂ H := Subgroup.classFunctionRestriction H φ
  have hsum :
      ((((∑ i, ((b.repr x i) • b i : classFunctionSubmodule ℂ H)) :
          classFunctionSubmodule ℂ H) : H → ℂ)) ∈
        characterRingScalarExtension (integralClosure ℤ ℂ) H := by
    have hsum_fun :
        (∑ i, ((((b.repr x i) • b i : classFunctionSubmodule ℂ H) : H → ℂ))) ∈
          characterRingScalarExtension (integralClosure ℤ ℂ) H := by
      refine Submodule.sum_mem (characterRingScalarExtension (integralClosure ℤ ℂ) H) ?_
      intro i hi
      have hmono : fdRepCharacterRing (π i) ∈ monomialCharacterSpan ↥H := by
        rw [monomialCharacterSpan_eq_top_of_isElementary (G := ↥H) hH]
        simp
      have hpairing :
          ⟪((fdRepCharacterRing (π i) : R(H)) : H → ℂ), (x : H → ℂ)⟫ ∈
            Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) :=
        pairing_mem_range_of_mem_monomialCharacterSpan_on_elementary_restriction_local_u
          φ hpair H hH hmono
      rcases hpairing with ⟨a, ha⟩
      have ha' : algebraMap (integralClosure ℤ ℂ) ℂ a =
          Representation.groupFunctionPairingOverField ℂ (x : H → ℂ) (π i).character := by
        simpa [fdRepCharacterRing, Representation.groupFunctionPairing_comm] using ha
      have hcoeff : b.repr x i = algebraMap (integralClosure ℤ ℂ) ℂ a := by
        calc
          b.repr x i =
              Representation.groupFunctionPairingOverField ℂ (x : H → ℂ) (π i).character :=
            repr_irreducible_character_basis_eq_pairing_local
              (π := π) hπ_pairwise hπ_complete x i
          _ = algebraMap (integralClosure ℤ ℂ) ℂ a := ha'.symm
      have hbase :
          (((b i : classFunctionSubmodule ℂ H) : H → ℂ)) ∈
            characterRingScalarExtension (integralClosure ℤ ℂ) H := by
        have hb :
            (((b i : classFunctionSubmodule ℂ H) : H → ℂ)) =
              (((fdRepCharacterRing (π i) : R(H)) : H → ℂ)) := by
          ext h
          simp [b, irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
        rw [hb]
        exact mem_characterRingScalarExtension_of_mem_characterRing
          (A := integralClosure ℤ ℂ)
          (((fdRepCharacterRing (π i) : R(H)) : H → ℂ))
          (fdRepCharacterRing (π i)).property
      have hterm :
          ((((b.repr x i) • b i : classFunctionSubmodule ℂ H) : H → ℂ)) =
            a • (((b i : classFunctionSubmodule ℂ H) : H → ℂ)) := by
        ext h
        simp [hcoeff, Algebra.smul_def]
      rw [hterm]
      exact (characterRingScalarExtension (integralClosure ℤ ℂ) H).smul_mem a hbase
    have hsum_coe :
        (∑ i, ((((b.repr x i) • b i : classFunctionSubmodule ℂ H) : H → ℂ))) =
          ((((∑ i, ((b.repr x i) • b i : classFunctionSubmodule ℂ H)) :
              classFunctionSubmodule ℂ H) : H → ℂ)) := by
      ext h
      let eval_h : classFunctionSubmodule ℂ H →ₗ[ℂ] ℂ :=
        { toFun := fun z ↦ z h
          map_add' := by
            intro y z
            rfl
          map_smul' := by
            intro a z
            rfl }
      simpa using
        (_root_.map_sum eval_h
          (fun j ↦ ((b.repr x j) • b j : classFunctionSubmodule ℂ H)) Finset.univ).symm
    exact hsum_coe.symm ▸ hsum_fun
  have hx :
      ((((∑ i, ((b.repr x i) • b i : classFunctionSubmodule ℂ H)) :
          classFunctionSubmodule ℂ H) : H → ℂ)) = (x : H → ℂ) := by
    exact congrArg (fun z : classFunctionSubmodule ℂ H ↦ (z : H → ℂ)) (b.sum_repr x)
  simpa [x] using hx ▸ hsum

/-- Helper for Theorem 11-11.2-3: the packaged owner already satisfies the elementary pairing
hypothesis in the exact bundled form used later in the proof. -/
private theorem normalizedInverseNthRootIndicator_packaged_pairing_hypothesis_local
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) :
    ∀ (H : Subgroup G) (_ : IsElementary H) (χ : H →* ℂˣ),
      ⟪χ.toCharacterRing,
          Subgroup.classFunctionRestriction H
            (normalizedInverseNthRootIndicatorClassFunction (G := G) n c g)⟫ ∈
        Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  intro H hH χ
  exact normalizedInverseNthRootIndicator_pairing_hypothesis (G := G) n c g H hH χ

/-- Helper for Theorem 11-11.2-3: the Chapter `11.1.4` elementary-pairing criterion can be used
directly in the realized scalar-extension form needed in this file. -/
lemma mem_characterRingScalarExtension_of_pairing_mem_range_on_elementary_linearCharacters_local_u
    (φ : classFunctionSubmodule ℂ G)
    (hpair : ∀ (H : Subgroup G) (_ : IsElementary H) (χ : H →* ℂˣ),
        ⟪χ.toCharacterRing, Subgroup.classFunctionRestriction H φ⟫ ∈
          Set.range (algebraMap (integralClosure ℤ ℂ) ℂ)) :
    (φ : G → ℂ) ∈ characterRingScalarExtension (integralClosure ℤ ℂ) G := by
  have hres : ∀ H : Subgroup G, IsElementary H →
      (H.classFunctionRestriction φ : H → ℂ) ∈
        characterRingScalarExtension (integralClosure ℤ ℂ) H := by
    intro H hH
    exact
      elementary_restriction_mem_characterRingScalarExtension_of_pairing_mem_range_local_u
        φ hpair H hH
  have hone :
      ((1 : R(G)) : G → ℂ) * (φ : G → ℂ) ∈
        characterRingScalarExtension (integralClosure ℤ ℂ) G := by
    have hone' : (1 : R(G)) ∈ (⨆ p : Nat.Primes, V[p](G)) := by
      simpa using character_mem_iSup_pElementaryInducedCharacterSpan (G := G) (1 : R(G))
    refine Submodule.iSup_induction
        (p := fun p : Nat.Primes ↦ V[p](G))
        (motive := fun χ : R(G) ↦
          ((χ : G → ℂ) * (φ : G → ℂ)) ∈
            characterRingScalarExtension (integralClosure ℤ ℂ) G)
        hone' ?_ ?_ ?_
    · intro p χ hχ
      exact
        pElementaryInducedCharacterSpan_mul_classFunction_mem_characterRingScalarExtension_local
          (A := integralClosure ℤ ℂ) φ hres p hχ
    · simp
    · intro χ ψ hχ hψ
      simpa [add_mul] using
        (characterRingScalarExtension (integralClosure ℤ ℂ) G).add_mem hχ hψ
  simpa [one_character_mul_classFunction_local φ] using hone

/-- Helper for Theorem 11-11.2-3: the elementary pairing hypothesis immediately specializes to
cyclic subgroups because cyclic groups are elementary. -/
private theorem normalizedInverseNthRootIndicator_pairing_mem_range_on_cyclicSubgroups_local
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier)
    (H : Subgroup G) (hH : IsCyclic H) (χ : H →* ℂˣ) :
    ⟪χ.toCharacterRing,
        Subgroup.classFunctionRestriction H
          (normalizedInverseNthRootIndicatorClassFunction (G := G) n c g)⟫ ∈
      Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  -- Upgrade the cyclic subgroup to an elementary subgroup and reuse the established pairing
  -- criterion.
  exact
    normalizedInverseNthRootIndicator_pairing_hypothesis (G := G) n c g H
      (isElementary_of_isCyclic_local hH) χ

/-- Helper for Theorem 11-11.2-3: the normalized inverse `n`th-root owner already belongs to the
realized integral-closure character span once the elementary-subgroup pairing criterion is
available in the current dependency closure. -/
lemma normalizedInverseNthRootIndicator_mem_characterRingScalarExtension_via_weighted_inverse
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) :
    normalizedInverseNthRootIndicator n c g ∈
      characterRingScalarExtension (integralClosure ℤ ℂ) G := by
  -- Route correction: the final descent is now a direct Chapter `11.1.4` application through
  -- the packaged pairing hypothesis, so the only remaining blocker in the file is arithmetic.
  simpa [normalizedInverseNthRootIndicatorClassFunction] using
    mem_characterRingScalarExtension_of_pairing_mem_range_on_elementary_linearCharacters_local_u
      (φ := normalizedInverseNthRootIndicatorClassFunction (G := G) n c g)
      (normalizedInverseNthRootIndicator_packaged_pairing_hypothesis_local (G := G) n c g)

/-- Helper for Theorem 11-11.2-3: the inverse `n`th-root indicator belongs to the integral-closure
scalar extension of the character ring. -/
lemma normalizedInverseNthRootIndicator_mem_characterRingScalarExtension_integralClosure
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) :
    normalizedInverseNthRootIndicator n c g ∈
      characterRingScalarExtension (integralClosure ℤ ℂ) G := by
  -- Route correction: compare directly with the already-realized weighted inverse-class Adams
  -- transform instead of rebuilding the owner through subgroup pairings.
  simpa using
    normalizedInverseNthRootIndicator_mem_characterRingScalarExtension_via_weighted_inverse
      (G := G) n c g

/-- Helper for Theorem 11-11.2-3: pairing an integral-closure scalar-extended class function with
an honest representation character stays in the image of `integralClosure ℤ ℂ`. -/
lemma scalarExtension_pairing_mem_range_with_rep_character
    (η : G → ℂ)
    (hη : η ∈ characterRingScalarExtension (integralClosure ℤ ℂ) G)
    (ρ : Representation ℂ G V) :
    ⟪η, ρ.character⟫ ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  -- The ambient-group case is the local scalar-extension pairing lemma with `H = G`.
  exact scalarExtension_pairing_mem_range_with_rep_character_local (η := η) hη ρ

/-- Helper for Theorem 11-11.2-3: the raw `n`th-root class sum is already an algebraic integer;
the remaining difficulty in the main theorem is only the extra division by `gcd(orderOf g,n)`. -/
lemma conjugacyClassNthRootCharacterSum_isIntegral
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) (ρ : Representation ℂ G V) :
    IsIntegral ℤ (conjugacyClassNthRootCharacterSum n c ρ) := by
  let η : G → ℂ :=
    fun x ↦
      algebraMap (integralClosure ℤ ℂ) ℂ
          (((orderOf x / Nat.gcd (orderOf x) (n : ℕ)) : ℕ) :
            integralClosure ℤ ℂ) *
        Ψ^n(((c⁻¹).indicator : G → ℂ)) x
  have hη :
      η ∈ characterRingScalarExtension (integralClosure ℤ ℂ) G := by
    simpa [η] using
      weighted_inverse_conjClass_mem_characterRingScalarExtension_integralClosure
        (G := G) n c
  have hpair_range :
      ⟪η, ρ.character⟫ ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) :=
    scalarExtension_pairing_mem_range_with_rep_character
      (G := G) (V := V) (η := η) hη ρ
  have hpair_integral : IsIntegral ℤ ⟪η, ρ.character⟫ :=
    (IsIntegralClosure.isIntegral_iff
      (A := integralClosure ℤ ℂ) (R := ℤ) (B := ℂ)).2 hpair_range
  have hscaled_integral :
      IsIntegral ℤ
        (((Nat.card G / orderOf (g : G) : ℕ) : ℂ) * ⟪η, ρ.character⟫) := by
    exact (isIntegral_algebraMap : IsIntegral ℤ (((Nat.card G / orderOf (g : G) : ℕ) : ℂ))).mul
      hpair_integral
  have hcard_ne_zero : (Nat.card G : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard_mul :
      (((Nat.card G / orderOf (g : G) : ℕ) : ℂ) * (orderOf (g : G) : ℂ)) =
        (Nat.card G : ℂ) := by
    exact_mod_cast Nat.div_mul_cancel (orderOf_dvd_natCard (g : G))
  have hscaled_eq :
      (((Nat.card G / orderOf (g : G) : ℕ) : ℂ) * ⟪η, ρ.character⟫) =
        conjugacyClassNthRootCharacterSum n c ρ := by
    rw [weighted_inverse_conjClass_pairing_eq (G := G) (V := V) (ρ := ρ) (g := g)]
    calc
      (((Nat.card G / orderOf (g : G) : ℕ) : ℂ) *
          (((orderOf (g : G) : ℂ) * (Nat.card G : ℂ)⁻¹) *
            conjugacyClassNthRootCharacterSum n c ρ))
        = ((((Nat.card G / orderOf (g : G) : ℕ) : ℂ) * (orderOf (g : G) : ℂ)) *
            (Nat.card G : ℂ)⁻¹) *
            conjugacyClassNthRootCharacterSum n c ρ := by
              ring
      _ = (((Nat.card G : ℂ) * (Nat.card G : ℂ)⁻¹) *
            conjugacyClassNthRootCharacterSum n c ρ) := by
              rw [hcard_mul]
      _ = conjugacyClassNthRootCharacterSum n c ρ := by
              rw [mul_inv_cancel₀ hcard_ne_zero, one_mul]
  exact hscaled_eq ▸ hscaled_integral

/-
theorem Representation.normalizedConjugacyClassNthRootCharacterSum_isIntegral
-/
/-- Theorem 11-11.2-3: for a conjugacy class `c`, a representative `g ∈ c`, and a complex
character `ρ.character` of `G`, the normalized sum of the values `ρ.character x` over all elements
whose `n`th power lies in `c` is an algebraic integer. -/
theorem normalizedConjugacyClassNthRootCharacterSum_isIntegral
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) (ρ : Representation ℂ G V) :
    IsIntegral ℤ
      (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
        conjugacyClassNthRootCharacterSum n c ρ) := by
  have hη :
      normalizedInverseNthRootIndicator n c g ∈
        characterRingScalarExtension (integralClosure ℤ ℂ) G :=
    normalizedInverseNthRootIndicator_mem_characterRingScalarExtension_integralClosure
      (G := G) n c g
  have hpair_range :
      ⟪normalizedInverseNthRootIndicator n c g, ρ.character⟫ ∈
        Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) :=
    scalarExtension_pairing_mem_range_with_rep_character
      (G := G) (V := V) (η := normalizedInverseNthRootIndicator n c g) hη ρ
  have hpair_integral :
      IsIntegral ℤ ⟪normalizedInverseNthRootIndicator n c g, ρ.character⟫ :=
    (IsIntegralClosure.isIntegral_iff
      (A := integralClosure ℤ ℂ) (R := ℤ) (B := ℂ)).2 hpair_range
  -- The source-facing pairing identity turns the scalar-extension integrality statement into the
  -- displayed normalized class sum.
  rwa [normalizedInverseNthRootIndicator_pairing_eq (G := G) (V := V) n c g ρ] at hpair_integral

end FrobeniusTheorem

end Representation
