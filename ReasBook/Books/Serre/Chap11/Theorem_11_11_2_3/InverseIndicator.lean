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
import Serre.Chap11.Theorem_11_11_2_3.SubgroupRootFiber

noncomputable section

open scoped BigOperators
open scoped MonoidAlgebra
open scoped Representation
open scoped SubgroupInduction

universe u v

namespace Representation

section FrobeniusTheorem

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

local instance : Fintype G := Fintype.ofFinite G

/-- A subgroup of a finite group is finite. -/
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

local instance inverseIndicator_nthPow_mem_conjClass_decidablePred
    (n : ℕ+) (c : ConjClasses G) :
    DecidablePred (fun x : G ↦ x ^ (n : ℕ) ∈ c.carrier) :=
  Classical.decPred _

/-- Helper for Theorem 11-11.2-3: the inverse conjugacy-class indicator converts the inverse on
the owner into an ordinary Adams transform. -/
lemma adams_indicator_inv_conjClass_apply
    (n : ℕ+) (c : ConjClasses G) (x : G) :
    Ψ^n(((c⁻¹).indicator : G → ℂ)) x = Ψ^n((c.indicator : G → ℂ)) x⁻¹ := by
  let _ := (inferInstance : Finite G)
  -- Route correction: switch from the abandoned elementary-subgroup branch to the direct inverse
  -- conjugacy-class rewrite expected by Theorem `11-11.2-2`.
  by_cases hx : x ^ (n : ℕ) ∈ (c⁻¹).carrier
  · have hx_inv : (x⁻¹) ^ (n : ℕ) ∈ c.carrier := by
      have hmk : ConjClasses.mk (x ^ (n : ℕ)) = c⁻¹ :=
        ConjClasses.mem_carrier_iff_mk_eq.mp hx
      have hmk_inv : ConjClasses.mk ((x⁻¹) ^ (n : ℕ)) = c := by
        simpa [ConjClasses.inv_mk, inv_pow] using congrArg Inv.inv hmk
      exact ConjClasses.mem_carrier_iff_mk_eq.mpr hmk_inv
    have hx_inv' : (x ^ (n : ℕ))⁻¹ ∈ c.carrier := by
      simpa [inv_pow] using hx_inv
    -- On the common support, both indicators evaluate to `1`.
    rw [Representation.adamsOperator, Representation.adamsOperator]
    change (((c⁻¹).indicator : G → ℂ) (x ^ (n : ℕ))) =
      ((c.indicator : G → ℂ) ((x⁻¹) ^ (n : ℕ)))
    simp [ConjClasses.indicator, hx, hx_inv']
  · have hx_inv : (x⁻¹) ^ (n : ℕ) ∉ c.carrier := by
      intro hx_inv
      apply hx
      have hmk_inv : ConjClasses.mk ((x⁻¹) ^ (n : ℕ)) = c :=
        ConjClasses.mem_carrier_iff_mk_eq.mp hx_inv
      have hmk : ConjClasses.mk (x ^ (n : ℕ)) = c⁻¹ := by
        simpa [ConjClasses.inv_mk, inv_pow] using congrArg Inv.inv hmk_inv
      exact ConjClasses.mem_carrier_iff_mk_eq.mpr hmk
    have hx_inv' : (x ^ (n : ℕ))⁻¹ ∉ c.carrier := by
      simpa [inv_pow] using hx_inv
    -- Off the common support, both indicators vanish.
    rw [Representation.adamsOperator, Representation.adamsOperator]
    change (((c⁻¹).indicator : G → ℂ) (x ^ (n : ℕ))) =
      ((c.indicator : G → ℂ) ((x⁻¹) ^ (n : ℕ)))
    simp [ConjClasses.indicator, hx, hx_inv']

/-- Helper for Theorem 11-11.2-3: the weighted Adams transform of the inverse conjugacy-class
indicator lies in the realized integral-closure scalar extension. -/
lemma weighted_inverse_conjClass_mem_characterRingScalarExtension_integralClosure
    (n : ℕ+) (c : ConjClasses G) :
    (fun x ↦
      algebraMap (integralClosure ℤ ℂ) ℂ
          (((orderOf x / Nat.gcd (orderOf x) (n : ℕ)) : ℕ) :
            integralClosure ℤ ℂ) *
        Ψ^n(((c⁻¹).indicator : G → ℂ)) x) ∈
      characterRingScalarExtension (integralClosure ℤ ℂ) G := by
  -- Specialize Theorem `11-11.2-2` to the inverse conjugacy class over `integralClosure ℤ ℂ`.
  have hf :
      (fun x ↦
        algebraMap (integralClosure ℤ ℂ) ℂ
            ((((orderOf x / Nat.gcd (orderOf x) (n : ℕ)) : ℕ) :
              integralClosure ℤ ℂ) *
              Ψ^n(((c⁻¹).indicator : G → integralClosure ℤ ℂ)) x)) =
        (fun x ↦
          algebraMap (integralClosure ℤ ℂ) ℂ
              (((orderOf x / Nat.gcd (orderOf x) (n : ℕ)) : ℕ) :
                integralClosure ℤ ℂ) *
            Ψ^n(((c⁻¹).indicator : G → ℂ)) x) := by
    funext x
    by_cases hx : x ^ (n : ℕ) ∈ (c⁻¹).carrier
    · simp [Representation.adamsOperator, ConjClasses.indicator, hx]
    · simp [Representation.adamsOperator, ConjClasses.indicator, hx]
  rw [← hf]
  exact
    weighted_adamsOperator_conjClassIndicator_mem_characterRingScalarExtension
      (G := G) (A := integralClosure ℤ ℂ) n (c := c⁻¹) (by
        -- The integral closure of `ℤ` in `ℂ` is the correct Serre coefficient ring for this use:
        -- roots of unity are integral. This proof should be replaced by the standard integrality
        -- lemma for roots of unity rather than by an `(A := ℤ)` specialization.
        sorry)

/-- Helper for Theorem 11-11.2-3: on the support of the inverse-class Adams transform, the
weight `orderOf x / gcd(orderOf x,n)` equals the order of the chosen class representative. -/
lemma inverse_rootfiber_weight_eq_class_order
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) {x : G}
    (hx : x ^ (n : ℕ) ∈ (c⁻¹).carrier) :
    orderOf x / Nat.gcd (orderOf x) (n : ℕ) = orderOf (g : G) := by
  have hg_inv : ((g : G)⁻¹) ∈ (c⁻¹).carrier := by
    apply ConjClasses.mem_carrier_iff_mk_eq.mpr
    simpa using congrArg Inv.inv (ConjClasses.mem_carrier_iff_mk_eq.mp g.property)
  -- Identify the order of `x ^ n` from its membership in the inverse conjugacy class.
  calc
    orderOf x / Nat.gcd (orderOf x) (n : ℕ) = orderOf (x ^ (n : ℕ)) := by
      symm
      simpa using (orderOf_pow (n := (n : ℕ)) x)
    _ = orderOf ((g : G)⁻¹) := by
      exact orderOf_eq_of_mem_conjClass (c := c⁻¹) ⟨(g : G)⁻¹, hg_inv⟩ hx
    _ = orderOf (g : G) := by
      simp

/-- Helper for Theorem 11-11.2-3: multiplying the class-size quotient by the support weight
recovers the normalized denominator quotient. -/
lemma card_quotient_mul_inverse_rootfiber_weight
    (n : ℕ+) (g : G) :
    (Nat.card G / orderOf g) * (orderOf g / Nat.gcd (orderOf g) (n : ℕ)) =
      Nat.card G / Nat.gcd (orderOf g) (n : ℕ) := by
  let _ := (inferInstance : Finite G)
  -- Rearrange the quotient using `gcd(orderOf g,n) ∣ orderOf g` and `orderOf g ∣ |G|`.
  calc
    (Nat.card G / orderOf g) * (orderOf g / Nat.gcd (orderOf g) (n : ℕ))
      = ((Nat.card G / orderOf g) * orderOf g) / Nat.gcd (orderOf g) (n : ℕ) := by
          symm
          exact Nat.mul_div_assoc _ (Nat.gcd_dvd_left (orderOf g) (n : ℕ))
    _ = Nat.card G / Nat.gcd (orderOf g) (n : ℕ) := by
          rw [Nat.div_mul_cancel (orderOf_dvd_natCard g)]

/-- Helper for Theorem 11-11.2-3: rewriting the owner through the inverse conjugacy class removes
the explicit inverse from the Adams transform. -/
lemma normalizedInverseNthRootIndicator_eq_inverse_class_adams
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) :
    normalizedInverseNthRootIndicator n c g =
      fun x ↦
        (Nat.card G : ℂ) *
          ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
            Ψ^n(((c⁻¹).indicator : G → ℂ)) x := by
  let _ := (inferInstance : Finite G)
  ext x
  -- Rewrite the owner through the inverse-class indicator pointwise.
  rw [normalizedInverseNthRootIndicator, adams_indicator_inv_conjClass_apply (n := n) (c := c)]

/-- Helper for Theorem 11-11.2-3: the normalized inverse `n`th-root owner is the integral scalar
multiple of the inverse conjugacy-class Adams indicator. -/
lemma normalizedInverseNthRootIndicator_eq_smul_inverse_conjClass_adams
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) :
    normalizedInverseNthRootIndicator n c g =
      (((Nat.card G / Nat.gcd (orderOf (g : G)) (n : ℕ) : ℕ) :
          integralClosure ℤ ℂ)) •
        Ψ^n(((c⁻¹).indicator : G → ℂ)) := by
  ext x
  have hgcd_dvd_card :
      Nat.gcd (orderOf (g : G)) (n : ℕ) ∣ Nat.card G := by
    exact dvd_trans (Nat.gcd_dvd_left _ _) (orderOf_dvd_natCard (g : G))
  have hgcd_ne_zero : ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℕ) : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.gcd_ne_zero_right n.ne_zero)
  -- The corrected bridge compares the owner only with the unweighted inverse Adams indicator.
  rw [normalizedInverseNthRootIndicator_eq_inverse_class_adams (G := G) (n := n) (c := c) (g := g)]
  rw [Pi.smul_apply]
  have hscalar :
      (Nat.card G : ℂ) * ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) =
        algebraMap (integralClosure ℤ ℂ) ℂ
          (((Nat.card G / Nat.gcd (orderOf (g : G)) (n : ℕ) : ℕ) :
              integralClosure ℤ ℂ)) := by
    rw [show
        algebraMap (integralClosure ℤ ℂ) ℂ
            (((Nat.card G / Nat.gcd (orderOf (g : G)) (n : ℕ) : ℕ) :
                integralClosure ℤ ℂ)) =
          ((Nat.card G / Nat.gcd (orderOf (g : G)) (n : ℕ) : ℕ) : ℂ) by
        rfl]
    rw [Nat.cast_div hgcd_dvd_card]
    · simp [div_eq_mul_inv]
    · exact hgcd_ne_zero
  rw [hscalar]
  simpa [Pi.smul_apply, Algebra.smul_def]

/-- Helper for Theorem 11-11.2-3: pairing the weighted inverse conjugacy-class Adams transform
with a character recovers the raw `n`th-root class sum up to the factor `orderOf g / |G|`. -/
lemma weighted_inverse_conjClass_pairing_eq
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) (ρ : Representation ℂ G V) :
    ⟪
      (fun x ↦
        algebraMap (integralClosure ℤ ℂ) ℂ
            (((orderOf x / Nat.gcd (orderOf x) (n : ℕ)) : ℕ) :
              integralClosure ℤ ℂ) *
          Ψ^n(((c⁻¹).indicator : G → ℂ)) x),
      ρ.character⟫ =
      ((orderOf (g : G) : ℂ) * (Nat.card G : ℂ)⁻¹) *
        conjugacyClassNthRootCharacterSum n c ρ := by
  let _ := (inferInstance : FiniteDimensional ℂ V)
  -- Expand the pairing and rewrite the inverse-class owner so its support is the direct root
  -- fiber `s ^ n ∈ c`.
  rw [Representation.groupFunctionPairingOverField]
  calc
    (Fintype.card G : ℂ)⁻¹ *
        ∑ s : G,
          ((algebraMap (integralClosure ℤ ℂ) ℂ
                (((orderOf s⁻¹ / Nat.gcd (orderOf s⁻¹) (n : ℕ)) : ℕ) :
                  integralClosure ℤ ℂ) *
              Ψ^n(((c⁻¹).indicator : G → ℂ)) s⁻¹) *
            ρ.character s)
      =
        (Fintype.card G : ℂ)⁻¹ *
          ∑ s : G,
            ((algebraMap (integralClosure ℤ ℂ) ℂ
                  (((orderOf s / Nat.gcd (orderOf s) (n : ℕ)) : ℕ) :
                    integralClosure ℤ ℂ)) *
                Ψ^n((c.indicator : G → ℂ)) s) *
              ρ.character s := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro s hs
            rw [adams_indicator_inv_conjClass_apply (n := n) (c := c) (x := s⁻¹)]
            simp
    _ =
        (Fintype.card G : ℂ)⁻¹ *
          ∑ s : G,
            if s ^ (n : ℕ) ∈ c.carrier then (orderOf (g : G) : ℂ) * ρ.character s else 0 := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro s hs
              by_cases hsroot : s ^ (n : ℕ) ∈ c.carrier
              · have hweight : orderOf s / Nat.gcd (orderOf s) (n : ℕ) = orderOf (g : G) := by
                  calc
                    orderOf s / Nat.gcd (orderOf s) (n : ℕ) = orderOf (s ^ (n : ℕ)) := by
                      symm
                      simpa using (orderOf_pow (n := (n : ℕ)) s)
                    _ = orderOf (g : G) := by
                      exact orderOf_eq_of_mem_conjClass (c := c) g hsroot
                simp [Representation.adamsOperator, ConjClasses.indicator, hsroot, hweight,
                ]
              · simp [Representation.adamsOperator, ConjClasses.indicator, hsroot]
    _ =
        (Fintype.card G : ℂ)⁻¹ *
          ((orderOf (g : G) : ℂ) *
            ∑ s : G, if s ^ (n : ℕ) ∈ c.carrier then ρ.character s else 0) := by
              congr 1
              simp [Finset.mul_sum]
    _ =
        ((orderOf (g : G) : ℂ) * (Fintype.card G : ℂ)⁻¹) *
          ∑ s : G, if s ^ (n : ℕ) ∈ c.carrier then ρ.character s else 0 := by
              ring
    _ =
        ((orderOf (g : G) : ℂ) * (Fintype.card G : ℂ)⁻¹) *
          ∑ s : G with s ^ (n : ℕ) ∈ c.carrier, ρ.character s := by
              congr 1
              rw [Finset.sum_filter]
    _ =
        ((orderOf (g : G) : ℂ) * (Nat.card G : ℂ)⁻¹) *
          conjugacyClassNthRootCharacterSum n c ρ := by
              rw [conjugacyClassNthRootCharacterSum, Nat.card_eq_fintype_card]

/-- Helper for Theorem 11-11.2-3: restricting the weighted inverse conjugacy-class owner to a
subgroup rewrites its pairing with a degree-`1` character as the subgroup-normalized weighted
root-fiber sum. -/
lemma weighted_inverse_conjClass_restricted_pairing_eq
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier)
    (H : Subgroup G) (χ : H →* ℂˣ) :
    ⟪
      (fun h : H ↦
        algebraMap (integralClosure ℤ ℂ) ℂ
            (((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) :
              integralClosure ℤ ℂ) *
          Ψ^n(((c⁻¹).indicator : G → ℂ)) h),
      χ.toRepresentation.character⟫ =
      ((Nat.card H : ℂ)⁻¹) *
        ((orderOf (g : G) : ℂ) *
          Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
            fun h ↦ (χ h : ℂ)) := by
  let ηH : H → ℂ := fun h ↦
    algebraMap (integralClosure ℤ ℂ) ℂ
        (((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) :
          integralClosure ℤ ℂ) *
      Ψ^n(((c⁻¹).indicator : G → ℂ)) h
  -- Expand the subgroup pairing and rewrite the inverse-class Adams term back to the direct
  -- root fiber inside `c`.
  rw [Representation.groupFunctionPairingOverField]
  change (Fintype.card H : ℂ)⁻¹ *
      ∑ s : H, ηH s⁻¹ * χ.toRepresentation.character s =
    ((Nat.card H : ℂ)⁻¹) *
      ((orderOf (g : G) : ℂ) *
        Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
          fun h ↦ (χ h : ℂ))
  have hstep1 :
      (Fintype.card H : ℂ)⁻¹ *
          ∑ s : H, ηH s⁻¹ * χ.toRepresentation.character s =
        (Fintype.card H : ℂ)⁻¹ *
          ∑ s : H,
            (algebraMap (integralClosure ℤ ℂ) ℂ
                (((orderOf s / Nat.gcd (orderOf s) (n : ℕ)) : ℕ) :
                  integralClosure ℤ ℂ)) *
              Ψ^n((c.indicator : G → ℂ)) s * (χ s : ℂ) := by
    have hsum :
        ∑ s : H, ηH s⁻¹ * χ.toRepresentation.character s =
          ∑ s : H,
            (algebraMap (integralClosure ℤ ℂ) ℂ
                (((orderOf s / Nat.gcd (orderOf s) (n : ℕ)) : ℕ) :
                  integralClosure ℤ ℂ)) *
              Ψ^n((c.indicator : G → ℂ)) s * (χ s : ℂ) := by
      unfold ηH
      refine Finset.sum_congr rfl ?_
      intro s hs
      have hadams :
          Ψ^n(((c⁻¹).indicator : G → ℂ)) ((s : G)⁻¹) =
            Ψ^n((c.indicator : G → ℂ)) (s : G) := by
        simpa using
          adams_indicator_inv_conjClass_apply (G := G) (n := n) (c := c) (x := (s : G)⁻¹)
      simpa [mul_assoc] using
        congrArg
          (fun z : ℂ ↦
            (algebraMap (integralClosure ℤ ℂ) ℂ
                (((orderOf s / Nat.gcd (orderOf s) (n : ℕ)) : ℕ) :
                  integralClosure ℤ ℂ)) *
              z * (χ s : ℂ))
          hadams
    exact congrArg (fun z : ℂ ↦ (Fintype.card H : ℂ)⁻¹ * z) hsum
  have hstep2 :
      (Fintype.card H : ℂ)⁻¹ *
          ∑ s : H,
            (algebraMap (integralClosure ℤ ℂ) ℂ
                (((orderOf s / Nat.gcd (orderOf s) (n : ℕ)) : ℕ) :
                  integralClosure ℤ ℂ)) *
              Ψ^n((c.indicator : G → ℂ)) s * (χ s : ℂ) =
        (Fintype.card H : ℂ)⁻¹ *
          ∑ s : H,
            if (s : G) ^ (n : ℕ) ∈ c.carrier then (orderOf (g : G) : ℂ) * (χ s : ℂ) else 0 := by
    congr 1
    refine Finset.sum_congr rfl ?_
    intro s hs
    by_cases hsroot : (s : G) ^ (n : ℕ) ∈ c.carrier
    · have hweight : orderOf s / Nat.gcd (orderOf s) (n : ℕ) = orderOf (g : G) := by
        calc
          orderOf s / Nat.gcd (orderOf s) (n : ℕ) = orderOf ((s : G) ^ (n : ℕ)) := by
            symm
            simpa using (orderOf_pow (n := (n : ℕ)) (s : G))
          _ = orderOf (g : G) := by
            exact orderOf_eq_of_mem_conjClass (c := c) g hsroot
      simp [Representation.adamsOperator, ConjClasses.indicator, hsroot, hweight]
    · simp [Representation.adamsOperator, ConjClasses.indicator, hsroot]
  have hstep3 :
      (Fintype.card H : ℂ)⁻¹ *
          (∑ s : H,
            if (s : G) ^ (n : ℕ) ∈ c.carrier then (orderOf (g : G) : ℂ) * (χ s : ℂ) else 0) =
        (Fintype.card H : ℂ)⁻¹ *
          ((orderOf (g : G) : ℂ) *
            ∑ s : H, if (s : G) ^ (n : ℕ) ∈ c.carrier then (χ s : ℂ) else 0) := by
    have hsum :
        (∑ s : H,
          if (s : G) ^ (n : ℕ) ∈ c.carrier then (orderOf (g : G) : ℂ) * (χ s : ℂ) else 0) =
          (orderOf (g : G) : ℂ) *
            ∑ s : H, if (s : G) ^ (n : ℕ) ∈ c.carrier then (χ s : ℂ) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro s hs
      by_cases hsroot : (s : G) ^ (n : ℕ) ∈ c.carrier
      · simp [hsroot, mul_assoc]
      · simp [hsroot]
    exact congrArg (fun z : ℂ ↦ (Fintype.card H : ℂ)⁻¹ * z) hsum
  have hstep4 :
      (Fintype.card H : ℂ)⁻¹ *
          ((orderOf (g : G) : ℂ) *
            ∑ s : H, if (s : G) ^ (n : ℕ) ∈ c.carrier then (χ s : ℂ) else 0) =
        ((Nat.card H : ℂ)⁻¹) *
          ((orderOf (g : G) : ℂ) *
            Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
              fun h ↦ (χ h : ℂ)) := by
    simpa [Nat.card_eq_fintype_card, Finset.sum_filter]
  calc
    (Fintype.card H : ℂ)⁻¹ *
        ∑ s : H, ηH s⁻¹ * χ.toRepresentation.character s
      = (Fintype.card H : ℂ)⁻¹ *
          ∑ s : H,
            (algebraMap (integralClosure ℤ ℂ) ℂ
                (((orderOf s / Nat.gcd (orderOf s) (n : ℕ)) : ℕ) :
                  integralClosure ℤ ℂ)) *
              Ψ^n((c.indicator : G → ℂ)) s * (χ s : ℂ) := hstep1
    _ =
        (Fintype.card H : ℂ)⁻¹ *
          ∑ s : H,
            if (s : G) ^ (n : ℕ) ∈ c.carrier then (orderOf (g : G) : ℂ) * (χ s : ℂ) else 0 :=
      hstep2
    _ =
        (Fintype.card H : ℂ)⁻¹ *
          ((orderOf (g : G) : ℂ) *
            ∑ s : H, if (s : G) ^ (n : ℕ) ∈ c.carrier then (χ s : ℂ) else 0) := hstep3
    _ =
        ((Nat.card H : ℂ)⁻¹) *
          ((orderOf (g : G) : ℂ) *
            Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
              fun h ↦ (χ h : ℂ)) := hstep4

/-- Helper for Theorem 11-11.2-3: after multiplying by the target gcd denominator, the normalized
inverse root owner becomes the class-size quotient times the weighted inverse conjugacy-class
owner already known to lie in the integral scalar extension. -/
lemma gcd_smul_normalizedInverseNthRootIndicator_eq_card_quotient_smul_weighted_inverse_conjClass
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) :
    (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℕ) : integralClosure ℤ ℂ)) •
        normalizedInverseNthRootIndicator n c g =
      (((Nat.card G / orderOf (g : G) : ℕ) : integralClosure ℤ ℂ)) •
        (fun x ↦
          algebraMap (integralClosure ℤ ℂ) ℂ
              (((orderOf x / Nat.gcd (orderOf x) (n : ℕ)) : ℕ) :
                integralClosure ℤ ℂ) *
            Ψ^n(((c⁻¹).indicator : G → ℂ)) x) := by
  ext x
  by_cases hx : x ^ (n : ℕ) ∈ (c⁻¹).carrier
  · have hweight :
      orderOf x / Nat.gcd (orderOf x) (n : ℕ) = orderOf (g : G) :=
      inverse_rootfiber_weight_eq_class_order (G := G) (n := n) (c := c) g hx
    have hgcd_ne_zero :
        (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℕ) : ℂ)) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.gcd_ne_zero_right n.ne_zero)
    have hadams :
        Ψ^n(((c⁻¹).indicator : G → ℂ)) x = 1 := by
      -- On the support, the inverse-class indicator contributes the unit value.
      simp [Representation.adamsOperator, ConjClasses.indicator, hx]
    have hcard_mul :
        (((Nat.card G / orderOf (g : G) : ℕ) : ℂ) * (orderOf (g : G) : ℂ)) =
          (Nat.card G : ℂ) := by
      exact_mod_cast Nat.div_mul_cancel (orderOf_dvd_natCard (g : G))
    -- Compare the two owners on the common support by collapsing the weight to `orderOf g`.
    rw [normalizedInverseNthRootIndicator_eq_inverse_class_adams (G := G) (n := n) (c := c)
      (g := g)]
    rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, hadams, hweight]
    calc
      ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ) *
          ((Nat.card G : ℂ) * ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) * 1))
        = (Nat.card G : ℂ) := by
            calc
              ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ) *
                  ((Nat.card G : ℂ) * ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) * 1))
                = ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ) *
                    ((Nat.card G : ℂ) * ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹))) := by
                    ring
              _ = (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ) *
                    ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹)) * (Nat.card G : ℂ)) := by
                    ring
              _ = (Nat.card G : ℂ) := by
                    rw [mul_inv_cancel₀ hgcd_ne_zero, one_mul]
      _ = ((Nat.card G / orderOf (g : G) : ℕ) : ℂ) * ((orderOf (g : G) : ℂ) * 1) := by
            rw [← hcard_mul]
            ring
  · have hadams :
      Ψ^n(((c⁻¹).indicator : G → ℂ)) x = 0 := by
      -- Off the support, both the normalized owner and the weighted owner vanish.
      simp [Representation.adamsOperator, ConjClasses.indicator, hx]
    -- Once the Adams value is zero, both sides collapse immediately.
    rw [normalizedInverseNthRootIndicator_eq_inverse_class_adams (G := G) (n := n) (c := c)
      (g := g)]
    rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, hadams]
    simp

/-- Helper for Theorem 11-11.2-3: the normalized inverse root owner defines a bundled class
function. -/
lemma normalizedInverseNthRootIndicator_mem_classFunctionSubmodule
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) :
    normalizedInverseNthRootIndicator n c g ∈ classFunctionSubmodule ℂ G := by
  let _ := (inferInstance : Finite G)
  -- Package the already-proved class-function property into the canonical owner.
  exact (mem_classFunctionSubmodule_iff ℂ _).2
    (normalizedInverseNthRootIndicator_isClassFunction (G := G) n c g)

/-- Helper for Theorem 11-11.2-3: the normalized inverse root owner bundled as a class function. -/
def normalizedInverseNthRootIndicatorClassFunction
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) : classFunctionSubmodule ℂ G :=
  ⟨normalizedInverseNthRootIndicator n c g,
    normalizedInverseNthRootIndicator_mem_classFunctionSubmodule (G := G) n c g⟩

/-- Helper for Theorem 11-11.2-3: if a subgroup contains no element whose `n`th power lands in
`c`, then the normalized subgroup root-fiber sum is zero. -/
lemma normalized_rootfiber_sum_eq_zero_of_no_subgroup_root
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier)
    (H : Subgroup G) (χ : H →* ℂˣ)
    (hroot : ¬ ∃ h : H, (h : G) ^ (n : ℕ) ∈ c.carrier) :
    (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
        Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
          fun h ↦ (χ h : ℂ)) = 0 := by
  -- First collapse the filtered sum itself, since any summand would contradict `hroot`.
  have hsum :
      Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
        (fun h ↦ (χ h : ℂ)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro h hh
    exfalso
    exact hroot ⟨h, by simpa using hh⟩
  -- The normalization factor preserves the vanishing of the raw root-fiber sum.
  simp [hsum]

/-- Helper for Theorem 11-11.2-3: a principal-ideal divisibility statement over the integral
closure yields the corresponding normalized scalar in the algebra-map image. -/
lemma normalized_mem_range_of_mem_span_nat_local
    (m : ℕ) (z : integralClosure ℤ ℂ)
    (hz : z ∈ Ideal.span ({(m : integralClosure ℤ ℂ)} : Set (integralClosure ℤ ℂ))) :
    ((m : ℂ)⁻¹) * (z : ℂ) ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  -- Rewrite the principal-ideal membership as an explicit multiple of the generator `m`.
  rcases Ideal.mem_span_singleton.mp hz with ⟨y, hy⟩
  by_cases hm : m = 0
  · -- If the generator vanishes, then the principal ideal is zero and the normalized scalar is `0`.
    refine ⟨0, ?_⟩
    subst hm
    have hz0 : z = 0 := by simpa using hy
    simp [hz0]
  · -- Otherwise the algebra-map image of `m` is invertible in `ℂ`, so the displayed factor cancels.
    refine ⟨y, ?_⟩
    symm
    rw [hy]
    have hmC : (m : ℂ) ≠ 0 := by
      exact_mod_cast hm
    calc
      ((m : ℂ)⁻¹) * (((((m : integralClosure ℤ ℂ) * y) : integralClosure ℤ ℂ)) : ℂ)
          = ((m : ℂ)⁻¹) * ((m : ℂ) * (y : ℂ)) := by
              simp
      _ = (((m : ℂ)⁻¹) * (m : ℂ)) * (y : ℂ) := by
              ring
      _ = (y : ℂ) := by
              simp [hmC]

/-- Helper for Theorem 11-11.2-3: a nontrivial degree-`1` character on a finite group has total
sum `0`. -/
lemma sum_linearCharacter_eq_zero_of_ne_one_local
    {K : Type*} [Group K] [Finite K] (χ : K →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ x : K, (χ x : ℂ) = 0 := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ : ∃ g : K, χ g ≠ 1 := by
    by_contra hnot
    apply hχ
    ext x
    have hx : χ x = 1 := by
      by_contra hx
      exact hnot ⟨x, hx⟩
    simpa using congrArg (fun u : ℂˣ ↦ (u : ℂ)) hx
  let s : ℂ := ∑ x : K, (χ x : ℂ)
  have htranslate : (χ g : ℂ) * s = s := by
    -- Left translation permutes the finite group, so multiplying by `χ g` preserves the total.
    calc
      (χ g : ℂ) * s = ∑ x : K, (χ g : ℂ) * (χ x : ℂ) := by
        simpa [s] using Finset.mul_sum (Finset.univ) (fun x : K ↦ (χ x : ℂ)) (χ g : ℂ)
      _ = ∑ x : K, (χ (g * x) : ℂ) := by
        exact Fintype.sum_congr
          (fun x : K ↦ (χ g : ℂ) * (χ x : ℂ))
          (fun x : K ↦ (χ (g * x) : ℂ))
          (fun x ↦ by simp [map_mul])
      _ = s := by
        simpa [s] using Equiv.sum_comp (Equiv.mulLeft g) (fun x : K ↦ (χ x : ℂ))
  have hgC : (χ g : ℂ) ≠ 1 := by
    intro hgC
    apply hg
    ext
    simpa using hgC
  have hfactor : ((χ g : ℂ) - 1) * s = 0 := by
    calc
      ((χ g : ℂ) - 1) * s = (χ g : ℂ) * s - s := by ring
      _ = s - s := by rw [htranslate]
      _ = 0 := sub_self s
  have hs : s = 0 := by
    refine (mul_eq_zero.mp hfactor).resolve_left ?_
    exact sub_ne_zero.mpr hgC
  simpa [s] using hs

/-- Helper for Theorem 11-11.2-3: in a commutative group, the fiber of the `n`th-power map above
`a0 ^ n` is exactly the translate of the kernel of `powMonoidHom n` by `a0`. -/
lemma cyclic_rootfiber_eq_powKer_translate_local
    {C : Type*} [CommGroup C] (n : ℕ) (a a0 : C) :
    a ^ n = a0 ^ n ↔ ∃ k : (powMonoidHom n : C →* C).ker, a = a0 * k := by
  constructor
  · intro ha
    -- Rewrite the fiber equation as membership in the kernel after translating by `a0⁻¹`.
    refine ⟨⟨a0⁻¹ * a, ?_⟩, ?_⟩
    · change (powMonoidHom n : C →* C) (a0⁻¹ * a) = 1
      calc
        (powMonoidHom n : C →* C) (a0⁻¹ * a) = (a0⁻¹ * a) ^ n := rfl
        _ = (a0⁻¹) ^ n * a ^ n := by
              rw [mul_pow]
        _ = (a0 ^ n)⁻¹ * a ^ n := by
              simp
        _ = 1 := by
              simp [ha]
    · simp
  · rintro ⟨k, rfl⟩
    -- Conversely, translating a kernel element by `a0` stays in the same `n`th-power fiber.
    have hk1 : (k : C) ^ n = 1 := by
      change (powMonoidHom n : C →* C) k = 1
      exact k.2
    calc
      (a0 * (k : C)) ^ n = a0 ^ n * (k : C) ^ n := by
        rw [mul_pow]
      _ = a0 ^ n := by
            simp [hk1]

/-- Helper for Theorem 11-11.2-3: on a finite cyclic group, the subgroup-gcd-normalized
`n`th-power fiber sum of a degree-`1` character lies in the image of the integral closure. -/
lemma cyclic_linearCharacter_normalized_rootfiber_sum_mem_range_integralClosure_local
    {C : Type*} [Group C] [Finite C] [DecidableEq C] (hC : IsCyclic C)
    (n : ℕ+) (χ : C →* ℂˣ) (a0 : C) :
    (((Nat.gcd (Nat.card C) (n : ℕ) : ℂ)⁻¹) *
        Finset.sum (Finset.univ.filter fun a : C ↦ a ^ (n : ℕ) = a0 ^ (n : ℕ))
          fun a ↦ (χ a : ℂ)) ∈
      Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  classical
  let _ : Fintype C := Fintype.ofFinite C
  let _ : CommGroup C := hC.commGroup
  let K : Subgroup C := (powMonoidHom (n : ℕ) : C →* C).ker
  let _ : Finite K := Finite.of_injective ((↑) : K → C) Subtype.val_injective
  let _ : Fintype K := Fintype.ofFinite K
  -- Reindex the filtered fiber through the translate of the power-map kernel.
  have hsum_subtype :
      Finset.sum (Finset.univ.filter fun a : C ↦ a ^ (n : ℕ) = a0 ^ (n : ℕ))
          (fun a ↦ (χ a : ℂ)) =
        Finset.sum (Finset.univ.subtype fun a : C ↦ a ^ (n : ℕ) = a0 ^ (n : ℕ))
          (fun a ↦ (χ a : ℂ)) := by
    simpa using
      (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
        (p := fun a : C ↦ a ^ (n : ℕ) = a0 ^ (n : ℕ)) (f := fun a ↦ (χ a : ℂ))).symm
  let eFiber : K ≃ {a : C // a ^ (n : ℕ) = a0 ^ (n : ℕ)} :=
    { toFun := fun k ↦ ⟨a0 * k, by
        have hk1 : (k : C) ^ (n : ℕ) = 1 := by
          change (powMonoidHom (n : ℕ) : C →* C) k = 1
          exact k.2
        calc
          (a0 * k) ^ (n : ℕ) = a0 ^ (n : ℕ) * (k : C) ^ (n : ℕ) := by
            rw [mul_pow]
          _ = a0 ^ (n : ℕ) := by
                simp [hk1]
      ⟩
      invFun := fun a ↦ ⟨a0⁻¹ * a, by
        -- The translated element lands in the kernel because the two `n`th powers agree.
        change (powMonoidHom (n : ℕ) : C →* C) (a0⁻¹ * a) = 1
        calc
          (powMonoidHom (n : ℕ) : C →* C) (a0⁻¹ * a) = (a0⁻¹ * a) ^ (n : ℕ) := rfl
          _ = (a0⁻¹) ^ (n : ℕ) * a ^ (n : ℕ) := by
                rw [mul_pow]
          _ = (a0 ^ (n : ℕ))⁻¹ * a ^ (n : ℕ) := by
                simp
          _ = 1 := by
                simp [a.property]
      ⟩
      left_inv := by
        intro k
        apply Subtype.ext
        simp
      right_inv := by
        intro a
        apply Subtype.ext
        simp [mul_comm] }
  have hsum_equiv :
      Finset.sum (Finset.univ.subtype fun a : C ↦ a ^ (n : ℕ) = a0 ^ (n : ℕ))
          (fun a ↦ (χ a : ℂ)) =
        ∑ k : K, (χ (a0 * k : C) : ℂ) := by
    simpa [eFiber] using
      (Fintype.sum_equiv eFiber.symm
        (fun a : {a : C // a ^ (n : ℕ) = a0 ^ (n : ℕ)} ↦ (χ a : ℂ))
        (fun k : K ↦ (χ (a0 * k : C) : ℂ))
        (by
          intro a
          simp [eFiber, mul_comm]))
  let χK : K →* ℂˣ := χ.comp K.subtype
  have hsum_translate :
      (∑ k : K, (χ (a0 * k : C) : ℂ)) = (χ a0 : ℂ) * ∑ k : K, (χK k : ℂ) := by
    -- Factor the translated character sum into the value at `a0` times the kernel sum.
    calc
      (∑ k : K, (χ (a0 * k : C) : ℂ)) = ∑ k : K, (χ a0 : ℂ) * (χK k : ℂ) := by
        apply Fintype.sum_congr
        intro k
        simp [χK, map_mul]
      _ = (χ a0 : ℂ) * ∑ k : K, (χK k : ℂ) := by
            simpa using (Finset.mul_sum Finset.univ (fun k : K ↦ (χK k : ℂ)) (χ a0 : ℂ)).symm
  by_cases hχK : χK = 1
  · -- If the restriction to the kernel is trivial, the normalized fiber sum collapses to `χ a0`.
    have hsumK : ∑ k : K, (χK k : ℂ) = Nat.card K := by
      rw [hχK]
      simp [Nat.card_eq_fintype_card]
    have hcardK : Nat.card K = Nat.gcd (Nat.card C) (n : ℕ) := by
      simpa [K] using IsCyclic.card_powMonoidHom_ker (G := C) (d := (n : ℕ))
    have hvalue_mem : (χ a0 : ℂ) ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
      exact
        (IsIntegralClosure.isIntegral_iff
          (A := integralClosure ℤ ℂ) (R := ℤ) (B := ℂ)).1
          (by simpa using Representation.char_isIntegral χ.toRepresentation a0)
    rw [hsum_subtype, hsum_equiv, hsum_translate, hsumK, hcardK]
    have hmain :
        ((Nat.gcd (Nat.card C) (n : ℕ) : ℂ)⁻¹) *
            ((χ a0 : ℂ) * (Nat.gcd (Nat.card C) (n : ℕ) : ℂ)) =
          (χ a0 : ℂ) := by
      calc
        ((Nat.gcd (Nat.card C) (n : ℕ) : ℂ)⁻¹) *
            ((χ a0 : ℂ) * (Nat.gcd (Nat.card C) (n : ℕ) : ℂ)) =
          (((Nat.gcd (Nat.card C) (n : ℕ) : ℂ)⁻¹) *
              (Nat.gcd (Nat.card C) (n : ℕ) : ℂ)) * (χ a0 : ℂ) := by
                ring
        _ = (χ a0 : ℂ) := by
              simp
    rw [hmain]
    exact hvalue_mem
  · -- If the restriction to the kernel is nontrivial, the kernel sum vanishes by translation.
    have hsumK : ∑ k : K, (χK k : ℂ) = 0 :=
      sum_linearCharacter_eq_zero_of_ne_one_local χK hχK
    rw [hsum_subtype, hsum_equiv, hsum_translate, hsumK]
    exact ⟨0, by simp⟩


end FrobeniusTheorem

end Representation
