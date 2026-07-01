import Mathlib
import Serre.Chap09.Proposition_9_9_4_2
import Serre.Chap09.Theorem_9_9_2_1
import Serre.Chap11.Exercise_11_11_2_7.CyclicPowerInvariant
import Serre.Chap11.Exercise_11_11_2_7.RestrictionAndPairing
import Serre.Chap11.Theorem_11_11_1_2
import Serre.Chap11.Theorem_11_11_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace Representation

open scoped BigOperators Representation SubgroupInduction

section FrobeniusTheorem

variable {G : Type} [Group G] [Finite G]

/-- A subgroup of a finite group is finite. -/
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Conjugacy classes in a finite group form a finite type. -/
local instance (H : Type*) [Group H] [Finite H] : Fintype (ConjClasses H) :=
  Fintype.ofFinite (ConjClasses H)

/-- Equality of subgroups is decidable by classical choice in this file-local proof environment. -/
local instance (H : Type*) [Group H] : DecidableEq (Subgroup H) := Classical.decEq _

/-- Helper for Exercise 11-11.2-7: integer pointwise scaling of a complex-valued function agrees
with complex scalar multiplication by the corresponding integer. -/
lemma int_smul_eq_complex_smul_function
    {H : Type*} (a : ℤ) (φ : H → ℂ) :
    (a • φ : H → ℂ) = ((a : ℂ) • φ) := by
  -- Compare both scalar actions pointwise; they are both multiplication by the same integer.
  ext h
  simp [Pi.smul_apply, Algebra.smul_def]

-- Source/core/bridge triage:
-- * source-facing: the power-invariance criteria from Exercise `11-11.2-7`.
-- * core/canonical owners: `classFunctionSubmodule`, `R(G)`, `A ⊗R(G)`,
--   `characterRingScalarExtension`, and `Ψ^n`.
-- * bridge/view: the cyclic-subgroup restriction criterion
--   `classFunction_mem_characterRingScalarExtension_of_restrict_mem_on_cyclicSubgroups` together
--   with the owner-level Adams statements from Corollary `11-11.2-5`.
--
-- Sampled domain declarations:
-- * `Representation.classFunction_mem_characterRingScalarExtension_of_restrict_mem_on_`
--   `cyclicSubgroups`
-- * `Representation.frobenius_weighted_adamsOperator_mem_characterRingScalarExtension`
-- * `Representation.weighted_adamsOperator_unitClassIndicator_mem_characterRing`
-- * `Representation.characterRingScalarExtension`
--
-- Primitive data here are the bundled rational/integral class functions together with the
-- source-facing power-invariance hypothesis. Membership in `characterRingScalarExtension ℚ G` and
-- `R(G)` is derived API through the existing Chapter `11` owners, not new local wrappers.

/-- Helper for Exercise 11-11.2-7: a rational-valued class function on a finite group that is
invariant under the power maps `x ↦ x ^ m` for every `m` prime to `|G|` belongs to `ℚ ⊗ R(G)`,
realized as `characterRingScalarExtension ℚ G`. -/
theorem rational_classFunction_mem_characterRingScalarExtension_of_power_invariant
    (f : classFunctionSubmodule ℚ G)
    (hpow : ∀ x : G, ∀ m : ℕ, Nat.Coprime m (Nat.card G) → f (x ^ m) = f x) :
    (fun x ↦ algebraMap ℚ ℂ (f x)) ∈ characterRingScalarExtension ℚ G := by
  let hfQ : _root_.IsClassFunction (f : G → ℚ) := (mem_classFunctionSubmodule_iff ℚ _).1 f.2
  let fC : classFunctionSubmodule ℂ G :=
    ⟨fun x ↦ algebraMap ℚ ℂ (f x),
      (mem_classFunctionSubmodule_iff ℂ _).2 <| hfQ.comp (algebraMap ℚ ℂ)⟩
  -- Reduce the global claim to the cyclic restrictions from Theorem `11-11.1-2`.
  refine
    Representation.classFunction_mem_characterRingScalarExtension_of_restrict_mem_on_cyclicSubgroups
      (A := ℚ) (φ := fC) ?_
  intro H hcyc
  let fH : classFunctionSubmodule ℚ H := rat_classFunctionRestriction (G := G) H f
  have hrespow :
      ∀ x : H, ∀ m : ℕ, Nat.Coprime m (Nat.card G) → fH (x ^ m) = fH x := by
    intro x m hm
    -- The subgroup restriction is evaluated pointwise, so the ambient hypothesis applies
    -- directly to the same element viewed in `G`.
    simpa [fH] using hpow (x : G) m hm
  -- The remaining work is the cyclic case for the restricted rational class function.
  simpa [fC, fH, Subgroup.classFunctionRestriction_apply] using
    cyclic_power_invariant_mem_characterRingScalarExtension
      (G := G) hcyc fH hrespow

/-- Helper for Exercise 11-11.2-7: after rationalizing the integer-valued weighted Adams
transform, part `(1)` places it in `ℚ ⊗ R(G)`. -/
lemma weighted_adamsOperator_mem_characterRingScalarExtension_of_integral_power_invariant
    (n : ℕ+) (f : classFunctionSubmodule ℤ G)
    (hpow : ∀ x : G, ∀ m : ℕ, Nat.Coprime m (Nat.card G) → f (x ^ m) = f x) :
    (fun x ↦
      algebraMap ℤ ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) * Ψ^n(f) x)) ∈
      characterRingScalarExtension ℚ G := by
  let k : ℤ := (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ)
  let w : G → ℤ := fun x ↦ k * Ψ^n(f) x
  have hfZ : _root_.IsClassFunction (f : G → ℤ) := (mem_classFunctionSubmodule_iff ℤ _).1 f.2
  have hwClassZ : _root_.IsClassFunction w := by
    letI : _root_.IsClassFunction (Ψ^n((f : G → ℤ))) := isClassFunction_adamsOperator n hfZ
    have hscaled : _root_.IsClassFunction ((k : ℤ) • Ψ^n((f : G → ℤ))) := inferInstance
    simpa [w, Pi.smul_apply, smul_eq_mul] using hscaled
  let wQ : classFunctionSubmodule ℚ G :=
    ⟨fun x ↦ algebraMap ℤ ℚ (w x),
      (mem_classFunctionSubmodule_iff ℚ _).2 <| hwClassZ.comp (algebraMap ℤ ℚ)⟩
  have hwpowQ :
      ∀ x : G, ∀ m : ℕ, Nat.Coprime m (Nat.card G) → wQ (x ^ m) = wQ x := by
    intro x m hm
    -- The rationalized weighted Adams function satisfies the same invariance because the integer
    -- source function already does.
    change algebraMap ℤ ℚ (w (x ^ m)) = algebraMap ℤ ℚ (w x)
    exact congrArg (algebraMap ℤ ℚ)
      (weighted_adamsOperator_power_invariant (G := G) n f hpow x m hm)
  have hwQmem :
      (fun x ↦ algebraMap ℚ ℂ (wQ x)) ∈ characterRingScalarExtension ℚ G :=
    rational_classFunction_mem_characterRingScalarExtension_of_power_invariant wQ hwpowQ
  -- The realized rational class function is exactly the complex-valued weighted Adams transform.
  simpa [wQ, w, k] using hwQmem

/-- Helper for Exercise 11-11.2-7: an integer-valued class function is the sum of its conjugacy
class coefficients against the corresponding indicator basis. -/
lemma integer_classFunction_eq_sum_conjClass_indicator
    {H : Type u} [Group H] [Finite H] (φ : classFunctionSubmodule ℤ H) :
    (φ : H → ℤ) =
      fun x : H ↦
        ∑ c : ConjClasses H,
          ((mem_classFunctionSubmodule_iff ℤ _).1 φ.2).lift c * c.indicator x := by
  let hφ : _root_.IsClassFunction (φ : H → ℤ) := (mem_classFunctionSubmodule_iff ℤ _).1 φ.2
  funext x
  let c₀ : ConjClasses H := ConjClasses.mk x
  have hxmem : x ∈ c₀.carrier := by
    exact ConjClasses.mem_carrier_iff_mk_eq.mpr rfl
  -- The conjugacy-class indicators form a partition indexed by `ConjClasses H`.
  calc
    (φ : H → ℤ) x = hφ.lift c₀ := by simp [c₀, _root_.IsClassFunction.lift_mk]
    _ =
        ∑ c : ConjClasses H,
          hφ.lift c * c.indicator x := by
            rw [Finset.sum_eq_single c₀]
            · simp [c₀, ConjClasses.indicator, hxmem]
            · intro c _ hc
              have hnot : x ∉ c.carrier := by
                intro hx
                have hc' : c = c₀ := by
                  exact (ConjClasses.mem_carrier_iff_mk_eq.mp hx).symm
                exact hc hc'
              simp [ConjClasses.indicator, hnot]
            · simp [c₀, ConjClasses.indicator, hxmem]
    _ =
        (fun x : H ↦
          ∑ c : ConjClasses H,
            ((mem_classFunctionSubmodule_iff ℤ _).1 φ.2).lift c * c.indicator x) x := by
              simp

/-- Helper for Exercise 11-11.2-7: elements of a fixed conjugacy class in a subgroup have the
same order. -/
lemma orderOf_eq_of_mem_conjClass_local
    {H : Type*} [Group H] [Finite H] {c : ConjClasses H} (g : c.carrier)
    {x : H} (hx : x ∈ c.carrier) :
    orderOf x = orderOf (g : H) := by
  let _ := (inferInstance : Finite H)
  -- Compare the two elements inside the same conjugacy class and transport order along
  -- semiconjugacy.
  have hxmk : ConjClasses.mk x = c := ConjClasses.mem_carrier_iff_mk_eq.mp hx
  have hgmk : ConjClasses.mk (g : H) = c := ConjClasses.mem_carrier_iff_mk_eq.mp g.property
  have hconj : ConjClasses.mk x = ConjClasses.mk (g : H) := hxmk.trans hgmk.symm
  rcases ConjClasses.mk_eq_mk_iff_isConj.mp hconj with ⟨a, ha⟩
  simpa using SemiconjBy.orderOf_eq (a := (a : H)) ha

/-- Helper for Exercise 11-11.2-7: if the `n`th-root fiber in a subgroup conjugacy class is
nonempty, then the class order divides the global Frobenius weight `|G| / gcd(|G|, n)`. -/
lemma class_order_dvd_global_frobenius_weight_of_exists_root
    (n : ℕ+) (H : Subgroup G) (c : ConjClasses H) (g : c.carrier)
    (hex : ∃ h : H, h ^ (n : ℕ) ∈ c.carrier) :
    orderOf (g : H) ∣ Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) := by
  rcases hex with ⟨h, hh⟩
  let m : ℕ := orderOf h
  let g₁ : ℕ := Nat.gcd m (n : ℕ)
  let g₂ : ℕ := Nat.gcd (Nat.card G) (n : ℕ)
  have hm_cardH : m ∣ Nat.card H := by
    simpa [m] using (orderOf_dvd_natCard h)
  have hm_cardG : m ∣ Nat.card G := by
    exact dvd_trans hm_cardH (Subgroup.card_subgroup_dvd_card H)
  have hg₁_m : g₁ ∣ m := by
    exact Nat.gcd_dvd_left m (n : ℕ)
  have hg₁_g₂ : g₁ ∣ g₂ := by
    exact Nat.dvd_gcd (dvd_trans hg₁_m hm_cardG) (Nat.gcd_dvd_right m (n : ℕ))
  have hclass_order :
      orderOf (g : H) = m / g₁ := by
    calc
      orderOf (g : H) = orderOf (h ^ (n : ℕ)) := by
        symm
        exact orderOf_eq_of_mem_conjClass_local (g := g) hh
      _ = orderOf h / Nat.gcd (orderOf h) (n : ℕ) := by
        simpa using (orderOf_pow (n := (n : ℕ)) h)
      _ = m / g₁ := by
        rfl
  have hdiv_aux : m / g₁ ∣ Nat.card G / g₁ := by
    refine ⟨Nat.card G / m, ?_⟩
    -- First divide `|G|` by the root order, then divide the root order by the common gcd.
    simpa [Nat.mul_comm, m, g₁] using (Nat.div_mul_div hm_cardG hg₁_m).symm
  have hcop_base : Nat.Coprime (m / g₁) ((n : ℕ) / g₁) := by
    simpa [m, g₁] using
      Nat.gcd_div_gcd_div_gcd_of_pos_right (Nat.pos_of_ne_zero n.ne_zero)
  have hfactor_dvd : g₂ / g₁ ∣ (n : ℕ) / g₁ := by
    refine ⟨(n : ℕ) / g₂, ?_⟩
    -- The extra factor removed from `|G|` is already a divisor of the corresponding factor in
    -- `n`, so the remaining quotient is compatible with the coprimality step.
    simpa [Nat.mul_comm, g₂, g₁] using
      (Nat.div_mul_div (Nat.gcd_dvd_right (Nat.card G) (n : ℕ)) hg₁_g₂).symm
  have hcop : Nat.Coprime (m / g₁) (g₂ / g₁) := by
    exact Nat.Coprime.of_dvd_right hfactor_dvd hcop_base
  have hprod :
      (Nat.card G / g₂) * (g₂ / g₁) = Nat.card G / g₁ := by
    -- Split the ambient denominator in two stages, first by `g₂` and then by the quotient
    -- `g₂ / g₁`.
    simpa [g₂, g₁] using
      (Nat.div_mul_div (Nat.gcd_dvd_left (Nat.card G) (n : ℕ)) hg₁_g₂)
  have hfinal : m / g₁ ∣ Nat.card G / g₂ := by
    exact hcop.dvd_of_dvd_mul_right (hprod ▸ hdiv_aux)
  simpa [hclass_order, g₂] using hfinal

/-- Helper for Exercise 11-11.2-7: in the nonempty-root case, the exercise's global weighted
indicator is an integral scalar multiple of the Chapter `11.2.2` local weighted owner. -/
lemma global_weighted_indicator_eq_zsmul_local_weighted_indicator
    (n : ℕ+) (H : Subgroup G) (c : ConjClasses H) (g : c.carrier)
    (hex : ∃ h : H, h ^ (n : ℕ) ∈ c.carrier) :
    (fun h : H ↦
      algebraMap ℤ ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
          Ψ^n((c.indicator : H → ℤ)) h)) =
      ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) / orderOf (g : H) : ℕ) : ℤ) •
        fun h : H ↦
          algebraMap ℤ ℂ
            ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : ℤ) *
              Ψ^n((c.indicator : H → ℤ)) h)) := by
  have hdiv :
      orderOf (g : H) ∣ Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) :=
    class_order_dvd_global_frobenius_weight_of_exists_root (G := G) n H c g hex
  funext h
  by_cases hsroot : h ^ (n : ℕ) ∈ c.carrier
  · have hweight :
      orderOf h / Nat.gcd (orderOf h) (n : ℕ) = orderOf (g : H) := by
      calc
        orderOf h / Nat.gcd (orderOf h) (n : ℕ) = orderOf (h ^ (n : ℕ)) := by
          symm
          simpa using (orderOf_pow (n := (n : ℕ)) h)
        _ = orderOf (g : H) := by
          exact orderOf_eq_of_mem_conjClass_local (g := g) hsroot
    have hcoeff :
        (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) : ℕ) : ℤ)) =
          (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) / orderOf (g : H) : ℕ) : ℤ) *
            (((orderOf h / Nat.gcd (orderOf h) (n : ℕ) : ℕ) : ℤ))) := by
      rw [hweight]
      exact_mod_cast (Nat.div_mul_cancel hdiv).symm
    have hadams :
        Ψ^n((c.indicator : H → ℤ)) h = 1 := by
      simp [Representation.adamsOperator, ConjClasses.indicator, hsroot]
    -- On the root fiber, both indicators are `1`, so the comparison is purely between the
    -- global coefficient and the local `orderOf g` coefficient.
    rw [Pi.smul_apply, hadams, hcoeff, Algebra.smul_def, map_mul]
    simp
  · -- Off the root fiber, the Adams-transformed indicator already vanishes on both sides.
    have hadams :
        Ψ^n((c.indicator : H → ℤ)) h = 0 := by
      simp [Representation.adamsOperator, ConjClasses.indicator, hsroot]
    rw [Pi.smul_apply, hadams, Algebra.smul_def]
    simp

/-- Helper for Exercise 11-11.2-7: pairing the exercise's weighted subgroup indicator with an
elementary linear character gives an algebraic integer. -/
lemma elementary_weighted_adams_indicator_pairing_isIntegral
    (n : ℕ+) (H : Subgroup G) (_hH : IsElementary H)
    (χ : H →* ℂˣ) (c : ConjClasses H) :
    IsIntegral ℤ
      ⟪χ.toCharacterRing, fun h : H ↦
        algebraMap ℤ ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
            Ψ^n((c.indicator : H → ℤ)) h)⟫ := by
  classical
  by_cases hroot : ∃ h : H, h ^ (n : ℕ) ∈ c.carrier
  · rcases hroot with ⟨h₀, hh₀⟩
    let g : c.carrier := ⟨h₀ ^ (n : ℕ), hh₀⟩
    let ω : H → ℂ := fun h ↦
      algebraMap ℤ ℂ
        ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : ℤ) *
          Ψ^n((c.indicator : H → ℤ)) h)
    let q : ℤ :=
      (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) / orderOf (g : H) : ℕ) : ℤ))
    have hω_scalar : ω ∈ characterRingScalarExtension ℤ H := by
      -- The Chapter `11.2.2` owner already places the local weighted indicator in the subgroup
      -- character ring.
      -- Important correction: Theorem 23 is not available with `(A := ℤ)`.
      -- Serre's `A` is generated by the `|H|`-th roots of unity; the weighted indicator must first
      -- be constructed over that cyclotomic coefficient ring and then descended integrally to `ℤ`.
      sorry
    have hω_mem : ω ∈ R(H) := by
      have hspan : characterRingScalarExtension ℤ H = (R(H)).toSubmodule := by
        rw [characterRingScalarExtension]
        exact Submodule.span_eq ((R(H)).toSubmodule : Submodule ℤ (H → ℂ))
      simpa [ω, hspan] using hω_scalar
    have htarget :
        (fun h : H ↦
          algebraMap ℤ ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
              Ψ^n((c.indicator : H → ℤ)) h)) =
          q • ω := by
      -- The global Frobenius weight is the integer quotient from the previous divisibility lemma
      -- times the local Chapter `11.2.2` weight.
      simpa [q, ω] using
        global_weighted_indicator_eq_zsmul_local_weighted_indicator
          (G := G) n H c g ⟨h₀, hh₀⟩
    rcases
      characterRing_pairing_mem_range_int_with_rep_character
        (η := ⟨ω, hω_mem⟩) χ.toRepresentation with ⟨m, hm⟩
    have hsmul : (q • ω : H → ℂ) = ((q : ℂ) • ω) := by
      -- Rewrite the integer scalar action as the ambient complex scalar action so the pairing
      -- linearity lemma applies directly.
      simpa using int_smul_eq_complex_smul_function q ω
    have hm' : groupFunctionPairingOverField ℂ (χ.toCharacterRing : H → ℂ) ω =
        algebraMap ℤ ℂ m := by
      simpa [Representation.groupFunctionPairing_comm] using hm.symm
    rw [htarget, hsmul, Representation.groupFunctionPairing_smul_right, hm']
    -- The resulting value is an algebraMap from `ℤ`, hence an algebraic integer.
    simpa [q, map_mul, mul_assoc] using
      (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ (q * m)))
  · have hzero :
      (fun h : H ↦
        algebraMap ℤ ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
            Ψ^n((c.indicator : H → ℤ)) h)) = 0 := by
      funext h
      have hhroot : h ^ (n : ℕ) ∉ c.carrier := by
        intro hh
        exact hroot ⟨h, hh⟩
      -- With no subgroup roots at all, the indicator term is zero pointwise.
      simp [Representation.adamsOperator, ConjClasses.indicator, hhroot]
    rw [hzero]
    simpa [Representation.groupFunctionPairingOverField] using
      (isIntegral_zero : IsIntegral ℤ (0 : ℂ))

/-- Helper for Exercise 11-11.2-7: pairing the exercise's weighted conjugacy-class indicator with
an honest representation character gives an algebraic integer. -/
lemma weighted_adams_indicator_pairing_isIntegral_with_rep_character
    (n : ℕ+) (H : Subgroup G)
    {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H W) (c : ConjClasses H) :
    IsIntegral ℤ
      ⟪fun h : H ↦
          algebraMap ℤ ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
              Ψ^n((c.indicator : H → ℤ)) h), ρ.character⟫ := by
  classical
  by_cases hroot : ∃ h : H, h ^ (n : ℕ) ∈ c.carrier
  · rcases hroot with ⟨h₀, hh₀⟩
    let g : c.carrier := ⟨h₀ ^ (n : ℕ), hh₀⟩
    let ω : H → ℂ := fun h ↦
      algebraMap ℤ ℂ
        ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : ℤ) *
          Ψ^n((c.indicator : H → ℤ)) h)
    let q : ℤ :=
      (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) / orderOf (g : H) : ℕ) : ℤ))
    have hω_scalar : ω ∈ characterRingScalarExtension ℤ H := by
      -- The Chapter `11.2.2` owner already places the local weighted indicator in the subgroup
      -- character ring.
      -- Important correction: Theorem 23 is not available with `(A := ℤ)`.
      -- Serre's `A` is generated by the `|H|`-th roots of unity; the weighted indicator must first
      -- be constructed over that cyclotomic coefficient ring and then descended integrally to `ℤ`.
      sorry
    have hω_mem : ω ∈ R(H) := by
      have hspan : characterRingScalarExtension ℤ H = (R(H)).toSubmodule := by
        rw [characterRingScalarExtension]
        exact Submodule.span_eq ((R(H)).toSubmodule : Submodule ℤ (H → ℂ))
      simpa [ω, hspan] using hω_scalar
    have htarget :
        (fun h : H ↦
          algebraMap ℤ ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
              Ψ^n((c.indicator : H → ℤ)) h)) =
          q • ω := by
      -- The global Frobenius weight is the integer quotient from the previous divisibility lemma
      -- times the local Chapter `11.2.2` weight.
      simpa [q, ω] using
        global_weighted_indicator_eq_zsmul_local_weighted_indicator
          (G := G) n H c g ⟨h₀, hh₀⟩
    have hpair_int :
        IsIntegral ℤ ⟪ω, ρ.character⟫ := by
      rcases characterRing_pairing_mem_range_int_with_rep_character (η := ⟨ω, hω_mem⟩) ρ with
        ⟨m, hm⟩
      rw [← hm]
      exact isIntegral_algebraMap
    have hsmul : (q • ω : H → ℂ) = ((q : ℂ) • ω) := by
      -- Rewrite the integer scalar action as the ambient complex scalar action so the pairing
      -- linearity lemma applies directly.
      simpa using int_smul_eq_complex_smul_function q ω
    rw [htarget, hsmul, Representation.groupFunctionPairing_smul_left]
    simpa [q, map_mul, mul_assoc] using
      IsIntegral.mul isIntegral_algebraMap hpair_int
  · have hzero :
      (fun h : H ↦
        algebraMap ℤ ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
            Ψ^n((c.indicator : H → ℤ)) h)) = 0 := by
      funext h
      have hhroot : h ^ (n : ℕ) ∉ c.carrier := by
        intro hh
        exact hroot ⟨h, hh⟩
      -- With no subgroup roots at all, the indicator term is zero pointwise.
      simp [Representation.adamsOperator, ConjClasses.indicator, hhroot]
    rw [hzero]
    simpa [Representation.groupFunctionPairingOverField] using
      (isIntegral_zero : IsIntegral ℤ (0 : ℂ))

/-- Helper for Exercise 11-11.2-7: if the global `n`th-root fiber of a conjugacy class is
nonempty, then the class order divides the exercise's Frobenius weight
`|G| / gcd(|G|, n)`. -/
lemma class_order_dvd_global_frobenius_weight_of_exists_root_global
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier)
    (hex : ∃ h : G, h ^ (n : ℕ) ∈ c.carrier) :
    orderOf (g : G) ∣ Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) := by
  rcases hex with ⟨h, hh⟩
  let m : ℕ := orderOf h
  let g₁ : ℕ := Nat.gcd m (n : ℕ)
  let g₂ : ℕ := Nat.gcd (Nat.card G) (n : ℕ)
  have hm_cardG : m ∣ Nat.card G := by
    simpa [m] using (orderOf_dvd_natCard h)
  have hg₁_m : g₁ ∣ m := by
    exact Nat.gcd_dvd_left m (n : ℕ)
  have hg₁_g₂ : g₁ ∣ g₂ := by
    exact Nat.dvd_gcd (dvd_trans hg₁_m hm_cardG) (Nat.gcd_dvd_right m (n : ℕ))
  have hclass_order :
      orderOf (g : G) = m / g₁ := by
    calc
      orderOf (g : G) = orderOf (h ^ (n : ℕ)) := by
        symm
        exact orderOf_eq_of_mem_conjClass_local (g := g) hh
      _ = orderOf h / Nat.gcd (orderOf h) (n : ℕ) := by
        simpa using (orderOf_pow (n := (n : ℕ)) h)
      _ = m / g₁ := by
        rfl
  have hdiv_aux : m / g₁ ∣ Nat.card G / g₁ := by
    refine ⟨Nat.card G / m, ?_⟩
    -- First divide `|G|` by the root order, then divide the root order by the common gcd.
    simpa [Nat.mul_comm, m, g₁] using (Nat.div_mul_div hm_cardG hg₁_m).symm
  have hcop_base : Nat.Coprime (m / g₁) ((n : ℕ) / g₁) := by
    simpa [m, g₁] using
      Nat.gcd_div_gcd_div_gcd_of_pos_right (Nat.pos_of_ne_zero n.ne_zero)
  have hfactor_dvd : g₂ / g₁ ∣ (n : ℕ) / g₁ := by
    refine ⟨(n : ℕ) / g₂, ?_⟩
    -- The extra factor removed from `|G|` is already a divisor of the corresponding factor in
    -- `n`, so the remaining quotient is compatible with the coprimality step.
    simpa [Nat.mul_comm, g₂, g₁] using
      (Nat.div_mul_div (Nat.gcd_dvd_right (Nat.card G) (n : ℕ)) hg₁_g₂).symm
  have hcop : Nat.Coprime (m / g₁) (g₂ / g₁) := by
    exact Nat.Coprime.of_dvd_right hfactor_dvd hcop_base
  have hprod :
      (Nat.card G / g₂) * (g₂ / g₁) = Nat.card G / g₁ := by
    -- Split the ambient denominator in two stages, first by `g₂` and then by the quotient
    -- `g₂ / g₁`.
    simpa [g₂, g₁] using
      (Nat.div_mul_div (Nat.gcd_dvd_left (Nat.card G) (n : ℕ)) hg₁_g₂)
  have hfinal : m / g₁ ∣ Nat.card G / g₂ := by
    exact hcop.dvd_of_dvd_mul_right (hprod ▸ hdiv_aux)
  simpa [hclass_order, g₂] using hfinal

/-- Helper for Exercise 11-11.2-7: in the nonempty-root case, the exercise's global weighted
conjugacy-class indicator is an integral scalar multiple of the Chapter `11.2.2` local weighted
owner. -/
lemma global_weighted_conjClass_indicator_eq_zsmul_local_weighted_indicator
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier)
    (hex : ∃ h : G, h ^ (n : ℕ) ∈ c.carrier) :
    (fun h : G ↦
      algebraMap ℤ ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
          Ψ^n((c.indicator : G → ℤ)) h)) =
      ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) / orderOf (g : G) : ℕ) : ℤ) •
        fun h : G ↦
          algebraMap ℤ ℂ
            ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : ℤ) *
              Ψ^n((c.indicator : G → ℤ)) h)) := by
  have hdiv :
      orderOf (g : G) ∣ Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) :=
    class_order_dvd_global_frobenius_weight_of_exists_root_global (G := G) n c g hex
  funext h
  by_cases hsroot : h ^ (n : ℕ) ∈ c.carrier
  · have hweight :
      orderOf h / Nat.gcd (orderOf h) (n : ℕ) = orderOf (g : G) := by
      calc
        orderOf h / Nat.gcd (orderOf h) (n : ℕ) = orderOf (h ^ (n : ℕ)) := by
          symm
          simpa using (orderOf_pow (n := (n : ℕ)) h)
        _ = orderOf (g : G) := by
          exact orderOf_eq_of_mem_conjClass_local (g := g) hsroot
    have hcoeff :
        (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) : ℕ) : ℤ)) =
          (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) / orderOf (g : G) : ℕ) : ℤ) *
            (((orderOf h / Nat.gcd (orderOf h) (n : ℕ) : ℕ) : ℤ))) := by
      rw [hweight]
      exact_mod_cast (Nat.div_mul_cancel hdiv).symm
    have hadams :
        Ψ^n((c.indicator : G → ℤ)) h = 1 := by
      simp [Representation.adamsOperator, ConjClasses.indicator, hsroot]
    -- On the root fiber, both indicators are `1`, so the comparison is purely between the
    -- global coefficient and the local `orderOf g` coefficient.
    rw [Pi.smul_apply, hadams, hcoeff, Algebra.smul_def, map_mul]
    simp
  · -- Off the root fiber, the Adams-transformed indicator already vanishes on both sides.
    have hadams :
        Ψ^n((c.indicator : G → ℤ)) h = 0 := by
      simp [Representation.adamsOperator, ConjClasses.indicator, hsroot]
    rw [Pi.smul_apply, hadams, Algebra.smul_def]
    simp

/-- Helper for Exercise 11-11.2-7: pairing the exercise's global weighted conjugacy-class
indicator with an honest representation character gives an algebraic integer. -/
lemma weighted_global_adams_indicator_pairing_isIntegral_with_rep_character
    (n : ℕ+)
    {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) (c : ConjClasses G) :
    IsIntegral ℤ
      ⟪fun h : G ↦
          algebraMap ℤ ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
              Ψ^n((c.indicator : G → ℤ)) h), ρ.character⟫ := by
  classical
  by_cases hroot : ∃ h : G, h ^ (n : ℕ) ∈ c.carrier
  · rcases hroot with ⟨h₀, hh₀⟩
    let g : c.carrier := ⟨h₀ ^ (n : ℕ), hh₀⟩
    let ω : G → ℂ := fun h ↦
      algebraMap ℤ ℂ
        ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : ℤ) *
          Ψ^n((c.indicator : G → ℤ)) h)
    let q : ℤ :=
      (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) / orderOf (g : G) : ℕ) : ℤ))
    have hω_scalar : ω ∈ characterRingScalarExtension ℤ G := by
      -- The Chapter `11.2.2` owner already places the local weighted indicator in the ambient
      -- character ring.
      -- Important correction: Theorem 23 is not available with `(A := ℤ)`.
      -- Serre's `A` is generated by the `|G|`-th roots of unity; the weighted indicator must first
      -- be constructed over that cyclotomic coefficient ring and then descended integrally to `ℤ`.
      sorry
    have hω_mem : ω ∈ R(G) := by
      have hspan : characterRingScalarExtension ℤ G = (R(G)).toSubmodule := by
        rw [characterRingScalarExtension]
        exact Submodule.span_eq ((R(G)).toSubmodule : Submodule ℤ (G → ℂ))
      simpa [ω, hspan] using hω_scalar
    have htarget :
        (fun h : G ↦
          algebraMap ℤ ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
              Ψ^n((c.indicator : G → ℤ)) h)) =
          q • ω := by
      -- The global Frobenius weight is the integer quotient from the previous divisibility lemma
      -- times the local Chapter `11.2.2` weight.
      simpa [q, ω] using
        global_weighted_conjClass_indicator_eq_zsmul_local_weighted_indicator
          (G := G) n c g ⟨h₀, hh₀⟩
    have hpair_int :
        IsIntegral ℤ ⟪ω, ρ.character⟫ := by
      rcases characterRing_pairing_mem_range_int_with_rep_character (η := ⟨ω, hω_mem⟩) ρ with
        ⟨m, hm⟩
      rw [← hm]
      exact isIntegral_algebraMap
    have hsmul : (q • ω : G → ℂ) = ((q : ℂ) • ω) := by
      -- Rewrite the integer scalar action as the ambient complex scalar action so the pairing
      -- linearity lemma applies directly.
      simpa using int_smul_eq_complex_smul_function q ω
    rw [htarget, hsmul, Representation.groupFunctionPairing_smul_left]
    simpa [q, map_mul, mul_assoc] using
      IsIntegral.mul isIntegral_algebraMap hpair_int
  · have hzero :
      (fun h : G ↦
        algebraMap ℤ ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
            Ψ^n((c.indicator : G → ℤ)) h)) = 0 := by
      funext h
      have hhroot : h ^ (n : ℕ) ∉ c.carrier := by
        intro hh
        exact hroot ⟨h, hh⟩
      -- With no global roots at all, the indicator term is zero pointwise.
      simp [Representation.adamsOperator, ConjClasses.indicator, hhroot]
    rw [hzero]
    simpa [Representation.groupFunctionPairingOverField] using
      (isIntegral_zero : IsIntegral ℤ (0 : ℂ))

/-- Helper for Exercise 11-11.2-7: the exercise's global weighted conjugacy-class indicator is a
virtual character. -/
lemma weighted_global_adams_indicator_mem_characterRing
    (n : ℕ+) (c : ConjClasses G) :
    (fun h : G ↦
      algebraMap ℤ ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
          Ψ^n((c.indicator : G → ℤ)) h)) ∈
      R(G) := by
  classical
  by_cases hroot : ∃ h : G, h ^ (n : ℕ) ∈ c.carrier
  · rcases hroot with ⟨h₀, hh₀⟩
    let g : c.carrier := ⟨h₀ ^ (n : ℕ), hh₀⟩
    let ω : G → ℂ := fun h ↦
      algebraMap ℤ ℂ
        ((((orderOf h / Nat.gcd (orderOf h) (n : ℕ)) : ℕ) : ℤ) *
          Ψ^n((c.indicator : G → ℤ)) h)
    let q : ℤ :=
      (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ) / orderOf (g : G) : ℕ) : ℤ))
    have hω_scalar : ω ∈ characterRingScalarExtension ℤ G := by
      -- Important correction: Theorem 23 is not available with `(A := ℤ)`.
      -- Serre's `A` is generated by the `|G|`-th roots of unity; the weighted indicator must first
      -- be constructed over that cyclotomic coefficient ring and then descended integrally to `ℤ`.
      sorry
    have hω_mem : ω ∈ R(G) := by
      have hspan : characterRingScalarExtension ℤ G = (R(G)).toSubmodule := by
        rw [characterRingScalarExtension]
        exact Submodule.span_eq ((R(G)).toSubmodule : Submodule ℤ (G → ℂ))
      simpa [ω, hspan] using hω_scalar
    have htarget :
        (fun h : G ↦
          algebraMap ℤ ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
              Ψ^n((c.indicator : G → ℤ)) h)) =
          q • ω := by
      simpa [q, ω] using
        global_weighted_conjClass_indicator_eq_zsmul_local_weighted_indicator
          (G := G) n c g ⟨h₀, hh₀⟩
    rw [htarget]
    simpa [q, ω, Pi.smul_apply, zsmul_eq_mul, Algebra.smul_def] using
      ((((q • (⟨ω, hω_mem⟩ : R(G))) : R(G)) : R(G)).property)
  · have hzero :
      (fun h : G ↦
        algebraMap ℤ ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
            Ψ^n((c.indicator : G → ℤ)) h)) = 0 := by
      funext h
      have hhroot : h ^ (n : ℕ) ∉ c.carrier := by
        intro hh
        exact hroot ⟨h, hh⟩
      simp [Representation.adamsOperator, ConjClasses.indicator, hhroot]
    rw [hzero]
    exact (R(G)).zero_mem

/-- Helper for Exercise 11-11.2-7: a rational complex number that is algebraically integral over
`ℤ` is already an integer. -/
lemma isInteger_of_mem_range_rat_of_isIntegral
    {z : ℂ} (hzQ : z ∈ Set.range (algebraMap ℚ ℂ)) (hzInt : IsIntegral ℤ z) :
    IsLocalization.IsInteger ℤ z := by
  rcases hzQ with ⟨q, rfl⟩
  have hqInt : IsIntegral ℤ q := by
    exact (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp hzInt
  rcases (show ∃ m : ℤ, algebraMap ℤ ℚ m = q by
      simpa [IsLocalization.IsInteger] using UniqueFactorizationMonoid.integer_of_integral hqInt)
    with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  simpa using congrArg (algebraMap ℚ ℂ) hm

/-- Helper for Exercise 11-11.2-7: finite sums of integer multiples of integral pairings remain
integral. -/
lemma isIntegral_pairing_sum_zsmul_of_isIntegral
    {H : Type u} [Group H] [Finite H] (χ : H →* ℂˣ)
    (a : ConjClasses H → ℤ) (ψ : ConjClasses H → H → ℂ)
    (hψ : ∀ c : ConjClasses H, IsIntegral ℤ ⟪χ.toCharacterRing, ψ c⟫) :
    IsIntegral ℤ
      ⟪χ.toCharacterRing, ∑ c : ConjClasses H, a c • ψ c⟫ := by
  classical
  -- Expand the finite class sum term-by-term and use the additive/multiplicative closure of
  -- algebraic integrality over `ℤ`.
  let s : Finset (ConjClasses H) := Finset.univ
  have hs :
      (∑ c : ConjClasses H, a c • ψ c) = Finset.sum s (fun c ↦ a c • ψ c) := by
    simp [s]
  rw [hs]
  change IsIntegral ℤ
    (groupFunctionPairingOverField ℂ (χ.toCharacterRing : H → ℂ)
      (Finset.sum s fun c ↦ a c • ψ c))
  induction s using Finset.induction_on with
  | empty =>
      simpa [Representation.groupFunctionPairingOverField] using
        (isIntegral_zero : IsIntegral ℤ (0 : ℂ))
  | @insert c s hc ih =>
      have hterm :
          IsIntegral ℤ
            (groupFunctionPairingOverField ℂ (χ.toCharacterRing : H → ℂ) (a c • ψ c)) := by
        have hsmul :
            (a c • ψ c : H → ℂ) = ((a c : ℂ) • ψ c) := by
          simpa using int_smul_eq_complex_smul_function (a c) (ψ c)
        rw [hsmul, Representation.groupFunctionPairing_smul_right]
        simpa [zsmul_eq_mul] using
          IsIntegral.mul isIntegral_algebraMap (hψ c)
      have hsum :
          IsIntegral ℤ
            (groupFunctionPairingOverField ℂ (χ.toCharacterRing : H → ℂ)
              ((a c • ψ c) + Finset.sum s fun d ↦ a d • ψ d)) := by
        rw [Representation.groupFunctionPairing_add_right]
        exact IsIntegral.add hterm ih
      simpa [Finset.sum_insert, hc] using hsum

/-- Helper for Exercise 11-11.2-7: finite sums of integer multiples of integral pairings with an
honest representation character remain integral. -/
lemma isIntegral_pairing_sum_zsmul_with_rep_character
    {H : Type u} [Group H] [Finite H]
    {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H W)
    (a : ConjClasses H → ℤ) (ψ : ConjClasses H → H → ℂ)
    (hψ : ∀ c : ConjClasses H, IsIntegral ℤ ⟪ψ c, ρ.character⟫) :
    IsIntegral ℤ
      ⟪∑ c : ConjClasses H, a c • ψ c, ρ.character⟫ := by
  classical
  -- Expand the finite class sum term-by-term and use the additive/multiplicative closure of
  -- algebraic integrality over `ℤ`.
  let s : Finset (ConjClasses H) := Finset.univ
  have hs :
      (∑ c : ConjClasses H, a c • ψ c) = Finset.sum s (fun c ↦ a c • ψ c) := by
    simp [s]
  rw [hs]
  change IsIntegral ℤ
    (groupFunctionPairingOverField ℂ (Finset.sum s fun c ↦ a c • ψ c) ρ.character)
  induction s using Finset.induction_on with
  | empty =>
      simpa [Representation.groupFunctionPairingOverField] using
        (isIntegral_zero : IsIntegral ℤ (0 : ℂ))
  | @insert c s hc ih =>
      have hterm :
          IsIntegral ℤ
            (groupFunctionPairingOverField ℂ (a c • ψ c) ρ.character) := by
        have hsmul :
            (a c • ψ c : H → ℂ) = ((a c : ℂ) • ψ c) := by
          simpa using int_smul_eq_complex_smul_function (a c) (ψ c)
        rw [hsmul, Representation.groupFunctionPairing_smul_left]
        simpa [zsmul_eq_mul] using
          IsIntegral.mul isIntegral_algebraMap (hψ c)
      have hsum :
          IsIntegral ℤ
            (groupFunctionPairingOverField ℂ
              ((a c • ψ c) + Finset.sum s fun d ↦ a d • ψ d) ρ.character) := by
        rw [Representation.groupFunctionPairing_add_left]
        exact IsIntegral.add hterm ih
      simpa [Finset.sum_insert, hc] using hsum

/-- Helper for Exercise 11-11.2-7: the weighted Adams transform of an integer-valued class
function is the conjugacy-class indicator expansion of the source function, with the exercise's
global Frobenius weight. -/
lemma weighted_adams_eq_sum_conjClass_indicator
    (n : ℕ+) (f : classFunctionSubmodule ℤ G) :
    (fun x : G ↦
      algebraMap ℤ ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) * Ψ^n(f) x)) =
      ∑ c : ConjClasses G,
        (((mem_classFunctionSubmodule_iff ℤ _).1 f.2).lift c) •
          (fun x : G ↦
            algebraMap ℤ ℂ
              ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
                Ψ^n((c.indicator : G → ℤ)) x)) := by
  let k : ℤ := (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ)
  let a : ConjClasses G → ℤ := fun c ↦ ((mem_classFunctionSubmodule_iff ℤ _).1 f.2).lift c
  -- Apply the indicator decomposition to `x ^ n`, then multiply by the global Frobenius weight.
  funext x
  have hdecomp :
      (f : G → ℤ) = fun y : G ↦ ∑ c : ConjClasses G, a c * c.indicator y := by
    simpa [a] using integer_classFunction_eq_sum_conjClass_indicator (H := G) f
  have hEval :
      Ψ^n(f) x = ∑ c : ConjClasses G, a c * Ψ^n((c.indicator : G → ℤ)) x := by
    simpa [Representation.adamsOperator] using
      congrArg (fun φ : G → ℤ => φ (x ^ (n : ℕ))) hdecomp
  have hweighted :
      k * Ψ^n(f) x =
        ∑ c : ConjClasses G, a c * (k * Ψ^n((c.indicator : G → ℤ)) x) := by
    calc
      k * Ψ^n(f) x = k * ∑ c : ConjClasses G, a c * Ψ^n((c.indicator : G → ℤ)) x := by
        rw [hEval]
      _ = ∑ c : ConjClasses G, k * (a c * Ψ^n((c.indicator : G → ℤ)) x) := by
        rw [Finset.mul_sum]
      _ = ∑ c : ConjClasses G, a c * (k * Ψ^n((c.indicator : G → ℤ)) x) := by
        refine Finset.sum_congr rfl ?_
        intro c hc
        ring
  -- Now transport the integer identity into `ℂ` and rewrite the function-valued `zsmul` sum.
  calc
    algebraMap ℤ ℂ (k * Ψ^n(f) x) =
        ∑ c : ConjClasses G, algebraMap ℤ ℂ (a c * (k * Ψ^n((c.indicator : G → ℤ)) x)) := by
          simpa [map_sum] using congrArg (algebraMap ℤ ℂ) hweighted
    _ =
        (∑ c : ConjClasses G, a c •
          (fun y : G ↦
            algebraMap ℤ ℂ
              (k * Ψ^n((c.indicator : G → ℤ)) y))) x := by
          simp [a, k, Algebra.smul_def, map_mul]

/-- Helper for Exercise 11-11.2-7: the restriction of the weighted Adams transform to an
elementary subgroup is the indicator-basis expansion of the restricted source function. -/
lemma weighted_adams_restriction_eq_sum_indicator
    (n : ℕ+) (f : classFunctionSubmodule ℤ G) (H : Subgroup G) :
    (fun h : H ↦
      algebraMap ℤ ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) * Ψ^n(f) h)) =
      ∑ c : ConjClasses H,
        (((mem_classFunctionSubmodule_iff ℤ _).1
          (int_classFunctionRestriction (G := G) H f).2).lift c) •
          (fun h : H ↦
            algebraMap ℤ ℂ
              ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
                Ψ^n((c.indicator : H → ℤ)) h)) := by
  let k : ℤ := (((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ)
  let fH : classFunctionSubmodule ℤ H := int_classFunctionRestriction (G := G) H f
  let a : ConjClasses H → ℤ :=
    fun c ↦ ((mem_classFunctionSubmodule_iff ℤ _).1 fH.2).lift c
  -- Apply the indicator decomposition to `h ^ n`, then multiply by the global Frobenius weight.
  funext h
  have hdecomp :
      (fH : H → ℤ) = fun x : H ↦ ∑ c : ConjClasses H, a c * c.indicator x := by
    simpa [fH, a] using integer_classFunction_eq_sum_conjClass_indicator (H := H) fH
  have hEval :
      Ψ^n(fH) h = ∑ c : ConjClasses H, a c * Ψ^n((c.indicator : H → ℤ)) h := by
    simpa [Representation.adamsOperator] using
      congrArg (fun φ : H → ℤ => φ (h ^ (n : ℕ))) hdecomp
  have hweighted :
      k * Ψ^n(fH) h =
        ∑ c : ConjClasses H, a c * (k * Ψ^n((c.indicator : H → ℤ)) h) := by
    calc
      k * Ψ^n(fH) h = k * ∑ c : ConjClasses H, a c * Ψ^n((c.indicator : H → ℤ)) h := by
        rw [hEval]
      _ = ∑ c : ConjClasses H, k * (a c * Ψ^n((c.indicator : H → ℤ)) h) := by
        rw [Finset.mul_sum]
      _ = ∑ c : ConjClasses H, a c * (k * Ψ^n((c.indicator : H → ℤ)) h) := by
        refine Finset.sum_congr rfl ?_
        intro c hc
        ring
  -- Now transport the integer identity into `ℂ` and rewrite the function-valued `zsmul` sum.
  calc
    algebraMap ℤ ℂ (k * Ψ^n(f) h) = algebraMap ℤ ℂ (k * Ψ^n(fH) h) := by
      simp [Representation.adamsOperator, fH, int_classFunctionRestriction]
    _ = ∑ c : ConjClasses H, algebraMap ℤ ℂ (a c * (k * Ψ^n((c.indicator : H → ℤ)) h)) := by
      simpa [map_sum] using congrArg (algebraMap ℤ ℂ) hweighted
    _ =
        (∑ c : ConjClasses H, a c •
          (fun x : H ↦
            algebraMap ℤ ℂ
              (k * Ψ^n((c.indicator : H → ℤ)) x))) h := by
          simp [a, k, Algebra.smul_def, map_mul]

/-- Helper for Exercise 11-11.2-7: pairing the restricted weighted Adams transform with an
elementary linear character is already integral over `ℤ`. -/
lemma elementary_linearCharacter_pairing_isInteger_of_integral_power_invariant
    (n : ℕ+) (f : classFunctionSubmodule ℤ G)
    (hpow : ∀ x : G, ∀ m : ℕ, Nat.Coprime m (Nat.card G) → f (x ^ m) = f x)
    (H : Subgroup G) (_hH : IsElementary H) (χ : H →* ℂˣ) :
    IsLocalization.IsInteger ℤ
      ⟪χ.toCharacterRing, fun h : H ↦
        algebraMap ℤ ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) * Ψ^n(f) h)⟫ := by
  let η : G → ℂ := fun x ↦
    algebraMap ℤ ℂ
      ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) * Ψ^n(f) x)
  have hηQ : η ∈ characterRingScalarExtension ℚ G := by
    -- Part `(1)` already places the weighted Adams transform in the rational scalar extension.
    simpa [η] using
      weighted_adamsOperator_mem_characterRingScalarExtension_of_integral_power_invariant
        (G := G) n f hpow
  have hηHQ : (fun h : H ↦ η h) ∈ characterRingScalarExtension ℚ H := by
    -- Restrict the global rational-span membership to the current elementary subgroup.
    exact classFunctionRestriction_mem_characterRingScalarExtension (G := G) (A := ℚ) H hηQ
  have hpairQ :
      ⟪χ.toCharacterRing, fun h : H ↦ η h⟫ ∈ Set.range (algebraMap ℚ ℂ) := by
    -- The rational half of the endgame is now isolated from the elementary-divisibility step.
    exact pairing_mem_range_rat_of_mem_characterRingScalarExtension
      (η := fun h : H ↦ η h) hηHQ χ
  have hpairInt :
      IsIntegral ℤ ⟪χ.toCharacterRing, fun h : H ↦ η h⟫ := by
    -- Rewrite the restricted weighted Adams transform in the conjugacy-class indicator basis.
    let a : ConjClasses H → ℤ :=
      fun c ↦ ((mem_classFunctionSubmodule_iff ℤ _).1
        (int_classFunctionRestriction (G := G) H f).2).lift c
    let ψ : ConjClasses H → H → ℂ := fun c h ↦
      algebraMap ℤ ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
          Ψ^n((c.indicator : H → ℤ)) h)
    have hη_eq :
        (fun h : H ↦ η h) = ∑ c : ConjClasses H, a c • ψ c := by
      -- This is the source-faithful basis expansion coming from the restricted integer class
      -- function on `H`.
      simpa [η, a, ψ] using
        weighted_adams_restriction_eq_sum_indicator (G := G) n f H
    have hψ :
        ∀ c : ConjClasses H, IsIntegral ℤ ⟪χ.toCharacterRing, ψ c⟫ := by
      intro c
      -- Each basis pairing is the single remaining Chapter `11.2` structural endpoint.
      simpa [ψ] using
        elementary_weighted_adams_indicator_pairing_isIntegral
          (G := G) n H _hH χ c
    rw [hη_eq]
    exact isIntegral_pairing_sum_zsmul_of_isIntegral χ a ψ hψ
  -- Once the value is both rational and algebraically integral, it must come from `ℤ`.
  exact isInteger_of_mem_range_rat_of_isIntegral hpairQ hpairInt

set_option maxHeartbeats 4000000 in
-- The character-ring proof expands the weighted Adams transform into the conjugacy-class
-- indicator basis, and that elaboration needs a larger heartbeat budget here.
/-- Helper for Exercise 11-11.2-7: the weighted Adams transform lies in the character ring by
expanding it into the conjugacy-class indicator basis. -/
lemma weighted_adamsOperator_integral_power_invariant_mem_characterRing
    (n : ℕ+) (f : classFunctionSubmodule ℤ G)
    (hpow : ∀ x : G, ∀ m : ℕ, Nat.Coprime m (Nat.card G) → f (x ^ m) = f x) :
    (fun x ↦
      algebraMap ℤ ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) * Ψ^n(f) x)) ∈
      R(G) := by
  let _ := hpow
  let φ : G → ℂ := fun x ↦
    algebraMap ℤ ℂ
      ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) * Ψ^n(f) x)
  have hφ_eq :
      φ =
        ∑ c : ConjClasses G,
          (((mem_classFunctionSubmodule_iff ℤ _).1 f.2).lift c) •
            (fun x : G ↦
              algebraMap ℤ ℂ
                ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
                  Ψ^n((c.indicator : G → ℤ)) x)) := by
    simpa [φ] using weighted_adams_eq_sum_conjClass_indicator (G := G) n f
  have htarget :
      (fun x ↦
        algebraMap ℤ ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) * Ψ^n(f) x)) =
        ∑ c : ConjClasses G,
          (((mem_classFunctionSubmodule_iff ℤ _).1 f.2).lift c) •
            (fun x : G ↦
              algebraMap ℤ ℂ
                ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
                  Ψ^n((c.indicator : G → ℤ)) x)) := by
    simpa [φ] using hφ_eq
  rw [htarget]
  refine (R(G)).sum_mem ?_
  intro c hc
  let a : ℤ := (((mem_classFunctionSubmodule_iff ℤ _).1 f.2).lift c)
  let η : G → ℂ := fun x : G ↦
    algebraMap ℤ ℂ
      ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
        Ψ^n((c.indicator : G → ℤ)) x)
  have hη : η ∈ R(G) := by
    simpa [η] using weighted_global_adams_indicator_mem_characterRing (G := G) n c
  simpa [a, η, Pi.smul_apply, zsmul_eq_mul, Algebra.smul_def] using
    ((((a • (⟨η, hη⟩ : R(G))) : R(G)) : R(G)).property)

/-- Exercise 11-11.2-7 (2): if the same power-invariant class function takes integer values, then
for every `n` the weighted Adams transform `(|G| / gcd(|G|, n)) Ψ^n f` is a virtual character. -/
theorem weighted_adamsOperator_mem_characterRing_of_integral_power_invariant
    (n : ℕ+) (f : classFunctionSubmodule ℤ G)
    (hpow : ∀ x : G, ∀ m : ℕ, Nat.Coprime m (Nat.card G) → f (x ^ m) = f x) :
    (fun x ↦
      algebraMap ℤ ℂ
        ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) * Ψ^n(f) x)) ∈
      R(G) := by
  simpa using
    weighted_adamsOperator_integral_power_invariant_mem_characterRing (G := G) n f hpow

/- Exercise 11-11.2-7 (3): the exact unit-class specialization from part (2) is already the
owner-level theorem in `Corollary_11_11_2_5`; this file omits the direct `recall` because the
current dependency-closed proof route avoids importing the conflicting `11.2.3` chain. -/

end FrobeniusTheorem

end Representation
