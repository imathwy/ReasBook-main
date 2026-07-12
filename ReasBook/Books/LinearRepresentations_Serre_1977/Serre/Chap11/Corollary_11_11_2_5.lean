import Mathlib
import LinearRepresentations_Serre_1977.Chap06.Corollary_6_6_5_4
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_3.SubgroupRootFiber

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace Representation

section FrobeniusTheorem

open scoped Representation

variable (G : Type u) [Group G] [Finite G]

local instance corollary111125GroupFintype : Fintype G := Fintype.ofFinite G

-- Source/core/bridge triage:
-- * source-facing: `dvd_card_pow_eq_one`, matching Serre's textbook corollary.
-- * core/canonical: divisibility of the `n`th-root fiber of `1` by `Nat.gcd (Nat.card G) n`.
-- * bridge/view: specialize the core statement along `Nat.gcd_eq_right` when `n ∣ Nat.card G`.
--
-- Sampled owner declarations in this domain:
-- * `ConjClasses.indicatorClassFunctionSubmodule`
-- * `Representation.frobenius_weighted_adamsOperator_lifts_to_tensorCharacterRing`
-- * `Representation.frobenius_weighted_adamsOperator_mem_characterRingScalarExtension`
-- * `Representation.weighted_adamsOperator_conjClassIndicator_mem_characterRingScalarExtension`
--
-- Primitive data: the unit conjugacy-class indicator and the source-facing `n`th-root fiber
-- `{x : G // x ^ n = 1}`.
-- Derived API: the textbook divisibility statement under the extra hypothesis `n ∣ Nat.card G`.

/-- Helper for Corollary 11-11.2-5: every `|G|`-th root of unity in `ℂˣ` already comes from the
integral closure `integralClosure ℤ ℂ`. -/
lemma rootOfUnity_mem_range_integralClosure_of_pow_card_eq_one
    (z : ℂˣ) (hz : z ^ Nat.card G = 1) :
    ((z : ℂ) ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ)) := by
  have hcard_pos : 0 < Fintype.card G := by
    exact Fintype.card_pos_iff.mpr (show Nonempty G from ⟨1⟩)
  have hz_pow : ((z : ℂ) ^ Fintype.card G) = 1 := by
    -- Coercing the unit equation to `ℂ` gives the polynomial relation needed for integrality.
    simpa [Nat.card_eq_fintype_card] using congrArg (fun u : ℂˣ ↦ (u : ℂ)) hz
  have hz_integral : IsIntegral ℤ (z : ℂ) := by
    -- A root of `X ^ |G| - 1` is integral over `ℤ`.
    refine IsIntegral.of_pow (n := Fintype.card G) hcard_pos ?_
    rw [hz_pow]
    exact isIntegral_one
  exact
    (IsIntegralClosure.isIntegral_iff
      (A := integralClosure ℤ ℂ) (R := ℤ) (B := ℂ)).mp hz_integral

/-- Helper for Corollary 11-11.2-5: the weighted Adams transform of the unit conjugacy-class
indicator belongs to the realized integral-closure scalar extension of the character ring. -/
lemma weightedUnitClassIndicator_mem_characterRingScalarExtension_integralClosure
    (n : ℕ+) :
    (fun x ↦
      algebraMap (integralClosure ℤ ℂ) ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) :
            integralClosure ℤ ℂ)) *
        Ψ^n(((ConjClasses.mk (1 : G)).indicator : G → ℂ)) x) ∈
      characterRingScalarExtension (integralClosure ℤ ℂ) G := by
  have hf :
      (fun x ↦
        algebraMap (integralClosure ℤ ℂ) ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) :
              integralClosure ℤ ℂ) *
              Ψ^n(((ConjClasses.mk (1 : G)).indicator : G → integralClosure ℤ ℂ)) x)) =
        (fun x ↦
          algebraMap (integralClosure ℤ ℂ) ℂ
              ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) :
                integralClosure ℤ ℂ)) *
            Ψ^n(((ConjClasses.mk (1 : G)).indicator : G → ℂ)) x) := by
    funext x
    by_cases hx : x ^ (n : ℕ) ∈ (ConjClasses.mk (1 : G)).carrier
    · -- On the support, both indicator-valued owners are the same constant.
      simp [Representation.adamsOperator, ConjClasses.indicator, hx]
    · -- Off the support, both indicator-valued owners vanish.
      simp [Representation.adamsOperator, ConjClasses.indicator, hx]
  -- Route correction: Theorem `11.11.2.2` must be used over the integral closure, not over `ℤ`.
  rw [← hf]
  exact
    weighted_adamsOperator_conjClassIndicator_mem_characterRingScalarExtension
      (G := G) (A := integralClosure ℤ ℂ) n (c := ConjClasses.mk (1 : G))
      (rootOfUnity_mem_range_integralClosure_of_pow_card_eq_one (G := G))

/-- Helper for Corollary 11-11.2-5: pairing an integral-closure scalar-extended class function
with an honest character lands in the image of `integralClosure ℤ ℂ → ℂ`. -/
lemma scalarExtensionPairing_mem_range_integralClosure_with_repCharacter
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (η : G → ℂ)
    (hη : η ∈ characterRingScalarExtension (integralClosure ℤ ℂ) G)
    (ρ : Representation ℂ G W) :
    ⟪η, ρ.character⟫ ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  -- Repeat the scalar-extension span induction directly in this item file.
  rw [characterRingScalarExtension] at hη
  refine
    Submodule.span_induction
      (s := (R(G) : Set (G → ℂ)))
      (p := fun ψ _ ↦
        ⟪ψ, ρ.character⟫ ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ))
      ?_ ?_ ?_ ?_ hη
  · intro ψ hψ
    let ηR : R(G) := ⟨ψ, hψ⟩
    have hIntegral : IsIntegral ℤ ⟪ψ, ρ.character⟫ :=
      characterRing_pairing_isIntegral_with_rep_character ηR ρ
    exact
      (IsIntegralClosure.isIntegral_iff
        (A := integralClosure ℤ ℂ) (R := ℤ) (B := ℂ)).1 hIntegral
  · change groupFunctionPairingOverField ℂ (0 : G → ℂ) ρ.character ∈
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

/-- Helper for Corollary 11-11.2-5: pairing the weighted unit-class owner with the trivial
character computes the normalized cardinality of the `n`th-root fiber of `1`. -/
lemma weighted_unit_class_pairing_eq_card_pow_eq_one_div_gcd
    (n : ℕ+) :
    ⟪
      (fun x ↦
        algebraMap ℤ ℂ
          ((((Nat.card G / Nat.gcd (Nat.card G) (n : ℕ)) : ℕ) : ℤ) *
            Ψ^n((ConjClasses.mk (1 : G)).indicator) x)),
      (trivial ℂ G ℂ).character
    ⟫ =
      ((Nat.card {x : G // x ^ (n : ℕ) = 1} : ℂ) / Nat.gcd (Nat.card G) (n : ℕ)) := by
  classical
  let d : ℕ := Nat.gcd (Nat.card G) (n : ℕ)
  let m : ℕ := Nat.card {x : G // x ^ (n : ℕ) = 1}
  have hdvd : d ∣ Nat.card G := Nat.gcd_dvd_left (Nat.card G) (n : ℕ)
  have hd_ne_zero : (d : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.gcd_ne_zero_right n.ne_zero)
  have hterm :
      ∀ x : G,
        algebraMap ℤ ℂ
            ((((Nat.card G / d) : ℕ) : ℤ) *
              Ψ^n((ConjClasses.mk (1 : G)).indicator) x) =
          if x ^ (n : ℕ) = 1 then ((Nat.card G / d : ℕ) : ℂ) else 0 := by
    intro x
    -- Reduce the unit-class indicator to the concrete equation `x ^ n = 1`.
    by_cases hx : x ^ (n : ℕ) = 1
    · have hmem : x ^ (n : ℕ) ∈ (ConjClasses.mk (1 : G)).carrier := by
        exact ConjClasses.mem_carrier_iff_mk_eq.2 <| by
          simpa [ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left] using hx
      rw [if_pos hx, Representation.adamsOperator]
      rw [ConjClasses.indicator, Set.indicator_of_mem hmem]
      simp only [Pi.one_apply, mul_one]
      calc
        (((Nat.card G : ℤ) / d : ℤ) : ℂ) = (Nat.card G : ℂ) / d := by
          exact Int.cast_div_ofNat_charZero (k := ℂ) hdvd
        _ = ((Nat.card G / d : ℕ) : ℂ) := by
          exact (Nat.cast_div hdvd hd_ne_zero).symm
    · have hnotmem : x ^ (n : ℕ) ∉ (ConjClasses.mk (1 : G)).carrier := by
        intro hmem
        exact hx <| by
          simpa [ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left] using
            (ConjClasses.mem_carrier_iff_mk_eq.1 hmem)
      rw [if_neg hx, Representation.adamsOperator]
      rw [ConjClasses.indicator, Set.indicator_apply]
      simp [hnotmem]
  have hsum :
      ∑ x : G,
          algebraMap ℤ ℂ
            ((((Nat.card G / d) : ℕ) : ℤ) *
              Ψ^n((ConjClasses.mk (1 : G)).indicator) x) =
        ((Nat.card G / d : ℕ) : ℂ) * m := by
    -- After the pointwise rewrite, the sum is a constant times the root count.
    simp_rw [hterm]
    calc
      ∑ x : G, (if x ^ (n : ℕ) = 1 then ((Nat.card G / d : ℕ) : ℂ) else 0)
          = ∑ x : G, ((Nat.card G / d : ℕ) : ℂ) * (if x ^ (n : ℕ) = 1 then (1 : ℂ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              by_cases hx : x ^ (n : ℕ) = 1 <;> simp [hx]
      _ = ((Nat.card G / d : ℕ) : ℂ) *
            ∑ x : G, (if x ^ (n : ℕ) = 1 then (1 : ℂ) else 0) := by
              rw [← Finset.mul_sum]
      _ = ((Nat.card G / d : ℕ) : ℂ) * m := by
              have hroot_count :
                  ∑ x : G, (if x ^ (n : ℕ) = 1 then (1 : ℂ) else 0) = m := by
                rw [show m = (Nat.card {x : G // x ^ (n : ℕ) = 1}) by rfl]
                rw [Nat.card_eq_fintype_card]
                rw [Fintype.card_of_subtype (Finset.univ.filter fun x : G ↦ x ^ (n : ℕ) = 1)]
                · simp
                · intro x
                  simp
              rw [hroot_count]
  -- Rewrite the normalized pairing as the displayed quotient and cancel the `|G|` factor.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  have htriv : ∀ x : G, (trivial ℂ G ℂ).character x⁻¹ = 1 := by
    intro x
    simp [Representation.character, Representation.trivial]
  simp_rw [htriv]
  simp only [mul_one]
  rw [hsum]
  rw [Nat.cast_div hdvd]
  field_simp [hd_ne_zero]
  · ring
  · exact hd_ne_zero

/-- Core/canonical Frobenius divisibility statement for the unit class: the number of elements
`x ∈ G` such that `x ^ n = 1` is divisible by `Nat.gcd (Nat.card G) n`. -/
theorem gcd_groupOrder_dvd_card_pow_eq_one
    (n : ℕ) :
    Nat.gcd (Nat.card G) n ∣ Nat.card {x : G // x ^ n = 1} := by
  classical
  -- Split off the degenerate `n = 0` case, where the root fiber is the whole group.
  cases n with
  | zero =>
      simp
  | succ k =>
      let npos : ℕ+ := ⟨k + 1, Nat.succ_pos _⟩
      let η : G → ℂ := fun x ↦
        algebraMap (integralClosure ℤ ℂ) ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (npos : ℕ)) : ℕ) :
              integralClosure ℤ ℂ)) *
          Ψ^npos(((ConjClasses.mk (1 : G)).indicator : G → ℂ)) x
      have hη :
          η ∈ characterRingScalarExtension (integralClosure ℤ ℂ) G := by
        -- The weighted unit-class owner is realized over Serre's integral-closure coefficient ring.
        simpa [η] using
          weightedUnitClassIndicator_mem_characterRingScalarExtension_integralClosure
            (G := G) npos
      have hpair_range :
          ⟪η, (trivial ℂ G ℂ).character⟫ ∈
            Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
        -- Pairing a scalar-extended virtual character with an honest character lands back in
        -- the integral closure.
        exact
          scalarExtensionPairing_mem_range_integralClosure_with_repCharacter
            (G := G) (W := ℂ) (η := η) hη (trivial ℂ G ℂ)
      have hpair_integral :
          IsIntegral ℤ ⟪η, (trivial ℂ G ℂ).character⟫ := by
        -- Convert the integral-closure range statement into ordinary integrality over `ℤ`.
        exact
          (IsIntegralClosure.isIntegral_iff
            (A := integralClosure ℤ ℂ) (R := ℤ) (B := ℂ)).2 hpair_range
      have hgcd_dvd_card :
          Nat.gcd (Fintype.card G) (npos : ℕ) ∣ Fintype.card G := by
        exact Nat.gcd_dvd_left (Fintype.card G) (npos : ℕ)
      have hgcd_ne_zero_cast :
          ((Nat.gcd (Fintype.card G) (npos : ℕ) : ℕ) : ℂ) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr (Nat.gcd_ne_zero_right npos.ne_zero)
      have hη_eq :
          η =
            fun x ↦
              algebraMap ℤ ℂ
                ((((Nat.card G / Nat.gcd (Nat.card G) (npos : ℕ)) : ℕ) : ℤ) *
                  Ψ^npos((ConjClasses.mk (1 : G)).indicator) x) := by
        funext x
        by_cases hx : x ^ (npos : ℕ) ∈ (ConjClasses.mk (1 : G)).carrier
        · -- On the support, both owners reduce to the same global constant.
          simp [η, Representation.adamsOperator, ConjClasses.indicator, hx]
          calc
            ((Fintype.card G / Nat.gcd (Fintype.card G) (npos : ℕ) : ℕ) : ℂ)
              = (Fintype.card G : ℂ) / Nat.gcd (Fintype.card G) (npos : ℕ) := by
                  exact Nat.cast_div hgcd_dvd_card hgcd_ne_zero_cast
            _ =
                (((Fintype.card G : ℤ) / Nat.gcd (Fintype.card G) (npos : ℕ) : ℤ) : ℂ) := by
                  symm
                  exact Int.cast_div_ofNat_charZero (k := ℂ) hgcd_dvd_card
        · -- Off the support, both owners vanish.
          simp [η, Representation.adamsOperator, ConjClasses.indicator, hx]
      have hpair_eq :
          ⟪η, (trivial ℂ G ℂ).character⟫ =
            ((Nat.card {x : G // x ^ Nat.succ k = 1} : ℂ) /
              Nat.gcd (Nat.card G) (Nat.succ k)) := by
        -- The owner pairing is exactly the normalized root count.
        rw [hη_eq]
        simpa [npos] using
          weighted_unit_class_pairing_eq_card_pow_eq_one_div_gcd (G := G) npos
      have hgcd_ne_zero : Nat.gcd (Nat.card G) (Nat.succ k) ≠ 0 := by
        exact Nat.gcd_ne_zero_right (Nat.succ_ne_zero _)
      rw [hpair_eq] at hpair_integral
      exact nat_dvd_of_isIntegral_natCast_div
        (m := Nat.card {x : G // x ^ Nat.succ k = 1})
        (n := Nat.gcd (Nat.card G) (Nat.succ k))
        hgcd_ne_zero hpair_integral

/-- Corollary 11-11.2-5: if `n` divides the order of the finite group `G`, then the number of
elements `x ∈ G` such that `x ^ n = 1` is divisible by `n`. -/
theorem dvd_card_pow_eq_one
    (n : ℕ) (hdiv : n ∣ Nat.card G) :
    n ∣ Nat.card {x : G // x ^ n = 1} := by
  have hdiv' : n ∣ Fintype.card G := by
    simpa [Nat.card_eq_fintype_card] using hdiv
  simpa [Nat.card_eq_fintype_card, Nat.gcd_eq_right hdiv'] using
    gcd_groupOrder_dvd_card_pow_eq_one G n

end FrobeniusTheorem

end Representation
