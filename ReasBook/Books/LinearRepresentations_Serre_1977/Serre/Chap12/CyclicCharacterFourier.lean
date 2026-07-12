import Mathlib

/-!
# Character orthogonality and Fourier inversion on a finite commutative group

General tools for Serre §12.7 (Lemma 15, `Infra_12_7_CyclicDescent`): the orthogonality of the
linear characters of a finite commutative group `C` valued in a field `Ω` with enough roots of
unity, and the resulting (pointwise) Fourier inversion formula.  These are the analytic backbone
of the cyclic-group rationality argument `reducedAmbientConstancySpanCard_descent_local`.

The hypotheses `[Fintype (C →* Ωˣ)]` and `[HasEnoughRootsOfUnity Ω (Monoid.exponent C)]` are
supplied at the use site; for `Ω = AlgebraicClosure K` the latter is automatic, and the former
follows from `CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity`.
-/

open scoped BigOperators

namespace Representation

section CyclicCharacterFourier

variable {C : Type*} [CommGroup C] [Fintype C] [DecidableEq C]
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
variable [Fintype (C →* Ωˣ)] [HasEnoughRootsOfUnity Ω (Monoid.exponent C)]

/-- Orthogonality of characters: the sum over all linear characters `β : C →* Ωˣ` of `β g`
equals `|C|` when `g = 1` and `0` otherwise.  Proved by the standard "shift the summation by a
character separating `g` from `1`" argument. -/
theorem cyclicCharacter_sum_eq (g : C) :
    ∑ β : C →* Ωˣ, (β g : Ω) = if g = 1 then (Nat.card C : Ω) else 0 := by
  classical
  rw [← CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity C Ω]
  by_cases hg : g = 1
  · subst hg; simp [Nat.card_eq_fintype_card]
  · obtain ⟨β₀, hβ₀⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity C Ω hg
    have key : (β₀ g : Ω) * (∑ β : C →* Ωˣ, (β g : Ω)) = ∑ β : C →* Ωˣ, (β g : Ω) := by
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft β₀) (fun β : C →* Ωˣ => (β g : Ω))]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      show (β₀ g : Ω) * (β g : Ω) = (((β₀ * β) g : Ωˣ) : Ω)
      rw [MonoidHom.mul_apply, Units.val_mul]
    have hsub : ((β₀ g : Ω) - 1) * (∑ β : C →* Ωˣ, (β g : Ω)) = 0 := by
      rw [sub_mul, one_mul, key, sub_self]
    have hne : (β₀ g : Ω) - 1 ≠ 0 := by
      rw [sub_ne_zero]; intro h; exact hβ₀ (Units.ext (by simpa using h))
    rw [if_neg hg]
    exact (mul_eq_zero.mp hsub).resolve_left hne

/-- Fourier inversion (pointwise): for any `Ω`-valued function `φ` on the finite commutative group
`C`, the value `|C| · φ c₀` is recovered from the character coefficients
`∑_c φ c · (β c)⁻¹`. -/
theorem cyclicFourier_inversion (φ : C → Ω) (c₀ : C) :
    (Nat.card C : Ω) * φ c₀ = ∑ β : C →* Ωˣ, (∑ c : C, φ c * (β c : Ω)⁻¹) * (β c₀ : Ω) := by
  classical
  have step2 : ∀ c : C, (if c = c₀ then (Nat.card C : Ω) else 0)
      = ∑ β : C →* Ωˣ, (β c₀ : Ω) * (β c : Ω)⁻¹ := by
    intro c
    have h1 : (∑ β : C →* Ωˣ, (β c₀ : Ω) * (β c : Ω)⁻¹) = ∑ β : C →* Ωˣ, (β (c₀ * c⁻¹) : Ω) := by
      refine Finset.sum_congr rfl (fun β _ => ?_)
      rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [h1, cyclicCharacter_sum_eq (c₀ * c⁻¹)]
    by_cases hcc : c = c₀
    · subst hcc; simp
    · rw [if_neg hcc, if_neg (fun h => hcc (mul_inv_eq_one.mp h).symm)]
  have step1 : (Nat.card C : Ω) * φ c₀
      = ∑ c : C, φ c * (if c = c₀ then (Nat.card C : Ω) else 0) := by
    rw [Finset.sum_eq_single c₀ (fun c _ hc => by rw [if_neg hc, mul_zero])
      (fun h => absurd (Finset.mem_univ c₀) h), if_pos rfl, mul_comm]
  rw [step1]
  simp_rw [step2, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun c _ => by ring)

end CyclicCharacterFourier

section CyclicFourierCoeffIntegral

variable {C : Type*} [CommGroup C] [Fintype C]
variable {A : Type*} [CommRing A]
variable {Ω : Type*} [Field Ω] [Algebra A Ω]

/-- Integrality of the Fourier coefficient: for `h : C → A` and a linear character `β`, the
coefficient `∑ c, (algebraMap A Ω (h c)) · (β c)⁻¹` is integral over `A` (each summand is an
`A`-image times a root of unity).  This is the `S3` step of Serre's Lemma 15 rationality argument:
it makes the coefficients land, after a final integral-closedness descent, back in `A`. -/
theorem cyclicFourier_coeff_isIntegral (h : C → A) (β : C →* Ωˣ) :
    IsIntegral A (∑ c : C, algebraMap A Ω (h c) * (β c : Ω)⁻¹) := by
  classical
  refine IsIntegral.sum _ (fun c _ => IsIntegral.mul isIntegral_algebraMap ?_)
  refine IsIntegral.of_pow (n := Nat.card C) Nat.card_pos ?_
  have hpow : ((β c : Ω)⁻¹) ^ (Nat.card C) = 1 := by
    rw [inv_pow, ← Units.val_pow_eq_pow_val, ← map_pow,
      show c ^ (Nat.card C) = 1 from by rw [Nat.card_eq_fintype_card]; exact pow_card_eq_one,
      map_one, Units.val_one, inv_one]
  rw [hpow]; exact isIntegral_one

end CyclicFourierCoeffIntegral

end Representation
