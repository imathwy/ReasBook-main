import Mathlib
import stacks_project.Chap10.Definition_10_63_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MvPolynomial IsLocalRing

/-- The quotient ring `k[x₁, x₂, x₃, \ldots]/(x_i^2)` from the counterexample in
Stacks, Remark 10.63.12 (`05BX`). -/
abbrev infiniteSquareZeroPolynomialQuotient (k : Type u) [CommRing k] :=
  MvPolynomial ℕ k ⧸ Ideal.span (Set.range fun i : ℕ ↦ ((X i : MvPolynomial ℕ k) ^ 2))

section

variable (k : Type u) [Field k]

local notation "I∞" =>
  Ideal.span (Set.range fun i : ℕ ↦ ((X i : MvPolynomial ℕ k) ^ 2))
local notation "S∞" => infiniteSquareZeroPolynomialQuotient k

-- Keep the quotient ring's canonical self-module structure local so theorem statements elaborate
-- without exposing any extra public API.
noncomputable local instance : Module S∞ S∞ :=
  Semiring.toModule

/-- The augmentation `k[x₁, x₂, x₃, \ldots] / (x_i^2) → k` given by the constant coefficient. -/
noncomputable def infiniteSquareZeroPolynomialQuotientAugmentation : S∞ →+* k :=
  Ideal.Quotient.lift I∞ MvPolynomial.constantCoeff <| by
    intro p hp
    have hker : I∞ ≤ RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial ℕ k →+* k) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]
    simpa [RingHom.mem_ker] using hker hp

/-- The augmentation `k[x₁, x₂, x₃, \ldots] / (x_i^2) → k` is surjective. -/
theorem infiniteSquareZeroPolynomialQuotientAugmentation_surjective :
    Function.Surjective (infiniteSquareZeroPolynomialQuotientAugmentation k) := by
  intro a
  refine ⟨Ideal.Quotient.mk I∞ (MvPolynomial.C a), ?_⟩
  simp [infiniteSquareZeroPolynomialQuotientAugmentation]

/-- An element of the infinite square-zero polynomial quotient is a unit exactly when its
augmentation is nonzero. -/
theorem infiniteSquareZeroPolynomialQuotient_isUnit_iff_augmentation_ne_zero (x : S∞) :
    IsUnit x ↔ infiniteSquareZeroPolynomialQuotientAugmentation k x ≠ 0 := by
  sorry

instance : IsLocalRing S∞ := by
  letI : Nontrivial S∞ := (infiniteSquareZeroPolynomialQuotientAugmentation k).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ ?_
  by_cases hx : infiniteSquareZeroPolynomialQuotientAugmentation k x = 0
  · right
    rw [infiniteSquareZeroPolynomialQuotient_isUnit_iff_augmentation_ne_zero]
    simp [map_sub, hx]
  · left
    exact (infiniteSquareZeroPolynomialQuotient_isUnit_iff_augmentation_ne_zero k x).2 hx

/-- The residue field of `k[x₁, x₂, x₃, \ldots] / (x_i^2)` is canonically `k`. -/
noncomputable def infiniteSquareZeroPolynomialQuotientResidueFieldEquiv :
    ResidueField S∞ ≃+* k := by
  let f := infiniteSquareZeroPolynomialQuotientAugmentation k
  letI : IsLocalHom f := IsLocalHom.of_surjective f
    (infiniteSquareZeroPolynomialQuotientAugmentation_surjective k)
  refine RingEquiv.ofBijective (IsLocalRing.ResidueField.lift f) ?_
  constructor
  · exact RingHom.injective _
  · intro a
    obtain ⟨x, rfl⟩ := infiniteSquareZeroPolynomialQuotientAugmentation_surjective k a
    refine ⟨residue S∞ x, ?_⟩
    change IsLocalRing.ResidueField.lift f (residue S∞ x) = f x
    simp [IsLocalRing.ResidueField.lift_residue_apply]

/-- In the Stacks counterexample ring `S = k[x₁, x₂, x₃, \ldots]/(x_i^2)`, the only
textbook-associated prime of `S` viewed as a `k`-module is `(0)`. -/
theorem infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_over_baseField_eq_singleton_bot :
    associatedPrimesOfModule k S∞ = {⊥} := by
  sorry

/-- Noetherian-field companion to
`infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_over_baseField_eq_singleton_bot`
in mathlib's radical-based `associatedPrimes` API. -/
theorem infiniteSquareZeroPolynomialQuotient_associatedPrimes_over_baseField_eq_singleton_bot :
    associatedPrimes k S∞ = {⊥} := by
  rw [← associatedPrimesOfModule_eq_associatedPrimes k S∞]
  exact infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_over_baseField_eq_singleton_bot
    k

/-- In the Stacks counterexample ring `S = k[x₁, x₂, x₃, \ldots]/(x_i^2)`, the textbook-associated
primes of `S` as an `S`-module are empty. -/
theorem infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_self_eq_empty :
    associatedPrimesOfModule S∞ S∞ = ∅ := by
  sorry

/-- Remark 10.63.12 (Stacks, tag `05BX`): for
`S = k[x₁, x₂, x₃, \ldots]/(x_i^2)` and `M = S`, the associated primes of `M` over the base field
`k` are nonempty, while the associated primes of `S` over itself are empty. -/
theorem infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_counterexample :
    (associatedPrimesOfModule k S∞).Nonempty ∧ associatedPrimesOfModule S∞ S∞ = ∅ := by
  refine ⟨?_, infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_self_eq_empty k⟩
  rw [infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_over_baseField_eq_singleton_bot k]
  exact Set.singleton_nonempty ⊥

/-- Noetherian-field companion to
`infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_counterexample` in mathlib's
`associatedPrimes` API. -/
theorem infiniteSquareZeroPolynomialQuotient_associatedPrimes_counterexample :
    (associatedPrimes k S∞).Nonempty ∧ associatedPrimesOfModule S∞ S∞ = ∅ := by
  rw [← associatedPrimesOfModule_eq_associatedPrimes k S∞]
  exact infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_counterexample k

/-- Remark 10.63.12 (Stacks, tag `05BX`): for the ring map
`k → k[x₁, x₂, x₃, \ldots]/(x_i^2)` with `M = S`, the image of `Ass_S(M)` in `Spec k` does not
contain `Ass_k(M)`. -/
theorem associatedPrimesOfModule_comap_not_superset_for_infiniteSquareZeroPolynomialQuotient :
    ¬ associatedPrimesOfModule k S∞ ⊆
      Ideal.comap (algebraMap k S∞) '' associatedPrimesOfModule S∞ S∞ := by
  rw [infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_over_baseField_eq_singleton_bot k,
    infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_self_eq_empty k]
  simp

/-- Noetherian-field companion to
`associatedPrimesOfModule_comap_not_superset_for_infiniteSquareZeroPolynomialQuotient` in
mathlib's radical-based `associatedPrimes` API. -/
theorem associatedPrimes_comap_not_superset_for_infiniteSquareZeroPolynomialQuotient :
    ¬ associatedPrimes k S∞ ⊆
      Ideal.comap (algebraMap k S∞) '' associatedPrimesOfModule S∞ S∞ := by
  rw [← associatedPrimesOfModule_eq_associatedPrimes k S∞]
  exact associatedPrimesOfModule_comap_not_superset_for_infiniteSquareZeroPolynomialQuotient k

end
