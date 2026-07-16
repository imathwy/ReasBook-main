import StacksProject_2024.stacks_project.Chap29.Definition_29_45_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_46_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {B : Type u} [CommRing B]

-- Semantic recall: `lean_leansearch` surfaced the affine-spectrum homeomorphism criterion
-- `PrimeSpectrum.isHomeomorph_comap`; local Chapter 29 precedent supplies
-- `UniversalHomeomorphism` for the source-facing scheme morphism `Spec(B) -> Spec(A)`.
-- The Stacks tag evidence is consistent: item tag `0CNC` agrees with the source URL ending in
-- `/tag/0CNC`.

/-- A prime number and an element outside a subring whose multiple by that prime and prime-th power
both lie in the subring. -/
class HasNatPrimeMulPowerInSubring (A : Subring B) (p : ℕ) (b : B) : Prop where
  prime : Nat.Prime p
  not_mem : b ∉ A
  mul_mem : (p : B) * b ∈ A
  power_mem : b ^ p ∈ A

/-- The prime-power subring witness property is proposition-valued. -/
instance instSubsingletonHasNatPrimeMulPowerInSubring
    (A : Subring B) (p : ℕ) (b : B) :
    Subsingleton (HasNatPrimeMulPowerInSubring A p b) :=
  inferInstance

/-- Lemma 29.46.6: if `A ⊂ B` is a ring extension such that `Spec(B) → Spec(A)` is a universal
homeomorphism and `A ≠ B`, then either some `b ∈ B \ A` has `b ^ 2 ∈ A` and `b ^ 3 ∈ A`, or for
some prime number `p` some `b ∈ B \ A` has `p * b ∈ A` and `b ^ p ∈ A`. -/
@[stacks 0CNC]
theorem exists_sq_cube_or_natPrime_mul_power_mem_subring_of_specMap_universalHomeomorphism
    (A : Subring B)
    (hSpec : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom A.subtype)))
    (hneq : A ≠ ⊤) :
    (∃ b : B, b ∉ A ∧ b ^ 2 ∈ A ∧ b ^ 3 ∈ A) ∨
      ∃ (p : ℕ) (b : B), HasNatPrimeMulPowerInSubring A p b := sorry

end AlgebraicGeometry
