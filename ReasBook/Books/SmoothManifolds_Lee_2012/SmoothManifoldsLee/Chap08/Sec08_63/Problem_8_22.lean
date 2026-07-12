import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic Lean search was unavailable in this runner; the statement shape was checked directly
-- against the chapter's earlier `linear_endomorphism_commutator_apply` recall together with
-- mathlib's associative Lie algebra structure on `Module.End R A` and the `LieSubalgebra` API.

universe u v

section

variable {R : Type v} {A : Type u} [CommRing R] [Ring A] [Algebra R A]

/-
Lee's Problem 8-22 is stated for an arbitrary associative algebra. Mathlib's canonical owner
`Derivation R A A` specializes to commutative `A`, so the source-facing primitive notion here
remains the Leibniz predicate on `Module.End R A`. The Lie-subalgebra structure below is derived
from that predicate, and the commutative specialization is bridged back to mathlib's canonical
`Derivation` Lie algebra.
-/

/-- A linear endomorphism of an associative `R`-algebra `A` is a derivation if it satisfies the
Leibniz rule. -/
def is_algebra_derivation (D : Module.End R A) : Prop :=
  ∀ x y : A, D (x * y) = D x * y + x * D y

/-- Problem 8-22 (1): if `D₁` and `D₂` are derivations of an associative `R`-algebra `A`, then
their Lie bracket `⁅D₁, D₂⁆`, i.e. their commutator, is also a derivation. -/
theorem is_algebra_derivation_lie {D₁ D₂ : Module.End R A}
    (hD₁ : is_algebra_derivation D₁) (hD₂ : is_algebra_derivation D₂) :
    is_algebra_derivation ⁅D₁, D₂⁆ := by
  intro x y
  -- Expand the commutator pointwise so each composite can use the Leibniz rule.
  calc
    (⁅D₁, D₂⁆ : Module.End R A) (x * y)
        = D₁ (D₂ (x * y)) - D₂ (D₁ (x * y)) := by
            simp [Ring.lie_def, Module.End.mul_apply]
    _ = (D₁ (D₂ x) * y + D₂ x * D₁ y + (D₁ x * D₂ y + x * D₁ (D₂ y)))
          - (D₂ (D₁ x) * y + D₁ x * D₂ y + (D₂ x * D₁ y + x * D₂ (D₁ y))) := by
            -- Apply the Leibniz rule first to `D₂ (x * y)` and `D₁ (x * y)`,
            -- then again to the outer derivation in each summand.
            rw [hD₂ x y, hD₁ x y]
            rw [map_add, map_add]
            rw [hD₁ (D₂ x) y, hD₁ x (D₂ y), hD₂ (D₁ x) y, hD₂ x (D₁ y)]
    _ = (D₁ (D₂ x) - D₂ (D₁ x)) * y + x * (D₁ (D₂ y) - D₂ (D₁ y)) := by
            -- The mixed terms cancel additively, leaving the commutator Leibniz rule.
            rw [sub_mul, mul_sub]
            abel_nf
    _ = (⁅D₁, D₂⁆ : Module.End R A) x * y + x * (⁅D₁, D₂⁆ : Module.End R A) y := by
            simp [Ring.lie_def, Module.End.mul_apply]

/-- Helper for Problem 8-22: the zero endomorphism satisfies the Leibniz rule. -/
theorem is_algebra_derivation_zero : is_algebra_derivation (0 : Module.End R A) := by
  intro x y
  -- The zero map annihilates each term of the Leibniz identity.
  simp

/-- Helper for Problem 8-22: the sum of two derivations is again a derivation. -/
theorem is_algebra_derivation_add {D₁ D₂ : Module.End R A}
    (hD₁ : is_algebra_derivation D₁) (hD₂ : is_algebra_derivation D₂) :
    is_algebra_derivation (D₁ + D₂) := by
  intro x y
  -- Expand both maps pointwise and regroup the resulting additive terms.
  calc
    (D₁ + D₂) (x * y) = D₁ (x * y) + D₂ (x * y) := by
      simp
    _ = (D₁ x * y + x * D₁ y) + (D₂ x * y + x * D₂ y) := by
      rw [hD₁ x y, hD₂ x y]
    _ = (D₁ x + D₂ x) * y + x * (D₁ y + D₂ y) := by
      simp only [add_mul, mul_add]
      abel
    _ = (D₁ + D₂) x * y + x * (D₁ + D₂) y := by
      simp

/-- Helper for Problem 8-22: scalar multiples of derivations remain derivations. -/
theorem is_algebra_derivation_smul (r : R) {D : Module.End R A}
    (hD : is_algebra_derivation D) : is_algebra_derivation (r • D) := by
  intro x y
  -- Move the scalar through the Leibniz identity using the algebra structure on `A`.
  calc
    (r • D) (x * y) = r • D (x * y) := by
      simp
    _ = r • (D x * y + x * D y) := by
      rw [hD x y]
    _ = r • (D x * y) + r • (x * D y) := by
      rw [smul_add]
    _ = (r • D x) * y + r • (x * D y) := by
      rw [Algebra.smul_mul_assoc]
    _ = (r • D x) * y + x * (r • D y) := by
      rw [mul_smul_comm]
    _ = (r • D) x * y + x * (r • D) y := by
      simp

/-- Problem 8-22 (2): the set of derivations of an associative `R`-algebra `A` is a Lie subalgebra
of the Lie algebra of linear endomorphisms of `A`, with bracket given by the commutator. -/
def algebra_derivations_lie_subalgebra : LieSubalgebra R (Module.End R A) where
  carrier := { D | is_algebra_derivation D }
  add_mem' := is_algebra_derivation_add
  zero_mem' := is_algebra_derivation_zero
  smul_mem' := is_algebra_derivation_smul
  lie_mem' := is_algebra_derivation_lie

/-- Membership in `algebra_derivations_lie_subalgebra` is exactly the Leibniz rule. -/
@[simp]
theorem mem_algebra_derivations_lie_subalgebra (D : Module.End R A) :
    D ∈ algebra_derivations_lie_subalgebra ↔ is_algebra_derivation D :=
  Iff.rfl

end

section Commutative

variable {R : Type v} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]

namespace Module.End

/-- On a commutative `R`-algebra, a source-facing algebra derivation is the same data as a
mathlib `Derivation`. -/
def toDerivation (D : Module.End R A) (hD : is_algebra_derivation D) : Derivation R A A :=
  Derivation.mk' D fun x y ↦ by
    simpa [smul_eq_mul, mul_comm, add_comm] using hD x y

@[simp]
theorem coe_toDerivation (D : Module.End R A) (hD : is_algebra_derivation D) :
    ((D.toDerivation hD : Derivation R A A) : Module.End R A) = D :=
  rfl

end Module.End

/-- A canonical `Derivation` on a commutative algebra satisfies the source-facing Leibniz rule on
`Module.End R A`. -/
theorem is_algebra_derivation_of_derivation (D : Derivation R A A) :
    is_algebra_derivation (D : Module.End R A) := by
  intro x y
  calc
    D (x * y) = x * D y + y * D x := by
      rw [D.leibniz, smul_eq_mul, smul_eq_mul]
    _ = D x * y + x * D y := by
      ac_rfl

/-- On a commutative `R`-algebra, the source-facing Lie subalgebra of algebra derivations is Lie
equivalent to mathlib's canonical Lie algebra `Derivation R A A`. -/
def algebra_derivations_lie_subalgebra_equiv_derivation :
    (algebra_derivations_lie_subalgebra : LieSubalgebra R (Module.End R A)) ≃ₗ⁅R⁆
      Derivation R A A where
  toFun D := (D : Module.End R A).toDerivation D.2
  map_add' := by
    intro D₁ D₂
    ext x
    rfl
  map_smul' := by
    intro r D
    ext x
    rfl
  map_lie' := by
    intro D₁ D₂
    ext x
    rfl
  invFun D := ⟨(D : Module.End R A), is_algebra_derivation_of_derivation D⟩
  left_inv D := by
    ext x
    rfl
  right_inv D := by
    ext x
    rfl

@[simp]
theorem algebra_derivations_lie_subalgebra_equiv_derivation_apply
    (D : (algebra_derivations_lie_subalgebra : LieSubalgebra R (Module.End R A))) :
    ((algebra_derivations_lie_subalgebra_equiv_derivation D : Derivation R A A) :
      Module.End R A) = (D : Module.End R A) :=
  Module.End.coe_toDerivation (D : Module.End R A) D.2

@[simp]
theorem algebra_derivations_lie_subalgebra_equiv_derivation_symm_apply (D : Derivation R A A) :
    ((algebra_derivations_lie_subalgebra_equiv_derivation.symm D :
      (algebra_derivations_lie_subalgebra : LieSubalgebra R (Module.End R A))) :
      Module.End R A) = D := by
  change (((algebra_derivations_lie_subalgebra_equiv_derivation :
      (algebra_derivations_lie_subalgebra : LieSubalgebra R (Module.End R A)) ≃ₗ⁅R⁆
        Derivation R A A).invFun D :
      (algebra_derivations_lie_subalgebra : LieSubalgebra R (Module.End R A))) :
      Module.End R A) = D
  rfl

end Commutative
