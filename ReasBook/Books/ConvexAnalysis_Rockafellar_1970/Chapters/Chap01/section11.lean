import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_1_11 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Text 1.11 considers affine self-maps of a module affine space of the form
  `x ↦ A x + a`, where `A` is invertible, and records the explicit affine inverse.
- `core/canonical`: the owner abstraction is `AffineEquiv.ofLinearEquiv`.
- `bridge/view`: the intrinsic affine-space inverse formula is
  `(ofLinearEquiv A p₀ p₁).symm x = A.symm (x -ᵥ p₁) +ᵥ p₀`;
  the textbook module-space formula `x ↦ A.symm (x - a)` is the specialization
  `P = V`, `p₀ = 0`, `p₁ = a`.
- Layer target: `bridge/view`.
- Primitive data vs derived API: the primitive data are the linear equivalence `A` and the
  translation vector `a`; the affine automorphism and its inverse formula are derived owner-level
  API and should be exposed through that owner rather than through a parallel bijectivity wrapper.
  The forward formula is already the direct owner theorem `ofLinearEquiv_apply`; the local bridge
  added below first identifies the inverse owner itself, then specializes to pointwise formulas.
-- Domain-style sampling: the relevant owner declarations are `AffineEquiv.ofLinearEquiv`,
  `AffineEquiv.ofLinearEquiv_apply`, and `AffineEquiv.linear_ofLinearEquiv`.
- Canonicalization decision record (this pass):
  - Codomain/ambient check: this item is already intrinsic in affine-space owners
    (`AffineEquiv.ofLinearEquiv`) and does not use any concrete ordered codomain.
  - Scalar/ambient check: `AffineEquiv.ofLinearEquiv` in mathlib currently lives at
    `[Ring k] [AddCommGroup V] [Module k V]`, so no weaker scalar layer is available here without
    upstream owner changes.
  - Owner check: keep `ofLinearEquiv` as the core owner, and expose the module specialization
    through source-facing pointwise formulas (both arbitrary-basepoint and `0`-origin bridges),
    avoiding implementation-level
    `trans`/`vaddConst` decomposition on the public theorem surface.
  - Topology check: this item is not topology-facing.
  - Notation check: no additional notation is needed; existing owner names already match the
    mathematical surface.
-/

namespace AffineEquiv

/- Text 1.11: the canonical affine automorphism attached to an invertible linear map and a
translation is `ofLinearEquiv`. -/
recall ofLinearEquiv
recall ofLinearEquiv_apply
recall linear_ofLinearEquiv

section Module

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

section AddTorsor

variable {P : Type*} [AddTorsor V P]

/- Owner-level inverse for `AffineEquiv.ofLinearEquiv` in an arbitrary affine space. -/
@[simp] theorem ofLinearEquiv_symm (A : V ≃ₗ[k] V) (p₀ p₁ : P) :
    (ofLinearEquiv A p₀ p₁).symm = ofLinearEquiv A.symm p₁ p₀ := by
  ext x
  apply (ofLinearEquiv A p₀ p₁).symm_apply_eq.2
  simp

/- Pointwise inverse formula, derived from the owner-level inverse identity. -/
@[simp] theorem ofLinearEquiv_symm_apply (A : V ≃ₗ[k] V) (p₀ p₁ x : P) :
    (ofLinearEquiv A p₀ p₁).symm x = A.symm (x -ᵥ p₁) +ᵥ p₀ := by
  simp [ofLinearEquiv_symm]

end AddTorsor

/- Module-space bridge view in additive notation, with arbitrary source/target basepoints. -/
theorem ofLinearEquiv_apply_sub (A : V ≃ₗ[k] V) (a₀ a₁ x : V) :
    ofLinearEquiv A a₀ a₁ x = A (x - a₀) + a₁ := by
  simp [ofLinearEquiv_apply, vsub_eq_sub, vadd_eq_add]

/- Module-space inverse bridge view in additive notation, with arbitrary basepoints. -/
theorem ofLinearEquiv_symm_apply_sub (A : V ≃ₗ[k] V) (a₀ a₁ x : V) :
    (ofLinearEquiv A a₀ a₁).symm x = A.symm (x - a₁) + a₀ := by
  simp [vsub_eq_sub, vadd_eq_add]

/- Text 1.11: in module affine space, `ofLinearEquiv` specializes pointwise to `x ↦ A x + a`. -/
@[simp] theorem ofLinearEquiv_zero_apply (A : V ≃ₗ[k] V) (a x : V) :
    ofLinearEquiv A 0 a x = A x + a := by
  rw [ofLinearEquiv_apply_sub (A := A) (a₀ := (0 : V)) (a₁ := a) (x := x)]
  simp

/- Text 1.11: the inverse of `x ↦ A x + a` is the affine map `x ↦ A.symm (x - a)`. -/
@[simp] theorem ofLinearEquiv_zero_symm_apply (A : V ≃ₗ[k] V) (a x : V) :
    (ofLinearEquiv A 0 a).symm x = A.symm (x - a) := by
  rw [ofLinearEquiv_symm_apply_sub (A := A) (a₀ := (0 : V)) (a₁ := a) (x := x)]
  simp

end Module

end AffineEquiv
