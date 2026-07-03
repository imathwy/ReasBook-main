import Mathlib

noncomputable section

open Representation

universe u v w

namespace Representation
namespace MatrixTailScalarExtension

section

variable {S : Type u}
variable {M : Type v} [AddCommGroup M] [Module ℤ M]
variable {N : Type v} [AddCommGroup N] [Module ℤ N]
variable {P : Type w} [AddCommGroup P] [Module ℤ P]

/-- Helper for Proposition 15-15.5-1: evaluating a left inverse on a point recovers that point. -/
theorem linearMap_eq_of_comp_eq_id_apply
    (s : N →ₗ[ℤ] M)
    (f : M →ₗ[ℤ] N)
    (h : s.comp f = LinearMap.id)
    (x : M) :
    s (f x) = x := by
  -- Evaluate the equality `s.comp f = id` at `x` to recover the original element.
  simpa [LinearMap.comp_apply] using LinearMap.congr_fun h x

/-- Helper for Proposition 15-15.5-1: a left inverse `bk.constr ℤ bK` identifies any vector whose
image is the `i`-th reduced basis vector with the corresponding `K`-basis vector. -/
theorem basis_image_of_left_inverse_and_basis_value
    (bK : Module.Basis S ℤ M)
    (bk : Module.Basis S ℤ N)
    (d : M →ₗ[ℤ] N)
    (x : M)
    (i : S)
    (hleftInv : (bk.constr ℤ bK).comp d = LinearMap.id)
    (hx : d x = bk i) :
    x = bK i := by
  let s : N →ₗ[ℤ] M := bk.constr ℤ bK
  -- Apply the left inverse to the basis-value identity and simplify the resulting basis
  -- reconstruction.
  calc
    x = s (d x) := by
      symm
      exact linearMap_eq_of_comp_eq_id_apply s d hleftInv x
    _ = s (bk i) := by
      rw [hx]
    _ = bK i := by
      simp [s]

/-- Helper for Proposition 15-15.5-1: once the triangle and decomposition left inverse are known
on the chosen bases, scalar extension sends each projective-envelope basis vector to the matching
`K`-simple basis vector. -/
theorem projectiveScalarExtension_basis_image_support_of_order_prime_to_p
    (bP : Module.Basis S ℤ P)
    (bK : Module.Basis S ℤ M)
    (bk : Module.Basis S ℤ N)
    (d : M →ₗ[ℤ] N)
    (e : P →ₗ[ℤ] M)
    (hleftInv : (bk.constr ℤ bK).comp d = LinearMap.id)
    (htriangle_basis : ∀ i, d (e (bP i)) = bk i) :
    ∀ i, e (bP i) = bK i := by
  intro i
  -- The decomposition left inverse identifies the unique preimage of `bk i` with `bK i`.
  exact
    basis_image_of_left_inverse_and_basis_value
      bK bk d (e (bP i)) i hleftInv (htriangle_basis i)

/-- Helper for Proposition 15-15.5-1: once the basis images agree pointwise, the corresponding
basis matrix is the identity. -/
theorem projectiveScalarExtension_toMatrix_support_of_order_prime_to_p
    (bP : Module.Basis S ℤ P)
    (bK : Module.Basis S ℤ M)
    (e : P →ₗ[ℤ] M)
    (himages : ∀ i, e (bP i) = bK i) :
    bK.toMatrix (fun i ↦ e (bP i)) = bK.toMatrix bK := by
  have himages' : (fun i ↦ e (bP i)) = bK := by
    -- Package the pointwise basis-image identities as an equality of functions.
    funext i
    exact himages i
  -- Once the column vectors agree pointwise, the basis matrices are identical.
  exact congrArg (fun g ↦ bK.toMatrix g) himages'

end

end MatrixTailScalarExtension
end Representation
