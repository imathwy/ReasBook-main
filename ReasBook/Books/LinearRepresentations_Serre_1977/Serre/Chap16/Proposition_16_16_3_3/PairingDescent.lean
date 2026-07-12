import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_3_3.PositiveBasics

noncomputable section

universe u

open CategoryTheory
open scoped Representation MonoidAlgebra

namespace Representation

section

/-- Helper for Proposition 16-16.3-3: the Schur-weighted simple-basis dot product with a fixed
class, packaged as a linear functional. -/
def weightedSimpleBasisPairing
    {κ : Type*} {M : Type*} [AddCommGroup M]
    (b : Module.Basis κ ℤ M) (w : κ → ℤ) (z : M) :
    M →ₗ[ℤ] ℤ :=
  b.constr ℤ (fun j ↦ w j * b.repr z j)

/-- Helper for Proposition 16-16.3-3: two classes with nonnegative coordinates have
nonnegative Schur-weighted simple-basis pairing when all Schur weights are nonnegative. -/
theorem weightedSimpleBasisPairing_nonneg_of_positive
    {κ : Type*} {M : Type*} [AddCommGroup M]
    (b : Module.Basis κ ℤ M) {w : κ → ℤ} {x z : M}
    (hw_nonneg : ∀ j, 0 ≤ w j)
    (hx : x ∈ b.positiveCone)
    (hz : z ∈ b.positiveCone) :
    0 ≤ weightedSimpleBasisPairing b w z x := by
  -- Evaluate the weighted functional in coordinates and check every summand is nonnegative.
  rw [weightedSimpleBasisPairing, Module.Basis.constr_apply]
  refine Finsupp.sum_nonneg ?_
  intro j _hj
  exact mul_nonneg (hx j) (mul_nonneg (hw_nonneg j) (hz j))

/-- Helper for Proposition 16-16.3-3: pairing against a basis vector reads the corresponding
Schur-weighted coordinate. -/
theorem weightedSimpleBasisPairing_basis_left
    {κ : Type*} {M : Type*} [AddCommGroup M]
    (b : Module.Basis κ ℤ M) (w : κ → ℤ) (i : κ) (x : M) :
    weightedSimpleBasisPairing b w (b i) x = w i * b.repr x i := by
  classical
  -- Replace the basis vector by its single coordinate and collapse the finite sum to `i`.
  rw [weightedSimpleBasisPairing, Module.Basis.constr_apply, b.repr_self i]
  rw [Finsupp.sum_eq_single i]
  · simp [mul_comm]
  · intro j _hj hji
    simp [Finsupp.single_eq_of_ne hji]
  · intro hi
    simp

end

end Representation
