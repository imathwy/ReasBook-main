import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Permutation

universe u

/-- The coordinate permutation induced by `σ` on the canonical Euclidean model
`EuclideanSpace ℝ (Fin N)`. -/
noncomputable abbrev permuteCoordVec {N : ℕ}
    (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm (((EuclideanSpace.equiv (Fin N) ℝ) x) ∘ σ.symm)

/-- `permuteCoordVec` is coordinatewise multiplication by `σ.permMatrix ℝ`. -/
theorem permuteCoordVec_eq_mulVec
    {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    (permuteCoordVec σ x : Fin N → ℝ) =
      Matrix.mulVec (σ.permMatrix ℝ)
        ((EuclideanSpace.equiv (Fin N) ℝ) x) := sorry

/-- A function on `EuclideanSpace ℝ (Fin N)` is symmetric when it is invariant under coordinate
permutations. -/
def CoordinatePermutationInvariant {N : ℕ} {α : Type u}
    (φ : EuclideanSpace ℝ (Fin N) → α) : Prop :=
  ∀ (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℝ (Fin N)),
    φ (permuteCoordVec σ x) = φ x

/-- Coordinate-permutation invariance can be applied to a chosen coordinate permutation. -/
theorem CoordinatePermutationInvariant.comp_perm_eq
    {N : ℕ} {α : Type u} {φ : EuclideanSpace ℝ (Fin N) → α}
    (hφ : CoordinatePermutationInvariant φ) (σ : Equiv.Perm (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) :
    φ (permuteCoordVec σ x) = φ x :=
  hφ σ x
