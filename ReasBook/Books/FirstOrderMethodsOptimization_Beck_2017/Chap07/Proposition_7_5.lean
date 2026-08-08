import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_15

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Matrix Matrix.Norms.Frobenius

noncomputable section

section

variable {m n : ℕ}

local notation "𝕄" => Matrix (Fin m) (Fin n) ℝ

/-- The ambient real matrix space is equipped with its Frobenius norm. -/
local instance prop75FrobeniusNormedAddCommGroup : NormedAddCommGroup 𝕄 :=
  Matrix.frobeniusNormedAddCommGroup

/- Proposition 7.5 is `source-facing`: the textbook defines
`T = {Y : ℝ^(m × n) | σ(Y) ∈ C}` and expresses the projection formula through the chapter's
projection owner `Proj[...]` together with the singular-value SVD data of `X`. The canonical matrix
reconstruction owner already present in the project is
`orthogonalRectangularDiagonalMap U V`. -/

/-- The rectangular diagonal matrix with diagonal entries `x` and off-diagonal entries `0`. -/
def rectangularDiagonal (x : Fin (min m n) → ℝ) : 𝕄 :=
  fun i j ↦
    if h : i.1 = j.1 then
      x ⟨i.1, Nat.lt_min.mpr ⟨i.2, h ▸ j.2⟩⟩
    else 0

-- Proof sketch: unfold `rectangularDiagonal`; its `(i,j)` entry is the corresponding coordinate
-- of `x` when the row and column indices agree, and `0` otherwise.
/-- Evaluating `rectangularDiagonal x` returns the corresponding diagonal entry of `x` on the
common diagonal and `0` away from it. -/
theorem rectangularDiagonal_apply (x : Fin (min m n) → ℝ) (i : Fin m) (j : Fin n) :
    rectangularDiagonal x i j =
      if h : i.1 = j.1 then
        x ⟨i.1, Nat.lt_min.mpr ⟨i.2, h ▸ j.2⟩⟩
      else 0 := sorry

/-- The orthogonal image of the rectangular diagonal matrix with diagonal `x`. -/
def orthogonalRectangularDiagonalMap
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ) :
    (Fin (min m n) → ℝ) → 𝕄 :=
  fun x ↦
    (U : Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonal x *
      ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ)

-- Proof sketch: unfold `orthogonalRectangularDiagonalMap`; evaluation at `x` is definitionally
-- the product `U * rectangularDiagonal x * Vᵀ`.
/-- Evaluating `orthogonalRectangularDiagonalMap U V` at `x` yields
`U * rectangularDiagonal x * Vᵀ`. -/
@[simp] theorem orthogonalRectangularDiagonalMap_apply
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : Fin (min m n) → ℝ) :
    orthogonalRectangularDiagonalMap U V x =
      (U : Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonal x *
        ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := sorry

/-- The rectangular spectral set associated with `C` consists of the real `m × n` matrices whose
ordered singular-value vector lies in `C`. -/
def rectangularSpectralSet (C : Set (Fin (min m n) → ℝ)) : Set 𝕄 :=
  {Y | singular_value_function Y ∈ C}

-- Proof sketch: unfold `rectangularSpectralSet`; membership is exactly the condition that the
-- ordered singular-value vector of `Y` lies in `C`.
/-- A matrix belongs to `rectangularSpectralSet C` exactly when its ordered singular-value vector
lies in `C`. -/
theorem mem_rectangularSpectralSet_iff {C : Set (Fin (min m n) → ℝ)} {Y : 𝕄} :
    Y ∈ rectangularSpectralSet C ↔ singular_value_function Y ∈ C := sorry

-- Proof sketch: let `T := rectangularSpectralSet C`. The projection-indicator identity rewrites
-- `Proj[T] X` and `Proj[C] (σ(X))` as proximal sets of the indicator functions `δ_T` and `δ_C`. Then
-- apply the rectangular spectral proximal formula to `δ_C ∘ singular_value_function`, using the
-- singular value decomposition `X = U * rectangularDiagonal (σ(X)) * Vᵀ`, and rewrite back in
-- terms of projection mappings.
/-- Proposition 7.5: if `C ⊆ ℝ^(min(m,n))` is nonempty, closed, and convex, then the projection
set of a real `m × n` matrix `X` onto the rectangular spectral set
`T = {Y | σ(Y) ∈ C}` is obtained by applying the same orthogonal singular-vector factors from a
singular value decomposition `X = U * rectangularDiagonal (σ(X)) * Vᵀ` to the projection set of
the singular-value vector `σ(X)` onto `C`. This is the chapter's set-valued rendering of the
textbook identity `P_T(X) = U dg(P_C(σ(X))) Vᵀ`. -/
theorem projection_mapping_rectangularSpectralSet_eq_image_projection_mapping_singular_values
    (C : Set (Fin (min m n) → ℝ)) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (X : 𝕄) (U : Matrix.orthogonalGroup (Fin m) ℝ)
    (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (hsvd : X = orthogonalRectangularDiagonalMap U V (singular_value_function X)) :
    Proj[rectangularSpectralSet C] X =
      orthogonalRectangularDiagonalMap U V '' Proj[C] (singular_value_function X) := sorry

end
