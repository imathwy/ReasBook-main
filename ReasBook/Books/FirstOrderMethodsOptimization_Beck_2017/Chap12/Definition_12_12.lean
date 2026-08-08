import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix Matrix.Norms.Frobenius

noncomputable section

section

variable {m n : ℕ}

local notation "Mmn" => Matrix (Fin m) (Fin n) ℝ

/-
Definition 12.12 is `source-facing`: it fixes the matrix-space denoising objective
`x ↦ (1 / 2) ‖x - d‖_F^2 + λ TV(x)` on `ℝ^(m × n)`.

Domain sampling against the nearby project owners gives:
- `source-facing`: the matrix-space denoising objective with regularizer `TV`;
- `core/canonical`: `denoising_problem_objective` from Definition 12.10, specialized to the
  identity map on the matrix space;
- `bridge/view`: the matrix space `Mmn`, viewed through mathlib's scoped Frobenius norm
  instances from `Matrix.Norms.Frobenius`.

Primitive data here are only the matrix datum `d`, the source-facing regularizer `TV`, and the
positive regularization parameter `λ`, encoded canonically by the chapter's `PosReal` owner. The
objective itself should therefore be a thin specialization of the Chapter 12 denoising owner, not
a parallel local reconstruction of the same pointwise sum; the pointwise formula remains derived
API from `denoising_problem_objective_apply`. -/

/-- Definition 12.12: for a fixed two-dimensional total-variation functional `TV`, datum
`d ∈ ℝ^(m × n)`, and positive parameter `λ`, encoded by `lam : PosReal`, the two-dimensional
total-variation denoising objective is `x ↦ (1 / 2) ‖x - d‖_F^2 + λ TV(x)`, realized through the
Chapter 12 denoising owner with the identity map on the matrix space. -/
abbrev two_dimensional_total_variation_denoising_objective
    (TV : Mmn → ℝ) (d : Mmn) (lam : PosReal) : Mmn → EReal :=
  denoising_problem_objective d
    (fun x ↦ ↑((lam : ℝ) * TV x))
    id

end
