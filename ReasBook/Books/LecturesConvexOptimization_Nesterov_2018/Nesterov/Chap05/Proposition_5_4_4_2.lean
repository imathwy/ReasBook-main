import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Alg_5_4_4_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_4_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "SymmMat" => 𝕊^n

/-
Proposition 5.4.4.2 lies in the Chapter 5 semidefinite Newton-direction domain.

Sampled owner-style declarations:
* `semidefiniteNewtonDirectionSet` in `Definition_5_4_4_7`, the source-facing Newton-direction
  owner;
* `mem_semidefiniteNewtonDirectionSet_iff_frobenius_isMinOn` in `Definition_5_4_4_7`, the
  tangent-kernel/minimizer bridge for that owner;
* `IsSemidefiniteNewtonDirectionOutput` and `IsSemidefiniteNewtonMultiplier` in `Alg_5_4_4_1`,
  the chapter owners for a Newton-system multiplier solution and its reconstructed direction;
* `semidefiniteNewtonNormalMatrix`, `semidefiniteNewtonNormalRhs`, and
  `semidefiniteNewtonDirectionFromMultiplier` in `Alg_5_4_4_1`, the canonical normal-system data.

Best owner abstraction:
* source-facing: `semidefiniteNewtonDirectionSet A X U`;
* core/canonical: `IsSemidefiniteNewtonDirectionOutput X U A multiplier Δ`;
* bridge/view: the coordinate normal equations obtained by expanding `Matrix.mulVec`.

Primitive data:
* `A : Fin m → 𝕊^n`;
* `X : 𝕊^n₊₊`;
* `U : 𝕊^n`;
* `Δ : 𝕊^n`.

Derived API:
* tangent feasibility `∀ i, ⟪A i, Δ⟫_F = 0`;
* the owner-level Newton-system multiplier/output relation;
* the coordinate normal equations and recovered direction.

This refinement removes the duplicate local KKT/stationarity/primal-step wrappers and reuses the
existing Chapter 5 Newton-system owner from `Alg_5_4_4_1`, keeping coordinate equations only as a
thin companion expansion.
-/

/-- A Newton direction is tangent to the Frobenius constraint kernel. -/
theorem semidefiniteNewtonDirectionSet_feasible
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat}
    (hΔ : Δ ∈ semidefiniteNewtonDirectionSet A X U) :
    ∀ i : Fin m, ⟪A i, Δ⟫_F = 0 := by
  exact (mem_semidefiniteNewtonDirectionSet_iff_frobenius_isMinOn.mp hΔ).1

/-- Expanding `IsSemidefiniteNewtonDirectionOutput` through `Matrix.mulVec` gives the coordinate
normal equations together with the reconstructed Newton direction. -/
theorem isSemidefiniteNewtonDirectionOutput_iff_coordinate
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat} {multiplier : Fin m → ℝ} :
    IsSemidefiniteNewtonDirectionOutput X U A multiplier Δ ↔
      (∀ i : Fin m,
        ∑ j, semidefiniteNewtonNormalMatrix X A i j * multiplier j =
          semidefiniteNewtonNormalRhs X U A i) ∧
      Δ = semidefiniteNewtonDirectionFromMultiplier X U A multiplier := by
  rw [isSemidefiniteNewtonDirectionOutput_iff]
  constructor
  · rintro ⟨hmul, rfl⟩
    refine ⟨?_, rfl⟩
    intro i
    simpa [Matrix.mulVec] using congrArg (fun v : Fin m → ℝ ↦ v i) hmul
  · rintro ⟨hcoord, rfl⟩
    refine ⟨?_, rfl⟩
    ext i
    simpa [Matrix.mulVec] using hcoord i

-- Proof sketch: first-order optimality of the quadratic Newton model on the tangent kernel
-- yields exactly the Chapter 5 Newton normal system already packaged by
-- `IsSemidefiniteNewtonDirectionOutput`.
/-- Proposition 5.4.4.2: a Newton direction is an output of the Chapter 5 semidefinite Newton
system. -/
theorem semidefiniteNewtonDirectionSet_output
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat}
    (hΔ : Δ ∈ semidefiniteNewtonDirectionSet A X U) :
    ∃ multiplier : Fin m → ℝ,
      IsSemidefiniteNewtonDirectionOutput X U A multiplier Δ := by
  sorry

/-- Proposition 5.4.4.2 in coordinate form: a Newton direction admits multipliers solving the
normal equations, and `Δ` is the reconstructed direction attached to those multipliers. -/
theorem semidefiniteNewtonDirectionSet_normal_system
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat}
    (hΔ : Δ ∈ semidefiniteNewtonDirectionSet A X U) :
    ∃ multiplier : Fin m → ℝ,
      (∀ i : Fin m,
        ∑ j, semidefiniteNewtonNormalMatrix X A i j * multiplier j =
          semidefiniteNewtonNormalRhs X U A i) ∧
      Δ = semidefiniteNewtonDirectionFromMultiplier X U A multiplier := by
  rcases semidefiniteNewtonDirectionSet_output hΔ with ⟨multiplier, hOutput⟩
  exact ⟨multiplier, isSemidefiniteNewtonDirectionOutput_iff_coordinate.mp hOutput⟩

end
