import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.Prod

open CategoryTheory

-- Semantic recall: `ChainComplex.of` with companions `ChainComplex.of_x` and `ChainComplex.of_d`
-- is the canonical mathlib owner for explicit `ℕ`-indexed chain complexes.

/-- The graded `ℤ`-modules underlying `intervalChainComplex`. -/
private def intervalChainComplexObj : ℕ → ModuleCat ℤ
  | 0 => ModuleCat.of ℤ (ℤ × ℤ)
  | 1 => ModuleCat.of ℤ ℤ
  | _ + 2 => ModuleCat.of ℤ (Fin 0 → ℤ)

/-- The boundary maps used to define `intervalChainComplex`. -/
private def intervalChainComplexBoundary (n : ℕ) :
    intervalChainComplexObj (n + 1) ⟶ intervalChainComplexObj n :=
  match n with
  | 0 => ModuleCat.ofHom ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).prod (-LinearMap.id))
  | _ + 1 => 0

/-- The boundary maps for `intervalChainComplex` square to zero. -/
private theorem intervalChainComplexBoundary_sq (n : ℕ) :
    intervalChainComplexBoundary (n + 1) ≫ intervalChainComplexBoundary n = 0 := by
  cases n <;> simp [intervalChainComplexBoundary]

/-- Definition 12.3.3: the interval chain complex `I` has generators `[0]`, `[1]` in degree `0`
and `[I]` in degree `1`, with boundary `d[I] = [0] - [1]`. -/
def intervalChainComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of intervalChainComplexObj intervalChainComplexBoundary
    intervalChainComplexBoundary_sq

/-- The degree-0 generator `[0]` of `intervalChainComplex`. -/
def intervalChainComplexPointZero : intervalChainComplex.X 0 := ((1, 0) : ℤ × ℤ)

/-- The degree-0 generator `[1]` of `intervalChainComplex`. -/
def intervalChainComplexPointOne : intervalChainComplex.X 0 := ((0, 1) : ℤ × ℤ)

/-- The degree-1 generator `[I]` of `intervalChainComplex`. -/
def intervalChainComplexEdge : intervalChainComplex.X 1 := (1 : ℤ)

/-- The unique nonzero differential of `intervalChainComplex` is `n ↦ (n, -n)` in degrees
`1 → 0`. -/
theorem intervalChainComplex_d_one_zero :
    intervalChainComplex.d 1 0 =
      ModuleCat.ofHom ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).prod (-LinearMap.id)) := by
  simpa [intervalChainComplex] using
    (ChainComplex.of_d intervalChainComplexObj intervalChainComplexBoundary
      intervalChainComplexBoundary_sq 0)

/-- All differentials of `intervalChainComplex` in degrees `n + 2 → n + 1` vanish. -/
theorem intervalChainComplex_d_succ_succ (n : ℕ) :
    intervalChainComplex.d (n + 2) (n + 1) = 0 := by
  have hd :
      intervalChainComplex.d (n + 2) (n + 1) = intervalChainComplexBoundary (n + 1) := by
    simpa only [intervalChainComplex] using
      (ChainComplex.of_d intervalChainComplexObj intervalChainComplexBoundary
        intervalChainComplexBoundary_sq (n + 1))
  rw [hd]
  cases n <;> rfl

/-- The boundary of the degree-1 generator `[I]` is `[0] - [1]`. -/
theorem intervalChainComplex_d_edge :
    intervalChainComplex.d 1 0 intervalChainComplexEdge =
      intervalChainComplexPointZero - intervalChainComplexPointOne := by
  change ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).prod (-LinearMap.id)) 1 =
      ((1, 0) : ℤ × ℤ) - ((0, 1) : ℤ × ℤ)
  simp
