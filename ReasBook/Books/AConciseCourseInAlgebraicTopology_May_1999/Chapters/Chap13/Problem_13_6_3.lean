import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.Prod

open CategoryTheory

-- Semantic recall: `ChainComplex.of` with companions `ChainComplex.of_x` and
-- `ChainComplex.of_d` is the canonical mathlib owner for explicit `ℕ`-indexed cellular chain
-- complexes with prescribed differentials.

/-- The graded `ℤ`-modules underlying `torusCellularChainComplex`. -/
private def torusCellularChainComplexObj : ℕ → ModuleCat ℤ
  | 0 => ModuleCat.of ℤ ℤ
  | 1 => ModuleCat.of ℤ (ℤ × ℤ)
  | 2 => ModuleCat.of ℤ ℤ
  | _ + 3 => ModuleCat.of ℤ (Fin 0 → ℤ)

/-- The cellular boundary maps for the standard CW structure on the torus. -/
private def torusCellularChainComplexBoundary (n : ℕ) :
    torusCellularChainComplexObj (n + 1) ⟶ torusCellularChainComplexObj n :=
  match n with
  | 0 => 0
  | 1 => 0
  | _ + 2 => 0

/-- The torus cellular boundary maps square to zero. -/
private theorem torusCellularChainComplexBoundary_sq (n : ℕ) :
    torusCellularChainComplexBoundary (n + 1) ≫ torusCellularChainComplexBoundary n = 0 := by
  cases n <;> simp [torusCellularChainComplexBoundary]

/-- Problem 13.6.3 (1): for the standard CW structure on the torus `T` with one `0`-cell, two
`1`-cells, and one `2`-cell, the cellular chain complex has chain groups
`C₀(T) = ℤ`, `C₁(T) = ℤ × ℤ`, `C₂(T) = ℤ`, and both cellular differentials are zero. -/
abbrev torusCellularChainComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of torusCellularChainComplexObj
    torusCellularChainComplexBoundary
    torusCellularChainComplexBoundary_sq

/-- The degree-`n` chain group of `torusCellularChainComplex` is the standard cellular chain
group for the CW structure with one `0`-cell, two `1`-cells, and one `2`-cell. -/
@[simp] theorem torusCellularChainComplex_X (n : ℕ) :
    torusCellularChainComplex.X n =
      match n with
      | 0 => ModuleCat.of ℤ ℤ
      | 1 => ModuleCat.of ℤ (ℤ × ℤ)
      | 2 => ModuleCat.of ℤ ℤ
      | _ + 3 => ModuleCat.of ℤ (Fin 0 → ℤ) := by
  rw [ChainComplex.of_x]
  cases n <;> rfl

/-- The differential of `torusCellularChainComplex` in degree `n` is the prescribed cellular
boundary map for the standard torus CW structure. -/
@[simp] theorem torusCellularChainComplex_d (n : ℕ) :
    torusCellularChainComplex.d (n + 1) n =
      match n with
      | 0 => 0
      | 1 => 0
      | _ + 2 => 0 := by
  rw [ChainComplex.of_d]
  cases n <;> rfl

/-- The degree-`1` cellular differential for the standard torus CW structure is zero. -/
@[simp] theorem torusCellularChainComplex_d_one_zero :
    torusCellularChainComplex.d 1 0 = 0 := by
  simp

/-- The degree-`2` cellular differential for the standard torus CW structure is zero. -/
@[simp] theorem torusCellularChainComplex_d_two_one :
    torusCellularChainComplex.d 2 1 = 0 := by
  simp

/-- The graded `ℤ`-modules underlying `realProjectivePlaneCellularChainComplex`. -/
private def realProjectivePlaneCellularChainComplexObj : ℕ → ModuleCat ℤ
  | 0 => ModuleCat.of ℤ ℤ
  | 1 => ModuleCat.of ℤ ℤ
  | 2 => ModuleCat.of ℤ ℤ
  | _ + 3 => ModuleCat.of ℤ (Fin 0 → ℤ)

/-- The cellular boundary maps for the standard CW structure on `RP²`. -/
private def realProjectivePlaneCellularChainComplexBoundary (n : ℕ) :
    realProjectivePlaneCellularChainComplexObj (n + 1) ⟶
      realProjectivePlaneCellularChainComplexObj n :=
  match n with
  | 0 => 0
  | 1 => ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))
  | _ + 2 => 0

/-- The `RP²` cellular boundary maps square to zero. -/
private theorem realProjectivePlaneCellularChainComplexBoundary_sq (n : ℕ) :
    realProjectivePlaneCellularChainComplexBoundary (n + 1) ≫
      realProjectivePlaneCellularChainComplexBoundary n = 0 := by
  cases n <;> simp [realProjectivePlaneCellularChainComplexBoundary]

/-- Problem 13.6.3 (2): for the standard CW structure on `RP²` with one cell in each degree
`0`, `1`, and `2`, the cellular chain complex has chain groups `C₀(RP²) = ℤ`, `C₁(RP²) = ℤ`,
`C₂(RP²) = ℤ`, with `d₁ = 0` and `d₂ = 2 • LinearMap.id`. -/
abbrev realProjectivePlaneCellularChainComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of realProjectivePlaneCellularChainComplexObj
    realProjectivePlaneCellularChainComplexBoundary
    realProjectivePlaneCellularChainComplexBoundary_sq

/-- The degree-`n` chain group of `realProjectivePlaneCellularChainComplex` is the standard
cellular chain group for the CW structure on `RP²` with one cell in each of the degrees `0`,
`1`, and `2`. -/
@[simp] theorem realProjectivePlaneCellularChainComplex_X (n : ℕ) :
    realProjectivePlaneCellularChainComplex.X n =
      match n with
      | 0 => ModuleCat.of ℤ ℤ
      | 1 => ModuleCat.of ℤ ℤ
      | 2 => ModuleCat.of ℤ ℤ
      | _ + 3 => ModuleCat.of ℤ (Fin 0 → ℤ) := by
  rw [ChainComplex.of_x]
  cases n <;> rfl

/-- The differential of `realProjectivePlaneCellularChainComplex` in degree `n` is the prescribed
cellular boundary map for the standard CW structure on `RP²`. -/
@[simp] theorem realProjectivePlaneCellularChainComplex_d (n : ℕ) :
    realProjectivePlaneCellularChainComplex.d (n + 1) n =
      match n with
      | 0 => 0
      | 1 => ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))
      | _ + 2 => 0 := by
  rw [ChainComplex.of_d]
  cases n <;> rfl

/-- The degree-`1` cellular differential for the standard CW structure on `RP²` is zero. -/
@[simp] theorem realProjectivePlaneCellularChainComplex_d_one_zero :
    realProjectivePlaneCellularChainComplex.d 1 0 = 0 := by
  simp

/-- The degree-`2` cellular differential for the standard CW structure on `RP²` is multiplication
by `2`. -/
@[simp] theorem realProjectivePlaneCellularChainComplex_d_two_one :
    realProjectivePlaneCellularChainComplex.d 2 1 =
      ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) := by
  simp

/-- The graded `ℤ`-modules underlying `kleinBottleCellularChainComplex`. -/
private def kleinBottleCellularChainComplexObj : ℕ → ModuleCat ℤ
  | 0 => ModuleCat.of ℤ ℤ
  | 1 => ModuleCat.of ℤ (ℤ × ℤ)
  | 2 => ModuleCat.of ℤ ℤ
  | _ + 3 => ModuleCat.of ℤ (Fin 0 → ℤ)

/-- The cellular boundary maps for the standard CW structure on the Klein bottle. -/
private def kleinBottleCellularChainComplexBoundary (n : ℕ) :
    kleinBottleCellularChainComplexObj (n + 1) ⟶ kleinBottleCellularChainComplexObj n :=
  match n with
  | 0 => 0
  | 1 =>
      ModuleCat.ofHom
        ((0 : ℤ →ₗ[ℤ] ℤ).prod ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)))
  | _ + 2 => 0

/-- The Klein-bottle cellular boundary maps square to zero. -/
private theorem kleinBottleCellularChainComplexBoundary_sq (n : ℕ) :
    kleinBottleCellularChainComplexBoundary (n + 1) ≫
      kleinBottleCellularChainComplexBoundary n = 0 := by
  cases n <;> simp [kleinBottleCellularChainComplexBoundary]

/-- Problem 13.6.3 (3): for the standard CW structure on the Klein bottle with one `0`-cell, two
`1`-cells `a` and `b`, and one `2`-cell, the cellular chain complex has chain groups
`C₀(K) = ℤ`, `C₁(K) = ℤ × ℤ`, `C₂(K) = ℤ`, with `d₁ = 0` and `d₂` equal to the map
`n ↦ (0, 2 * n)` in the ordered basis `(a, b)` of `C₁(K)`. -/
abbrev kleinBottleCellularChainComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of kleinBottleCellularChainComplexObj
    kleinBottleCellularChainComplexBoundary
    kleinBottleCellularChainComplexBoundary_sq

/-- The degree-`n` chain group of `kleinBottleCellularChainComplex` is the standard cellular
chain group for the CW structure on the Klein bottle with one `0`-cell, two `1`-cells, and one
`2`-cell. -/
@[simp] theorem kleinBottleCellularChainComplex_X (n : ℕ) :
    kleinBottleCellularChainComplex.X n =
      match n with
      | 0 => ModuleCat.of ℤ ℤ
      | 1 => ModuleCat.of ℤ (ℤ × ℤ)
      | 2 => ModuleCat.of ℤ ℤ
      | _ + 3 => ModuleCat.of ℤ (Fin 0 → ℤ) := by
  rw [ChainComplex.of_x]
  cases n <;> rfl

/-- The differential of `kleinBottleCellularChainComplex` in degree `n` is the prescribed
cellular boundary map for the standard Klein-bottle CW structure. -/
@[simp] theorem kleinBottleCellularChainComplex_d (n : ℕ) :
    kleinBottleCellularChainComplex.d (n + 1) n =
      match n with
      | 0 => 0
      | 1 =>
          ModuleCat.ofHom
            ((0 : ℤ →ₗ[ℤ] ℤ).prod ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)))
      | _ + 2 => 0 := by
  rw [ChainComplex.of_d]
  cases n <;> rfl

/-- The degree-`1` cellular differential for the standard Klein-bottle CW structure is zero. -/
@[simp] theorem kleinBottleCellularChainComplex_d_one_zero :
    kleinBottleCellularChainComplex.d 1 0 = 0 := by
  simp

/-- The degree-`2` cellular differential for the standard Klein-bottle CW structure is
`n ↦ (0, 2 * n)` in the ordered basis `(a, b)` of `C₁(K)`. -/
@[simp] theorem kleinBottleCellularChainComplex_d_two_one :
    kleinBottleCellularChainComplex.d 2 1 =
      ModuleCat.ofHom
        ((0 : ℤ →ₗ[ℤ] ℤ).prod ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) := by
  simp
