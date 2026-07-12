import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_36

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SoftThreshold

noncomputable section

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "l1NormFn" => (fun y : E ↦ ‖y‖₁)
local notation "l1Epigraph" => realEpigraph (fun y : E ↦ (l1NormFn y : EReal))


/-- The Euclidean product space used by the textbook epigraph projection formula. This avoids
the default product type `E × ℝ`, whose norm is not the Euclidean product norm. -/
local notation "EP" => EuclideanSpace ℝ (Option ι)

/-- The Euclidean product point `(x, s)` represented in `EuclideanSpace ℝ (Option ι)`. -/
def l1EuclideanProductPoint (x : E) (s : ℝ) : EP :=
  fun j ↦ Option.elim j s x

/-- Base coordinates of a Euclidean product point. -/
def l1EuclideanProductBase (p : EP) : E :=
  fun i ↦ p (some i)

/-- Height coordinate of a Euclidean product point. -/
def l1EuclideanProductHeight (p : EP) : ℝ :=
  p none

/-- The epigraph of the Euclidean `ℓ¹` norm inside the Euclidean product model. -/
def l1EuclideanEpigraph : Set EP :=
  {p | ‖l1EuclideanProductBase p‖₁ ≤ l1EuclideanProductHeight p}

/- Example 6.38 is `bridge/view` in the Chapter 6 epigraph-projection domain. Domain sampling
uses the project owners `realEpigraph`, the set-valued projection map `P[...]`, the generic
epigraph-projection theorem from Theorem 6.36, and the coordinatewise soft-thresholding formula
from Example 6.8. The residual owner is therefore already fixed upstream as
`epigraph_projection_residual`; this file should only expose its textbook `ℓ¹` specialization and
the resulting singleton projection formula, not a parallel local root-function owner. Primitive
data: the real-valued owner `l1NormFn`. Derived API: its epigraph view `l1Epigraph` and the
specialized residual/projection formulas. -/

-- Proof sketch: unfold `realEpigraph`; membership is definitionally the inequality
-- `‖y‖₁ ≤ t` in Euclidean coordinates.
/-- A pair `(y, t)` belongs to the real epigraph of the Euclidean `ℓ¹` norm exactly when
`‖y‖₁ ≤ t`, specializing to the textbook `ℝ^n` model when `ι = Fin n`. -/
@[simp] theorem mem_realEpigraph_euclidean_l1_iff (y : E) (t : ℝ) :
    (y, t) ∈ l1Epigraph ↔ ‖y‖₁ ≤ t := by
  simp [realEpigraph]

/-- Helper for Example 6.38: the Euclidean `ℓ¹` norm is convex on the whole finite-dimensional
space. -/
lemma convexOn_univ_euclidean_l1_norm :
    ConvexOn ℝ Set.univ l1NormFn := by
  let l1Map : E →ₗ[ℝ] WithLp (1 : ENNReal) (ι → ℝ) :=
    ((WithLp.linearEquiv (p := (1 : ENNReal)) (K := ℝ) (V := ι → ℝ)).symm.toLinearMap).comp
      ((WithLp.linearEquiv (p := (2 : ENNReal)) (K := ℝ) (V := ι → ℝ)).toLinearMap)
  -- Transport convexity of the ambient `ℓ¹` norm through the linear `WithLp` identification.
  have hconv : ConvexOn ℝ Set.univ (fun y : E ↦ ‖l1Map y‖) := by
    simpa using convexOn_univ_norm.comp_linearMap l1Map
  simpa [l1Map, EuclideanSpace.l1Norm] using hconv

/-- On the nonnegative branch relevant for Example 6.38, the chapter owner
`epigraph_projection_residual` specializes to the textbook scalar residual
`φ(λ) = ‖T_[λ] x‖₁ - λ - s`. -/
theorem epigraph_projection_residual_euclidean_l1_eq
    (x : E) (s lam : ℝ) (hlam : 0 ≤ lam) :
    epigraph_projection_residual l1NormFn x s lam =
      ((‖T_[lam] x‖₁ - lam - s : ℝ) : EReal) := by
  -- Example 6.8 identifies the scaled proximal set with the soft-thresholded singleton.
  have hprox : prox[fun y : E ↦ (lam : EReal) * (l1NormFn y : EReal)] x = {T_[lam] x} := by
    change prox[fun y : E ↦ ((lam * ‖y‖₁ : ℝ) : EReal)] x = {T_[lam] x}
    simpa using prox_euclidean_l1_eq_singleton_softThreshold hlam x
  -- Singleton collapse turns the abstract residual into the textbook scalar function.
  simpa using
    epigraph_projection_residual_eq_of_scaled_prox_eq_singleton
      l1NormFn x s lam (T_[lam] x) hprox

-- Proof sketch: for each coordinate `i`, the magnitude of the `i`-th coordinate of
-- `T_[λ] x` is `( |x i| - λ )⁺`, which is nonincreasing in `λ`. Summing these coordinates gives
-- a nonincreasing `ℓ¹` norm, and subtracting `λ + s` preserves antitonicity on `[0, ∞)`.
/-- The canonical epigraph residual for the Euclidean `ℓ¹` norm is nonincreasing on `[0, ∞)`.
Via `epigraph_projection_residual_euclidean_l1_eq`, this is exactly the textbook monotonicity of
`φ(λ) = ‖T_[λ] x‖₁ - λ - s`. -/
theorem epigraph_projection_residual_euclidean_l1_antitoneOn_nonneg
    (x : E) (s : ℝ) :
    AntitoneOn (epigraph_projection_residual l1NormFn x s) (Set.Ici 0) := by
  -- The generic convex epigraph residual theorem applies once `‖·‖₁` is known to be convex.
  simpa using
    epigraph_projection_residual_antitoneOn_nonneg
      l1NormFn convexOn_univ_euclidean_l1_norm x s

-- Proof sketch: if `‖x‖₁ ≤ s`, then `(x, s)` already lies in the real epigraph of the Euclidean
-- `ℓ¹` norm, so the projection is the singleton `{(x, s)}`. Otherwise the hypothesis supplies a
-- positive root of the canonical residual
-- `epigraph_projection_residual l1NormFn x s`; via
-- `epigraph_projection_residual_euclidean_l1_eq` this is the textbook equation
-- `φ(λ) = ‖T_[λ] x‖₁ - λ - s = 0`. Then Theorem 6.36 reduces the projection to the proximal
-- singleton of Example 6.8, yielding `(T_[λ] x, s + λ)`.
/-- Example 6.38: let
`C = {(y, t) | ‖y‖₁ ≤ t}` be represented in the Euclidean product space
`EuclideanSpace ℝ (Option ι)`, specializing to the textbook `ℝ^n × ℝ` with its Euclidean product
norm when `ι = Fin n`. Then the set-valued orthogonal projection onto `C` is `{(x, s)}` when
`‖x‖₁ ≤ s`; otherwise, if `λ` is a positive root of the canonical residual
`epigraph_projection_residual l1NormFn x s`, equivalently of the nonincreasing function
`φ(λ) = ‖T_[λ] x‖₁ - λ - s` by `epigraph_projection_residual_euclidean_l1_eq`, then the
projection is the singleton `{(T_[λ] x, s + λ)}` in the Euclidean product model. -/
theorem projection_mapping_euclidean_l1Epigraph_eq_singleton_piecewise
    (x : E) (s lam : ℝ)
    (hactive : s < ‖x‖₁ →
      0 < lam ∧ epigraph_projection_residual l1NormFn x s lam = 0) :
    P[l1EuclideanEpigraph] (l1EuclideanProductPoint x s) =
      {if hfeas : ‖x‖₁ ≤ s then
        l1EuclideanProductPoint x s
      else
        l1EuclideanProductPoint (T_[lam] x) (s + lam)} := by
  -- This is the source-facing `ℓ¹` specialization of Theorem 6.36 in the Euclidean product
  -- model. The previous `E × ℝ` formulation used the default product max norm and is false.
  sorry

end
