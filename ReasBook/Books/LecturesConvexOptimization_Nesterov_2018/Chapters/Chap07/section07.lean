import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_7 (from Chap07) -/
universe u v

noncomputable section

open Metric
open scoped WithTopConvexAnalysis

/- Definition 7.7 lies in the real continuous-dual / convex-analysis domain.

Sampled owner-style declarations:
- project `_root_.subdifferential` in `Chap03/Definition_3_1_5`
- project `_root_.mem_subdifferential_iff` in `Chap03/Definition_3_1_5`
- mathlib `InnerProductSpace.toDual`
- mathlib `normSeminorm`

Best owner abstraction:
- source-facing: the seminorm-based dual closed ball on `StrongDual ℝ E` and the resulting
  asphericity condition
- core/canonical: the chapter owner `_root_.subdifferential`
- bridge/view: the direct dual affine-support set transported through `InnerProductSpace.toDual`

Primitive data:
- the affine lower-support inequality for a continuous linear functional `g : StrongDual ℝ E`
- the seminorm `p : Seminorm ℝ E` determining the dual ball

Derived API:
- `dualClosedBall`
- `SatisfiesAsphericityCondition`
- the `InnerProductSpace.toDual` comparison theorem that rewrites the origin case into the chapter
  owner `∂`

Source/core/bridge triage:
- source-facing: `dualClosedBall` and `SatisfiesAsphericityCondition`
- core/canonical: `_root_.subdifferential`
- bridge/view: the `toDual` membership equivalence theorems

The seminorm-based `StrongDual` ball is the genuinely new source-facing object here, while the
subdifferential owner already exists upstream in the chapter. This file therefore defines
Definition 7.7 directly as the dual-ball sandwich around the affine-support set it needs, and then
proves that, under the stronger inner-product-space hypotheses needed for
`InnerProductSpace.toDual`, the origin case is exactly the chapter owner `∂`. -/

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/- The closed dual ball of radius `γ` for the seminorm `p`, written on continuous linear
functionals as the pointwise estimate `|g x| ≤ γ p x`. -/
def dualClosedBall (p : Seminorm ℝ E) (γ : ℝ) : Set (StrongDual ℝ E) :=
  {g | ∀ x : E, |g x| ≤ γ * p x}

/-- Membership in `dualClosedBall p γ` is exactly the defining dual support estimate. -/
@[simp] theorem mem_dualClosedBall_iff
    (p : Seminorm ℝ E) (γ : ℝ) (g : StrongDual ℝ E) :
    g ∈ dualClosedBall p γ ↔ ∀ x : E, |g x| ≤ γ * p x :=
  Iff.rfl

/-- For the ambient norm seminorm, `dualClosedBall` is exactly the operator-norm closed ball in
the continuous dual. -/
theorem dualClosedBall_normSeminorm_eq_closedBall
    (γ : ℝ) (hγ : 0 ≤ γ) :
    dualClosedBall (normSeminorm ℝ E) γ = closedBall (0 : StrongDual ℝ E) γ := by
  ext g
  rw [mem_dualClosedBall_iff]
  simp only [Metric.mem_closedBall, dist_eq_norm, coe_normSeminorm]
  have hg : ‖g‖ ≤ γ ↔ ∀ x : E, ‖g x‖ ≤ γ * ‖x‖ := ContinuousLinearMap.opNorm_le_iff hγ
  simpa using hg.symm

/-- Definition 7.7: positive scalars `γ₀ ≤ γ₁` satisfy the asphericity condition for `f` with
respect to the chosen seminorm `p` when the dual affine supports of `f` at the origin are
sandwiched between the corresponding dual closed balls of radii `γ₀` and `γ₁`. -/
def SatisfiesAsphericityCondition (f : E → ℝ) (p : Seminorm ℝ E) (γ₀ γ₁ : ℝ) : Prop :=
  0 < γ₀ ∧
    γ₀ ≤ γ₁ ∧
    dualClosedBall p γ₀ ⊆ {g : StrongDual ℝ E | ∀ y : E, f 0 + g y ≤ f y} ∧
    {g : StrongDual ℝ E | ∀ y : E, f 0 + g y ≤ f y} ⊆ dualClosedBall p γ₁

/-- In the ambient norm case `p = normSeminorm ℝ E`, Definition 7.7 recovers the operator-norm
closed-ball formulation around the same dual affine-support set. -/
theorem satisfiesAsphericityCondition_normSeminorm_iff
    (f : E → ℝ) (γ₀ γ₁ : ℝ) :
    SatisfiesAsphericityCondition f (normSeminorm ℝ E) γ₀ γ₁ ↔
      0 < γ₀ ∧
        γ₀ ≤ γ₁ ∧
        closedBall (0 : StrongDual ℝ E) γ₀ ⊆
          {g : StrongDual ℝ E | ∀ y : E, f 0 + g y ≤ f y} ∧
        {g : StrongDual ℝ E | ∀ y : E, f 0 + g y ≤ f y} ⊆
          closedBall (0 : StrongDual ℝ E) γ₁ := by
  constructor
  · rintro ⟨hγ₀, hγ₀γ₁, hlower, hupper⟩
    refine ⟨hγ₀, hγ₀γ₁, ?_, ?_⟩
    · simpa [dualClosedBall_normSeminorm_eq_closedBall, hγ₀.le] using hlower
    · have hγ₁ : 0 ≤ γ₁ := le_trans hγ₀.le hγ₀γ₁
      simpa [dualClosedBall_normSeminorm_eq_closedBall, hγ₁] using hupper
  · rintro ⟨hγ₀, hγ₀γ₁, hlower, hupper⟩
    refine ⟨hγ₀, hγ₀γ₁, ?_, ?_⟩
    · simpa [dualClosedBall_normSeminorm_eq_closedBall, hγ₀.le] using hlower
    · have hγ₁ : 0 ≤ γ₁ := le_trans hγ₀.le hγ₀γ₁
      simpa [dualClosedBall_normSeminorm_eq_closedBall, hγ₁] using hupper

section InnerProductBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Under the Riesz identification, the dual affine-support inequality is exactly the chapter
subgradient predicate. -/
theorem dualAffineSupport_iff_isSubgradientAt
    {f : E → ℝ} {x : E} {g : StrongDual ℝ E} :
    (∀ y : E, f x + (g y - g x) ≤ f y) ↔
      IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x ((InnerProductSpace.toDual ℝ E).symm g) := by
  constructor
  · intro hg
    refine ⟨by simp [withTopEffectiveDomain], ?_⟩
    intro y hy
    have hreal : f x + (g y - g x) ≤ f y := by
      simpa using hg y
    have htop : (((f x + (g y - g x) : ℝ) : WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      exact_mod_cast hreal
    simpa [map_sub, InnerProductSpace.toDual_symm_apply] using htop
  · intro hg y
    have htop := hg.2 (by simp [withTopEffectiveDomain] : y ∈ dom (fun z ↦ (f z : WithTop ℝ)))
    have htop' :
        (((f x + inner ℝ ((InnerProductSpace.toDual ℝ E).symm g) (y - x) : ℝ) :
            WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      simpa using htop
    have hreal : f x + inner ℝ ((InnerProductSpace.toDual ℝ E).symm g) (y - x) ≤ f y := by
      exact_mod_cast htop'
    simpa [map_sub, InnerProductSpace.toDual_symm_apply] using hreal

/-- Under the Riesz identification, the dual affine-support condition is exactly membership in the
chapter subdifferential `∂ (fun y ↦ (f y : WithTop ℝ))(x)`. -/
@[simp] theorem toDual_symm_mem_subdifferential_iff
    {f : E → ℝ} {x : E} {g : StrongDual ℝ E} :
    (InnerProductSpace.toDual ℝ E).symm g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))(x) ↔
      ∀ y : E, f x + (g y - g x) ≤ f y := by
  rw [mem_subdifferential_iff]
  exact dualAffineSupport_iff_isSubgradientAt.symm

/-- At the origin, the chapter subdifferential bridge is exactly the source-facing affine-support
inequality from Definition 7.7. -/
@[simp] theorem toDual_symm_mem_subdifferential_zero_iff
    {f : E → ℝ} {g : StrongDual ℝ E} :
    (InnerProductSpace.toDual ℝ E).symm g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))((0 : E)) ↔
      ∀ y : E, f 0 + g y ≤ f y := by
  rw [toDual_symm_mem_subdifferential_iff]
  constructor
  · intro hg y
    simpa using hg y
  · intro hg y
    simpa using hg y

/-- Under the stronger inner-product-space hypotheses needed for `InnerProductSpace.toDual`,
Definition 7.7 is exactly the chapter’s existing subdifferential ball-sandwich condition at the
origin. -/
theorem satisfiesAsphericityCondition_normSeminorm_iff_chapterSubdifferential
    (f : E → ℝ) (γ₀ γ₁ : ℝ) :
    SatisfiesAsphericityCondition f (normSeminorm ℝ E) γ₀ γ₁ ↔
      0 < γ₀ ∧
        γ₀ ≤ γ₁ ∧
        closedBall (0 : E) γ₀ ⊆ ∂ (fun y ↦ (f y : WithTop ℝ))((0 : E)) ∧
        ∂ (fun y ↦ (f y : WithTop ℝ))((0 : E)) ⊆ closedBall (0 : E) γ₁ := by
  constructor
  · rintro ⟨hγ₀, hγ₀γ₁, hlower, hupper⟩
    refine ⟨hγ₀, hγ₀γ₁, ?_, ?_⟩
    · intro x hx
      have hxDual : (InnerProductSpace.toDual ℝ E) x ∈ dualClosedBall (normSeminorm ℝ E) γ₀ := by
        rw [dualClosedBall_normSeminorm_eq_closedBall γ₀ hγ₀.le]
        simpa [Metric.mem_closedBall] using hx
      have hxSupport :
          (InnerProductSpace.toDual ℝ E) x ∈ {g : StrongDual ℝ E | ∀ y : E, f 0 + g y ≤ f y} :=
        hlower hxDual
      simpa using
        (toDual_symm_mem_subdifferential_zero_iff.mpr (by simpa using hxSupport) :
          (InnerProductSpace.toDual ℝ E).symm ((InnerProductSpace.toDual ℝ E) x) ∈
            ∂ (fun y ↦ (f y : WithTop ℝ))((0 : E)))
    · have hγ₁ : 0 ≤ γ₁ := le_trans hγ₀.le hγ₀γ₁
      intro x hx
      have hxSupport :
          (InnerProductSpace.toDual ℝ E) x ∈ {g : StrongDual ℝ E | ∀ y : E, f 0 + g y ≤ f y} := by
        exact toDual_symm_mem_subdifferential_zero_iff.mp (by simpa using hx)
      have hxDual : (InnerProductSpace.toDual ℝ E) x ∈ dualClosedBall (normSeminorm ℝ E) γ₁ :=
        hupper hxSupport
      rw [dualClosedBall_normSeminorm_eq_closedBall γ₁ hγ₁] at hxDual
      simpa [Metric.mem_closedBall] using hxDual
  · rintro ⟨hγ₀, hγ₀γ₁, hlower, hupper⟩
    refine ⟨hγ₀, hγ₀γ₁, ?_, ?_⟩
    · intro g hg
      rw [dualClosedBall_normSeminorm_eq_closedBall γ₀ hγ₀.le] at hg
      have hgSub :
          (InnerProductSpace.toDual ℝ E).symm g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))((0 : E)) :=
        hlower (by simpa [Metric.mem_closedBall] using hg)
      simpa using
        (toDual_symm_mem_subdifferential_zero_iff.mp hgSub :
          ∀ y : E, f 0 + g y ≤ f y)
    · have hγ₁ : 0 ≤ γ₁ := le_trans hγ₀.le hγ₀γ₁
      intro g hg
      have hgSub :
          (InnerProductSpace.toDual ℝ E).symm g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))((0 : E)) := by
        simpa using
          (toDual_symm_mem_subdifferential_zero_iff.mpr (by simpa using hg) :
            (InnerProductSpace.toDual ℝ E).symm g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))((0 : E)))
      have hgBall :
          (InnerProductSpace.toDual ℝ E).symm g ∈ closedBall (0 : E) γ₁ :=
        hupper hgSub
      rw [dualClosedBall_normSeminorm_eq_closedBall γ₁ hγ₁]
      simpa [Metric.mem_closedBall] using hgBall

end InnerProductBridge

/-! ### Lemma_7_7 (from Chap07) -/
noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Matₙ" => Matrix (Fin n) (Fin n) ℝ

/- Lemma 7.7 lies in Chapter 7's diagonal ellipsoid / dual-norm comparison domain.

Sampled owner-style declarations:
- `Matrix.IsDiag` and `Matrix.PosDef` in mathlib's diagonal / positive-definite matrix API, the
  canonical matrix-level owners for diagonal positive-definite matrices;
- `positiveDefMatrixNorm` and its dual notation `‖g‖[G,*]` in `Definition_7_23`, the core owner
  for the weighted dual norm;
- `matrixEllipsoid` with centered notation `W[r](G)` in `Definition_7_26`, the chapter owner for
  ellipsoids;
- `ellipsoidBoxGeneratedConvexSet`, `ellipsoidBoxInterpolationMatrix`, and
  `ellipsoidBoxLogVolumePotential` in `Definition_7_34`, the source-facing owners introduced for
  the present geometric construction.

Best owner abstraction:
- source-facing: `ellipsoidBoxAlphaStar` and the four theorem-level consequences of Lemma 7.7;
- core/canonical: `Matrix.PosDef`, `‖g‖[G,*]`, `W[r](G)`, and
  `ellipsoidBoxLogVolumePotential`;
- bridge/view: the explicit formula for `α*` and the scalar logarithmic comparison expression used
  in parts (3) and (4).

Primitive data:
- a matrix `D : Matₙ`;
- its positive-definiteness proof when the dual norm is used;
- a vector `g : Eₙ`;
- scalar parameters `α` and `γ`.

Derived API:
- the dual-norm square `‖g‖[⟨D, hDpos⟩,*] ^ 2` is derived from the upstream owner and is not kept
  as a separate public definition;
- the source-facing critical value `α*`;
- the theorem-level logarithmic comparison bounds used in parts (3) and (4).

Source/core/bridge triage:
- source-facing: `ellipsoidBoxAlphaStar`;
- core/canonical: `⟨D, hDpos⟩`, `W[r](G)`, `ellipsoidBoxLogVolumePotential`;
- bridge/view: the theorem-level inequalities below.

This refinement removes the duplicate public scalar wrapper for `‖g‖*_D²` and rewrites the target
file directly against the canonical dual-norm owner supplied upstream. -/

/-- The critical value `α* = (S - n) / ((2 S - n) S)` used in the sign-invariant rounding step,
where `S = ‖g‖[⟨D, hDpos⟩,*]^2`. -/
def ellipsoidBoxAlphaStar
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) : ℝ :=
  (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ) - (n : ℝ)) /
    ((((2 : ℝ) * (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ))) - (n : ℝ)) *
      (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ)))

-- Proof sketch: unfold `ellipsoidBoxAlphaStar`.
/-- Expanding `ellipsoidBoxAlphaStar d g` gives the closed formula
`(S - n) / ((2 S - n) S)` with `S = ‖g‖[⟨D, hDpos⟩,*]^2`. -/
theorem ellipsoidBoxAlphaStar_eq
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) :
    ellipsoidBoxAlphaStar D hDpos g =
      (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ) - (n : ℝ)) /
        ((((2 : ℝ) * (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ))) - (n : ℝ)) *
          (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ))) :=
  rfl

-- Proof sketch: write `S = ‖g‖[d.toPositiveDefMatrix,*]^2`. The hypothesis `S > n` gives
-- positivity of the numerator and denominator in the defining formula for `α*`; if `n = 0`, then
-- `α* = 1 / (2 S)`, while if `0 < n`, `ellipsoidBoxAlphaStar_mem_Ioc_inv_dim` yields
-- `0 < α* ≤ 1 / n ≤ 1`. In either case `α* ∈ [0, 1)`.
/-- Under `S > n`, the canonical value `α*` lies in the half-open unit interval `[0, 1)`. -/
theorem ellipsoidBoxAlphaStar_mem_halfOpenUnitInterval
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ)
    (hS : (n : ℝ) < ‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ)) :
    ellipsoidBoxAlphaStar D hDpos g ∈ Set.Ico (0 : ℝ) 1 := sorry

-- Proof sketch: compare the Minkowski functional of the centered ellipsoid with shape matrix
-- `(1 - α) D + α D²(g)` to the support function of `Conv(W₁(D) ∪ B(|g|))`, using the coordinatewise
-- bound `(∑ i (g i * |x i|)^2) ≤ (∑ i g i * |x i|)^2`.
/-- Lemma 7.7 (1): for every `α ∈ [0, 1]`, the unit ellipsoid with interpolation matrix
`G(α) = (1 - α) D + α D²(g)` is contained in `C = Conv(W₁(D) ∪ B(|g|))`. -/
theorem centeredMatrixEllipsoid_closedInterpolation_subset_ellipsoidBoxGeneratedConvexSet
    (D : Matₙ) (g : Eₙ) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    W[1]((ellipsoidBoxInterpolationMatrix D g α)) ⊆
      ellipsoidBoxGeneratedConvexSet D g := sorry

-- Proof sketch: write `S = ‖g‖[d.toPositiveDefMatrix,*]^2`; the hypothesis `S > n` gives
-- positivity of the numerator, and the algebraic inequality
-- `ellipsoidBoxAlphaStar d g ≤ 1 / n` reduces to `0 ≤ 2 S^2 - n S + n^2`.
/-- Lemma 7.7 (2): if `S = ‖g‖*_D² > n`, then the critical value
`α* = (S - n) / ((2 S - n) S)` lies in the interval `(0, 1 / n]`. -/
theorem ellipsoidBoxAlphaStar_mem_Ioc_inv_dim
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) (hn : 0 < n)
    (hS : (n : ℝ) < ‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ)) :
    ellipsoidBoxAlphaStar D hDpos g ∈ Set.Ioc (0 : ℝ) (1 / (n : ℝ)) := sorry

-- Proof sketch: combine the self-concordant upper estimate for `V(α)` with the choice
-- `α = ellipsoidBoxAlphaStar d g`, rewrite the resulting scalar bound in terms of
-- `S = ‖g‖[d.toPositiveDefMatrix,*]^2`, and then use the interval hypothesis
-- `1 < γ ≤ ‖g‖[d.toPositiveDefMatrix,*] / √n`. Its upper bound already forces the comparison
-- regime `n < S`, so no separate nontriviality or `S > n` hypothesis is needed in the public
-- statement. This yields the comparison with
-- `log (1 + (γ² - 1) / γ²) - (γ² - 1) / γ²`.
/-- Lemma 7.7 (3): if `1 < γ ≤ ‖g‖*_D / √n`, then the logarithmic potential at `α*` is bounded
above by the scalar
comparison term `log (1 + (γ² - 1) / γ²) - (γ² - 1) / γ²`. -/
theorem ellipsoidBoxLogVolumePotential_alphaStar_le_gammaComparison
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) (γ : ℝ)
    (hγ :
      γ ∈
        Set.Ioc
          (1 : ℝ)
          (‖g‖[⟨D, hDpos⟩,*] / Real.sqrt (n : ℝ))) :
    ellipsoidBoxLogVolumePotential D g (ellipsoidBoxAlphaStar D hDpos g) ≤
      Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)) -
        (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) := sorry

-- Proof sketch: set `u = (γ² - 1) / γ²`; the assumption `γ > 1` gives `u > 0`, and the standard
-- inequality `log (1 + u) < u` yields the strict negativity.
/-- Lemma 7.7 (4): for every `γ > 1`, the comparison term
`log (1 + (γ² - 1) / γ²) - (γ² - 1) / γ²` is strictly negative. -/
theorem ellipsoidBoxGammaComparison_neg
    (γ : ℝ) (hγ : 1 < γ) :
    Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)) -
        (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) < 0 := sorry

end

/-! ### Proposition_7_7 (from Chap07) -/
open scoped BigOperators Matrix
open scoped WeightedGramMatrix

noncomputable section

variable {ι : Type} [Fintype ι]

section PsiStar

/-- The feasible strict-simplex weights for `ψ*` are exactly those whose weighted Gram matrix is
invertible, so the inverse-defined objective is evaluated only on its intended domain. -/
def psiStarFeasibleSet {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) :
    Set (StdSimplex.Strict ℝ ι) :=
  {t | IsUnit (B[a](t.1.weights))}

/-- The source-facing objective `⟪B(t)⁻¹ f, f⟫` for `ψ*`, viewed as a function on the feasible
strict-simplex subtype. -/
def psiStarObjective {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) :
    psiStarFeasibleSet a → ℝ :=
  fun ⟨t, _⟩ ↦ dotProduct ((B[a](t.1.weights))⁻¹ *ᵥ f) f

/-- The constrained minimization problem defining `ψ*` on the strict simplex of weights. -/
def psiStarProblem {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) :
    SetConstrainedMinimizationProblem (StdSimplex.Strict ℝ ι) where
  feasibleSet := psiStarFeasibleSet a
  objective :=
    let _ : DecidablePred (· ∈ psiStarFeasibleSet a) := Classical.decPred (· ∈ psiStarFeasibleSet a)
    fun t ↦ if ht : t ∈ psiStarFeasibleSet a then psiStarObjective a f ⟨t, ht⟩ else 0

/-- On a feasible strict-simplex point, the constrained-problem objective recovers the source-facing
`ψ*` objective. -/
@[simp] theorem psiStarProblem_apply_of_mem_feasibleSet {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (t : StdSimplex.Strict ℝ ι) (ht : t ∈ psiStarFeasibleSet a) :
    psiStarProblem a f t = psiStarObjective a f ⟨t, ht⟩ := by
  classical
  simp [psiStarProblem, ht]

/-- The value `ψ*`, recorded as the canonical constrained optimal value on strict simplex
combinations. Using `EReal` keeps the infimum faithful even when the displayed real minimum is not
attained. -/
def psiStar {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) : EReal :=
  (psiStarProblem a f).optimalValue

end PsiStar

section MaxAbsoluteInner

variable [Nonempty ι]

/-- The unconstrained minimization problem whose negated optimal value is the quadratic max
formulation `maxₓ [2⟪f, x⟫ - maxᵢ ⟪aᵢ, x⟫²]`. -/
def maxQuadraticProblem {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) :
    SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n)) where
  feasibleSet := Set.univ
  objective := fun x ↦
    -(2 * dotProduct f x -
      (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2)

/-- The quadratic max value, defined through the constrained-optimization owner so that
unbounded-above cases are represented faithfully in `EReal`. -/
def maxQuadraticValue {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) : EReal :=
  -(maxQuadraticProblem a f).optimalValue

/-- The feasible set for the ratio formulation consists of points where the denominator
`maxᵢ ⟪aᵢ, x⟫²` is strictly positive. -/
def maxRatioFeasibleSet {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | 0 < (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2}

/-- The constrained minimization problem whose negated optimal value is the ratio max formulation.
The feasible set explicitly excludes the non-mathematical totalization of division by zero. -/
def maxRatioProblem {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) :
    SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n)) where
  feasibleSet := maxRatioFeasibleSet a
  objective := fun x ↦
    -((dotProduct f x) ^ 2 /
      (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2)

/-- The ratio max value, defined on the faithful feasible set `0 < maxᵢ ⟪aᵢ, x⟫²`. -/
def maxRatioValue {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) : EReal :=
  -(maxRatioProblem a f).optimalValue

section SupportAbsMin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The constrained minimization problem defining
`f* = min {maxᵢ |⟪aᵢ, x⟫| | ⟪f, x⟫ = 1}` on a real inner-product space. Specializing `E` to
`EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` presentation. -/
def supportAbsMinProblem (a : ι → E) (f : E) :
    SetConstrainedMinimizationProblem E where
  feasibleSet := hyperplane f 1
  objective := maxTypeObjective (fun i x ↦ |inner ℝ (a i) x|)

/-- The constrained support minimum `f*`, recorded as the canonical optimal value of the affine
slice problem. Using `EReal` keeps empty or non-attained cases faithful. -/
def supportAbsMin (a : ι → E) (f : E) : EReal :=
  (supportAbsMinProblem a f).optimalValue

/-- The objective of the constrained support-minimum problem is the finite max
`x ↦ maxᵢ |⟪aᵢ, x⟫|`. -/
@[simp] theorem supportAbsMinProblem_apply (a : ι → E) (f x : E) :
    supportAbsMinProblem a f x =
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  rfl

/-- The feasible set of the constrained support-minimum problem is the affine hyperplane
`hyperplane f 1`. -/
@[simp] theorem supportAbsMinProblem_feasibleSet (a : ι → E) (f : E) :
    (supportAbsMinProblem a f).feasibleSet = hyperplane f 1 :=
  rfl

/-- Membership in the feasible set of the constrained support-minimum problem is exactly the
normalization constraint `⟪f, x⟫ = 1`. -/
@[simp] theorem mem_supportAbsMinProblem_feasibleSet_iff (a : ι → E) {f x : E} :
    x ∈ (supportAbsMinProblem a f).feasibleSet ↔ inner ℝ f x = 1 := by
  rfl

end SupportAbsMin

end MaxAbsoluteInner

section PsiStarTheorems

variable [Nonempty ι]

-- Proof sketch: for each interior simplex point `t`, identify `⟪B(t)⁻¹ f, f⟫` with the
-- optimum of the quadratic form `2⟪f, x⟫ - ⟪B(t)x, x⟫`, compare `⟪B(t)x, x⟫` with
-- `maxᵢ ⟪aᵢ, x⟫²`, and then optimize over `t` and `x`; the ratio identity follows by rescaling
-- along each nonzero ray.
/-- Proposition 7.7: if every interior simplex combination `B(t)` is invertible, then `ψ*`
coincides with both the quadratic max formulation and the ratio max formulation, provided the
index family is nonempty and the ambient space has positive dimension. -/
theorem psiStar_eq_max_formulations
    (n : ℕ) (hn : 0 < n) (a : ι → EuclideanSpace ℝ (Fin (2 * n)))
    (f : EuclideanSpace ℝ (Fin (2 * n)))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights))) :
    psiStar a f = maxQuadraticValue a f ∧ maxQuadraticValue a f = maxRatioValue a f :=
  sorry

-- Proof sketch: normalize vectors by the constraint `⟪f, x⟫ = 1` and rewrite the ratio
-- formulation in terms of the minimum of `maxᵢ |⟪aᵢ, x⟫|`.
/-- Under the same nondegeneracy hypotheses as Proposition 7.7, the constrained support minimum
`f*` satisfies the identity `ψ* = (f*)⁻²`. -/
theorem psiStar_eq_supportAbsMin_inv_sq
    (n : ℕ) (hn : 0 < n) (a : ι → EuclideanSpace ℝ (Fin (2 * n)))
    (f : EuclideanSpace ℝ (Fin (2 * n)))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights))) :
    psiStar a f = (supportAbsMin a f)⁻¹ ^ 2 :=
  sorry

end PsiStarTheorems

/-! ### Theorem_7_7 (from Chap07) -/
noncomputable section

open Matrix
open scoped EllipsoidNotation

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Theorem 7.7 lies in Chapter 7's translated ellipsoid-rounding / determinant-growth domain.

Sampled owner-style declarations:
- `GeneralConvexRoundingAlgorithm.radius` and
  `GeneralConvexRoundingAlgorithm.oneSidedRoundingSigma` in `Algorithm_7_7`, the owner-level run
  API for Algorithm 7.7;
- `matrixEllipsoid` and the notation `W[r](v, G)` in `Definition_7_26`, the source-facing owner of
  translated ellipsoids;
- `_root_.oneSidedRoundingSigma` in `Lemma_7_5`, the chapter owner of the per-step scalar
  quantity `σ = (r - n) / (n + 1)`;
- `IsBetaRounding` in `Definition_7_27`, the chapter owner for the initial translated inner/outer
  ellipsoid containment data;
- `CentralSymmetricRoundingMethod.stoppingIndex_le` in `Theorem_7_6`, the nearby owner-style
  iteration bound organized as initial rounding data plus continuing-step hypotheses.

Best owner abstraction:
- source-facing: the iteration bound for a run of Algorithm 7.7 up to a terminal iterate `T`;
- core/canonical: `GeneralConvexRoundingAlgorithm` for the run data and `IsBetaRounding` for the
  initial translated ellipsoid containment;
- bridge/view: the terminal unit-ellipsoid containment and the theorem-level logarithmic
  determinant-growth inequalities.

Primitive data:
- the algorithm run;
- the initial outer radius `R`;
- the total number of performed updates `T`.

Derived API:
- the center sequence `vₖ = algorithm k` and the shape sequence `Gₖ = algorithm.shape k`;
- the initial translated rounding datum, packaged canonically by `IsBetaRounding`;
- the canonical per-step scalar `σₖ = algorithm.oneSidedRoundingSigma k`, derived from the current
  shape and maximizer displacement through the Chapter 7 owner `_root_.oneSidedRoundingSigma`;
- the initial and terminal positive-definiteness, derived from `algorithm.initial_shape_posDef`
  and `algorithm.shape_posDef` rather than stored as extra theorem inputs;
- the per-step logarithmic determinant increment estimate.

Source/core/bridge triage:
- source-facing: the theorem below;
- core/canonical: `GeneralConvexRoundingAlgorithm`, `IsBetaRounding`;
- bridge/view: the terminal comparison data and the stepwise logarithmic determinant inequalities.

The previous statement still left the source-defined per-step scalar `σₖ` as a primitive theorem
parameter. This refinement moves the theorem back to the owner layer of
`GeneralConvexRoundingAlgorithm`, reuses `IsBetaRounding` for the initial containment data, and
states both the continuation lower bound and the determinant-growth estimate directly in terms of
the canonical owner-side step quantity `algorithm.oneSidedRoundingSigma k`.
-/

-- Proof sketch: sum the lower bound
-- `2 σₖ² / ((1 + σₖ) (2 + σₖ))` over all continuing iterations, with
-- `σₖ = algorithm.oneSidedRoundingSigma k`, use
-- `σₖ ≥ (n / (n + 1)) (γ - 1)` to replace each increment by the uniform constant
-- `4 (γ - 1)² / ((1 + 2γ) (2 + γ))`, and compare the resulting lower bound for
-- `log det G_T - log det G₀` with the upper bound coming from the initial translated rounding
-- `W₁(v₀,G₀) ⊆ C ⊆ W_R(v₀,G₀)`. The lower bound `1 ≤ R` is recovered internally from
-- `algorithm.initial_shape_posDef`, `hInitial`, and `n ≥ 1`, while the terminal inner
-- containment is supplied in the source-facing form `W₁(v_T,G_T) ⊆ C`.

namespace GeneralConvexRoundingAlgorithm

section IterationBounds

variable {C : Set E} {gamma R : ℝ} {v0 : E} {G0 : Mat}

/-- Theorem 7.7: if `n ≥ 1`, an Algorithm 7.7 run starts from an `R`-rounding
`W₁(v₀,G₀) ⊆ C ⊆ W_R(v₀,G₀)`, its terminal iterate satisfies `W₁(v_T,G_T) ⊆ C`, the
canonical per-step quantities `σₖ = algorithm.oneSidedRoundingSigma k` satisfy
`σₖ ≥ (n / (n + 1)) (γ - 1)` for `k < T`, and the logarithmic determinant gains satisfy
`log det Gₖ₊₁ - log det Gₖ ≥ 2 σₖ² / ((1 + σₖ) (2 + σₖ))` for `k < T`, then
`T ≤ ((1 + 2γ) (2 + γ) / (2 (γ - 1)²)) n log R`. -/
theorem iterations_le
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0)
    (hn : 1 ≤ n)
    {T : ℕ}
    (hInitial : IsBetaRounding C R G0 v0)
    (hFinal : W[1]((algorithm.center T), (algorithm.shape T)) ⊆ C)
    (hsigma :
      ∀ k : ℕ, k < T →
        ((n : ℝ) / (n + 1 : ℝ)) * (gamma - 1) ≤ algorithm.oneSidedRoundingSigma k)
    (hlogDet :
      ∀ k : ℕ, k < T →
        Real.log (Matrix.det (algorithm.shape (k + 1))) ≥
          Real.log (Matrix.det (algorithm.shape k)) +
            (2 * (algorithm.oneSidedRoundingSigma k) ^ (2 : ℕ)) /
              ((1 + algorithm.oneSidedRoundingSigma k) *
                (2 + algorithm.oneSidedRoundingSigma k))) :
    (T : ℝ) ≤
      ((1 + 2 * gamma) * (2 + gamma)) / (2 * (gamma - 1) ^ (2 : ℕ)) *
        (n : ℝ) * Real.log R := sorry

end IterationBounds

end GeneralConvexRoundingAlgorithm

end
