import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_34_1_1 (from Chap07) -/
noncomputable section

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.1 is the explicit Section 34 example obtained from the finite kernel
  `(u, v) ↦ u^v` on `(0, 1) × (0, 1)` after extending it by one of the two Chapter 33 simple
  extensions and then applying the Chapter 34 iterated closures.
- `core/canonical`: for this item file, the relevant owner data are the Definition 33.0.2
  ambient bridge surfaces `K₁[· | ·, ·]` and `K₂[· | ·, ·]`, together with the Chapter 34 owners
  `upperClosure` and `lowerClosure`.
- `bridge/view`: the explicit piecewise formulas are recorded here as concrete comparison
  bifunctions on `ℝ × ℝ`, while the upper-boundary-extension formulas are derived from the
  saddle-extension formulas through primitive closure-equality hypotheses.

Domain-style sampling used here:
- the canonical ambient bridge owners `K₁[· | ·, ·]` and `K₂[· | ·, ·]` from
  `Definition33_0_2`;
- the Chapter 34 iterated closures `upperClosure` and `lowerClosure` from `Defn_34_1`;
- mathlib's canonical real-power owner `Real.rpow`.

Scalar-layer note:
- This item remains at scalar `ℝ` for owner correctness, not proof convenience: the primitive
  kernel data are exactly `Real.rpow`, and the chapter reuses that canonical real-only owner
  directly rather than introducing a project-local scalar-generic replacement.

Primitive data vs derived API:
- primitive source data: the open interval `(0, 1)` and the finite kernel `(u, v) ↦ u^v`;
- primitive source-facing owners in this file: the canonical ambient bridge expressions
  `K₁[Real.rpow | Ioo 0 1, Ioo 0 1]` and `K₂[Real.rpow | Ioo 0 1, Ioo 0 1]`;
- derived API: hypothesis-parameterized consequences of primitive closure equalities together with
  the explicit iterated-closure formulas for `cl₁ (cl₂ K)` and `cl₂ (cl₁ K)`, including the
  origin discrepancy.

Layer target: `source-facing` for the finite kernel and the displayed closure formulas, with the
upper-boundary-extension formulas handled as `bridge/view` consequences of primitive closure
equalities.
-/

section

attribute [local instance] Classical.propDecidable

/- The open unit interval used by the canonical Chapter 33 extension owners in this file. -/
private def openUnitInterval : Set ℝ := Set.Ioo (0 : ℝ) 1

/- The closed unit interval used by the explicit closure formulas in Text 34.1.1. -/
private def closedUnitInterval : Set ℝ := Set.Icc (0 : ℝ) 1

/-- The explicit piecewise formula claimed in Text 34.1.1 for the upper closure
`K̅ = cl₁ (cl₂ K)`. -/
def openUnitIntervalPowUpperClosureFormula : ℝ → ℝ → WithBotTop ℝ :=
  fun u v ↦
    if u ∈ closedUnitInterval then
      if v ∈ closedUnitInterval then
        if u = 0 ∧ v = 0 then
          (1 : WithBotTop ℝ)
        else
          (Real.rpow u v : ℝ)
      else
        ⊤
    else if v ∈ closedUnitInterval then
      ⊥
    else
      ⊤

/-- The explicit piecewise formula claimed in Text 34.1.1 for the lower closure
`K̲ = cl₂ (cl₁ K)`. -/
def openUnitIntervalPowLowerClosureFormula : ℝ → ℝ → WithBotTop ℝ :=
  fun u v ↦
    if u ∈ closedUnitInterval then
      if v ∈ closedUnitInterval then
        if u = 0 ∧ v = 0 then
          (0 : WithBotTop ℝ)
        else
          (Real.rpow u v : ℝ)
      else
        ⊤
    else
      ⊥

section SaddleExtension

-- Proof sketch: specialize the upper-closure formula at `(u,v) = (0,0)`.
/-- At the origin, the upper iterated closure of the saddle extension takes the value `1`. -/
theorem upperClosure_saddleExtension_openUnitIntervalPowKernel_origin_eq_one :
    (K₁[Real.rpow | openUnitInterval, openUnitInterval])̅ =
        openUnitIntervalPowUpperClosureFormula →
      (K₁[Real.rpow | openUnitInterval, openUnitInterval])̅ 0 0 = 1 := by
  intro hUpperSaddle
  rw [hUpperSaddle]
  simp [openUnitIntervalPowUpperClosureFormula, closedUnitInterval]

-- Proof sketch: specialize the lower-closure formula at `(u,v) = (0,0)`.
/-- At the origin, the lower iterated closure of the saddle extension takes the value `0`. -/
theorem lowerClosure_saddleExtension_openUnitIntervalPowKernel_origin_eq_zero :
    (K₁[Real.rpow | openUnitInterval, openUnitInterval])̲ =
        openUnitIntervalPowLowerClosureFormula →
      (K₁[Real.rpow | openUnitInterval, openUnitInterval])̲ 0 0 = 0 := by
  intro hLowerSaddle
  rw [hLowerSaddle]
  simp [openUnitIntervalPowLowerClosureFormula, closedUnitInterval]

-- Proof sketch: compare the two origin-value theorems, which give `1` and `0` respectively.
/-- For the saddle extension, the two iterated closures are different; the discrepancy is
already visible at the origin `(0,0)`. -/
theorem upperClosure_ne_lowerClosure_saddleExtension_openUnitIntervalPowKernel :
    (K₁[Real.rpow | openUnitInterval, openUnitInterval])̅ =
        openUnitIntervalPowUpperClosureFormula →
      (K₁[Real.rpow | openUnitInterval, openUnitInterval])̲ =
        openUnitIntervalPowLowerClosureFormula →
      (K₁[Real.rpow | openUnitInterval, openUnitInterval])̅ ≠
        (K₁[Real.rpow | openUnitInterval, openUnitInterval])̲ := by
  intro hUpperSaddle hLowerSaddle hEq
  have hOrigin := congrArg (fun K ↦ K 0 0) hEq
  change
      (K₁[Real.rpow | openUnitInterval, openUnitInterval])̅ 0 0 =
        (K₁[Real.rpow | openUnitInterval, openUnitInterval])̲ 0 0 at hOrigin
  rw [upperClosure_saddleExtension_openUnitIntervalPowKernel_origin_eq_one hUpperSaddle,
    lowerClosure_saddleExtension_openUnitIntervalPowKernel_origin_eq_zero hLowerSaddle] at hOrigin
  change (((1 : ℝ) : WithBotTop ℝ) = (0 : WithBotTop ℝ)) at hOrigin
  have hne : (((1 : ℝ) : WithBotTop ℝ)) ≠ 0 := by simp
  exact hne hOrigin

end SaddleExtension

section UpperBoundaryExtension

/-- For the upper-boundary extension of `(u,v) ↦ u^v`, the upper iterated closure
`K̅ = cl₁ (cl₂ K)` is the explicit piecewise formula with value `1` at the origin. -/
theorem upperClosure_upperBoundaryExtension_openUnitIntervalPowKernel :
    cl₂ (K₂[Real.rpow | openUnitInterval, openUnitInterval]) =
        cl₂ (K₁[Real.rpow | openUnitInterval, openUnitInterval]) →
      (K₁[Real.rpow | openUnitInterval, openUnitInterval])̅ =
        openUnitIntervalPowUpperClosureFormula →
    (K₂[Real.rpow | openUnitInterval, openUnitInterval])̅ =
      openUnitIntervalPowUpperClosureFormula := by
  intro hcl₂ hUpperSaddle
  calc
    (K₂[Real.rpow | openUnitInterval, openUnitInterval])̅ =
        (K₁[Real.rpow | openUnitInterval, openUnitInterval])̅ := by
          simp [Bifunction.upperClosure, hcl₂]
    _ = openUnitIntervalPowUpperClosureFormula := hUpperSaddle

/-- For the upper-boundary extension of `(u,v) ↦ u^v`, the lower iterated closure
`K̲ = cl₂ (cl₁ K)` is the explicit piecewise formula with value `0` at the origin. -/
theorem
    lowerClosure_upperBoundaryExtension_openUnitIntervalPowKernel :
    cl₁ (K₂[Real.rpow | openUnitInterval, openUnitInterval]) =
        cl₁ (K₁[Real.rpow | openUnitInterval, openUnitInterval]) →
      (K₁[Real.rpow | openUnitInterval, openUnitInterval])̲ =
        openUnitIntervalPowLowerClosureFormula →
    (K₂[Real.rpow | openUnitInterval, openUnitInterval])̲ =
      openUnitIntervalPowLowerClosureFormula := by
  intro hcl₁ hLowerSaddle
  calc
    (K₂[Real.rpow | openUnitInterval, openUnitInterval])̲ =
        (K₁[Real.rpow | openUnitInterval, openUnitInterval])̲ := by
          simp [Bifunction.lowerClosure, hcl₁]
    _ = openUnitIntervalPowLowerClosureFormula := hLowerSaddle

-- Proof sketch: specialize the upper-closure formula at `(u,v) = (0,0)`.
/-- At the origin, the upper iterated closure of the upper-boundary extension takes the value
`1`. -/
theorem upperClosure_upperBoundaryExtension_openUnitIntervalPowKernel_origin_eq_one :
    cl₂ (K₂[Real.rpow | openUnitInterval, openUnitInterval]) =
        cl₂ (K₁[Real.rpow | openUnitInterval, openUnitInterval]) →
      (K₁[Real.rpow | openUnitInterval, openUnitInterval])̅ =
        openUnitIntervalPowUpperClosureFormula →
      (K₂[Real.rpow | openUnitInterval, openUnitInterval])̅ 0 0 = 1 := by
  intro hcl₂ hUpperSaddle
  rw [upperClosure_upperBoundaryExtension_openUnitIntervalPowKernel
    hcl₂ hUpperSaddle]
  simp [openUnitIntervalPowUpperClosureFormula, closedUnitInterval]

-- Proof sketch: specialize the lower-closure formula at `(u,v) = (0,0)`.
/-- At the origin, the lower iterated closure of the upper-boundary extension takes the value
`0`. -/
theorem lowerClosure_upperBoundaryExtension_openUnitIntervalPowKernel_origin_eq_zero :
    cl₁ (K₂[Real.rpow | openUnitInterval, openUnitInterval]) =
        cl₁ (K₁[Real.rpow | openUnitInterval, openUnitInterval]) →
      (K₁[Real.rpow | openUnitInterval, openUnitInterval])̲ =
        openUnitIntervalPowLowerClosureFormula →
      (K₂[Real.rpow | openUnitInterval, openUnitInterval])̲ 0 0 = 0 := by
  intro hcl₁ hLowerSaddle
  rw [lowerClosure_upperBoundaryExtension_openUnitIntervalPowKernel
    hcl₁ hLowerSaddle]
  simp [openUnitIntervalPowLowerClosureFormula, closedUnitInterval]

-- Proof sketch: compare the two origin-value theorems, which give `1` and `0` respectively.
/-- For the upper-boundary extension, the two iterated closures are different; the discrepancy is
already visible at the origin `(0,0)`. -/
theorem upperClosure_ne_lowerClosure_upperBoundaryExtension_openUnitIntervalPowKernel :
    cl₂ (K₂[Real.rpow | openUnitInterval, openUnitInterval]) =
        cl₂ (K₁[Real.rpow | openUnitInterval, openUnitInterval]) →
      cl₁ (K₂[Real.rpow | openUnitInterval, openUnitInterval]) =
        cl₁ (K₁[Real.rpow | openUnitInterval, openUnitInterval]) →
      (K₁[Real.rpow | openUnitInterval, openUnitInterval])̅ =
        openUnitIntervalPowUpperClosureFormula →
      (K₁[Real.rpow | openUnitInterval, openUnitInterval])̲ =
        openUnitIntervalPowLowerClosureFormula →
      (K₂[Real.rpow | openUnitInterval, openUnitInterval])̅ ≠
        (K₂[Real.rpow | openUnitInterval, openUnitInterval])̲ := by
  intro hcl₂ hcl₁ hUpperSaddle hLowerSaddle hEq
  have hOrigin := congrArg (fun K ↦ K 0 0) hEq
  change
      (K₂[Real.rpow | openUnitInterval, openUnitInterval])̅ 0 0 =
        (K₂[Real.rpow | openUnitInterval, openUnitInterval])̲ 0 0 at hOrigin
  rw [upperClosure_upperBoundaryExtension_openUnitIntervalPowKernel_origin_eq_one
      hcl₂ hUpperSaddle,
    lowerClosure_upperBoundaryExtension_openUnitIntervalPowKernel_origin_eq_zero
      hcl₁ hLowerSaddle] at hOrigin
  change (((1 : ℝ) : WithBotTop ℝ) = (0 : WithBotTop ℝ)) at hOrigin
  have hne : (((1 : ℝ) : WithBotTop ℝ)) ≠ 0 := by simp
  exact hne hOrigin

end UpperBoundaryExtension

end

end Bifunction

/-! ### Theorem_34_1 (from Chap07) -/
noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

open SaddleFunction

section Closedness

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Ring 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [NoMaxOrder 𝕜]
variable [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜] [NoBotOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U] [TopologicalSpace U]
variable [AddCommMonoid X] [SMul 𝕜 X] [TopologicalSpace X]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 34.1 concerns saddle-functions. The text fixes the
  concave-convex orientation for definiteness; this file keeps those direct branch theorems and
  records the convex-concave branch through the canonical symmetry bridge `Function.swap`.
- `core/canonical`: the closure representatives are the Chapter 34 owners
  `Bifunction.lowerClosure` and `Bifunction.upperClosure`; the closedness owners are
  `SaddleFunction.IsLowerClosed` and `SaddleFunction.IsUpperClosed` from
  `Definition33_0_42`.
- `bridge/view`: the saddle-shape part is expressed through the canonical Chapter 33 owners
  `SaddleFunction.IsConcaveConvex 𝕜` and `SaddleFunction.IsConvexConcave 𝕜`, related by
  `Function.swap`; no surrogate wrapper owner is introduced.

Domain-style sampling used here:
- `SaddleFunction.IsConcaveConvex` and `SaddleFunction.IsConvexConcave` from
  `Definition33_0_1`;
- `SaddleFunction.IsConcaveConvex.closure1_closed` and
  `SaddleFunction.IsConcaveConvex.closure2_closed` from `Corollary33_1_1`;
- `Bifunction.lowerClosure`, `Bifunction.upperClosure`, `Bifunction.lowerClosure_idem`, and
  `Bifunction.upperClosure_idem` from `Text_34_0_1`;
- `SaddleFunction.IsLowerClosed` and `SaddleFunction.IsUpperClosed` from `Definition33_0_42`;
- `Function.swap` as the canonical symmetry bridge.

Layer target: `source-facing`, with atomic owner-level consequences for the lower and upper
closures and the branchwise source-facing conjunction clauses.
-/

/-- The lower closure of a concave-convex saddle-function is lower closed. -/
theorem lowerClosure_isLowerClosed
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    IsLowerClosed K̲ := by
  exact (isLowerClosed_iff K̲).2 (lowerClosure_idem hK)

/-- The upper closure of a concave-convex saddle-function is upper closed. -/
theorem upperClosure_isUpperClosed
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    IsUpperClosed K̅ := by
  exact (isUpperClosed_iff K̅).2 (upperClosure_idem hK)

end Closedness

section Shape

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Ring 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [NoMaxOrder 𝕜]
variable [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜] [NoBotOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [TopologicalSpace U] [TopologicalSpace X]

/-- The lower closure of a concave-convex saddle-function is again concave-convex. -/
theorem lowerClosure_isConcaveConvex
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    IsConcaveConvex 𝕜 K̲ := by
  change IsConcaveConvex 𝕜 (cl₂ (cl₁ K))
  exact (hK.closure1.closure2_closed).1

/-- The upper closure of a concave-convex saddle-function is again concave-convex. -/
theorem upperClosure_isConcaveConvex
    [IsOrderedAddMonoid 𝕜]
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    IsConcaveConvex 𝕜 K̅ := by
  change IsConcaveConvex 𝕜 (cl₁ (cl₂ K))
  exact (hK.closure2.closure1_closed).1

section WithClosedness

/-- Theorem 34.1 (1): if `K` is a concave-convex saddle-function, then its lower closure is again
a concave-convex saddle-function and is lower closed. -/
theorem lowerClosure_isConcaveConvex_and_isLowerClosed
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    IsConcaveConvex 𝕜 K̲ ∧ IsLowerClosed K̲ := by
  exact ⟨lowerClosure_isConcaveConvex hK, lowerClosure_isLowerClosed hK⟩

/-- Theorem 34.1 (2): if `K` is a concave-convex saddle-function, then its upper closure is again
a concave-convex saddle-function and is upper closed. -/
theorem upperClosure_isConcaveConvex_and_isUpperClosed
    [IsOrderedAddMonoid 𝕜]
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    IsConcaveConvex 𝕜 K̅ ∧ IsUpperClosed K̅ := by
  exact ⟨upperClosure_isConcaveConvex hK, upperClosure_isUpperClosed hK⟩

/-- The convex-concave symmetry companion to Theorem 34.1 (1): if `K` is convex-concave, then the
lower closure of `Function.swap K` is again concave-convex and lower closed. By the terminology
swap of `Definition33_0_42`, this is the upper-closed branch for the original orientation. -/
theorem swap_lowerClosure_isConcaveConvex_and_isLowerClosed
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConvexConcave 𝕜 K) :
    IsConcaveConvex 𝕜 ((Function.swap K)̲) ∧ IsLowerClosed ((Function.swap K)̲) := by
  have hK' : IsConcaveConvex 𝕜 (Function.swap K) := hK.swap
  exact lowerClosure_isConcaveConvex_and_isLowerClosed hK'

/-- The convex-concave symmetry companion to Theorem 34.1 (2): if `K` is convex-concave, then the
upper closure of `Function.swap K` is again concave-convex and upper closed. By the terminology
swap of `Definition33_0_42`, this is the lower-closed branch for the original orientation. -/
theorem swap_upperClosure_isConcaveConvex_and_isUpperClosed
    [IsOrderedAddMonoid 𝕜]
    {K : U → X → WithBotTop 𝕜}
    (hK : IsConvexConcave 𝕜 K) :
    IsConcaveConvex 𝕜 ((Function.swap K)̅) ∧ IsUpperClosed ((Function.swap K)̅) := by
  have hK' : IsConcaveConvex 𝕜 (Function.swap K) := hK.swap
  exact upperClosure_isConcaveConvex_and_isUpperClosed hK'

end WithClosedness

end Shape

end Bifunction

/-! ### Text_34_1_2 (from Chap07) -/
noncomputable section

open scoped Rockafellar

namespace Bifunction

open Function

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.2 gives a concrete Chapter 34 counterexample for the iterated partial
  closures of a saddle-function built from the kernel `(u, v) ↦ u / v` on the positive quadrant.
- `core/canonical`: the ambient example is the Chapter 33 bridge owner
  `Bifunction.saddleExtension` applied to the ratio kernel and the positive-quadrant domain sets;
  iterated closures use the Chapter 34 owners `lowerClosure` / `upperClosure`.
- `bridge/view`: Text 34.1.2's pointwise formulas are exposed as formula owners, and the effective
  domain consequences are recorded in hypothesis-parameterized bridge form.

Domain-style sampling used here:
- `Bifunction.saddleExtension` from `Definition33_0_2`;
- `Bifunction.lowerClosure` and `Bifunction.upperClosure` from `Chap07.Defn_34_1`;
- `Function.uncurry` from mathlib as the canonical bridge from a bifunction to an ordinary
  function on `𝕜 × 𝕜`;
- `effectiveDomain` from `Chap01.Definition_4_4`, written in theorem surfaces as `dom(·)`.

Primitive data vs derived API:
- primitive source data: the ratio kernel `(u, v) ↦ u / v` on `𝕜 × 𝕜` together with the domain
  sets `(Ici 0)` and `(Ioi 0)`;
- derived API: the thin saddle-function bridge `saddleExtension`, formula owners for the displayed
  iterated closures, and hypothesis-parameterized effective-domain counterexample consequences.
- scalar/ambient layer: this item is stated over an ordered field-type scalar `𝕜`, because the
  source counterexample only uses ratio and sign/zero boundary behavior at `(0, 0)`.

Layer target: `source-facing`.
-/

section BasicLayer

variable (𝕜 : Type*)

attribute [local instance] Classical.propDecidable

/-- The ratio kernel `(u, v) ↦ u / v` underlying Text 34.1.2. -/
def positiveQuadrantRatio [Div 𝕜] (u v : 𝕜) : 𝕜 :=
  u / v

variable [Preorder 𝕜] [Zero 𝕜] [Div 𝕜]

/-- The Chapter 34 counterexample saddle-function, represented canonically by the Chapter 33
bridge owner `saddleExtension` for the ratio kernel on the positive quadrant. -/
abbrev positiveQuadrantRatioSaddle :
    𝕜 → 𝕜 → WithBotTop 𝕜 :=
  K₁[positiveQuadrantRatio 𝕜 | Set.Ici 0, Set.Ioi 0]

-- Proof sketch: rewrite to the canonical owner `saddleExtension`; on the positive quadrant,
-- the owner-side branch lemma returns the finite value `u / v`.
/-- On the positive quadrant branch, `positiveQuadrantRatioSaddle` agrees with the finite kernel
`u / v`. -/
@[simp] theorem positiveQuadrantRatioSaddle_apply_of_nonneg_pos
    {u v : 𝕜} (hu : 0 ≤ u) (hv : 0 < v) :
    positiveQuadrantRatioSaddle 𝕜 u v = ((u / v : 𝕜) : WithBotTop 𝕜) := by
  change K₁[positiveQuadrantRatio 𝕜 | Set.Ici (0 : 𝕜), Set.Ioi (0 : 𝕜)] u v =
    ((u / v : 𝕜) : WithBotTop 𝕜)
  simpa [positiveQuadrantRatio] using
    (saddleExtension_apply_of_mem
      (K := positiveQuadrantRatio 𝕜) (C := Set.Ici (0 : 𝕜)) (D := Set.Ioi (0 : 𝕜)) hu hv)

-- Proof sketch: rewrite to `saddleExtension`; outside the first-coordinate domain `Ici 0`,
-- the owner-side branch lemma gives the constant value `-∞`.
/-- On the negative first-variable half-plane, `positiveQuadrantRatioSaddle` takes the value
`-∞`. -/
@[simp] theorem positiveQuadrantRatioSaddle_apply_of_neg
    {u v : 𝕜} (hu : u < 0) :
    positiveQuadrantRatioSaddle 𝕜 u v = ⊥ := by
  change K₁[positiveQuadrantRatio 𝕜 | Set.Ici (0 : 𝕜), Set.Ioi (0 : 𝕜)] u v = ⊥
  exact saddleExtension_apply_of_not_mem_left
    (K := positiveQuadrantRatio 𝕜) (C := Set.Ici (0 : 𝕜)) (D := Set.Ioi (0 : 𝕜))
    (show u ∉ Set.Ici (0 : 𝕜) from by simpa using not_le_of_gt hu)

-- Proof sketch: rewrite to `saddleExtension`; once `u ∈ Ici 0` and `v ∉ Ioi 0`, the owner-side
-- branch lemma gives the constant value `+∞`.
/-- On the nonpositive second-variable half-plane over `u ≥ 0`, `positiveQuadrantRatioSaddle`
takes the value `+∞`. -/
@[simp] theorem positiveQuadrantRatioSaddle_apply_of_nonneg_nonpos
    {u v : 𝕜} (hu : 0 ≤ u) (hv : v ≤ 0) :
    positiveQuadrantRatioSaddle 𝕜 u v = ⊤ := by
  change K₁[positiveQuadrantRatio 𝕜 | Set.Ici (0 : 𝕜), Set.Ioi (0 : 𝕜)] u v = ⊤
  exact saddleExtension_apply_of_mem_left_of_not_mem_right
    (K := positiveQuadrantRatio 𝕜) (C := Set.Ici (0 : 𝕜)) (D := Set.Ioi (0 : 𝕜))
    (show u ∈ Set.Ici (0 : 𝕜) from hu)
    (show v ∉ Set.Ioi (0 : 𝕜) from by simpa using not_lt_of_ge hv)

/-! Formula owners used for the two displayed piecewise expressions of Text 34.1.2. -/

/-- The displayed piecewise formula in Text 34.1.2 for the upper iterated closure
`cl₁ (cl₂ K)` of `positiveQuadrantRatioSaddle`. It equals
`u / v` on `u ≥ 0, v > 0`, equals `-∞` on `u < 0, v > 0`, and equals `+∞` on `v ≤ 0`. -/
def positiveQuadrantRatioSaddleUpperClosureFormula
    [Preorder 𝕜] [Zero 𝕜] [Div 𝕜]
    (u v : 𝕜) :
    WithBotTop 𝕜 :=
  if 0 < v then
    if 0 ≤ u then
      ((u / v : 𝕜) : WithBotTop 𝕜)
    else
      ⊥
  else
    ⊤

/-- The displayed piecewise formula in Text 34.1.2 for the lower iterated closure
`cl₂ (cl₁ K)` of `positiveQuadrantRatioSaddle`. It equals
`u / v` on `u ≥ 0, v > 0`, equals `0` at the origin, equals `+∞` on the remaining points with
`u ≥ 0, v ≤ 0`, and equals `-∞` on `u < 0`. -/
def positiveQuadrantRatioSaddleLowerClosureFormula
    [Preorder 𝕜] [Zero 𝕜] [Div 𝕜]
    (u v : 𝕜) :
    WithBotTop 𝕜 :=
  if u < 0 then
    ⊥
  else if 0 < v then
    ((u / v : 𝕜) : WithBotTop 𝕜)
  else if u = 0 ∧ v = 0 then
    0
  else
    ⊤

end BasicLayer

section EffectiveDomainLayer

variable (𝕜 : Type*) [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜]

-- Proof sketch: `lowerClosure positiveQuadrantRatioSaddle` and
-- `upperClosure positiveQuadrantRatioSaddle` take different values at the origin (`0` vs `+∞`);
-- therefore their effective domains cannot coincide.
/-- Text 34.1.2 (3): the effective domains of the lower and upper closures of this counterexample
are different, assuming the two displayed closure formulas. -/
theorem effectiveDomain_lowerClosure_ne_upperClosure_positiveQuadrantRatioSaddle :
    (positiveQuadrantRatioSaddle 𝕜)̲ =
      positiveQuadrantRatioSaddleLowerClosureFormula 𝕜 →
    (positiveQuadrantRatioSaddle 𝕜)̅ =
      positiveQuadrantRatioSaddleUpperClosureFormula 𝕜 →
    dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̲)) ≠
      dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̅)) := by
  intro hLowerFormula hUpperFormula hdom
  have hOriginLower :
      ((0 : 𝕜), (0 : 𝕜)) ∈ dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̲)) := by
    rw [hLowerFormula]
    rw [effectiveDomain]
    simpa [Function.uncurry, positiveQuadrantRatioSaddleLowerClosureFormula] using
      (WithBotTop.coe_lt_top (0 : 𝕜))
  have hOriginUpper :
      ((0 : 𝕜), (0 : 𝕜)) ∈ dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̅)) := by
    simpa [hdom] using hOriginLower
  rw [hUpperFormula] at hOriginUpper
  simp [effectiveDomain, Function.uncurry, positiveQuadrantRatioSaddleUpperClosureFormula]
    at hOriginUpper

-- Proof sketch: by the lower-closure formula, points `(0,0)` and `(1,1)` lie in the effective
-- domain, while `(1,0)` does not. A product decomposition `A ×ˢ B` would force `(1,0)` to belong
-- once `(1,1)` and `(0,0)` do, giving a contradiction.
/-- Text 34.1.2 (4): the effective domain of the lower closure of this counterexample is not a
product set, assuming the displayed lower-closure formula. -/
theorem effectiveDomain_lowerClosure_not_prod_positiveQuadrantRatioSaddle
    [IsOrderedRing 𝕜] :
    (positiveQuadrantRatioSaddle 𝕜)̲ =
      positiveQuadrantRatioSaddleLowerClosureFormula 𝕜 →
    ¬ ∃ A B : Set 𝕜,
      dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̲)) = A ×ˢ B := by
  intro hLowerFormula
  rintro ⟨A, B, hAB⟩
  have h00 :
      ((0 : 𝕜), (0 : 𝕜)) ∈ dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̲)) := by
    rw [hLowerFormula]
    rw [effectiveDomain]
    simpa [Function.uncurry, positiveQuadrantRatioSaddleLowerClosureFormula] using
      (WithBotTop.coe_lt_top (0 : 𝕜))
  have h11 :
      ((1 : 𝕜), (1 : 𝕜)) ∈ dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̲)) := by
    rw [hLowerFormula]
    rw [effectiveDomain]
    have hnot : ¬ (1 : 𝕜) < 0 := not_lt.mpr zero_le_one
    have hpos : (0 : 𝕜) < 1 := zero_lt_one
    simp only [Set.mem_setOf_eq, uncurry_apply_pair, positiveQuadrantRatioSaddleLowerClosureFormula,
      hnot, hpos, reduceIte, gt_iff_lt]
    exact WithBotTop.coe_lt_top ((1 : 𝕜) / 1)
  have h10 :
      ((1 : 𝕜), (0 : 𝕜)) ∉ dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̲)) := by
    rw [hLowerFormula]
    simp [effectiveDomain, Function.uncurry, positiveQuadrantRatioSaddleLowerClosureFormula]
  have hB0 : (0 : 𝕜) ∈ B := by
    have hPair : ((0 : 𝕜), (0 : 𝕜)) ∈ A ×ˢ B := by
      simpa [hAB] using h00
    exact hPair.2
  have hA1 : (1 : 𝕜) ∈ A := by
    have hPair : ((1 : 𝕜), (1 : 𝕜)) ∈ A ×ˢ B := by
      simpa [hAB] using h11
    exact hPair.1
  have h10In :
      ((1 : 𝕜), (0 : 𝕜)) ∈ dom(uncurry ((positiveQuadrantRatioSaddle 𝕜)̲)) := by
    have hPair : ((1 : 𝕜), (0 : 𝕜)) ∈ A ×ˢ B := ⟨hA1, hB0⟩
    simpa [hAB] using hPair
  exact h10 h10In

end EffectiveDomainLayer

end Bifunction

/-! ### Text_34_1_3 (from Chap07) -/
noncomputable section

universe u

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.3 studies the explicit saddle-function on `𝕜 × 𝕜` whose value is
  `+∞`, `0`, or `-∞` according to the sign of the product `uv`, together with its upper/lower
  closures and its finite-value locus.
- `core/canonical`: the Chapter 34 iterated closure owners `Bifunction.upperClosure` and
  `Bifunction.lowerClosure` from `Defn_34_1`, together with the chapter finite-value owner surface
  `dom(Function.uncurry K) ∩ dom(-Function.uncurry K)`.

Domain-style sampling used here:
- `Bifunction.upperClosure` and `Bifunction.lowerClosure` from `Defn_34_1`;
- `Function.uncurry` as the canonical owner bridge from a bifunction to an ordinary function;
- `dom(·)` from `Definition_4_4`, paired intrinsically as
  `dom(Function.uncurry K) ∩ dom(-Function.uncurry K)`;
- `Convex 𝕜` and the product-set notation `×ˢ` from mathlib.

Primitive data vs derived API:
- primitive source datum: the explicit bifunction `productSignSaddle`;
- derived API: the upper-closure and lower-closure formulas, the finite-value-locus description,
  and the non-product consequence for that locus.

Layer target: `source-facing`, written directly on the canonical iterated closure formulas and the
intrinsic finite-value owner.
-/

variable (𝕜 : Type u)

/-- The explicit saddle-function of Text 34.1.3, equal to `+∞`, `0`, or `-∞` according to the
sign of `uv`. -/
def productSignSaddle [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
    𝕜 → 𝕜 → WithBotTop 𝕜 :=
  fun u v =>
    if 0 < u * v then ⊤ else if u * v = 0 then 0 else ⊥

-- Proof sketch: unfold `productSignSaddle`; this is the defining case split on the sign
-- of `u * v`.
/-- Evaluating `productSignSaddle` amounts to the defining sign-of-product case split. -/
@[simp] theorem productSignSaddle_apply [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (u v : 𝕜) :
    productSignSaddle 𝕜 u v =
      if 0 < u * v then ⊤ else if u * v = 0 then 0 else ⊥ := rfl

-- Proof sketch: first fix `u` and compute `cl₂` of the slice `v ↦ productSignSaddle u v`.
-- For `u ≠ 0`, that slice is `-∞` on an open half-line, so its convex closure collapses to `-∞`
-- everywhere; for `u = 0`, the slice is constantly `0`. Applying `cl₁` to the resulting spike in
-- the `u`-variable preserves `0` on the axis and `-∞` off it.
/-- Text 34.1.3 (1): the upper closure `K̅` of the product-sign saddle-function is `0` on the
axis `u = 0` and `-∞` away from that axis. -/
theorem upperClosure_productSignSaddle [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] :
    (productSignSaddle 𝕜)̅ =
      fun u _ ↦ if u = 0 then 0 else ⊥ := sorry

-- Proof sketch: first fix `v` and compute `cl₁` of the slice `u ↦ productSignSaddle u v`.
-- For `v ≠ 0`, that slice is `+∞` on an open half-line, so its concave closure collapses to `+∞`
-- everywhere; for `v = 0`, the slice is constantly `0`. Applying `cl₂` to the resulting spike in
-- the `v`-variable preserves `0` on the axis and `+∞` off it.
/-- The lower closure `K̲` of the product-sign saddle-function is `0` on the axis `v = 0` and
`+∞` away from that axis. -/
theorem lowerClosure_productSignSaddle [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] :
    (productSignSaddle 𝕜)̲ =
      fun _ v ↦ if v = 0 then 0 else ⊤ := sorry

-- Proof sketch: finite-valuedness is written as
-- `p ∈ dom(Function.uncurry (productSignSaddle 𝕜)) ∩
--   dom(-Function.uncurry (productSignSaddle 𝕜))`.
-- For `productSignSaddle`, this conjunction holds exactly in the middle branch of the defining
-- case split, so exactly when `u * v = 0`. In an ordered ring,
-- `u * v = 0` is equivalent to `u = 0 ∨ v = 0`, giving the union of the two coordinate axes.
/-- The finite-value locus of `productSignSaddle` is the union of the two coordinate axes. -/
theorem finiteValueLocus_productSignSaddle_eq_axes [Ring 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] :
    dom(Function.uncurry (productSignSaddle 𝕜)) ∩
      dom(-Function.uncurry (productSignSaddle 𝕜)) =
      {p : 𝕜 × 𝕜 | p.1 = 0} ∪ {p : 𝕜 × 𝕜 | p.2 = 0} := sorry

-- Proof sketch: by the previous theorem, the finite-value locus is the union of the two axes. If
-- that locus were a product `A ×ˢ B` with `A` and `B` convex, then `(0, 0)`, `(1, 0)`, and
-- `(0, 1)` would lie in `A ×ˢ B`, forcing both `0` and `1` to lie in each factor. Hence `(1, 1)`
-- would also lie in `A ×ˢ B`, contradicting that `(1, 1)` is not on either axis.
/-- The finite-value locus of `productSignSaddle` is not a product of two convex subsets of `𝕜`.
-/
theorem finiteValueLocus_productSignSaddle_not_prod_of_convex_sets [Ring 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] :
    ¬ ∃ A B : Set 𝕜, Convex 𝕜 A ∧ Convex 𝕜 B ∧
      dom(Function.uncurry (productSignSaddle 𝕜)) ∩
        dom(-Function.uncurry (productSignSaddle 𝕜)) = A ×ˢ B :=
  sorry

end Bifunction

/-! ### Text_34_1_4 (from Chap07) -/
noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

open SaddleFunction

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.4 records the relations between the Chapter 34 lower closure
  `K̲ = cl₂ (cl₁ K)` and upper closure `K̅ = cl₁ (cl₂ K)`.
- `core/canonical`: the owner level is the Chapter 34 API `Bifunction.lowerClosure`,
  `Bifunction.upperClosure`, and the partial closures `Bifunction.closure1`, `Bifunction.closure2`
  already introduced upstream.
- `bridge/view`: this item only records the two closure identities relating those canonical
  Chapter 34 owners.

Domain-style sampling used here:
- `Bifunction.lowerClosure` from `Defn_34_1`;
- `Bifunction.upperClosure` from `Defn_34_1`;
- `Bifunction.closure1` from `Definition33_0_4`;
- `Bifunction.closure2` from `Definition33_0_4`.

Primitive data vs derived API:
- primitive source datum: a concave-convex saddle bifunction `K : U → X → WithBotTop 𝕜`;
- primitive owner API reused here: the Chapter 34 partial closures `cl₁`, `cl₂` and the
  canonical closure representatives `lowerClosure`, `upperClosure`;
- derived API: the two displayed relations of Text 34.1.4.

Layer target: `bridge/view`, stated directly on the canonical Chapter 34 closure owners.
-/

section

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Ring 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [NoMaxOrder 𝕜]
variable [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜] [NoBotOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U] [TopologicalSpace U]
variable [AddCommMonoid X] [SMul 𝕜 X] [TopologicalSpace X]

-- This is the first mixed closure relation between the canonical Chapter 34 iterated closures.
-- It is the bridge used immediately downstream to prove idempotence of `lowerClosure` and
-- `upperClosure`.
/-- Text 34.1.4: applying `cl₁` to the lower closure `K̲ = cl₂ (cl₁ K)` gives the upper closure
`K̅ = cl₁ (cl₂ K)`. This is the first displayed relation of the text, and the companion theorem
below records the symmetric second relation. -/
@[simp] theorem _root_.SaddleFunction.IsConcaveConvex.closure1_lowerClosure_eq_upperClosure
    {K : U → X → WithBotTop 𝕜} (hK : SaddleFunction.IsConcaveConvex 𝕜 K) :
    cl₁ K̲ = K̅ := by
  sorry

@[simp] theorem closure1_lowerClosure_eq_upperClosure
    {K : U → X → WithBotTop 𝕜} (hK : SaddleFunction.IsConcaveConvex 𝕜 K) :
    cl₁ K̲ = K̅ :=
  hK.closure1_lowerClosure_eq_upperClosure

-- This is the symmetric mixed closure relation paired with the preceding theorem.
/-- Applying `cl₂` to the upper closure `K̅ = cl₁ (cl₂ K)` gives back the lower closure
`K̲ = cl₂ (cl₁ K)`. This is the symmetric second displayed relation from the text. -/
@[simp] theorem _root_.SaddleFunction.IsConcaveConvex.closure2_upperClosure_eq_lowerClosure
    {K : U → X → WithBotTop 𝕜} (hK : SaddleFunction.IsConcaveConvex 𝕜 K) :
    cl₂ K̅ = K̲ := by
  sorry

@[simp] theorem closure2_upperClosure_eq_lowerClosure
    {K : U → X → WithBotTop 𝕜} (hK : SaddleFunction.IsConcaveConvex 𝕜 K) :
    cl₂ K̅ = K̲ :=
  hK.closure2_upperClosure_eq_lowerClosure

end

end Bifunction

/-! ### Text_34_1_5 (from Chap07) -/
noncomputable section

universe u v w w' z

namespace Bifunction

open scoped Rockafellar
open SaddleFunction

section

variable {𝕜 : Type z} {U : Type u} {X : Type v} {XStar : Type w} {UStar : Type w'}
variable [Field 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U] [FiniteDimensional 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousConstSMul 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar]
variable [IsTopologicalAddGroup XStar] [ContinuousConstSMul 𝕜 XStar]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [FiniteDimensional 𝕜 UStar]
variable [IsTopologicalAddGroup UStar] [ContinuousConstSMul 𝕜 UStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]
variable [HasLinearPairing XStar X 𝕜] [HasContinuousPairing XStar X 𝕜]
variable [Module 𝕜 (WithBotTop 𝕜)] [PosSMulMono 𝕜 (WithBotTop 𝕜)]

local notation:50 F " represents_closed_convex_pair[" K ", " Kbar "]" =>
  IsClosedConvex F ∧
    K = lowerPairing XStar F ∧
    Kbar = upperAdjointPairing XStar UStar F

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.5 says that for a concave-convex saddle-function `K`, there exists a
  unique closed-convex bifunction `F` whose lower and upper representatives are the iterated
  closures `cl₂ (cl₁ K)` and `cl₁ (cl₂ K)`.
- `core/canonical`: those owners are already the Chapter 34 canonical API:
  `Bifunction.lowerClosure`, `Bifunction.upperClosure`,
  `Bifunction.IsClosedConvex`, `Bifunction.lowerPairing`, and
  `Bifunction.upperAdjointPairing`.
- `bridge/view`: the unique-generator statement is a thin bridge through the existing closure
  relation theorem
  `SaddleFunction.existsUnique_closedConvex_bifunction_iff_closure_relations`, applied to the
  canonical representatives `K̲` and `K̅`.

Domain-style sampling used here:
- `Bifunction.lowerClosure_isConcaveConvex` from `Theorem_34_1`;
- `Bifunction.closure1_lowerClosure_eq_upperClosure` from `Text_34_1_4`;
- `Bifunction.closure2_upperClosure_eq_lowerClosure` from `Text_34_1_4`;
- `SaddleFunction.existsUnique_closedConvex_bifunction_iff_closure_relations` from
  `Corollary33_3_1`.

Layer target: `source-facing`, using the canonical Chapter 34 owner names.
-/

/-- Text 34.1.5: for a concave-convex saddle-function `K : U → XStar → WithBotTop 𝕜`, there
exists a unique closed-convex bifunction `F : U → X → WithBotTop 𝕜` whose canonical
representatives are the iterated closures of `K`:
`K̲ = lowerPairing XStar F` and `K̅ = upperAdjointPairing XStar UStar F`. -/
theorem existsUnique_closedConvex_bifunction_generating_closure_representatives
    {K : U → XStar → WithBotTop 𝕜}
    (hK : IsConcaveConvex 𝕜 K) :
    ∃! F : U → X → WithBotTop 𝕜,
      F represents_closed_convex_pair[K̲, K̅] := by
  have hKlower : IsConcaveConvex 𝕜 K̲ :=
    lowerClosure_isConcaveConvex hK
  have hclosure :
      cl₁ K̲ = K̅ ∧ cl₂ K̅ = K̲ :=
    ⟨closure1_lowerClosure_eq_upperClosure hK, closure2_upperClosure_eq_lowerClosure hK⟩
  exact (existsUnique_closedConvex_bifunction_iff_closure_relations UStar hKlower).2 hclosure

end

end Bifunction

/-! ### Text_34_1_6 (from Chap07) -/
noncomputable section

universe u v w z

open scoped Rockafellar

namespace SaddleFunction

section ConvexDom₁

variable {𝕜 : Type z} {U : Type u} {X : Type v} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid β] [PartialOrder β] [Bot β]
variable [Module 𝕜 β]
variable [IsOrderedCancelAddMonoid β]
variable [PosSMulStrictMono 𝕜 β]

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.6 states that the first-coordinate and second-coordinate effective
  domains of a concave-convex saddle-function are convex, and deduces convexity and
  finite-valuedness on the product domain.
- `core/canonical`: the chapter already owns the saddle-shape predicate
  `SaddleFunction.IsConcaveConvex 𝕜 K` together with the Chapter 34 source-facing domain owners
  `SaddleFunction.dom₁`, `SaddleFunction.dom₂`, and `SaddleFunction.dom` from `Defn_34_3`.
- `bridge/view`: for each fixed slice, the mathlib strict sublevel/superlevel convexity owners
  `ConvexOn.convex_lt` and `ConcaveOn.convex_gt` give convexity of the slice domain conditions;
  `convex_iInter` then packages the coordinate domains as intersections of those convex slices.

Primary mathematical domain:
- convex analysis of concave-convex saddle-functions and their coordinate effective domains.

Domain-style sampling used here:
- `SaddleFunction.IsConcaveConvex` from `Chap07.Definition33_0_1`;
- the Chapter 34 domain owners `SaddleFunction.dom₁`, `SaddleFunction.dom₂`, and
  `SaddleFunction.dom` from `Chap07.Defn_34_3`;
- `ConcaveOn.convex_gt` and `ConvexOn.convex_lt` from mathlib for strict slice domains;
- `convex_iInter` from mathlib for the coordinate-domain intersections.

Primitive data vs derived API:
- primitive source datum: a bifunction `K : U → X → β` into an ordered codomain with endpoints;
- primitive owner hypothesis: `IsConcaveConvex 𝕜 K`;
- derived API: convexity of `dom₁ K`, convexity of `dom₂ K`, convexity of
  `dom K = dom₁ K ×ˢ dom₂ K`, and finiteness of `K` on that domain.

Layer target: `source-facing`.
-/

-- Proof sketch: unpack `IsConcaveConvex 𝕜 K`. For each fixed `v`, use
-- `ConcaveOn.convex_gt` at level `⊥` to get convexity of the slice set
-- `{u | ⊥ < K u v}`, then intersect those convex slice domains over all `v`.
/-- Text 34.1.6 (1): the first-coordinate effective domain of a concave-convex saddle-function is
a convex set. -/
theorem convex_dom₁_of_isConcaveConvex
    {K : U → X → β} (hK : IsConcaveConvex 𝕜 K) :
    Convex 𝕜 (dom₁ K) := by
  rcases (isConcaveConvex_iff (𝕜 := 𝕜) K).1 hK with ⟨hConcave, _⟩
  simpa [dom₁, Set.iInter_setOf, Set.univ_inter] using
    (convex_iInter (fun v => (hConcave v).convex_gt (⊥ : β)))

end ConvexDom₁

section ConvexDom₂

variable {𝕜 : Type z} {U : Type u} {X : Type v} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid β] [PartialOrder β] [Top β]
variable [Module 𝕜 β]
variable [IsOrderedCancelAddMonoid β]
variable [PosSMulStrictMono 𝕜 β]

-- Proof sketch: unpack `IsConcaveConvex 𝕜 K`. For each fixed `u`, apply
-- `ConvexOn.convex_lt` at level `⊤` to get convexity of the slice set
-- `{v | K u v < ⊤}`, then intersect those convex slice domains over all `u`.
/-- Text 34.1.6 (2): the second-coordinate effective domain of a concave-convex saddle-function is
a convex set. -/
theorem convex_dom₂_of_isConcaveConvex
    {K : U → X → β} (hK : IsConcaveConvex 𝕜 K) :
    Convex 𝕜 (dom₂ K) := by
  rcases (isConcaveConvex_iff (𝕜 := 𝕜) K).1 hK with ⟨_, hConvex⟩
  simpa [dom₂, Set.iInter_setOf, Set.univ_inter] using
    (convex_iInter (fun u => (hConvex u).convex_lt (⊤ : β)))

end ConvexDom₂

section ConvexEffectiveDomain

variable {𝕜 : Type z} {U : Type u} {X : Type v} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid β] [PartialOrder β] [Bot β] [Top β]
variable [Module 𝕜 β]
variable [IsOrderedCancelAddMonoid β]
variable [PosSMulStrictMono 𝕜 β]

-- Proof sketch: `dom K` is definitionally `dom₁ K ×ˢ dom₂ K`, so its convexity
-- follows from the two preceding coordinate-domain convexity statements and the standard product
-- theorem for convex sets.
/-- Text 34.1.6 (3): consequently, `dom K = dom₁ K ×ˢ dom₂ K` is a convex set in the product
space. -/
theorem convex_dom_of_isConcaveConvex
    {K : U → X → β} (hK : IsConcaveConvex 𝕜 K) :
    Convex 𝕜 (dom K) := by
  exact
    (convex_dom₁_of_isConcaveConvex hK).prod
      (convex_dom₂_of_isConcaveConvex hK)

end ConvexEffectiveDomain

section FiniteOnEffectiveDomain

variable {U : Type u} {X : Type v} {β : Type w}
variable [LT β] [Bot β] [Top β]

/-- Text 34.1.6 (4): if `u ∈ dom₁ K` and `v ∈ dom₂ K`, then `K u v` is finite, i.e.
`⊥ < K u v` and `K u v < ⊤`. This is a direct consequence of the Chapter 34 coordinate-domain
owners and does not require the concave-convex shape hypothesis. -/
theorem bot_lt_and_lt_top_of_mem_dom₁_of_mem_dom₂
    {K : U → X → β} {u : U} {v : X}
    (hu : u ∈ dom₁ K) (hv : v ∈ dom₂ K) :
    ⊥ < K u v ∧ K u v < ⊤ :=
  ⟨hu v, hv u⟩

/-- Equivalent product-domain form of the finiteness clause in Text 34.1.6. -/
theorem bot_lt_and_lt_top_of_mem_dom
    {K : U → X → β} {p : U × X}
    (hp : p ∈ dom K) :
    ⊥ < K p.1 p.2 ∧ K p.1 p.2 < ⊤ := by
  rcases hp with ⟨hp₁, hp₂⟩
  exact bot_lt_and_lt_top_of_mem_dom₁_of_mem_dom₂ hp₁ hp₂

end FiniteOnEffectiveDomain

end SaddleFunction

/-! ### Text_34_1_7 (from Chap07) -/
noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

open SaddleFunction

section

variable {U : Type u} {V : Type v} {α : Type w}
variable [LT α]
variable {C : Set U} {D : Set V}

attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.7 identifies the Chapter 34 domains and properness of the lower and
  upper simple extensions of a finite kernel on a product set `C × D`.
- `core/canonical`: the natural owner layer is the Chapter 33/34 simple-extension/domain API.
- `bridge/view`: this item is stated directly on those canonical owners, with no local duplicate
  owner namespace.

Primary mathematical domain:
- saddle-function effective domains and properness for simple extensions.

Domain-style sampling used here:
- endpoint-order data `⊥`, `⊤`, and `<` at the primitive codomain layer;
- product sets `×ˢ` and `Set.Nonempty` from the canonical `Set` API;
- the canonical finite-kernel codomain lift `Bifunction.toWithBotTop` for the concrete bridge;
- the Chapter 33 owners `lowerSimpleExtension` and `upperSimpleExtension`;
- the Chapter 34 owners `dom₁`, `dom₂`, `dom`, and `IsProper`.

Primitive data vs derived API:
- primitive source data: a finite-valued kernel on `C × D` at the endpoint-order layer;
- primitive owner data reused here: the simple extensions and the Chapter 34 domain/properness
  owners;
- concrete bridge data: the canonical codomain lift `toWithBotTop` for `J : C → D → α`;
- derived API in this file: coordinate-domain equalities, effective-domain equalities, and the
  resulting properness consequences.

Layer target: `source-facing`.
-/

section FiniteValuedSimpleExtension

variable {β : Type w}
variable [LT β] [Bot β] [Top β]
variable (K : C → D → β)

-- Proof sketch: unfold `SaddleFunction.dom₁` and `Bifunction.lowerSimpleExtension`. If `u ∈ C`,
-- every second-variable value is either finite by `hK` or `⊤`, hence strictly above `⊥`;
-- if `u ∉ C`, the extension is identically `⊥` in the second variable.
/-- Primitive domain-layer form of Text 34.1.7: if `K` is finite-valued on `C × D`, then the
first-coordinate domain of its lower simple extension is exactly `C`, provided `V` is nonempty. -/
theorem dom₁_lowerSimpleExtension_eq_of_finite [Nonempty V]
    (hbot_irrefl : ¬ ((⊥ : β) < ⊥)) (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    dom₁ (lowerSimpleExtension K) = C := by
  intro hK
  ext u
  constructor
  · intro hu
    by_contra huc
    let v : V := Classical.choice ‹Nonempty V›
    have hbot : lowerSimpleExtension K u v = ⊥ := by
      simp [lowerSimpleExtension, huc]
    exact hbot_irrefl (by simpa [hbot] using hu v)
  · intro hu v
    by_cases hv : v ∈ D
    · simpa [lowerSimpleExtension, hu, hv] using (hK ⟨u, hu⟩ ⟨v, hv⟩).1
    · simpa [lowerSimpleExtension, hu, hv] using hbot_top

-- Proof sketch: unfold `SaddleFunction.dom₂` and `Bifunction.lowerSimpleExtension`. For `v ∈ D`,
-- every first-variable value is either finite by `hK` or `⊥`, hence strictly below `⊤`.
-- For `v ∉ D`, choose `u ∈ C` from `hC`; the lower simple extension then takes value `⊤`.
/-- Primitive domain-layer form of Text 34.1.7: if `K` is finite-valued on `C × D` and `C` is
nonempty, then the second-coordinate domain of its lower simple extension is exactly `D`. -/
theorem dom₂_lowerSimpleExtension_eq_of_finite (hC : C.Nonempty)
    (htop_irrefl : ¬ ((⊤ : β) < ⊤)) (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    dom₂ (lowerSimpleExtension K) = D := by
  intro hK
  ext v
  constructor
  · intro hv
    by_contra hvD
    rcases hC with ⟨u, hu⟩
    have htop : lowerSimpleExtension K u v = ⊤ := by
      simp [lowerSimpleExtension, hu, hvD]
    exact htop_irrefl (by simpa [htop] using hv u)
  · intro hv u
    by_cases hu : u ∈ C
    · simpa [lowerSimpleExtension, hu, hv] using (hK ⟨u, hu⟩ ⟨v, hv⟩).2
    · simpa [lowerSimpleExtension, hu] using hbot_top

-- Proof sketch: combine the two preceding coordinate-domain formulas with the definition
-- `SaddleFunction.dom K = SaddleFunction.dom₁ K ×ˢ SaddleFunction.dom₂ K`.
/-- Primitive domain-layer form of Text 34.1.7 for the lower simple extension:
if `K` is finite-valued on `C × D` and `C` is nonempty, then its effective domain is `C ×ˢ D`. -/
theorem dom_lowerSimpleExtension_eq_of_finite (hC : C.Nonempty)
    (hbot_irrefl : ¬ ((⊥ : β) < ⊥)) (htop_irrefl : ¬ ((⊤ : β) < ⊤))
    (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    dom (lowerSimpleExtension K) = C ×ˢ D := by
  intro hK
  ext p
  constructor
  · intro hp
    rcases mem_dom.mp hp with ⟨hu, hv⟩
    haveI : Nonempty V := ⟨p.2⟩
    refine ⟨?_, ?_⟩
    · simpa [dom₁_lowerSimpleExtension_eq_of_finite (K := K) hbot_irrefl hbot_top hK] using hu
    · simpa [dom₂_lowerSimpleExtension_eq_of_finite (K := K) hC htop_irrefl hbot_top hK] using hv
  · rintro ⟨hu, hv⟩
    refine mem_dom.mpr ?_
    constructor
    · haveI : Nonempty V := ⟨p.2⟩
      have hp₁ : p.1 ∈ dom₁ (lowerSimpleExtension K) := by
        simpa [dom₁_lowerSimpleExtension_eq_of_finite (K := K) hbot_irrefl hbot_top hK] using hu
      exact hp₁
    · simpa [dom₂_lowerSimpleExtension_eq_of_finite (K := K) hC htop_irrefl hbot_top hK] using hv

-- Proof sketch: use the preceding effective-domain identity and the hypotheses that both factors
-- are nonempty to obtain a point of `C ×ˢ D`, hence of the effective domain.
/-- Primitive properness-layer form of Text 34.1.7 for the lower simple extension:
if `K` is finite-valued on `C × D` and both factors are nonempty, then
`lowerSimpleExtension K` is proper. -/
theorem isProper_lowerSimpleExtension_of_finite (hC : C.Nonempty) (hD : D.Nonempty)
    (hbot_irrefl : ¬ ((⊥ : β) < ⊥)) (htop_irrefl : ¬ ((⊤ : β) < ⊤))
    (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    IsProper (lowerSimpleExtension K) := by
  intro hK
  letI : Nonempty V := ⟨Classical.choose hD⟩
  refine (isProper_iff _).2 ?_
  refine ⟨?_, ?_⟩
  · simpa [dom₁_lowerSimpleExtension_eq_of_finite (K := K) hbot_irrefl hbot_top hK] using hC
  · simpa [dom₂_lowerSimpleExtension_eq_of_finite (K := K) hC htop_irrefl hbot_top hK] using hD

-- Proof sketch: unfold `SaddleFunction.dom₁` and `Bifunction.upperSimpleExtension`. If `u ∈ C`,
-- each second-variable value is either finite by `hK` or `⊤`, hence strictly above `⊥`. If
-- `u ∉ C`, choose `v ∈ D` from `hD`; the upper simple extension takes value `⊥` at `(u, v)`.
/-- Primitive domain-layer form of Text 34.1.7: if `K` is finite-valued on `C × D` and `D` is
nonempty, then the first-coordinate domain of its upper simple extension is exactly `C`. -/
theorem dom₁_upperSimpleExtension_eq_of_finite (hD : D.Nonempty)
    (hbot_irrefl : ¬ ((⊥ : β) < ⊥)) (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    dom₁ (upperSimpleExtension K) = C := by
  intro hK
  ext u
  constructor
  · intro hu
    by_contra huc
    rcases hD with ⟨v, hv⟩
    have hbot : upperSimpleExtension K u v = ⊥ := by
      simp [upperSimpleExtension, huc, hv]
    exact hbot_irrefl (by simpa [hbot] using hu v)
  · intro hu v
    by_cases hv : v ∈ D
    · simpa [upperSimpleExtension, hu, hv] using (hK ⟨u, hu⟩ ⟨v, hv⟩).1
    · simpa [upperSimpleExtension, hv] using hbot_top

-- Proof sketch: unfold `SaddleFunction.dom₂` and `Bifunction.upperSimpleExtension`. If `v ∈ D`,
-- every first-variable value is either finite by `hK` or `⊥`, so it is strictly below `⊤`;
-- if `v ∉ D`, the extension is identically `⊤` in the first variable.
/-- Primitive domain-layer form of Text 34.1.7: if `K` is finite-valued on `C × D`, then the
second-coordinate domain of its upper simple extension is exactly `D`, provided `U` is nonempty. -/
theorem dom₂_upperSimpleExtension_eq_of_finite [Nonempty U]
    (htop_irrefl : ¬ ((⊤ : β) < ⊤)) (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    dom₂ (upperSimpleExtension K) = D := by
  intro hK
  ext v
  constructor
  · intro hv
    by_contra hvD
    let u : U := Classical.choice ‹Nonempty U›
    have htop : upperSimpleExtension K u v = ⊤ := by
      simp [upperSimpleExtension, hvD]
    exact htop_irrefl (by simpa [htop] using hv u)
  · intro hv u
    by_cases hu : u ∈ C
    · simpa [upperSimpleExtension, hu, hv] using (hK ⟨u, hu⟩ ⟨v, hv⟩).2
    · simpa [upperSimpleExtension, hu, hv] using hbot_top

-- Proof sketch: combine the two preceding upper-extension coordinate-domain formulas with the
-- product definition of `SaddleFunction.dom`.
/-- Primitive domain-layer form of Text 34.1.7 for the upper simple extension:
if `K` is finite-valued on `C × D` and `D` is nonempty, then its effective domain is `C ×ˢ D`. -/
theorem dom_upperSimpleExtension_eq_of_finite (hD : D.Nonempty)
    (hbot_irrefl : ¬ ((⊥ : β) < ⊥)) (htop_irrefl : ¬ ((⊤ : β) < ⊤))
    (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    dom (upperSimpleExtension K) = C ×ˢ D := by
  intro hK
  ext p
  constructor
  · intro hp
    rcases mem_dom.mp hp with ⟨hu, hv⟩
    haveI : Nonempty U := ⟨p.1⟩
    refine ⟨?_, ?_⟩
    · simpa [dom₁_upperSimpleExtension_eq_of_finite (K := K) hD hbot_irrefl hbot_top hK] using hu
    · simpa [dom₂_upperSimpleExtension_eq_of_finite (K := K) htop_irrefl hbot_top hK] using hv
  · rintro ⟨hu, hv⟩
    refine mem_dom.mpr ?_
    constructor
    · simpa [dom₁_upperSimpleExtension_eq_of_finite (K := K) hD hbot_irrefl hbot_top hK] using hu
    · haveI : Nonempty U := ⟨p.1⟩
      have hp₂ : p.2 ∈ dom₂ (upperSimpleExtension K) := by
        simpa [dom₂_upperSimpleExtension_eq_of_finite (K := K) htop_irrefl hbot_top hK] using hv
      exact hp₂

-- Proof sketch: use the preceding effective-domain identity and the nonemptiness of both factors
-- to produce a point of `C ×ˢ D`, hence a point of the effective domain.
/-- Primitive properness-layer form of Text 34.1.7 for the upper simple extension:
if `K` is finite-valued on `C × D` and both factors are nonempty, then
`upperSimpleExtension K` is proper. -/
theorem isProper_upperSimpleExtension_of_finite (hC : C.Nonempty) (hD : D.Nonempty)
    (hbot_irrefl : ¬ ((⊥ : β) < ⊥)) (htop_irrefl : ¬ ((⊤ : β) < ⊤))
    (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    IsProper (upperSimpleExtension K) := by
  intro hK
  letI : Nonempty U := ⟨Classical.choose hC⟩
  refine (isProper_iff _).2 ?_
  refine ⟨?_, ?_⟩
  · simpa [dom₁_upperSimpleExtension_eq_of_finite (K := K) hD hbot_irrefl hbot_top hK] using hC
  · simpa [dom₂_upperSimpleExtension_eq_of_finite (K := K) htop_irrefl hbot_top hK] using hD

end FiniteValuedSimpleExtension

private theorem withBotTop_not_bot_lt_bot :
    ¬ ((⊥ : WithBotTop α) < ⊥) := by
  intro h
  cases h

private theorem withBotTop_not_top_lt_top :
    ¬ ((⊤ : WithBotTop α) < ⊤) := by
  intro h
  cases h with
  | coe_lt_coe h' =>
      cases h'

private theorem withBotTop_bot_lt_top :
    (⊥ : WithBotTop α) < ⊤ :=
  WithBot.bot_lt_coe (⊤ : WithTop α)

private theorem toWithBotTop_isFinite (J : C → D → α) :
    ∀ u : C, ∀ v : D,
      (⊥ : WithBotTop α) < toWithBotTop J u v ∧ toWithBotTop J u v < ⊤ := by
  intro u v
  constructor
  · change (⊥ : WithBotTop α) < ((J u v : α) : WithBotTop α)
    exact WithBot.bot_lt_coe ((J u v : α) : WithTop α)
  · simpa [toWithBotTop_apply] using
      (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top (J u v)))

section LowerSimpleExtension

variable (J : C → D → α)

/-- Text 34.1.7: the first-coordinate domain of the lower simple extension of a finite kernel
`J : C → D → α` is exactly `C`, provided the second ambient variable type is nonempty. -/
theorem dom₁_lowerSimpleExtension_eq [Nonempty V] :
    dom₁ (lowerSimpleExtension (toWithBotTop J)) = C := by
  simpa using
    (dom₁_lowerSimpleExtension_eq_of_finite
      (K := toWithBotTop J) withBotTop_not_bot_lt_bot withBotTop_bot_lt_top
      (toWithBotTop_isFinite J))

/-- If `C` is nonempty, then the second-coordinate domain of the lower simple extension of `J`
is exactly `D`. -/
theorem dom₂_lowerSimpleExtension_eq (hC : C.Nonempty) :
    dom₂ (lowerSimpleExtension (toWithBotTop J)) = D := by
  simpa using
    (dom₂_lowerSimpleExtension_eq_of_finite
      (K := toWithBotTop J) hC withBotTop_not_top_lt_top withBotTop_bot_lt_top
      (toWithBotTop_isFinite J))

/-- If `C` is nonempty, the effective domain of the lower simple extension of `J` is the product
set `C ×ˢ D`. -/
theorem dom_lowerSimpleExtension_eq (hC : C.Nonempty) :
    dom (lowerSimpleExtension (toWithBotTop J)) = C ×ˢ D := by
  simpa using
    (dom_lowerSimpleExtension_eq_of_finite
      (K := toWithBotTop J) hC withBotTop_not_bot_lt_bot withBotTop_not_top_lt_top
      withBotTop_bot_lt_top (toWithBotTop_isFinite J))

/-- If `C` and `D` are nonempty, the lower simple extension of `J` is proper. -/
theorem isProper_lowerSimpleExtension (hC : C.Nonempty) (hD : D.Nonempty) :
    IsProper (lowerSimpleExtension (toWithBotTop J)) := by
  simpa using
    (isProper_lowerSimpleExtension_of_finite
      (K := toWithBotTop J) hC hD withBotTop_not_bot_lt_bot withBotTop_not_top_lt_top
      withBotTop_bot_lt_top (toWithBotTop_isFinite J))

end LowerSimpleExtension

section UpperSimpleExtension

variable (J : C → D → α)

/-- If `D` is nonempty, then the first-coordinate domain of the upper simple extension of `J` is
exactly `C`. -/
theorem dom₁_upperSimpleExtension_eq (hD : D.Nonempty) :
    dom₁ (upperSimpleExtension (toWithBotTop J)) = C := by
  simpa using
    (dom₁_upperSimpleExtension_eq_of_finite
      (K := toWithBotTop J) hD withBotTop_not_bot_lt_bot withBotTop_bot_lt_top
      (toWithBotTop_isFinite J))

/-- The second-coordinate domain of the upper simple extension of a finite kernel `J : C → D → α`
is exactly `D`, provided the first ambient variable type is nonempty. -/
theorem dom₂_upperSimpleExtension_eq [Nonempty U] :
    dom₂ (upperSimpleExtension (toWithBotTop J)) = D := by
  simpa using
    (dom₂_upperSimpleExtension_eq_of_finite
      (K := toWithBotTop J) withBotTop_not_top_lt_top withBotTop_bot_lt_top
      (toWithBotTop_isFinite J))

/-- If `D` is nonempty, the effective domain of the upper simple extension of `J` is the product
set `C ×ˢ D`. -/
theorem dom_upperSimpleExtension_eq (hD : D.Nonempty) :
    dom (upperSimpleExtension (toWithBotTop J)) = C ×ˢ D := by
  simpa using
    (dom_upperSimpleExtension_eq_of_finite
      (K := toWithBotTop J) hD withBotTop_not_bot_lt_bot withBotTop_not_top_lt_top
      withBotTop_bot_lt_top (toWithBotTop_isFinite J))

/-- If `C` and `D` are nonempty, the upper simple extension of `J` is proper. -/
theorem isProper_upperSimpleExtension (hC : C.Nonempty) (hD : D.Nonempty) :
    IsProper (upperSimpleExtension (toWithBotTop J)) := by
  simpa using
    (isProper_upperSimpleExtension_of_finite
      (K := toWithBotTop J) hC hD withBotTop_not_bot_lt_bot withBotTop_not_top_lt_top
      withBotTop_bot_lt_top (toWithBotTop_isFinite J))

end UpperSimpleExtension

end

end Bifunction

/-! ### Text_34_1_8 (from Chap07) -/
noncomputable section

universe u v w z

open scoped Rockafellar
open SaddleFunction

namespace Bifunction

section

variable {R : Type z} {α : Type w} {U : Type u} {V : Type v}
variable [Semiring R] [PartialOrder R]
variable [AddCommMonoid U] [SMul R U] [TopologicalSpace U]
variable [AddCommMonoid V] [SMul R V] [TopologicalSpace V]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [AddCommGroup α] [SMul R α]

attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.8 states that a finite saddle-function on a nonempty product
  domain `C × D` has equivalent lower and upper ambient extensions; the convexity of `C` and `D`
  is already encoded by the slice owners inside `IsSaddleOn` once the domains are nonempty.
- `core/canonical`: the theorem uses the Chapter 34 equivalence relation `K ∼ L` from
  `Defn_34_4`.
- `bridge/view`: the theorem surface uses the textbook Chapter 34 extension notation
  `K₁[J | C, D]` and `K₂[J | C, D]`, avoiding re-expansion of restricted kernel lambdas.

Domain-style sampling used here:
- `SaddleFunction.IsSaddleOn R C D J`;
- the primitive branch owners `SaddleFunction.IsConcaveConvexOn R C D J` and
  `SaddleFunction.IsConvexConcaveOn R C D J`;
- the source extension notation `K₁[· | ·, ·]` and `K₂[· | ·, ·]`;
- source notation `K ∼ L` for equality of Chapter 34 closure pairs.

Layer target: `source-facing`. The theorem keeps the textbook lower/upper extension semantics on
the short canonical bridge owners, avoiding theorem-surface lambda noise. The primitive branch
owners are surfaced directly, and the disjunctive saddle owner is kept as a thin wrapper.
-/

-- Proof sketch: compare the two canonical ambient bridge extensions of a finite saddle kernel on
-- `C × D` in the Chapter 34 equivalence relation.
/-- Text 34.1.8: if `J` is a finite saddle-function on a nonempty product domain `C × D` at
scalar layer `R`,
then its canonical lower and upper ambient bridge extensions are equivalent in the Chapter 34 sense
`∼`. -/
theorem saddleExtension_equivalent_upperBoundaryExtension_of_isSaddleOn
    {C : Set U} {D : Set V} {J : U → V → α}
    (hCD_nonempty : (C ×ˢ D).Nonempty)
    (hJ : IsSaddleOn R C D J) :
    K₁[J | C, D] ∼ K₂[J | C, D] := by
  sorry

end

end Bifunction

/-! ### Text_34_1_9 (from Chap07) -/
/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.9 identifies closed saddle-functions by the two mixed closure
  identities `cl₁ (cl₂ K) = cl₁ K` and `cl₂ (cl₁ K) = cl₂ K`.
- `core/canonical`: the natural owner abstraction is the Chapter 34 closedness predicate
  `SaddleFunction.IsClosed` together with its canonical characterization theorem
  `SaddleFunction.isClosed_iff`.
- `bridge/view`: this item is therefore a pure recall of that canonical owner theorem, rather than
  a second local reconstruction of the partial-closure operators or equivalence relation.

Primary mathematical domain:
- saddle-functions, partial closures, and closedness in minimax theory.

Domain-style sampling used here:
- `Bifunction.closure1` and `Bifunction.closure2` from `Chap07.Definition33_0_4`;
- `SaddleFunction.IsClosed` from `Chap07.Defn_34_2`;
- `SaddleFunction.isClosed_iff` from `Chap07.Defn_34_2`.

Primitive data vs derived API:
- primitive source datum: a bifunction `K : U → X → WithBotTop 𝕜`;
- primitive owner layer already provided upstream: the partial closures `cl₁`, `cl₂` and the
  closedness predicate `SaddleFunction.IsClosed` on the canonical extended codomain layer;
- derived API for this item: the mixed-closure characterization of that owner predicate.

Layer target: `bridge/view`, via direct reuse of the existing canonical Chapter 34 theorem.
-/

/- Text 34.1.9: the Chapter 34 closedness criterion says that a saddle-function is closed exactly
when the mixed closure identities `cl₁ (cl₂ K) = cl₁ K` and `cl₂ (cl₁ K) = cl₂ K` hold. -/
recall SaddleFunction.isClosed_iff
