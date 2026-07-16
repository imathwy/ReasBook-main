import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_1

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
