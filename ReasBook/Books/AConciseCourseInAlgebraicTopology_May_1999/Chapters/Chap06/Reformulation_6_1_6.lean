import Mathlib.Topology.CompactOpen
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4

open scoped unitInterval
open ContinuousMap

universe u v w

variable {A : Type u} {X : Type v} [TopologicalSpace A] [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: mathlib's compact-open evaluation API makes evaluation
-- at a fixed time a bundled continuous map on `C(I, Y)`, while `IsCofibration` remains the
-- source-faithful owner for Chapter 6.

/-- Evaluating a path at time `t` gives a bundled map `C(I, Y) ⟶ Y`. -/
def pathSpaceEvalAt (t : I) (Y : Type w) [TopologicalSpace Y] : C(C(I, Y), Y) where
  toFun γ := γ t
  continuous_toFun := continuous_eval_const t

/-- Evaluating `pathSpaceEvalAt t` on a path returns its value at time `t`. -/
@[simp] theorem pathSpaceEvalAt_apply {Y : Type w} [TopologicalSpace Y] (t : I) (γ : C(I, Y)) :
    pathSpaceEvalAt t Y γ = γ t := rfl

/-- The path-space projection `p₀ : C(I, Y) → Y` evaluating a path at time `0`. -/
abbrev pathSpaceEvalAtZero (Y : Type w) [TopologicalSpace Y] : C(C(I, Y), Y) :=
  pathSpaceEvalAt 0 Y

/-- Evaluating `pathSpaceEvalAtZero` on a path returns its value at time `0`. -/
@[simp] theorem pathSpaceEvalAtZero_apply {Y : Type w} [TopologicalSpace Y] (γ : C(I, Y)) :
    pathSpaceEvalAtZero Y γ = γ 0 := rfl

namespace ContinuousMap.Homotopy

variable {Y : Type w} [TopologicalSpace Y] {f₀ f₁ : C(A, Y)}

/-- A homotopy `f₀ ≃ f₁` determines a map `A ⟶ C(I, Y)` by following each point of `A`
through the homotopy. -/
def toPathSpaceMap (H : f₀.Homotopy f₁) : C(A, C(I, Y)) :=
  (H.toContinuousMap.comp ContinuousMap.prodSwap).curry

/-- Evaluating the path attached to `a : A` at time `t` recovers the original homotopy value
`H (t, a)`. -/
@[simp] theorem toPathSpaceMap_apply (H : f₀.Homotopy f₁) (a : A) (t : I) :
    H.toPathSpaceMap a t = H (t, a) := rfl

/-- Evaluating the path-space map attached to a homotopy at time `t` recovers the `t`-slice of
the homotopy. -/
@[simp] theorem pathSpaceEvalAt_comp_toPathSpaceMap (H : f₀.Homotopy f₁) (t : I) :
    (pathSpaceEvalAt t Y).comp H.toPathSpaceMap = H.curry t := by
  ext a
  rfl

/-- Evaluating the path-space map attached to a homotopy at time `0` recovers its initial map. -/
@[simp] theorem pathSpaceEvalAtZero_comp_toPathSpaceMap (H : f₀.Homotopy f₁) :
    (pathSpaceEvalAtZero Y).comp H.toPathSpaceMap = f₀ := by
  ext a
  simp [pathSpaceEvalAtZero, pathSpaceEvalAt]

/-- A map `A ⟶ C(I, Y)` with prescribed values at `0` and `1` determines a homotopy from its
initial endpoint map to its terminal endpoint map. -/
def ofPathSpaceMap (d : C(A, C(I, Y))) (h₀ : (pathSpaceEvalAt 0 Y).comp d = f₀)
    (h₁ : (pathSpaceEvalAt 1 Y).comp d = f₁) : f₀.Homotopy f₁ where
  toContinuousMap := d.uncurry.comp ContinuousMap.prodSwap
  map_zero_left := by
    intro a
    simpa [pathSpaceEvalAt] using ContinuousMap.congr_fun h₀ a
  map_one_left := by
    intro a
    simpa [pathSpaceEvalAt] using ContinuousMap.congr_fun h₁ a

/-- The homotopy reconstructed from a path-space map evaluates by applying that path-space map. -/
@[simp] theorem ofPathSpaceMap_apply (d : C(A, C(I, Y))) (h₀ : (pathSpaceEvalAt 0 Y).comp d = f₀)
    (h₁ : (pathSpaceEvalAt 1 Y).comp d = f₁) (t : I) (a : A) :
    ofPathSpaceMap d h₀ h₁ (t, a) = d a t := rfl

end ContinuousMap.Homotopy

/-- Reformulation 6.1.6. Using the path-space projection `p₀ : C(I, Y) → Y`, a map `i : A → X`
is a cofibration exactly when every commutative square
`pathSpaceEvalAtZero Y ∘ d = f₀ ∘ i`
admits a lift `D : C(X, C(I, Y))`. -/
theorem isCofibration_iff_lift_pathSpaceEvalAtZero {i : C(A, X)} :
    IsCofibration.{u, v, w} i ↔
      ∀ ⦃Y : Type w⦄ [TopologicalSpace Y] (f₀ : C(X, Y)) (d : C(A, C(I, Y))),
        (pathSpaceEvalAtZero Y).comp d = f₀.comp i →
          ∃ D : C(X, C(I, Y)),
            D.comp i = d ∧ (pathSpaceEvalAtZero Y).comp D = f₀ := by
  constructor
  · intro hi Y _ f₀ d hd
    let H : (f₀.comp i).Homotopy ((pathSpaceEvalAt 1 Y).comp d) :=
      ContinuousMap.Homotopy.ofPathSpaceMap d hd rfl
    obtain ⟨_, F, hF⟩ := hi f₀ ((pathSpaceEvalAt 1 Y).comp d) H
    refine ⟨F.toPathSpaceMap, ?_, ?_⟩
    · ext a t
      exact hF (t, a)
    · exact F.pathSpaceEvalAtZero_comp_toPathSpaceMap
  · intro h Y _ f₀ g H
    obtain ⟨D, hD, hD₀⟩ :=
      h f₀ H.toPathSpaceMap H.pathSpaceEvalAtZero_comp_toPathSpaceMap
    refine ⟨(pathSpaceEvalAt 1 Y).comp D, ContinuousMap.Homotopy.ofPathSpaceMap D hD₀ rfl, ?_⟩
    intro z
    rcases z with ⟨t, a⟩
    have hDa : D (i a) t = H.toPathSpaceMap a t :=
      ContinuousMap.congr_fun (ContinuousMap.congr_fun hD a) t
    simpa using hDa
