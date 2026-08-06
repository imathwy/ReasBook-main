import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_6_6

open Set
open scoped unitInterval Topology.Homotopy

universe u v

variable {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]

-- Semantic recall via `lean_leansearch`: no direct mathlib owner surfaced for the excisive-triad
-- boundary-collar reduction, so this file adds the explicit neighborhood-lift datum on `D^(n+1)`
-- near `S^n` as a thin companion to `HasSphereConeHelp`.

/-- The canonical inclusion of `S^n` into an open subset `U ⊆ D^(n+1)` that contains the image of
`sphereBoundaryInclusion n`. -/
def sphereBoundaryNeighborhoodInclusion (n : ℕ) {U : Set (unitDisk n)}
    (hU : Set.range (sphereBoundaryInclusion n) ⊆ U) : C(sphereBoundary n, U) where
  toFun x := ⟨sphereBoundaryInclusion n x, hU ⟨x, rfl⟩⟩
  continuous_toFun := (sphereBoundaryInclusion n).continuous.subtype_mk fun x ↦ hU ⟨x, rfl⟩

/-- Forgetting the codomain restriction recovers `sphereBoundaryInclusion n`. -/
@[simp] theorem subtype_val_comp_sphereBoundaryNeighborhoodInclusion (n : ℕ)
    {U : Set (unitDisk n)} (hU : Set.range (sphereBoundaryInclusion n) ⊆ U) :
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, unitDisk n)).comp
      (sphereBoundaryNeighborhoodInclusion n hU)) = sphereBoundaryInclusion n :=
  rfl

/-- An open-neighborhood lift of `g : D^(n+1) → Z` near the boundary sphere `S^n`, expressed using
the canonical inclusion `S^n ↪ U` for an open neighborhood `U` of the boundary image. -/
def HasBoundaryNeighborhoodLift (n : ℕ) (e : C(Y, Z)) (f : C(sphereBoundary n, Y))
    (g : C(unitDisk n, Z)) : Prop :=
  ∃ U : Set (unitDisk n), IsOpen U ∧
    ∃ hU : Set.range (sphereBoundaryInclusion n) ⊆ U,
      ∃ gU : C(U, Y),
        e.comp gU = ContinuousMap.restrict U g ∧
          gU.comp (sphereBoundaryNeighborhoodInclusion n hU) = f

/-- ProofStep 10.7.11: in the excisive-triad theorem, a boundary-collar deformation lets one
reduce the HELP problem for `e` to the case where the lift is already defined on an open
neighborhood of the boundary sphere. Here that reduction is encoded by a hypothesis producing
`HasBoundaryNeighborhoodLift n e f g` for each boundary datum. -/
theorem HasSphereConeHelp.of_boundaryNeighborhoodLiftReduction
    (n : ℕ) (e : C(Y, Z))
    (hSolveNearBoundary :
      ∀ (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
        (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))),
          HasBoundaryNeighborhoodLift n e f g →
            ∃ G : C(unitDisk n, Y), ∃ K : (e.comp G).Homotopy g,
              G.comp (sphereBoundaryInclusion n) = f ∧
                ∀ z : I × sphereBoundary n, K (z.1, sphereBoundaryInclusion n z.2) = H z)
    (hBoundaryCollar :
      ∀ (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z)),
        HasBoundaryNeighborhoodLift n e f g) :
    HasSphereConeHelp n e := by
  sorry
/-
  refine ⟨?_⟩
  intro f g H
  exact hSolveNearBoundary f g H (hBoundaryCollar f g)
-/
