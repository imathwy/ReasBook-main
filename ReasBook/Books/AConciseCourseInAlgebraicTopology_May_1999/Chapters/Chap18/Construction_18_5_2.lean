import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Topology.CWComplex.Classical.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Definition_18_5_1

open scoped TopCat Topology Topology.Homotopy
open Path.Homotopic.Quotient

noncomputable section

universe u v

-- Semantic recall via `lean_leansearch`: `Topology.RelCWComplex.cell`,
-- `Topology.RelCWComplex.skeleton`, `sphereBasepoint`, and the Chapter 9
-- Section 9.5 sphere-fiber owner provide the source-facing boundary-map model.
-- This file keeps the explicit cube/sphere-model comparison private, but
-- exports the resulting cellwise boundary-sphere map and obstruction cochain
-- in that Chapter 9 owner. The simple-space condition is then recorded through
-- path-independence of the transport to the fixed basepoint.

section

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {Y : Type v} [TopologicalSpace Y]
  [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y]
variable (C : Set X) {D : Set X} [Topology.RelCWComplex C D]

/-- The boundary sphere in the cube model used by `RelCWComplex.map`. -/
private abbrev cubeBoundary (n : ℕ) :=
  Metric.sphere (0 : Fin (n + 1) → ℝ) 1

/-- The Euclidean sphere model underlying `𝕊 n`. -/
private abbrev sphereModel (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The chosen homeomorphism from `𝕊 n` to the Euclidean sphere model. -/
private abbrev sphereModelHomeomorph (n : ℕ) : (𝕊 n : TopCat.{v}) ≃ₜ sphereModel n :=
  Homeomorph.ulift

/-- Boundary points map to nonzero vectors in the Euclidean sphere model. -/
private theorem cubeBoundary_toLp_ne_zero (n : ℕ) (x : cubeBoundary n) :
    (WithLp.toLp 2 (x : Fin (n + 1) → ℝ) : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := by
  rcases x with ⟨x, hx_mem⟩
  intro hx
  have hx0 : (x : Fin (n + 1) → ℝ) = 0 := by
    simpa using congrArg (WithLp.ofLp) hx
  have hdist : ‖x - 0‖ = 1 := by
    rwa [Metric.mem_sphere, dist_eq_norm] at hx_mem
  have hnorm : ‖(x : Fin (n + 1) → ℝ)‖ = 1 := by
    simpa using hdist
  rw [hx0, norm_zero] at hnorm
  norm_num at hnorm

/-- Sphere-model points have nonzero coordinate representatives. -/
private theorem sphereModel_ofLp_ne_zero (n : ℕ) (x : sphereModel n) :
    ((x.1).ofLp : Fin (n + 1) → ℝ) ≠ 0 := by
  rcases x with ⟨x, hx_mem⟩
  intro hx
  have hx0 : (x : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
    simpa using congrArg (WithLp.toLp 2) hx
  have hdist : ‖x - 0‖ = 1 := by
    rwa [Metric.mem_sphere, dist_eq_norm] at hx_mem
  have hnorm : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa using hdist
  rw [hx0, norm_zero] at hnorm
  norm_num at hnorm

/-- The cube-boundary model used by `RelCWComplex.map` is homeomorphic to the
Euclidean-sphere model underlying `𝕊 n`. The data are explicit; only the
homeomorphism laws and continuity are deferred. -/
private noncomputable def cubeBoundaryHomeomorphSphereModel (n : ℕ) :
    cubeBoundary n ≃ₜ sphereModel n where
  toFun x :=
    let y : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (x : Fin (n + 1) → ℝ)
    let hy : y ≠ 0 := cubeBoundary_toLp_ne_zero n x
    (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin (n + 1))) ⟨y, hy⟩).1
  invFun x :=
    let y : Fin (n + 1) → ℝ := x.1.ofLp
    let hy : y ≠ 0 := sphereModel_ofLp_ne_zero n x
    (homeomorphUnitSphereProd (Fin (n + 1) → ℝ) ⟨y, hy⟩).1
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

/-- The sphere map into the cube-boundary model for the chosen sphere presentation. -/
private noncomputable def sphereToCubeBoundaryMap (n : ℕ) :
    C((𝕊 n : TopCat.{v}), cubeBoundary n) :=
  ⟨fun s ↦
      (cubeBoundaryHomeomorphSphereModel n).symm ((sphereModelHomeomorph n) s),
    (cubeBoundaryHomeomorphSphereModel n).symm.continuous_toFun.comp
      (sphereModelHomeomorph n).continuous_toFun⟩

/-- Boundary points also lie in the corresponding closed ball. -/
private theorem cubeBoundary_mem_closedBall (n : ℕ) (x : cubeBoundary n) :
    x.1 ∈ Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 :=
  Metric.sphere_subset_closedBall x.2

/-- The boundary sphere includes into the corresponding closed ball. -/
private def cubeBoundaryInclusion (n : ℕ) :
    C(cubeBoundary n, Metric.closedBall (0 : Fin (n + 1) → ℝ) 1) where
  toFun x := ⟨x.1, cubeBoundary_mem_closedBall n x⟩
  continuous_toFun := sorry

/-- The characteristic map of a cell restricted to the closed ball model. -/
private def cellCharacteristicClosedBallMap (n : ℕ)
    (j : Topology.RelCWComplex.cell C (n + 1)) :
    C(Metric.closedBall (0 : Fin (n + 1) → ℝ) 1, X) where
  toFun x := Topology.RelCWComplex.map (n + 1) j x.1
  continuous_toFun := sorry

/-- The boundary sphere of a cell as a map into the ambient complex. -/
private def cellBoundaryMapToComplex (n : ℕ)
    (j : Topology.RelCWComplex.cell C (n + 1)) : C((𝕊 n : TopCat.{v}), X) :=
  (cellCharacteristicClosedBallMap C n j).comp
    ((cubeBoundaryInclusion n).comp (sphereToCubeBoundaryMap n))

/-- The boundary map of a cell lands in the `n`-skeleton. -/
private theorem cellBoundaryMapToComplex_mem_skeleton (n : ℕ)
    (j : Topology.RelCWComplex.cell C (n + 1)) (s : (𝕊 n : TopCat.{v})) :
    cellBoundaryMapToComplex C n j s ∈ Topology.RelCWComplex.skeleton C n := sorry

/-- The boundary of an `(n + 1)`-cell, viewed as a map `𝕊 n ⟶ skeleton C n` using the chosen
characteristic map and the inclusion `cellFrontier (n + 1) j ⊆ skeleton C n`. -/
private def cellBoundarySphereMap (n : ℕ) (j : Topology.RelCWComplex.cell C (n + 1)) :
    C((𝕊 n : TopCat.{v}), Topology.RelCWComplex.skeleton C n) where
  toFun s :=
    ⟨cellBoundaryMapToComplex C n j s, cellBoundaryMapToComplex_mem_skeleton C n j s⟩
  continuous_toFun := sorry

/-- The boundary sphere map of an `(n + 1)`-cell after applying
`f : skeleton C n → Y`. -/
def obstructionSphereMap (n : ℕ)
    (f : ContinuousMap (Topology.RelCWComplex.skeleton C n) Y)
    (j : Topology.RelCWComplex.cell C (n + 1)) : C((𝕊 n : TopCat.{v}), Y) :=
  f.comp (cellBoundarySphereMap C n j)

/-- The boundary sphere map lies in the fiber over its value at `sphereBasepoint n`. -/
theorem obstructionSphereMap_mem_sphereBasepointFiber (n : ℕ)
    (f : ContinuousMap (Topology.RelCWComplex.skeleton C n) Y)
    (j : Topology.RelCWComplex.cell C (n + 1)) :
    obstructionSphereMap C n f j ∈
      sphereBasepointFiber n ((obstructionSphereMap C n f j) (sphereBasepoint n)) := sorry

/-- The path-component class of the `j`th boundary sphere map in the explicit sphere-evaluation
fiber owner from Construction 9.5.1. -/
private def obstructionFiberClass (n : ℕ)
    (f : ContinuousMap (Topology.RelCWComplex.skeleton C n) Y)
    (j : Topology.RelCWComplex.cell C (n + 1)) :
    ZerothHomotopy
      (sphereBasepointFiber
        n ((obstructionSphereMap C n f j) (sphereBasepoint n))) :=
  let g : C((𝕊 n : TopCat.{v}), Y) := obstructionSphereMap C n f j
  Quotient.mk (pathSetoid _) ⟨g, rfl⟩

private theorem sphereBasepointFiberTransport_indep
    (n : ℕ) [SimpleSpace Y] {y y₀ : Y}
    (α β : Path.Homotopic.Quotient y y₀)
    (η : ZerothHomotopy (sphereBasepointFiber n y)) :
    sphereBasepointFiberZerothEquivOfPathClass n α η =
      sphereBasepointFiberZerothEquivOfPathClass n β η := sorry

/-- The obstruction value of the `j`th boundary sphere map after transport to the fixed basepoint
`y₀` along a specified path class. This keeps the Chapter 9 sphere-fiber owner
`ZerothHomotopy (sphereBasepointFiber n y₀)` as the public target surface. -/
def obstructionValueOfPathClass (n : ℕ) (y₀ : Y)
    (f : ContinuousMap (Topology.RelCWComplex.skeleton C n) Y)
    (j : Topology.RelCWComplex.cell C (n + 1))
    (α : Path.Homotopic.Quotient
      ((obstructionSphereMap C n f j) (sphereBasepoint n)) y₀) :
    ZerothHomotopy (sphereBasepointFiber n y₀) :=
  sphereBasepointFiberZerothEquivOfPathClass n α (obstructionFiberClass C n f j)

/-- For a simple target, the transported obstruction value is independent of the path class used
to move the cellwise basepoint to `y₀`. -/
theorem obstructionValueOfPathClass_eq (n : ℕ) [SimpleSpace Y] (y₀ : Y)
    (f : ContinuousMap (Topology.RelCWComplex.skeleton C n) Y)
    (j : Topology.RelCWComplex.cell C (n + 1))
    (α β : Path.Homotopic.Quotient
      ((obstructionSphereMap C n f j) (sphereBasepoint n)) y₀) :
    obstructionValueOfPathClass C n y₀ f j α =
      obstructionValueOfPathClass C n y₀ f j β :=
  sphereBasepointFiberTransport_indep n α β (obstructionFiberClass C n f j)

/-- The obstruction cochain determined by an explicit choice of path class for each cellwise
basepoint. -/
def obstructionCochainOfPathChoice (n : ℕ) (y₀ : Y)
    (f : ContinuousMap (Topology.RelCWComplex.skeleton C n) Y)
    (α :
      ∀ j : Topology.RelCWComplex.cell C (n + 1),
        Path.Homotopic.Quotient
          ((obstructionSphereMap C n f j) (sphereBasepoint n)) y₀) :
    Topology.RelCWComplex.cell C (n + 1) →
      ZerothHomotopy (sphereBasepointFiber n y₀) :=
  fun j ↦ obstructionValueOfPathClass C n y₀ f j (α j)

/-- Applying `obstructionCochainOfPathChoice` to a cell uses the chosen path class attached to
that cell. -/
theorem obstructionCochainOfPathChoice_apply (n : ℕ) (y₀ : Y)
    (f : ContinuousMap (Topology.RelCWComplex.skeleton C n) Y)
    (α :
      ∀ j : Topology.RelCWComplex.cell C (n + 1),
        Path.Homotopic.Quotient
          ((obstructionSphereMap C n f j) (sphereBasepoint n)) y₀)
    (j : Topology.RelCWComplex.cell C (n + 1)) :
    obstructionCochainOfPathChoice C n y₀ f α j =
      obstructionValueOfPathClass C n y₀ f j (α j) :=
  rfl

/-- Construction 18.5.2: for a map `f : skeleton C n → Y` from the `n`-skeleton of a relative
CW complex to a path-connected target with fixed basepoint `y₀ : Y`, choose for each
`(n + 1)`-cell the path class from the cellwise basepoint of its boundary sphere map to `y₀`
coming from `PathConnectedSpace.somePath`. The resulting cochain takes values in the Chapter 9
sphere-fiber owner of `π_ n(Y, y₀)`. The simple-space condition enters through the companion
path-independence lemmas, not through the data of this chosen representative. -/
noncomputable def obstructionCochain (n : ℕ) [PathConnectedSpace Y] (y₀ : Y)
    (f : ContinuousMap (Topology.RelCWComplex.skeleton C n) Y) :
    Topology.RelCWComplex.cell C (n + 1) →
      ZerothHomotopy (sphereBasepointFiber n y₀) :=
  obstructionCochainOfPathChoice C n y₀ f fun j ↦
    mk (PathConnectedSpace.somePath
      ((obstructionSphereMap C n f j) (sphereBasepoint n)) y₀)

/-- Applying `obstructionCochain` to a cell uses the Chapter 9 transport along the chosen path
class `mk (PathConnectedSpace.somePath _ y₀)` from the cellwise basepoint to `y₀`. -/
theorem obstructionCochain_apply (n : ℕ) [PathConnectedSpace Y]
    (y₀ : Y)
    (f : ContinuousMap (Topology.RelCWComplex.skeleton C n) Y)
    (j : Topology.RelCWComplex.cell C (n + 1)) :
    obstructionCochain C n y₀ f j =
      obstructionValueOfPathClass C n y₀ f j
        (mk (PathConnectedSpace.somePath
          ((obstructionSphereMap C n f j) (sphereBasepoint n)) y₀)) :=
  rfl

/-- For a simple target, the chosen-path formula for `obstructionCochain` agrees with transport
along any prescribed path class from the cellwise basepoint to `y₀`. -/
theorem obstructionCochain_apply_eq_of_pathClass
    (n : ℕ) [PathConnectedSpace Y] [SimpleSpace Y] (y₀ : Y)
    (f : ContinuousMap (Topology.RelCWComplex.skeleton C n) Y)
    (j : Topology.RelCWComplex.cell C (n + 1))
    (α : Path.Homotopic.Quotient
      ((obstructionSphereMap C n f j) (sphereBasepoint n)) y₀) :
    obstructionCochain C n y₀ f j = obstructionValueOfPathClass C n y₀ f j α := by
  rw [obstructionCochain_apply]
  exact obstructionValueOfPathClass_eq C n y₀ f j _ α

/-- For a simple target, the cochain obtained from `PathConnectedSpace.somePath` agrees with the
cochain obtained from any other family of path classes to `y₀`. -/
theorem obstructionCochain_eq_of_pathChoice
    (n : ℕ) [PathConnectedSpace Y] [SimpleSpace Y] (y₀ : Y)
    (f : ContinuousMap (Topology.RelCWComplex.skeleton C n) Y)
    (α :
      ∀ j : Topology.RelCWComplex.cell C (n + 1),
        Path.Homotopic.Quotient
          ((obstructionSphereMap C n f j) (sphereBasepoint n)) y₀) :
    obstructionCochain C n y₀ f = obstructionCochainOfPathChoice C n y₀ f α := by
  funext j
  exact obstructionCochain_apply_eq_of_pathClass C n y₀ f j (α j)

end
