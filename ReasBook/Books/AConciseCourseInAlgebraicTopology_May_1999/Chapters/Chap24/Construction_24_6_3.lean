import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_6_1
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Homotopy.HSpaces

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- Semantic recall via `lean_leansearch`: `HSpace` and `HSpace.mk` are the canonical mathlib
-- owners for a multiplication-like map together with its distinguished unit and unit homotopies.
-- No verified existing Hopf-construction owner producing a map `S^(2n - 1) → S^n` surfaced in
-- the current environment, so this file packages the source-facing multiplication-like datum
-- explicitly and uses it to build the Hopf map.

/-- A multiplication-like datum on `S^(n - 1)` consists of a continuous multiplication map, a
distinguished unit point, and the left/right unit homotopies required by the source notion. -/
structure SphereMultiplicationLike (n : ℕ+) where
  /-- The source multiplication map `S^(n - 1) × S^(n - 1) → S^(n - 1)`. -/
  map :
    C(TopCat.sphere ((n : ℕ) - 1) × TopCat.sphere ((n : ℕ) - 1), TopCat.sphere ((n : ℕ) - 1))
  /-- The distinguished unit point for the multiplication-like datum. -/
  unit : TopCat.sphere ((n : ℕ) - 1)
  /-- Left multiplication by the distinguished unit is homotopic to the identity relative to
  the distinguished unit point. -/
  unit_mul_homotopy :
    (map.comp ((ContinuousMap.const _ unit).prodMk (ContinuousMap.id _))).HomotopyRel
      (ContinuousMap.id _) {unit}
  /-- Right multiplication by the distinguished unit is homotopic to the identity relative to
  the distinguished unit point. -/
  mul_unit_homotopy :
    (map.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ unit))).HomotopyRel
      (ContinuousMap.id _) {unit}

namespace SphereMultiplicationLike

/-- The distinguished unit pair is sent to the distinguished unit point. This follows from either
relative unit homotopy, so it is derived rather than stored as separate data. -/
@[simp] theorem map_unit_unit {n : ℕ+} (μ : SphereMultiplicationLike n) :
    μ.map (μ.unit, μ.unit) = μ.unit := by
  simpa using μ.unit_mul_homotopy.fst_eq_snd (by simp)

end SphereMultiplicationLike

/-- A multiplication-like datum on `S^(n - 1)` induces the corresponding `HSpace` structure. -/
instance instHSpaceSphereMultiplicationLike {n : ℕ+} (μ : SphereMultiplicationLike n) :
    HSpace (TopCat.sphere ((n : ℕ) - 1)) where
  hmul := μ.map
  e := μ.unit
  hmul_e_e := μ.map_unit_unit
  eHmul := μ.unit_mul_homotopy
  hmulE := μ.mul_unit_homotopy

/-- The canonical multiplication-like bridge associated to an `HSpace` structure on
`S^(n - 1)`. -/
def sphereMultiplicationLikeOfHSpace (n : ℕ+)
    [HSpace (TopCat.sphere ((n : ℕ) - 1))] : SphereMultiplicationLike n where
  map := HSpace.hmul
  unit := HSpace.e
  unit_mul_homotopy := HSpace.eHmul
  mul_unit_homotopy := HSpace.hmulE

/-- The bridge `sphereMultiplicationLikeOfHSpace n` reuses the ambient `HSpace` multiplication. -/
@[simp] theorem sphereMultiplicationLikeOfHSpace_map (n : ℕ+)
    [HSpace (TopCat.sphere ((n : ℕ) - 1))] :
    (sphereMultiplicationLikeOfHSpace n).map = HSpace.hmul := rfl

/-- The bridge `sphereMultiplicationLikeOfHSpace n` reuses the ambient distinguished point. -/
@[simp] theorem sphereMultiplicationLikeOfHSpace_unit (n : ℕ+)
    [HSpace (TopCat.sphere ((n : ℕ) - 1))] :
    (sphereMultiplicationLikeOfHSpace n).unit = HSpace.e := rfl

/-- The bridge `sphereMultiplicationLikeOfHSpace n` reuses the ambient left-unit homotopy. -/
@[simp] theorem sphereMultiplicationLikeOfHSpace_unit_mul_homotopy (n : ℕ+)
    [HSpace (TopCat.sphere ((n : ℕ) - 1))] :
    (sphereMultiplicationLikeOfHSpace n).unit_mul_homotopy = HSpace.eHmul := rfl

/-- The bridge `sphereMultiplicationLikeOfHSpace n` reuses the ambient right-unit homotopy. -/
@[simp] theorem sphereMultiplicationLikeOfHSpace_mul_unit_homotopy (n : ℕ+)
    [HSpace (TopCat.sphere ((n : ℕ) - 1))] :
    (sphereMultiplicationLikeOfHSpace n).mul_unit_homotopy = HSpace.hmulE := rfl

private theorem normalize_mem_metricSphere {m : ℕ}
    {v : EuclideanSpace ℝ (Fin m)} (hv : v ≠ 0) :
    NormedSpace.normalize v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 := by
  simpa [mem_sphere_zero_iff_norm] using NormedSpace.norm_normalize hv

private def spherePointOfVector {n : ℕ+} (μ : SphereMultiplicationLike n)
    (v : EuclideanSpace ℝ (Fin (n : ℕ))) : TopCat.sphere ((n : ℕ) - 1) :=
  if hv : v = 0 then
    μ.unit
  else
    let normalized : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n : ℕ))) 1 :=
      ⟨NormedSpace.normalize v, normalize_mem_metricSphere hv⟩
    let hSphere : ((n : ℕ) - 1) + 1 = (n : ℕ) :=
      Nat.succ_pred_eq_of_pos n.2
    let hTarget :
        ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n : ℕ))) 1) =
          TopCat.sphere ((n : ℕ) - 1) :=
      Eq.trans
        (congrArg (fun k ↦ ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1))
          hSphere.symm)
        rfl
    cast hTarget (ULift.up normalized)

/-- The pointwise Hopf-construction coordinate formula attached to a multiplication-like map
datum on `S^(n - 1)`. -/
def hopfConstructionPointVec (n : ℕ+) (μ : SphereMultiplicationLike n)
    (x : TopCat.sphere (2 * (n : ℕ) - 1)) :
    EuclideanSpace ℝ (Fin ((n : ℕ) + 1)) :=
  let hSource : (2 * (n : ℕ) - 1) + 1 = (n : ℕ) + (n : ℕ) :=
    Eq.trans
      (Nat.succ_pred_eq_of_pos (Nat.mul_pos (Nat.succ_pos 1) n.2))
      (two_mul (n : ℕ))
  let hSphere : ((n : ℕ) - 1) + 1 = (n : ℕ) :=
    Nat.succ_pred_eq_of_pos n.2
  let xVec : EuclideanSpace ℝ (Fin ((n : ℕ) + (n : ℕ))) :=
    ∑ i : Fin ((n : ℕ) + (n : ℕ)),
      EuclideanSpace.single i (x.down.1 ((Equiv.cast (congrArg Fin hSource)).symm i))
  let leftVec : EuclideanSpace ℝ (Fin (n : ℕ)) :=
    ∑ i : Fin (n : ℕ),
      EuclideanSpace.single i (xVec (Fin.castAdd (n : ℕ) i))
  let rightVec : EuclideanSpace ℝ (Fin (n : ℕ)) :=
    ∑ i : Fin (n : ℕ),
      EuclideanSpace.single i (xVec (Fin.natAdd (n : ℕ) i))
  let midpoint : TopCat.sphere ((n : ℕ) - 1) :=
    μ.map (spherePointOfVector μ leftVec, spherePointOfVector μ rightVec)
  let scale : ℝ := 2 * ‖leftVec‖ * ‖rightVec‖
  (∑ i : Fin (n : ℕ),
      EuclideanSpace.single (Fin.castSucc i)
        (scale * midpoint.down.1 ((Equiv.cast (congrArg Fin hSphere)).symm i))) +
    EuclideanSpace.single (Fin.last (n : ℕ)) (‖leftVec‖ ^ 2 - ‖rightVec‖ ^ 2)

/-- The explicit Hopf-construction coordinate formula lands on the target sphere `S^n`. -/
theorem hopfConstructionPointVec_mem (n : ℕ+) (μ : SphereMultiplicationLike n)
    (x : TopCat.sphere (2 * (n : ℕ) - 1)) :
    hopfConstructionPointVec n μ x ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((n : ℕ) + 1))) 1 := sorry

/-- The pointwise Hopf construction associated to a multiplication-like datum on `S^(n - 1)`. -/
def hopfConstructionPoint (n : ℕ+) (μ : SphereMultiplicationLike n)
    (x : TopCat.sphere (2 * (n : ℕ) - 1)) :
    TopCat.sphere (n : ℕ) :=
  ULift.up ⟨hopfConstructionPointVec n μ x, hopfConstructionPointVec_mem n μ x⟩

/-- The pointwise Hopf construction varies continuously with the source point. -/
theorem hopfConstructionPoint_continuous (n : ℕ+) (μ : SphereMultiplicationLike n) :
    Continuous (hopfConstructionPoint n μ) := sorry

/-- Construction 24.6.3. The Hopf construction turns a multiplication-like map
`μ : SphereMultiplicationLike n` on `S^(n - 1)` into a map `S^(2n - 1) → S^n`, represented here
as an element of `HopfSphereMap (n : ℕ)`. -/
def hopfConstructionMap (n : ℕ+) (μ : SphereMultiplicationLike n) :
    HopfSphereMap (n : ℕ) :=
  ⟨hopfConstructionPoint n μ, hopfConstructionPoint_continuous n μ⟩

/-- As a continuous map, `hopfConstructionMap n μ` is represented by
`hopfConstructionPoint n μ`. -/
theorem hopfConstructionMap_def (n : ℕ+)
    (μ : SphereMultiplicationLike n) :
    hopfConstructionMap n μ = hopfConstructionPoint n μ := rfl

/-- Evaluating `hopfConstructionMap n μ` at a source point returns the corresponding
Hopf-construction point on `S^n`. -/
@[simp] theorem hopfConstructionMap_apply (n : ℕ+)
    (μ : SphereMultiplicationLike n)
    (x : TopCat.sphere (2 * (n : ℕ) - 1)) :
    hopfConstructionMap n μ x = hopfConstructionPoint n μ x := rfl

/-- The `HSpace`-packaged Hopf construction is obtained by applying `hopfConstructionMap` to the
canonical multiplication-like datum associated to the `HSpace` structure. -/
def hopfConstructionMapOfHSpace (n : ℕ+)
    [HSpace (TopCat.sphere ((n : ℕ) - 1))] : HopfSphereMap (n : ℕ) :=
  hopfConstructionMap n (sphereMultiplicationLikeOfHSpace n)
