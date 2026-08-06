import Mathlib.Analysis.InnerProductSpace.PiL2

local notation "V[" n "]" => EuclideanSpace ℝ (Fin (n + 1))

/-- The standard closed disk `D^(n+1)` in `ℝ^(n + 1)`. -/
def unitDisk (n : ℕ) : Set V[n] :=
  Metric.closedBall (0 : V[n]) 1

/-- Membership in `unitDisk n` is the usual norm bound `‖x‖ ≤ 1`. -/
theorem mem_unitDisk_iff {n : ℕ} {x : V[n]} :
    x ∈ unitDisk n ↔ ‖x‖ ≤ 1 := by
  rw [unitDisk, Metric.mem_closedBall, dist_zero_right]

/-- The standard sphere `S^n`, realized as the boundary sphere of `D^(n+1)`. -/
abbrev sphereBoundary (n : ℕ) : Set V[n] :=
  Metric.sphere (0 : V[n]) 1

/-- Membership in `sphereBoundary n` is the usual norm equation `‖x‖ = 1`. -/
theorem mem_sphereBoundary_iff {n : ℕ} {x : V[n]} :
    x ∈ sphereBoundary n ↔ ‖x‖ = 1 := by
  rw [sphereBoundary, Metric.mem_sphere, dist_zero_right]

/-- A point of `sphereBoundary n` lies in `unitDisk n`. -/
theorem sphereBoundary_mem_unitDisk {n : ℕ} (x : sphereBoundary n) :
    x.1 ∈ unitDisk n := by
  rw [mem_unitDisk_iff]
  exact (mem_sphereBoundary_iff.mp x.2).le

/-- The first standard basis vector lies on `sphereBoundary n`. -/
theorem sphereBoundaryBasepoint_mem (n : ℕ) :
    EuclideanSpace.single 0 (1 : ℝ) ∈ sphereBoundary n := by
  simp [sphereBoundary]

/-- The canonical basepoint of the boundary sphere `sphereBoundary n`, given by the first standard
basis vector. -/
noncomputable def sphereBoundaryBasepoint (n : ℕ) : sphereBoundary n :=
  ⟨EuclideanSpace.single 0 (1 : ℝ), sphereBoundaryBasepoint_mem n⟩

/-- The canonical inclusion `S^n = ∂D^(n+1) ↪ D^(n+1)` for the standard disk model. -/
def sphereBoundaryInclusion (n : ℕ) : C(sphereBoundary n, unitDisk n) where
  toFun x := ⟨x.1, sphereBoundary_mem_unitDisk x⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val fun x ↦
    sphereBoundary_mem_unitDisk x
