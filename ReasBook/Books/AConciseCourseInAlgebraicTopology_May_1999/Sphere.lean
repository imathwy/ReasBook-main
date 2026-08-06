import Mathlib.Topology.Category.TopCat.Sphere

noncomputable section

open scoped TopCat

/-- A concrete basepoint of the sphere `𝕊 n`, given by the first standard basis vector. -/
def sphereBasepoint (n : ℕ) : 𝕊 n :=
  ULift.up <| ⟨EuclideanSpace.single 0 (1 : ℝ), by
    simp⟩
