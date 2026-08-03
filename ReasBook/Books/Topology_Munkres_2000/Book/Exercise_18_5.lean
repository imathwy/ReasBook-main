module

public import Topology_Munkres_2000.Book.Exercise_18_5.OpenInterval

public section

universe u

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]

/-- Exercise 18.5 (1): The positive affine homeomorphism from `Set.Ioo a b` to
`Set.Ioo (0 : 𝕜) 1` has the expected formula. -/
@[simp]
theorem iooHomeoI_apply_coe (a b : 𝕜) (h : a < b) (x : Set.Ioo a b) :
    (iooHomeoI a b h x : 𝕜) = (x - a) / (b - a) := by
  -- Use the computation rule proved alongside the homeomorphism definition.
  exact iooHomeoI_coe_formula a b h x

/- Exercise 18.5 (2): For `a < b`, the closed interval `Set.Icc a b` is homeomorphic to the
closed unit interval `Set.Icc (0 : ℝ) 1`. -/
#check iccHomeoI
