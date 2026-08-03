module

public import Mathlib.Topology.UnitInterval

public section

universe u

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]

/-- The positive affine homeomorphism from a nondegenerate open interval to the open unit
interval. -/
noncomputable def iooHomeoI (a b : 𝕜) (h : a < b) :
    Set.Ioo a b ≃ₜ Set.Ioo (0 : 𝕜) 1 :=
  let e := Homeomorph.image (affineHomeomorph (b - a) a (sub_pos.mpr h).ne.symm)
    (Set.Ioo (0 : 𝕜) 1)
  (e.trans (Homeomorph.setCongr (by
    rw [affineHomeomorph_image_Ioo _ _ _ _ (sub_pos.mpr h)]
    simp))).symm

/-- Helper for Exercise 18.5: the open-interval affine homeomorphism has the expected
underlying value. -/
theorem iooHomeoI_coe_formula (a b : 𝕜) (h : a < b) (x : Set.Ioo a b) :
    (iooHomeoI a b h x : 𝕜) = (x - a) / (b - a) := by
  -- Evaluate the inverse affine composite defining the interval homeomorphism.
  unfold iooHomeoI
  simp
  -- The remaining equality only changes the proof component of the subtype.
  rfl
