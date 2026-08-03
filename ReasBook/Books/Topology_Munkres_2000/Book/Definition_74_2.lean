module

public import Topology_Munkres_2000.Book.Definition_74_2.Parameterization
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

public section

namespace OrientedSegment

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Definition 74.2: The positive homeomorphism between oriented segments preserves their
common affine parameter. -/
noncomputable def positiveHomeomorph (L : OrientedSegment E) (L' : OrientedSegment F) :
    L.carrier ≃ₜ L'.carrier :=
  L.paramHomeomorph.symm.trans L'.paramHomeomorph

/-- Companion for Definition 74.2: the positive homeomorphism sends equal affine parameters
to equal affine parameters. -/
theorem positiveHomeomorph_apply (L : OrientedSegment E) (L' : OrientedSegment F)
    (s : unitInterval) :
    L.positiveHomeomorph L' (L.paramHomeomorph s) = L'.paramHomeomorph s := by
  -- Composition first recovers `s`, then applies the target parameterization.
  simp only [positiveHomeomorph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]

/-- Companion for Definition 74.2: the positive homeomorphism from an oriented segment to
itself is the identity. -/
theorem positiveHomeomorph_refl (L : OrientedSegment E) :
    L.positiveHomeomorph L = Homeomorph.refl L.carrier := by
  -- The parameter homeomorphism cancels its inverse.
  exact L.paramHomeomorph.symm_trans_self

/-- Companion for Definition 74.2: positive homeomorphisms compose by preserving the same
affine parameter. -/
theorem positiveHomeomorph_trans (L₁ L₂ : OrientedSegment E) (L₃ : OrientedSegment F) :
    (L₁.positiveHomeomorph L₂).trans (L₂.positiveHomeomorph L₃) =
      L₁.positiveHomeomorph L₃ := by
  -- Extensionality exposes the middle parameterization and its inverse, which cancel.
  ext x
  simp only [positiveHomeomorph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]

/-- Companion for Definition 74.2: the inverse positive homeomorphism travels in the reverse
direction. -/
theorem positiveHomeomorph_symm (L : OrientedSegment E) (L' : OrientedSegment F) :
    (L.positiveHomeomorph L').symm = L'.positiveHomeomorph L := by
  -- Both sides send a target point back through its parameter and then into `L`.
  ext x
  simp only [positiveHomeomorph, Homeomorph.symm_trans_apply, Homeomorph.trans_apply,
    Homeomorph.symm_symm]


end OrientedSegment
