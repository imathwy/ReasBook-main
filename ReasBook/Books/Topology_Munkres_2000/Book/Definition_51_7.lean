module

public import Mathlib.Topology.UnitInterval

public section

namespace Set.Icc

universe u

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
variable {a b c d e f : 𝕜}

/-- Definition 51.7: The canonical positive affine homeomorphism between two nondegenerate
closed intervals. -/
def positiveHomeomorph (hab : a < b) (hcd : c < d) : Set.Icc a b ≃ₜ Set.Icc c d :=
  (iccHomeoI a b hab).trans (iccHomeoI c d hcd).symm

/-- Helper for Definition 51.7: The canonical positive homeomorphism has the expected affine
formula. -/
theorem positiveHomeomorph_apply (hab : a < b) (hcd : c < d) (x : Set.Icc a b) :
    (positiveHomeomorph hab hcd x : 𝕜) =
      (d - c) * ((x - a) / (b - a)) + c := by
  -- Compute through the two standard interval homeomorphisms.
  simp only [positiveHomeomorph, Homeomorph.trans_apply,
    iccHomeoI_apply_coe, iccHomeoI_symm_apply_coe]

/-- Helper for Definition 51.7: The canonical positive homeomorphism sends the left endpoint to
the left endpoint. -/
theorem positiveHomeomorph_left (hab : a < b) (hcd : c < d) :
    positiveHomeomorph hab hcd ⟨a, le_rfl, hab.le⟩ = ⟨c, le_rfl, hcd.le⟩ := by
  -- Reduce equality of interval points to the affine carrier formula.
  apply Subtype.ext
  rw [positiveHomeomorph_apply]
  simp

/-- Helper for Definition 51.7: The canonical positive homeomorphism sends the right endpoint to
the right endpoint. -/
theorem positiveHomeomorph_right (hab : a < b) (hcd : c < d) :
    positiveHomeomorph hab hcd ⟨b, hab.le, le_rfl⟩ = ⟨d, hcd.le, le_rfl⟩ := by
  -- The right endpoint corresponds to affine parameter one.
  apply Subtype.ext
  rw [positiveHomeomorph_apply]
  field_simp [sub_ne_zero.mpr hab.ne]
  ring

omit [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] in
/-- Helper for Definition 51.7: The slope of the canonical positive affine homeomorphism is
positive. -/
theorem positiveHomeomorph_slope_pos (hab : a < b) (hcd : c < d) :
    0 < (d - c) / (b - a) := by
  -- Both interval lengths are positive, hence so is their ratio.
  exact div_pos (sub_pos.mpr hcd) (sub_pos.mpr hab)

/-- Helper for Definition 51.7: An affine map between nondegenerate closed intervals that
preserves both endpoints is the canonical positive homeomorphism. -/
theorem eq_positiveHomeomorph (hab : a < b) (hcd : c < d)
    (g : Set.Icc a b → Set.Icc c d) (m k : 𝕜)
    (hg : ∀ x, (g x : 𝕜) = m * x + k)
    (hleft : g ⟨a, le_rfl, hab.le⟩ = ⟨c, le_rfl, hcd.le⟩)
    (hright : g ⟨b, hab.le, le_rfl⟩ = ⟨d, hcd.le, le_rfl⟩) :
    g = positiveHomeomorph hab hcd := by
  -- Project the endpoint equations to scalar affine equations.
  have hleftValue : m * a + k = c := by
    calc
      m * a + k = (g ⟨a, le_rfl, hab.le⟩ : 𝕜) := by
        simpa using (hg (⟨a, le_rfl, hab.le⟩ : Set.Icc a b)).symm
      _ = c := congrArg Subtype.val hleft
  have hrightValue : m * b + k = d := by
    calc
      m * b + k = (g ⟨b, hab.le, le_rfl⟩ : 𝕜) := by
        simpa using (hg (⟨b, hab.le, le_rfl⟩ : Set.Icc a b)).symm
      _ = d := congrArg Subtype.val hright
  have hslopeValue : m * (b - a) = d - c := by
    calc
      m * (b - a) = (m * b + k) - (m * a + k) := by ring
      _ = d - c := by rw [hrightValue, hleftValue]
  -- The two endpoint equations determine every affine value by interpolation.
  funext x
  apply Subtype.ext
  rw [hg, positiveHomeomorph_apply]
  field_simp [sub_ne_zero.mpr hab.ne]
  rw [← hslopeValue, ← hleftValue]
  ring

/-- Helper for Definition 51.7: The inverse of a canonical positive homeomorphism is the
canonical map in the reverse direction. -/
theorem positiveHomeomorph_symm (hab : a < b) (hcd : c < d) :
    (positiveHomeomorph hab hcd).symm = positiveHomeomorph hcd hab := by
  -- Reversing the defining composite swaps the two interval coordinates.
  rfl

/-- Helper for Definition 51.7: Canonical positive homeomorphisms compose to the canonical map
between the outer intervals. -/
theorem positiveHomeomorph_trans (hab : a < b) (hcd : c < d) (hef : e < f) :
    (positiveHomeomorph hab hcd).trans (positiveHomeomorph hcd hef) =
      positiveHomeomorph hab hef := by
  -- The middle interval coordinates cancel pointwise.
  ext x
  simp only [positiveHomeomorph, Homeomorph.trans_apply]
  rw [(iccHomeoI c d hcd).apply_symm_apply]


end Set.Icc
