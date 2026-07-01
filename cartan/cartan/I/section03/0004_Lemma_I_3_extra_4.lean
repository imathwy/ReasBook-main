import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open Real

namespace Circle

/-- The intrinsic quarter-arc of the unit circle, obtained by restricting `Circle.argEquiv` to the
interval `[0, π / 2]`. This is the canonical owner; the corresponding subset of `ℂ` is only a
bridge/view. -/
def quarterArc : Set Circle :=
  { z | 0 ≤ (argEquiv z : ℝ) ∧ (argEquiv z : ℝ) ≤ π / 2 }

@[simp] theorem mem_quarterArc_iff {z : Circle} :
    z ∈ quarterArc ↔ 0 ≤ Complex.arg (z : ℂ) ∧ Complex.arg (z : ℂ) ≤ π / 2 :=
  Iff.rfl

private def quarterArgTarget : Set (Set.Ioc (-π) π) :=
  { θ | 0 ≤ (θ : ℝ) ∧ (θ : ℝ) ≤ π / 2 }

private theorem mem_slitPlane_of_mem_quarterArc {z : Circle} (hz : z ∈ quarterArc) :
    (z : ℂ) ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff_arg.mpr ?_
  constructor
  · exact ne_of_lt <| lt_of_le_of_lt hz.2 (by nlinarith [Real.pi_pos])
  · exact z.coe_ne_zero

/-- The redundant target condition inside `(-π, π]` collapses to the ordinary interval
`[0, π / 2]`. -/
private noncomputable def quarterArgTargetEquivIcc :
    quarterArgTarget ≃ Set.Icc (0 : ℝ) (π / 2) where
  toFun θ := ⟨θ, θ.2.1, θ.2.2⟩
  invFun θ := by
    refine ⟨⟨θ, ?_, ?_⟩, θ.2.1, θ.2.2⟩
    · have hπ : (0 : ℝ) < π := Real.pi_pos
      linarith [θ.2.1, hπ]
    · linarith [θ.2.2, Real.pi_pos]
  left_inv θ := rfl
  right_inv θ := rfl

/-- `Circle.argEquiv` restricted to the quarter-arc. -/
noncomputable def quarterArcEquivIcc : quarterArc ≃ Set.Icc (0 : ℝ) (π / 2) :=
  (argEquiv.subtypeEquiv fun _ ↦ Iff.rfl).trans quarterArgTargetEquivIcc

/-- Lemma I.3-extra-4: the quarter-arc of the unit circle is canonically homeomorphic to the
interval `[0, π / 2]`, via the restriction of `Circle.argEquiv` and its inverse `Circle.exp`. -/
noncomputable def quarterArcHomeomorphIcc : quarterArc ≃ₜ Set.Icc (0 : ℝ) (π / 2) where
  toEquiv := quarterArcEquivIcc
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ ?_
    rw [continuous_iff_continuousAt]
    intro z
    exact ((Complex.continuousAt_arg (mem_slitPlane_of_mem_quarterArc z.2)).comp
      continuousAt_subtype_val).comp continuousAt_subtype_val
  continuous_invFun := by
    exact Continuous.subtype_mk (exp.continuous.comp continuous_subtype_val) fun θ ↦ by
      have harg : Complex.arg (Circle.exp θ : ℂ) = (θ : ℝ) :=
        arg_exp (by nlinarith [θ.2.1, Real.pi_pos]) (by nlinarith [θ.2.2, Real.pi_pos])
      refine ⟨?_, ?_⟩
      · change 0 ≤ Complex.arg (Circle.exp θ : ℂ)
        rw [harg]
        exact θ.2.1
      · change Complex.arg (Circle.exp θ : ℂ) ≤ π / 2
        rw [harg]
        exact θ.2.2

/-- The corresponding quarter of the complex unit circle, viewed inside `ℂ`. This is a bridge from
the intrinsic owner `Circle.quarterArc` to the concrete `Set ℂ` presentation. -/
def quarterUnitCircle : Set ℂ :=
  ((↑) : Circle → ℂ) '' quarterArc

@[simp] theorem mem_quarterUnitCircle_iff {z : ℂ} :
    z ∈ quarterUnitCircle ↔ ‖z‖ = 1 ∧ 0 ≤ Complex.arg z ∧ Complex.arg z ≤ π / 2 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨norm_coe w, hw.1, hw.2⟩
  · rintro ⟨hz, hz₀, hz₁⟩
    refine ⟨⟨z, by simpa [Submonoid.unitSphere] using mem_sphere_zero_iff_norm.2 hz⟩,
      ⟨hz₀, hz₁⟩, rfl⟩

/-- The concrete `Set ℂ` quarter-circle is homeomorphic to the intrinsic quarter-arc of `Circle`
via the ambient coercion. -/
noncomputable def quarterArcHomeomorphQuarterUnitCircle : quarterArc ≃ₜ quarterUnitCircle :=
  Topology.IsEmbedding.homeomorphImage
    (show Topology.IsEmbedding ((↑) : Circle → ℂ) from .subtypeVal) quarterArc

/-- The concrete quarter of the unit circle in `ℂ` is homeomorphic to `[0, π / 2]`; this is the
derived bridge obtained from the intrinsic `Circle` owner. -/
noncomputable def quarterUnitCircleHomeomorphIcc :
    quarterUnitCircle ≃ₜ Set.Icc (0 : ℝ) (π / 2) :=
  quarterArcHomeomorphQuarterUnitCircle.symm.trans quarterArcHomeomorphIcc

end Circle
