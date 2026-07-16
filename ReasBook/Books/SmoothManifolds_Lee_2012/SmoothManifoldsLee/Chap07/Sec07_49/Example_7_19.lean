import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_26.Example_4_35
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_49.Proposition_7_17

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped LieGroup Manifold ContDiff FourierTransform Torus

noncomputable section

local notation "T2Model" => ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)

-- `lean_leansearch` was unavailable in this session, so the source-facing API below was chosen by
-- checking the local `AddChar` owner and reusing Proposition 7.17's `LieSubgroup` owner for the
-- image of an injective smooth homomorphism.

/-- The dense torus curve of slope `α`, given by
`t ↦ (e^{2π i t}, e^{2π i α t}) : ℝ → 𝕋²`. -/
def torusSlopeCurve (α : ℝ) : ℝ → 𝕋^{2} :=
  fun t ↦ ![𝐞 t, 𝐞 (α * t)]

/-- The curve `torusSlopeCurve α` sends `0` to the identity element of `𝕋²`. -/
theorem torusSlopeCurve_map_zero (α : ℝ) :
    torusSlopeCurve α 0 = 1 := sorry

/-- The curve `torusSlopeCurve α` is additive with values in the multiplicative torus `𝕋²`. -/
theorem torusSlopeCurve_map_add (α s t : ℝ) :
    torusSlopeCurve α (s + t) = torusSlopeCurve α s * torusSlopeCurve α t := sorry

/-- The dense torus curve as an additive character from `ℝ` to `𝕋²`. -/
def torusSlopeCurve_addChar (α : ℝ) : AddChar ℝ (𝕋^{2}) where
  toFun := torusSlopeCurve α
  map_zero_eq_one' := torusSlopeCurve_map_zero α
  map_add_eq_mul' := torusSlopeCurve_map_add α

/-- The additive character `torusSlopeCurve_addChar α` has underlying map
`t ↦ (e^{2π i t}, e^{2π i α t})`. -/
theorem torusSlopeCurve_addChar_apply (α : ℝ) (t : ℝ) :
    torusSlopeCurve_addChar α t = torusSlopeCurve α t := sorry

/-- The additive character `torusSlopeCurve_addChar α` is smooth. -/
theorem torusSlopeCurve_addChar_contMDiff (α : ℝ) :
    ContMDiff 𝓘(ℝ) T2Model ∞ (torusSlopeCurve_addChar α) := sorry

/-- The carrier set of the subgroup range of `torusSlopeCurve_addChar α` is exactly the image set
of the dense torus curve. -/
theorem torusSlopeCurve_addChar_range (α : ℝ) :
    ((torusSlopeCurve_addChar α).toMonoidHom.range : Set (𝕋^{2})) =
      Set.range (torusSlopeCurve α) := sorry

/-- Example 7.19 (1): for irrational `α`, the dense torus curve, viewed as a Lie group
homomorphism from the additive Lie group `ℝ` to `𝕋²`, is injective. -/
theorem torusSlopeCurve_addChar_injective (α : ℝ) (hα : Irrational α) :
    Function.Injective (torusSlopeCurve_addChar α) := sorry

/-- Example 7.19 (2): for irrational `α`, the image of the dense torus curve from Example 4.20 is
an immersed Lie subgroup of `𝕋²`. -/
theorem torusSlopeCurve_range_has_immersed_lie_subgroup_structure
    (α : ℝ) (hα : Irrational α) :
    ∃ K : LieSubgroup T2Model,
      (K.carrier : Set (𝕋^{2})) = Set.range (torusSlopeCurve α) := sorry
