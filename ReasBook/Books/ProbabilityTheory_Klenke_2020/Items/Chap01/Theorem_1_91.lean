import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
variable {h : Ω → ℝ} {f g : Ω → EuclideanSpace ℝ (Fin n)}

/-- Theorem 1.91: if `h : Ω → ℝ` and `f, g : Ω → ℝ^n` are measurable, then the four maps
`f + g`, `f - g`, `f · h`, and `f / h` are measurable; here the last two are encoded as
`ω ↦ h ω • f ω` and `ω ↦ (h ω)⁻¹ • f ω`. -/
-- Proof sketch: `ℝ^n` is closed under addition, subtraction, and scalar multiplication by
-- measurable real-valued functions, so each coordinate map is measurable by the standard
-- measurable operation lemmas. Then combine these four measurable maps into one measurable map
-- with values in the fourfold product.
theorem measurable_vector_add_sub_smul_div
    (hh : Measurable h) (hf : Measurable f) (hg : Measurable g) :
    Measurable fun ω ↦ (f ω + g ω, f ω - g ω, h ω • f ω, (h ω)⁻¹ • f ω) := by
  -- Each component is measurable by the standard measurable arithmetic operations.
  -- The bundled four-tuple is then measurable by repeated product measurability.
  fun_prop

end
