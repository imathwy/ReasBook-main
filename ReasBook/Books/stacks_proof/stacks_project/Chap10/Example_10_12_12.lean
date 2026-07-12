import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open TensorProduct

private abbrev twoZLinearMap : ℤ →ₗ[ℤ] ℤ := (2 : ℤ) • LinearMap.id

private theorem intTensor_zmodTwo_one_ne_zero :
    (TensorProduct.lid ℤ (ZMod 2)).symm 1 ≠ 0 := by
  intro h
  exact (show (1 : ZMod 2) ≠ 0 by decide)
    (by simpa using congrArg (TensorProduct.lid ℤ (ZMod 2)) h)

private theorem two_zsmul_rTensor_zmodTwo_not_injective :
    ¬ Function.Injective (twoZLinearMap.rTensor (ZMod 2)) := by
  let f : ℤ ⊗[ℤ] ZMod 2 →ₗ[ℤ] ℤ ⊗[ℤ] ZMod 2 := twoZLinearMap.rTensor (ZMod 2)
  let z : ℤ ⊗[ℤ] ZMod 2 := (TensorProduct.lid ℤ (ZMod 2)).symm 1
  intro h
  apply intTensor_zmodTwo_one_ne_zero
  apply h
  calc
    f z = 0 := by
      apply (TensorProduct.lid ℤ (ZMod 2)).injective
      change (2 : ZMod 2) = 0
      decide
    _ = f 0 := by
      simp [f]

/-- Example 10.12.12: for the injective map `2 : ℤ → ℤ` of `ℤ`-modules, tensoring with `ZMod 2`
does not preserve injectivity. -/
@[stacks 00DI]
theorem tensoring_zmodTwo_does_not_preserve_injectivity :
    Function.Injective ((2 : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ) ∧
      ¬ Function.Injective (((2 : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ).rTensor (ZMod 2)) := by
  refine ⟨?_, by simpa [twoZLinearMap] using two_zsmul_rTensor_zmodTwo_not_injective⟩
  simpa [twoZLinearMap] using smul_right_injective ℤ (show (2 : ℤ) ≠ 0 by decide)

/-- Bridge to the owner abstraction: `ZMod 2` is not flat as a `ℤ`-module because right tensoring
fails to preserve injectivity for multiplication by `2`. -/
theorem zmodTwo_not_flat : ¬ Module.Flat ℤ (ZMod 2) := by
  intro hflat
  letI := hflat
  exact two_zsmul_rTensor_zmodTwo_not_injective <|
    Module.Flat.rTensor_preserves_injective_linearMap twoZLinearMap <|
      by simpa [twoZLinearMap] using smul_right_injective ℤ (show (2 : ℤ) ≠ 0 by decide)
