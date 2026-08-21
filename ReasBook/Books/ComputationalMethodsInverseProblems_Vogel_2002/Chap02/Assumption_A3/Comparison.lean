module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

public section

universe u v w

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
variable [SeminormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]

namespace IsBoundedLinearMap

/-- Evaluating the bundled operator associated to `hf` recovers the original map. -/
@[simp] theorem toContinuousLinearMap_apply {f : H₁ → H₂} (hf : IsBoundedLinearMap 𝕜 f)
    (x : H₁) :
    IsBoundedLinearMap.toContinuousLinearMap f hf x = f x :=
  rfl

end IsBoundedLinearMap

namespace ContinuousLinearMap

/-- Bundling the unbundled bounded-linearity witness of `K` recovers `K`. -/
@[simp] theorem toContinuousLinearMap_isBoundedLinearMap (K : H₁ →L[𝕜] H₂) :
    IsBoundedLinearMap.toContinuousLinearMap K K.isBoundedLinearMap = K := by
  ext x
  rfl

end ContinuousLinearMap
