import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- 10.12.10.1: tensoring a right exact sequence of `R`-modules with a fixed module `N`
preserves exactness, so `M₁ ⊗[R] N ⟶ M₂ ⊗[R] N ⟶ M₃ ⊗[R] N ⟶ 0` is exact whenever
`M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` is exact. This is exactly the canonical pair
`rTensor_exact` and `LinearMap.rTensor_surjective`. -/
recall rTensor_exact
recall LinearMap.rTensor_surjective
