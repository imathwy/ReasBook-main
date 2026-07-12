import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (R : CommRingCat.{u})
variable {ℱ 𝒢 : (Spec R).Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

-- Semantic recall: `lean_leansearch` surfaced the canonical quasi-coherent owner
-- `SheafOfModules.IsQuasicoherent`; local Chapter 26 precedent states affine module sheaves on
-- `Spec R` using `(Spec R).Modules`, so the closure statements below use the canonical
-- categorical `kernel` and `cokernel` in that module category.

/-- Lemma 26.7.6 (1): let `X = Spec(R)` be an affine scheme. The kernel of a map of
quasi-coherent `\mathcal O_X`-modules is quasi-coherent. -/
@[stacks 01IC]
theorem isQuasicoherent_kernel (φ : ℱ ⟶ 𝒢) :
    (kernel φ).IsQuasicoherent := sorry

/-- Lemma 26.7.6 (2): let `X = Spec(R)` be an affine scheme. The cokernel of a map of
quasi-coherent `\mathcal O_X`-modules is quasi-coherent. -/
@[stacks 01IC]
theorem isQuasicoherent_cokernel (φ : ℱ ⟶ 𝒢) :
    (cokernel φ).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Modules
