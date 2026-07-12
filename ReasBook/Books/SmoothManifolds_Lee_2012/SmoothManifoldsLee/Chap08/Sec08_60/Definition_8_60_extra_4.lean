import Mathlib.Algebra.Lie.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe uR u𝔤 u𝔥

variable {R : Type uR} [CommRing R]
variable {𝔤 : Type u𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {𝔥 : Type u𝔥} [LieRing 𝔥] [LieAlgebra R 𝔥]
variable (A : 𝔤 →ₗ⁅R⁆ 𝔥)
variable (e : 𝔤 ≃ₗ⁅R⁆ 𝔥)

-- Semantic search note: no `lean_leansearch`-style MCP tool was available in this runner, so the
-- canonical owners were verified directly against `Mathlib.Algebra.Lie.Basic` and nearby local
-- Lie-algebra precedents.

/- Definition 8.60-extra-4: the owner abstractions are `LieHom R 𝔤 𝔥` and `LieEquiv R 𝔤 𝔥`,
written source-facing as `𝔤 →ₗ⁅R⁆ 𝔥` and `𝔤 ≃ₗ⁅R⁆ 𝔥`. The derived API for a Lie algebra
homomorphism includes bracket preservation `A.map_lie`, and Lie algebra isomorphism is expressed by
`𝔤 ≃ₗ⁅R⁆ 𝔥`; existence of such an isomorphism is `Nonempty (𝔤 ≃ₗ⁅R⁆ 𝔥)`. -/
#check LieHom
#check (𝔤 →ₗ⁅R⁆ 𝔥)
#check A.map_lie
#check LieEquiv
#check (𝔤 ≃ₗ⁅R⁆ 𝔥)
#check e.toLieHom
#check Nonempty (𝔤 ≃ₗ⁅R⁆ 𝔥)
