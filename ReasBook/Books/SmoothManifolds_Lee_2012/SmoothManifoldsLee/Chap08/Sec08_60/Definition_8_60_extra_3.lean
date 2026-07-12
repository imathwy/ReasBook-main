import Mathlib.Algebra.Lie.Subalgebra

-- Declarations for this item will be appended below by the statement pipeline.

universe uR u𝔤

variable {R : Type uR} [CommRing R]
variable {𝔤 : Type u𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]

-- Semantic search tool unavailable in this runner; canonical recall verified directly in
-- `Mathlib.Algebra.Lie.Subalgebra`.

/- Definition 8.60-extra-3: the canonical mathlib notion is `LieSubalgebra R 𝔤`, namely an
`R`-submodule of `𝔤` that is closed under the Lie bracket. Its basic derived API includes
`LieSubalgebra.lie_mem` for bracket closure and `LieSubalgebra.lieAlgebra` for the induced Lie
algebra structure on a subalgebra. -/
#check LieSubalgebra R 𝔤
#check LieSubalgebra.lie_mem
#check LieSubalgebra.lieAlgebra
