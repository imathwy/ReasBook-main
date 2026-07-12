import Mathlib.Algebra.Lie.Ideal

-- Declarations for this item will be appended below by the statement pipeline.

universe uR u𝔤 u𝔤'

variable {R : Type uR} [CommRing R]
variable {𝔤 : Type u𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {𝔤' : Type u𝔤'} [LieRing 𝔤'] [LieAlgebra R 𝔤']
variable (f : 𝔤 →ₗ⁅R⁆ 𝔤')

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so the canonical
-- owners were verified directly in `Mathlib.Algebra.Lie.Ideal` and
-- `Mathlib.Algebra.Lie.Subalgebra`.

/- Exercise 8.34: for a Lie algebra homomorphism `f`, mathlib provides the canonical derived
subobjects `f.ker : LieIdeal R 𝔤` and `f.range : LieSubalgebra R 𝔤'`. The kernel also carries
its induced `LieSubalgebra` structure via the standard coercion from Lie ideals. This is the
source-faithful canonical recall surface for the exercise. -/
#check f.ker
#check (f.ker : LieSubalgebra R 𝔤)
#check f.range
