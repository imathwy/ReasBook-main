import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe uR u𝔤 u𝔤'

section

variable {R : Type uR} [CommRing R]
variable {𝔤 : Type u𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {𝔤' : Type u𝔤'} [LieRing 𝔤'] [LieAlgebra R 𝔤']

-- Domain sampling pass:
-- * primary domain: Lie algebra quotients and kernels;
-- * owner abstraction: `LieSubmodule.Quotient`, whose primitive data is the Lie ideal/submodule
--   and whose derived API includes the quotient Lie algebra, quotient map, surjectivity, and
--   kernel calculation;
-- * relevant canonical declarations inspected: `LieSubmodule.Quotient.lieQuotientLieAlgebra`,
--   `LieSubmodule.Quotient.mk'`, `LieSubmodule.Quotient.surjective_mk'`,
--   `LieSubmodule.Quotient.mk'_ker`, `LieHom.ker`, and `LieHom.ker_toSubmodule`.

/- Problem 8-31 (1): for a Lie ideal `I`, the quotient `𝔤 ⧸ I` carries its canonical Lie algebra
structure. -/
recall LieSubmodule.Quotient.lieQuotientLieAlgebra

/- Problem 8-31 (1) and (3): the canonical quotient projection is naturally a Lie algebra
homomorphism, so bracket preservation is expressed at the `LieHom` layer. -/
recall LieSubmodule.Quotient.mk'

/- Problem 8-31 (2): the quotient projection onto `𝔤 ⧸ I` is surjective. -/
recall LieSubmodule.Quotient.surjective_mk'

/- Problem 8-31 (4): every Lie ideal is the kernel of its quotient projection. -/
recall LieSubmodule.Quotient.mk'_ker

/- Problem 8-31 (5): the kernel of a Lie algebra homomorphism is canonically a Lie ideal in the
domain, whose underlying linear subspace is the usual linear kernel. -/
recall LieHom.ker
recall LieHom.ker_toSubmodule
recall LieHom.mem_ker

end
