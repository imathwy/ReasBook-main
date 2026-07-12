import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Flat

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

-- Semantic recall: `lean_leansearch` surfaced the canonical owners `Flat`, `IsIntegral`, and
-- `Scheme.Hom.fiber`; local Chapter 29 precedent confirms that the fibre over `y : Y` is recorded
-- as `Scheme.Hom.fiber f y`, so the source's generic fibre is formalized at `genericPoint Y`.

/-- Lemma 31.11.7: let `f : X ⟶ Y` be a flat morphism of schemes. If `Y` is integral and the
generic fibre of `f` is integral, then `X` is integral. Here the generic fibre is the canonical
scheme fibre `Scheme.Hom.fiber f (genericPoint Y)`. -/
@[stacks 0BCM]
theorem isIntegral_of_flat_of_genericFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsIntegral Y]
    (hgeneric : IsIntegral (Scheme.Hom.fiber f (genericPoint Y))) :
    IsIntegral X := sorry

end AlgebraicGeometry.Scheme.Hom
