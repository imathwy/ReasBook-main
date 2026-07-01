import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.TypeTags.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (G : Type u) [CommGroup G]

/- Remark 1.1.25: the integers form an additive commutative group under addition, with identity
element `0`. This is the canonical additive-group structure on `ℤ`. -/
#check (inferInstance : AddCommGroup ℤ)

/- A commutative group can be viewed in additive notation via the canonical type tag
`Additive G`, whose operation is written as `+` and whose identity is written as `0`. -/
#check (inferInstance : AddCommGroup (Additive G))
