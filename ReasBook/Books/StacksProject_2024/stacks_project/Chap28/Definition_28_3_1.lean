import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/- Semantic recall: `lean_leansearch` points to the canonical scheme predicate
`AlgebraicGeometry.IsIntegral`, together with the affine specialization
`AlgebraicGeometry.affine_isIntegral_iff` and the section-ring consequence
`AlgebraicGeometry.IsIntegral.component_integral`. The source item therefore stays a direct
canonical recall surface rather than introducing a parallel local alias. -/

/- Definition 28.3.1: a scheme `X` is integral via the canonical mathlib predicate `IsIntegral X`;
this packages nonemptiness together with integrality of the section ring on every nonempty open,
hence in particular on every nonempty affine open. -/
#check IsIntegral X

end AlgebraicGeometry
