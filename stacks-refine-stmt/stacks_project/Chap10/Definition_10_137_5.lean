import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

/- Definition 10.137.5: a standard smooth `R`-algebra is the canonical notion
`Algebra.IsStandardSmooth`; it is presented by a quotient of a polynomial algebra by finitely many
relations together with an invertible Jacobian determinant in the quotient. -/
recall IsStandardSmooth

/- A submersive presentation packages the quotient presentation and Jacobian-unit condition used in
the definition of a standard smooth algebra. -/
recall SubmersivePresentation

end Algebra

namespace RingHom

/- Standard smoothness for a ring map is the ring-hom version of the same canonical notion. -/
recall IsStandardSmooth

/- For an algebra map, ring-hom standard smoothness agrees with algebra standard smoothness. -/
recall isStandardSmooth_algebraMap

end RingHom
