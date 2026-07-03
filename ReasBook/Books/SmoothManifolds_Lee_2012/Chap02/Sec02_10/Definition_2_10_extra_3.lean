import Mathlib.Tactic.Recall
import Mathlib.Topology.Algebra.Support

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 2.10-extra-3: the support of a function on a topological space is the topological
support `tsupport f`, i.e. the closure of the set where the function is nonzero, and compact
support is formalized by `HasCompactSupport`. -/
recall tsupport

/- In mathlib and in the surrounding chapter files, “`f` is supported in `U`” is written directly
as `tsupport f ⊆ U`; no separate owner declaration is introduced for this view. -/

-- `HasCompactSupport f` is the canonical mathlib notion that `f` is compactly supported.
recall HasCompactSupport

/- Any function on a compact space is compactly supported; this is
`HasCompactSupport.of_compactSpace`. -/
recall HasCompactSupport.of_compactSpace
