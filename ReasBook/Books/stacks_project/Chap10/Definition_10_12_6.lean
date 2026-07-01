import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {A : Type u} {B : Type v} {N : Type w}
variable [Ring A] [Ring B] [AddCommGroup N]
variable [Module A N] [Module B N]

/- Definition 10.12.6: an `(A, B)`-bimodule is an abelian group `N` equipped with an `A`-module
structure and a `B`-module structure whose scalar actions commute. The canonical Lean expression
of this compatibility is `SMulCommClass A B N`. -/
recall SMulCommClass
