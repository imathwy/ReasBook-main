import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {K : Type u} {L : Type v} {M : Type w}
variable [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
variable [FiniteDimensional K L] [FiniteDimensional L M]

/- Lemma 9.20.5 (1): in a tower of finite field extensions `M/L/K`, the trace from `M` to `K`
is the composite of the trace from `M` to `L` with the trace from `L` to `K`. This is the
canonical theorem `Algebra.trace_comp_trace`. -/
recall Algebra.trace_comp_trace

/- Lemma 9.20.5 (2): in a tower of finite field extensions `M/L/K`, the norm from `M` to `K` is
the composite of the norm from `M` to `L` with the norm from `L` to `K`. This is the canonical
theorem `Algebra.norm_norm`. -/
recall Algebra.norm_norm
