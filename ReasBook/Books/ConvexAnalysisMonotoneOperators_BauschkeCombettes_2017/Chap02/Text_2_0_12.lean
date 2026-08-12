import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter
open scoped Topology

variable {A : Type v} [Preorder A] [IsDirected A fun a b ↦ a ≤ b] [Nonempty A]
variable {𝓗 : Type u} [SeminormedAddCommGroup 𝓗]

/- Text 2.0.12: strong convergence of a net in a normed space is exactly the canonical
metric/net criterion recalled below; mathlib states it in the slightly more general setting of a
seminormed additive commutative group. -/
recall NormedAddCommGroup.tendsto_atTop
