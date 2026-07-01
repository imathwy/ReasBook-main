import Mathlib.Order.KrullDimension
import Mathlib.Topology.Sets.Closeds
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 5.11.1: for an irreducible closed subset `Y` of `X`, the codimension `codim(Y, X)`
is the canonical order-theoretic notion `Order.coheight Y` in the poset `IrreducibleCloseds X`. -/
recall Order.coheight

/- Companion recall: for `Y : IrreducibleCloseds X`, the codimension of `Y` in `X` is also the
Krull dimension of the upper interval of irreducible closed subsets of `X` containing `Y`, via the
canonical theorem `Order.coheight_eq_krullDim_Ici`. -/
recall Order.coheight_eq_krullDim_Ici
