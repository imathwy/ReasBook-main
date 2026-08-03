module

import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact

/- Example 26.5 (1): Every closed subspace of a closed real interval is compact. -/
#check (fun {a b : ℝ} (s : Set (Set.Icc a b)) (hs : IsClosed s) ↦ hs.isCompact :
  ∀ {a b : ℝ} (s : Set (Set.Icc a b)), IsClosed s → IsCompact s)

/- Example 26.5 (2): If `a < b`, then the half-open interval `(a, b]` is not compact. -/
#check (fun {a b : ℝ} (hab : a < b) (hcompact : IsCompact (Set.Ioc a b)) ↦
  not_le_of_gt hab (isCompact_Ioc_iff.mp hcompact) :
  ∀ {a b : ℝ}, a < b → ¬ IsCompact (Set.Ioc a b))

/- Example 26.5 (3): If `a < b`, then the open interval `(a, b)` is not compact. -/
#check (fun {a b : ℝ} (hab : a < b) (hcompact : IsCompact (Set.Ioo a b)) ↦
  not_le_of_gt hab (isCompact_Ioo_iff.mp hcompact) :
  ∀ {a b : ℝ}, a < b → ¬ IsCompact (Set.Ioo a b))
