module

import Mathlib.Topology.GDelta.Basic

universe u

variable {X : Type u} [TopologicalSpace X]

/-
Definition 48.3. Mathlib's `IsMeagre A` says exactly that `A : Set X` is of the
first category in `X`: it is contained in a countable union of closed sets with
empty interior. The set `A` is of the second category in `X` when
`¬ IsMeagre A`.
-/
#check (IsMeagre : Set X → Prop)
#check isMeagre_iff_countable_union_isNowhereDense
#check IsNowhereDense.subset_of_closed_isNowhereDense
#check IsClosed.isNowhereDense_iff
#check fun A : Set X ↦ ¬ IsMeagre A
