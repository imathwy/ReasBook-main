module

import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Topology.Algebra.Group.Quotient

universe u

/- Definition 2.99.4: For a subgroup `H` of a group `G`, the quotient `G ⧸ H`
is the collection of left cosets of `H`, these cosets partition `G`, and the
topology on `G ⧸ H` is the quotient topology induced by `QuotientGroup.mk`. -/
#check fun {G : Type u} [Group G] (H : Subgroup G) ↦ G ⧸ H
#check fun {G : Type u} [Group G] (H : Subgroup G) ↦
  QuotientGroup.leftRel_r_eq_leftCosetEquivalence H
#check fun {G : Type u} [Group G] (H : Subgroup G) ↦
  Setoid.isPartition_classes (QuotientGroup.leftRel H)
#check fun {G : Type u} [Group G] [TopologicalSpace G] (H : Subgroup G) ↦
  (inferInstance : TopologicalSpace (G ⧸ H))
#check fun {G : Type u} [Group G] [TopologicalSpace G] (H : Subgroup G) ↦
  QuotientGroup.isQuotientMap_mk H
