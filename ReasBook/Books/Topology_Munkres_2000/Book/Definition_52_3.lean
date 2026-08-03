module

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Setoid.Partition

universe u v

open scoped Pointwise

/- Definition 52.3: Left and right cosets of a subgroup partition a group. A
subgroup `H` is normal when it is closed under conjugation, equivalently when
its left and right cosets agree. For normal `H`, the quotient `G ⧸ H` is a
group and the canonical projection is surjective with kernel `H`. Conversely,
the kernel of a surjective group homomorphism is normal, and the homomorphism
induces the canonical isomorphism from the quotient by its kernel. -/
#check fun {G : Type u} [Group G] (H : Subgroup G) ↦ H.Normal
#check fun {G : Type u} [Group G] (H : Subgroup G) (x : G) ↦ x • (H : Set G)
#check fun {G : Type u} [Group G] (H : Subgroup G) (x : G) ↦ MulOpposite.op x • (H : Set G)
#check fun {G : Type u} [Group G] (H : Subgroup G) ↦
  QuotientGroup.leftRel_r_eq_leftCosetEquivalence H
#check fun {G : Type u} [Group G] (H : Subgroup G) ↦
  Setoid.isPartition_classes (QuotientGroup.leftRel H)
#check fun {G : Type u} [Group G] (H : Subgroup G) ↦
  QuotientGroup.rightRel_r_eq_rightCosetEquivalence H
#check fun {G : Type u} [Group G] (H : Subgroup G) ↦
  Setoid.isPartition_classes (QuotientGroup.rightRel H)
#check fun {G : Type u} [Group G] (H : Subgroup G) ↦ normal_iff_eq_cosets H
#check fun {G : Type u} [Group G] (H : Subgroup G) ↦ G ⧸ H
#check fun {G : Type u} [Group G] (H : Subgroup G) [H.Normal] ↦
  (inferInstance : Group (G ⧸ H))
#check fun {G : Type u} [Group G] (H : Subgroup G) [H.Normal] ↦ QuotientGroup.mk' H
#check fun {G : Type u} [Group G] (H : Subgroup G) [H.Normal] (x : G) ↦
  QuotientGroup.mk'_apply H x
#check fun {G : Type u} [Group G] (H : Subgroup G) [H.Normal] (x y : G) ↦
  (QuotientGroup.mk' H).map_mul x y
#check fun {G : Type u} [Group G] (H : Subgroup G) [H.Normal] ↦
  QuotientGroup.mk'_surjective H
#check fun {G : Type u} [Group G] (H : Subgroup G) [H.Normal] ↦ QuotientGroup.ker_mk' H
#check fun {G : Type u} {G' : Type v} [Group G] [Group G'] (f : G →* G') ↦
  MonoidHom.normal_ker f
#check fun {G : Type u} {G' : Type v} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) ↦ QuotientGroup.quotientKerEquivOfSurjective f hf
#check fun {G : Type u} {G' : Type v} [Group G] [Group G'] (f : G →* G') (x : G) ↦
  QuotientGroup.kerLift_mk f x
