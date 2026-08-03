module

public import Topology_Munkres_2000.Book.Exercise_2_99_7.Separation

public section

universe u

open Topology
open scoped Pointwise

namespace IsTopologicalGroup

/-- Exercise 2.99.7 (2): Distinct points of a T1 topological group have disjoint right
translates of a common neighborhood of the identity. -/
theorem exists_nhds_one_disjoint_mul_right
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [T1Space G]
    {x y : G} (hxy : x ≠ y) :
    ∃ V ∈ 𝓝 (1 : G), Disjoint (V * {x}) (V * {y}) := by
  -- Translate disjoint neighborhoods of the two points back to the identity.
  rcases t2_separation_nhds hxy with ⟨U, W, hU, hW, hUW⟩
  have hxnhds : U * {x⁻¹} ∈ 𝓝 (1 : G) := by
    simpa only [mul_inv_cancel] using mul_singleton_mem_nhds x⁻¹ hU
  have hynhds : W * {y⁻¹} ∈ 𝓝 (1 : G) := by
    simpa only [mul_inv_cancel] using mul_singleton_mem_nhds y⁻¹ hW
  refine ⟨(U * {x⁻¹}) ∩ (W * {y⁻¹}), Filter.inter_mem hxnhds hynhds, ?_⟩
  -- Translating the intersection forward places each translate in its original neighborhood.
  refine hUW.mono ?_ ?_
  · calc
      ((U * {x⁻¹}) ∩ (W * {y⁻¹})) * {x} ⊆ (U * {x⁻¹}) * {x} :=
        Set.mul_subset_mul_right Set.inter_subset_left
      _ = U := by
        rw [mul_assoc, Set.singleton_mul_singleton, inv_mul_cancel]
        simp
  · calc
      ((U * {x⁻¹}) ∩ (W * {y⁻¹})) * {y} ⊆ (W * {y⁻¹}) * {y} :=
        Set.mul_subset_mul_right Set.inter_subset_right
      _ = W := by
        rw [mul_assoc, Set.singleton_mul_singleton, inv_mul_cancel]
        simp

end IsTopologicalGroup

/- Exercise 2.99.7 (1): Every identity neighborhood contains a symmetric identity
neighborhood whose pointwise square is contained in the original neighborhood. -/
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) ↦
  exists_closed_nhds_one_inv_eq_mul_subset hU

/- Exercise 2.99.7 (2): Distinct points have disjoint right translates of a common
neighborhood of the identity. -/
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T1Space G] {x y : G} (hxy : x ≠ y) ↦
  IsTopologicalGroup.exists_nhds_one_disjoint_mul_right hxy

/- Exercise 2.99.7 (2): In particular, every topological group in the book's T1
convention is Hausdorff. -/
#check fun (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T1Space G] ↦ (inferInstance : T2Space G)

/- Exercise 2.99.7 (3): A topological group in the book's T1 convention has the
regularity property. -/
#check fun (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    ↦ (inferInstance : RegularSpace G)

/- Exercise 2.99.7 (4): More generally, every coset quotient of a topological group
satisfies the regularity axiom; the source's closed-subgroup case follows immediately. -/
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (H : Subgroup G) ↦ (inferInstance : RegularSpace (G ⧸ H))
