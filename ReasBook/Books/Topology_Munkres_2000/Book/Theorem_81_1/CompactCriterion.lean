module

public import Mathlib.Topology.Algebra.ConstMulAction

public section

open Set

universe u v

variable {G : Type u} {X : Type v} [Group G] [TopologicalSpace X] [MulAction G X]

/-- The compact-pair definition of `ProperlyDiscontinuousSMul G X` is equivalent to
checking only self-intersections of each compact set with its translates. -/
theorem properlyDiscontinuousSMul_iff_compact_inter_self :
    ProperlyDiscontinuousSMul G X ↔
      ∀ {C : Set X}, IsCompact C →
        {g : G | (C ∩ (g • ·) '' C).Nonempty}.Finite := by
  constructor
  · intro hproper C hC
    -- The self-intersection condition is the compact-pair condition with both sets equal to `C`.
    simpa only [inter_comm] using hproper.finite_disjoint_inter_image hC hC
  · intro hself
    rw [properlyDiscontinuousSMul_iff]
    intro K L hK hL
    -- Any translate meeting `K` and `L` also gives a self-intersection of `K ∪ L`.
    refine (hself (hK.union hL)).subset ?_
    intro g hg
    rcases hg with ⟨x, ⟨y, hyK, rfl⟩, hxL⟩
    exact ⟨g • y, Or.inr hxL, y, Or.inl hyK, rfl⟩
