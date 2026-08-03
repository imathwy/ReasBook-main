module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Topology.Algebra.ConstMulAction

public section

open Filter Set
open scoped Topology

universe u v

/- Definition 81.6: A group action is properly discontinuous when each point has a neighborhood
disjoint from every nonidentity translate; distinct translates of that neighborhood are then
pairwise disjoint. -/
/-- Definition 81.6: A continuous group action is properly discontinuous when every point has a
neighborhood disjoint from each of its nonidentity translates. -/
class ProperlyDiscontinuousMulAction (G : Type u) (X : Type v) [Group G]
    [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X] : Prop where
  exists_nhds_disjoint_image (x : X) :
    ∃ U ∈ 𝓝 x, ∀ g : G, g ≠ 1 → Disjoint ((g • ·) '' U) U

namespace ProperlyDiscontinuousMulAction

variable {G : Type u} {X : Type v} [Group G] [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [ProperlyDiscontinuousMulAction G X]

/-- Helper for Definition 81.6: every point has a neighborhood whose translates by distinct
group elements are pairwise disjoint. -/
theorem exists_nhds_pairwise_disjoint_image (x : X) :
    ∃ U ∈ 𝓝 x, ∀ ⦃g₀ g₁ : G⦄, g₀ ≠ g₁ →
      Disjoint ((g₀ • ·) '' U) ((g₁ • ·) '' U) := by
  -- Start with a neighborhood disjoint from each of its nonidentity translates.
  obtain ⟨U, hU, hdisjoint⟩ :=
    ProperlyDiscontinuousMulAction.exists_nhds_disjoint_image (G := G) x
  refine ⟨U, hU, fun {g₀ g₁} hne ↦ Set.disjoint_left.mpr ?_⟩
  intro y hy₀ hy₁
  obtain ⟨u₀, hu₀, rfl⟩ := hy₀
  obtain ⟨u₁, hu₁, heq⟩ := hy₁
  -- Translate a common point by `g₀⁻¹`, reducing to the defining disjointness.
  have hrelative : g₀⁻¹ * g₁ ≠ 1 := by
    intro h
    exact hne (inv_mul_eq_one.mp h)
  have hu₀eq : u₀ = (g₀⁻¹ * g₁) • u₁ := by
    simpa only [mul_smul, inv_smul_smul] using
      (congrArg (fun z ↦ g₀⁻¹ • z) heq).symm
  exact Set.disjoint_left.mp (hdisjoint (g₀⁻¹ * g₁) hrelative)
    ⟨u₁, hu₁, hu₀eq.symm⟩ hu₀

end ProperlyDiscontinuousMulAction
