module

public import Mathlib.Topology.Algebra.Group.Quotient

public section

universe u

open Topology
open scoped Pointwise

/-- Helper for Exercise 2.99.7: a closed set and an exterior point admit disjoint
right translates of one open identity neighborhood. -/
lemma exists_open_nhds_one_disjoint_mul_right_set
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {A : Set G} {x : G} (hA : IsClosed A) (hx : x ∉ A) :
    ∃ V : Set G, IsOpen V ∧ V ∈ 𝓝 (1 : G) ∧ Disjoint (V * {x}) (V * A) := by
  -- Pull the open complement of `A` back along right multiplication by `x`.
  have hpre : (fun g : G => g * x) ⁻¹' Aᶜ ∈ 𝓝 (1 : G) := by
    refine (hA.isOpen_compl.preimage (continuous_mul_const x)).mem_nhds ?_
    simpa only [Set.mem_preimage, one_mul, Set.mem_compl_iff]
  rcases exists_open_nhds_one_mul_subset hpre with ⟨U, hUopen, hUone, hUU⟩
  refine ⟨U ∩ U⁻¹, hUopen.inter hUopen.inv, ?_, ?_⟩
  · exact (hUopen.inter hUopen.inv).mem_nhds
      ⟨hUone, by simpa only [Set.mem_inv, inv_one]⟩
  -- A common point would force a product from `U * U` to carry `x` into `A`.
  · rw [Set.disjoint_left]
    intro z hzx hzA
    rcases Set.mem_mul.mp hzx with ⟨v, hv, x', hx', hvx⟩
    rcases Set.mem_mul.mp hzA with ⟨w, hw, a, ha, hwa⟩
    simp only [Set.mem_inter_iff] at hv hw
    simp only [Set.mem_singleton_iff] at hx'
    subst x'
    have hwinv : w⁻¹ ∈ U := by
      simpa only [Set.mem_inv, inv_inv] using hw.2
    have hprod : w⁻¹ * v ∈ U * U := Set.mul_mem_mul hwinv hv.1
    have hnotmem : (w⁻¹ * v) * x ∉ A := hUU hprod
    apply hnotmem
    have heq : (w⁻¹ * v) * x = a := by
      calc
        (w⁻¹ * v) * x = w⁻¹ * (v * x) := by rw [mul_assoc]
        _ = w⁻¹ * z := by rw [hvx]
        _ = w⁻¹ * (w * a) := by rw [hwa]
        _ = a := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    rwa [heq]

namespace Disjoint

/-- Helper for Exercise 2.99.7: right saturation by a subgroup preserves separation
from a right-invariant set. -/
lemma mul_right_subgroup_of_right_invariant
    {G : Type u} [Group G] {H : Subgroup G} {A V : Set G} {x : G}
    (hA : A * (H : Set G) = A) (hdisj : Disjoint (V * {x}) (V * A)) :
    Disjoint ((V * {x}) * (H : Set G)) (V * A) := by
  rw [Set.disjoint_left] at hdisj ⊢
  intro z hzsat hzA
  rcases Set.mem_mul.mp hzsat with ⟨p, hp, h, hh, hph⟩
  rcases Set.mem_mul.mp hp with ⟨v, hv, x', hx', hvx⟩
  rcases Set.mem_mul.mp hzA with ⟨w, hw, a, ha, hwa⟩
  simp only [Set.mem_singleton_iff] at hx'
  subst x'
  -- Move the subgroup factor to the closed-set component using right invariance.
  have hahinv : a * h⁻¹ ∈ A := by
    rw [← hA]
    exact Set.mul_mem_mul ha (H.inv_mem hh)
  refine hdisj (Set.mul_mem_mul hv (Set.mem_singleton x)) ?_
  have heq : v * x = w * (a * h⁻¹) := by
    calc
      v * x = (v * x * h) * h⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = (p * h) * h⁻¹ := by rw [hvx]
      _ = z * h⁻¹ := by rw [hph]
      _ = (w * a) * h⁻¹ := by rw [hwa]
      _ = w * (a * h⁻¹) := by rw [mul_assoc]
  rw [heq]
  exact Set.mul_mem_mul hw hahinv

end Disjoint

namespace QuotientGroup

/-- The left-coset quotient of a topological group is regular. -/
instance instRegularSpace
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (H : Subgroup G) : RegularSpace (G ⧸ H) := by
  constructor
  intro C q hC hq
  rcases (QuotientGroup.mk_surjective (s := H)) q with ⟨x, rfl⟩
  let A : Set G := (QuotientGroup.mk (s := H)) ⁻¹' C
  have hAclosed : IsClosed A := hC.preimage QuotientGroup.continuous_mk
  have hxA : x ∉ A := hq
  rcases exists_open_nhds_one_disjoint_mul_right_set hAclosed hxA with
    ⟨V, hVopen, hVnhds, hdisj⟩
  -- The lifted closed set is saturated under right multiplication by `H`.
  have hAsat : A * (H : Set G) = A := by
    calc
      A * (H : Set G) = QuotientGroup.mk ⁻¹' (QuotientGroup.mk (s := H) '' A) :=
        (QuotientGroup.preimage_image_mk_eq_mul H A).symm
      _ = (QuotientGroup.mk (s := H)) ⁻¹' C := by
        rw [Set.image_preimage_eq C (QuotientGroup.mk_surjective (s := H))]
      _ = A := rfl
  have hQsat : (V * A) * (H : Set G) = V * A := by
    calc
      (V * A) * (H : Set G) = V * (A * (H : Set G)) := by rw [mul_assoc]
      _ = V * A := by rw [hAsat]
  -- Prove quotient-image disjointness by comparing preimages under the surjective quotient map.
  have himages : Disjoint
      (QuotientGroup.mk (s := H) '' (V * {x}))
      (QuotientGroup.mk (s := H) '' (V * A)) := by
    apply Disjoint.of_preimage (QuotientGroup.mk_surjective (s := H))
    rw [QuotientGroup.preimage_image_mk_eq_mul H,
      QuotientGroup.preimage_image_mk_eq_mul H, hQsat]
    exact Disjoint.mul_right_subgroup_of_right_invariant hAsat hdisj
  have hone : (1 : G) ∈ V := mem_of_mem_nhds hVnhds
  have hCsubset : C ⊆ QuotientGroup.mk (s := H) '' (V * A) := by
    rw [← Set.image_preimage_eq C (QuotientGroup.mk_surjective (s := H))]
    exact Set.image_mono fun a ha ↦ by
      simpa only [one_mul] using Set.mul_mem_mul hone ha
  have hxmem : (x : G ⧸ H) ∈ QuotientGroup.mk (s := H) '' (V * {x}) := by
    exact ⟨x, by simpa only [one_mul] using
      Set.mul_mem_mul hone (Set.mem_singleton x), rfl⟩
  -- The two open quotient images furnish the required disjoint filters.
  refine Filter.disjoint_of_disjoint_of_mem himages.symm ?_ ?_
  · exact (QuotientGroup.isOpenMap_coe (V * A) hVopen.mul_right).mem_nhdsSet.mpr hCsubset
  · exact (QuotientGroup.isOpenMap_coe (V * {x}) hVopen.mul_right).mem_nhds hxmem

end QuotientGroup
