module

public import Topology_Munkres_2000.Book.Definition_60_3.Quotient
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

import Topology_Munkres_2000.Book.Theorem_54_4
import Topology_Munkres_2000.Book.Theorem_59_3
import Topology_Munkres_2000.Book.Theorem_60_3
import Mathlib.Data.Set.Card

public section

namespace RealProjectivePlane

/-- Helper for Corollary 60.4: the fiber over the image of a sphere point is its
antipodal pair. -/
private lemma quotientMap_fiber_eq_pair (x : StandardSphere 2) :
    quotientMap ⁻¹' {quotientMap x} = {x, -x} := by
  -- Reduce fiber membership to the quotient's equal-or-antipodal relation.
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff, quotientMap_eq_iff,
    Set.mem_insert_iff]
  constructor
  · rintro (rfl | hz)
    · exact Or.inl rfl
    · right
      have hneg := congrArg Neg.neg hz
      simpa using hneg.symm
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · right
      simp

/-- Helper for Corollary 60.4: every fiber of the projective-plane quotient has exactly
two points. -/
private lemma quotientMap_fiber_ncard (y : RealProjectivePlane) :
    (quotientMap ⁻¹' {y}).ncard = 2 := by
  -- Choose a representative, expose its antipodal pair, and count its distinct points.
  obtain ⟨x, rfl⟩ := quotientMap_surjective y
  rw [quotientMap_fiber_eq_pair]
  exact Set.ncard_pair (ne_neg_of_mem_unit_sphere ℝ x)

/-- Corollary 60.4. The fundamental group of the real projective plane at any
basepoint has order two. -/
theorem fundamentalGroup_card (y : RealProjectivePlane) :
    Nat.card (FundamentalGroup RealProjectivePlane y) = 2 := by
  -- Simple connectedness makes the lifting correspondence a bijection with one fiber.
  have htwo : 2 ≤ 2 := Nat.le_refl 2
  letI : SimplyConnectedSpace (StandardSphere 2) :=
    simplyConnectedSpace_standardSphere 2 htwo
  have hcover : IsCoveringMap quotientMap := quotientMap_isCoveringMap
  obtain ⟨x, hx⟩ := quotientMap_surjective y
  have hxmem : x ∈ quotientMap ⁻¹' {y} := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx
  let e₀ : quotientMap ⁻¹' {y} := ⟨x, hxmem⟩
  have hlift : Function.Bijective (hcover.liftingCorrespondence e₀) :=
    hcover.liftingCorrespondence_bijective e₀
  -- Transport cardinality across that bijection, then count the antipodal fiber.
  calc
    Nat.card (FundamentalGroup RealProjectivePlane y) =
        Nat.card (quotientMap ⁻¹' {y}) :=
      Nat.card_eq_of_bijective (hcover.liftingCorrespondence e₀) hlift
    _ = (quotientMap ⁻¹' {y}).ncard := Nat.card_coe_set_eq _
    _ = 2 := quotientMap_fiber_ncard y

end RealProjectivePlane
