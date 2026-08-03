module

public import Topology_Munkres_2000.Book.Definition_60_3.Quotient
public import Topology_Munkres_2000.Book.Definition_60_4.Covering
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

import Topology_Munkres_2000.Book.Theorem_54_4
import Topology_Munkres_2000.Book.Theorem_59_3
import Mathlib.Data.Set.Card

public section

/- Definition 60.4 (1): Real projective `n`-space is the antipodal quotient of the
unit sphere `Sⁿ`, with its canonical quotient projection. -/
#check RealProjectiveSpace
#check RealProjectiveSpace.quotientMap

/- Definition 60.4 (2): For positive `n`, the projection from `Sⁿ` to real
projective `n`-space is a covering map in Munkres's surjective sense. -/
#check RealProjectiveSpace.quotientMap_isMunkresCoveringMap

/- The covering-map component in mathlib's canonical API. -/
#check RealProjectiveSpace.quotientMap_isCoveringMap

namespace RealProjectiveSpace

/-- Helper for Definition 60.4: the fiber over the image of a sphere point is its
antipodal pair. -/
private lemma quotientMap_fiber_eq_pair (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    (quotientMap n) ⁻¹' {quotientMap n x} = {x, -x} := by
  -- Reduce fiber membership to the quotient's equal-or-antipodal relation.
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff, quotientMap_eq_iff,
    Set.mem_insert_iff]
  constructor
  · rintro (rfl | hy)
    · exact Or.inl rfl
    · right
      have hneg := congrArg Neg.neg hy
      simpa using hneg.symm
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · right
      simp

/-- Helper for Definition 60.4: every fiber of the projective-space quotient has
exactly two points. -/
private lemma quotientMap_fiber_ncard (n : ℕ) (y : RealProjectiveSpace n) :
    ((quotientMap n) ⁻¹' {y}).ncard = 2 := by
  -- Choose a representative, expose its antipodal pair, and use freeness of negation.
  obtain ⟨x, rfl⟩ := quotientMap_surjective n y
  rw [quotientMap_fiber_eq_pair]
  exact Set.ncard_pair (ne_neg_of_mem_unit_sphere ℝ x)

/-- Definition 60.4: for `2 ≤ n`, the fundamental group of real projective `n`-space
at any basepoint has order two. -/
theorem fundamentalGroup_card (n : ℕ) (hn : 2 ≤ n) (y : RealProjectiveSpace n) :
    Nat.card (FundamentalGroup (RealProjectiveSpace n) y) = 2 := by
  -- Simple connectedness makes the lifting correspondence a bijection with one fiber.
  letI : SimplyConnectedSpace (StandardSphere n) :=
    simplyConnectedSpace_standardSphere n hn
  have hnpos : 0 < n := Nat.zero_lt_two.trans_le hn
  have hcover : IsCoveringMap (quotientMap n) := quotientMap_isCoveringMap n hnpos
  obtain ⟨x, hx⟩ := quotientMap_surjective n y
  have hxmem : x ∈ (quotientMap n) ⁻¹' {y} := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx
  let e₀ : (quotientMap n) ⁻¹' {y} := ⟨x, hxmem⟩
  have hlift : Function.Bijective (hcover.liftingCorrespondence e₀) :=
    hcover.liftingCorrespondence_bijective e₀
  -- Transport cardinality across that bijection and count the antipodal pair.
  calc
    Nat.card (FundamentalGroup (RealProjectiveSpace n) y) =
        Nat.card ((quotientMap n) ⁻¹' {y}) :=
      Nat.card_eq_of_bijective (hcover.liftingCorrespondence e₀) hlift
    _ = ((quotientMap n) ⁻¹' {y}).ncard := Nat.card_coe_set_eq _
    _ = 2 := quotientMap_fiber_ncard n y

end RealProjectiveSpace
