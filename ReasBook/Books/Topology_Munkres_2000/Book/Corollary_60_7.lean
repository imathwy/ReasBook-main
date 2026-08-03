module

public import Topology_Munkres_2000.Book.Definition_53_4.Torus
public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_60_3.Quotient
public import Topology_Munkres_2000.Book.Definition_74_5.OrientablePasting

import Topology_Munkres_2000.Book.Theorem_59_3
import Topology_Munkres_2000.Book.Corollary_60_2
import Topology_Munkres_2000.Book.Corollary_60_4
import Topology_Munkres_2000.Book.Theorem_60_6
import Topology_Munkres_2000.Book.Definition_9_0_2
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

public section

open OrientableSurfacePresentation

/-- Helper for Corollary 60.7: multiplicative equivalences preserve commutativity. -/
private lemma isMulCommutativeOfMulEquiv {G H : Type*} [Mul G] [Mul H]
    (e : G ≃* H) (hG : IsMulCommutative G) : IsMulCommutative H := by
  -- Push commutativity forward along the surjective multiplicative map.
  exact Function.Surjective.mul_comm (f := e.toMulHom) e.surjective hG

/-- Helper for Corollary 60.7: the fundamental group of the torus is infinite. -/
private lemma torusFundamentalGroupNatCard :
    Nat.card (FundamentalGroup Torus (1, 1)) = 0 := by
  -- Transport cardinality to the product of two copies of `Multiplicative ℤ`.
  calc
    Nat.card (FundamentalGroup Torus (1, 1)) =
        Nat.card (Multiplicative ℤ × Multiplicative ℤ) :=
      Nat.card_congr fundamentalGroup_circle_prod_circle.toEquiv
    _ = 0 := Nat.card_eq_zero_of_infinite

/-- Helper for Corollary 60.7: the fundamental group of the torus is commutative. -/
private lemma torusFundamentalGroupIsMulCommutative :
    IsMulCommutative (FundamentalGroup Torus (1, 1)) := by
  -- Pull product commutativity back through the standard torus equivalence.
  exact isMulCommutativeOfMulEquiv fundamentalGroup_circle_prod_circle.symm inferInstance

/-- Helper for Corollary 60.7: every projective-plane fundamental group is commutative. -/
private lemma realProjectivePlaneFundamentalGroupIsMulCommutative
    (y : RealProjectivePlane) :
    IsMulCommutative (FundamentalGroup RealProjectivePlane y) := by
  -- A group of prime order two is cyclic, hence commutative.
  exact
    (isCyclic_of_prime_card (RealProjectivePlane.fundamentalGroup_card y)).isMulCommutative

/-- Corollary 60.7 (1). The 2-sphere and torus are not homeomorphic. -/
theorem twoSphere_not_homeomorphic_torus :
    ¬ Nonempty (StandardSphere 2 ≃ₜ Torus) := by
  rintro ⟨e⟩
  letI : SimplyConnectedSpace (StandardSphere 2) :=
    simplyConnectedSpace_standardSphere 2 (Nat.le_refl 2)
  -- A hypothetical homeomorphism would equate an infinite group with a trivial one.
  have hcard :=
    Nat.card_congr
      (e.symm.fundamentalGroupMulEquiv ((1, 1) : Torus)).toEquiv
  rw [torusFundamentalGroupNatCard, Nat.card_unique] at hcard
  omega

/-- Corollary 60.7 (2). The 2-sphere and real projective plane are not homeomorphic. -/
theorem twoSphere_not_homeomorphic_realProjectivePlane :
    ¬ Nonempty (StandardSphere 2 ≃ₜ RealProjectivePlane) := by
  rintro ⟨e⟩
  letI : SimplyConnectedSpace (StandardSphere 2) :=
    simplyConnectedSpace_standardSphere 2 (Nat.le_refl 2)
  obtain ⟨x⟩ : Nonempty (StandardSphere 2) :=
    NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  -- Compare the trivial sphere group with the order-two projective-plane group.
  have hcard := Nat.card_congr (e.fundamentalGroupMulEquiv x).toEquiv
  rw [Nat.card_unique, RealProjectivePlane.fundamentalGroup_card] at hcard
  omega

/-- Corollary 60.7 (3). The 2-sphere and double torus are not homeomorphic. -/
theorem twoSphere_not_homeomorphic_doubleTorus :
    ¬ Nonempty
      (StandardSphere 2 ≃ₜ
        nFoldTorus 2 zero_lt_two) := by
  rintro ⟨e⟩
  letI : SimplyConnectedSpace (StandardSphere 2) :=
    simplyConnectedSpace_standardSphere 2 (Nat.le_refl 2)
  obtain ⟨x⟩ : Nonempty (StandardSphere 2) :=
    NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  have hsphere : IsMulCommutative (FundamentalGroup (StandardSphere 2) x) :=
    inferInstance
  -- Transport sphere commutativity and contradict the double-torus theorem.
  have hdouble :=
    isMulCommutativeOfMulEquiv (e.fundamentalGroupMulEquiv x) hsphere
  exact fundamentalGroup_not_isMulCommutative 2 Nat.one_lt_two (e x) hdouble

/-- Corollary 60.7 (4). The torus and real projective plane are not homeomorphic. -/
theorem torus_not_homeomorphic_realProjectivePlane :
    ¬ Nonempty (Torus ≃ₜ RealProjectivePlane) := by
  rintro ⟨e⟩
  -- Compare the infinite torus group with the order-two projective-plane group.
  have hcard :=
    Nat.card_congr
      (e.fundamentalGroupMulEquiv ((1, 1) : Torus)).toEquiv
  rw [torusFundamentalGroupNatCard,
    RealProjectivePlane.fundamentalGroup_card] at hcard
  omega

/-- Corollary 60.7 (5). The torus and double torus are not homeomorphic. -/
theorem torus_not_homeomorphic_doubleTorus :
    ¬ Nonempty
      (Torus ≃ₜ
        nFoldTorus 2 zero_lt_two) := by
  rintro ⟨e⟩
  -- Transport torus commutativity and contradict the double-torus theorem.
  have hdouble :=
    isMulCommutativeOfMulEquiv
      (e.fundamentalGroupMulEquiv ((1, 1) : Torus))
      torusFundamentalGroupIsMulCommutative
  exact
    fundamentalGroup_not_isMulCommutative 2 Nat.one_lt_two (e (1, 1)) hdouble

/-- Corollary 60.7 (6). The real projective plane and double torus are not homeomorphic. -/
theorem realProjectivePlane_not_homeomorphic_doubleTorus :
    ¬ Nonempty
      (RealProjectivePlane ≃ₜ
        nFoldTorus 2 zero_lt_two) := by
  rintro ⟨e⟩
  obtain ⟨x⟩ : Nonempty (StandardSphere 2) :=
    NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  let y : RealProjectivePlane := RealProjectivePlane.quotientMap x
  -- Transport projective-plane commutativity and use double-torus noncommutativity.
  have hdouble :=
    isMulCommutativeOfMulEquiv (e.fundamentalGroupMulEquiv y)
      (realProjectivePlaneFundamentalGroupIsMulCommutative y)
  exact fundamentalGroup_not_isMulCommutative 2 Nat.one_lt_two (e y) hdouble
