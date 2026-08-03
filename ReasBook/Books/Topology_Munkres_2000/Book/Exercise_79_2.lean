module

public import Topology_Munkres_2000.Book.Definition_60_3.Quotient
public import Topology_Munkres_2000.Book.Definition_53_4.Torus
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Homotopy.Contractible

import Topology_Munkres_2000.Book.Corollary_60_4
import Topology_Munkres_2000.Book.Exercise_55_2
import Topology_Munkres_2000.Book.Theorem_59_3
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

public section

/-- Helper for Exercise 79.2: a homomorphism from a finite group to a multiplicatively
torsion-free group is trivial. -/
private lemma MonoidHom.eq_one_of_finite_to_isMulTorsionFree
    {G H : Type*} [Group G] [Finite G] [Group H] [IsMulTorsionFree H]
    (φ : G →* H) : φ = 1 := by
  -- Every source element has finite order, so its image must be the target identity.
  ext g
  exact (φ.isOfFinOrder (isOfFinOrder_of_finite g)).eq_one'

/-- Helper for Exercise 79.2: a map from a space with finite fundamental group induces the
trivial homomorphism into the fundamental group of the circle. -/
private lemma fundamentalGroupMap_toCircle_eq_one_of_finite
    {X : Type*} [TopologicalSpace X] (f : C(X, Circle)) (x : X)
    [Finite (FundamentalGroup X x)] :
    FundamentalGroup.map f x = 1 := by
  let circleCoordinates :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (f x) 1).trans
      Circle.fundamentalGroupEquivInt
  -- In integer coordinates the induced homomorphism is finite-to-torsion-free, hence trivial.
  have hcoordinates :
      circleCoordinates.toMonoidHom.comp (FundamentalGroup.map f x) = 1 :=
    MonoidHom.eq_one_of_finite_to_isMulTorsionFree _
  -- Injectivity of the coordinate equivalence reflects triviality back to the circle group.
  ext γ
  apply circleCoordinates.injective
  simpa only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.one_apply, map_one,
    MulEquiv.coe_toMonoidHom] using DFunLike.congr_fun hcoordinates γ

/-- Exercise 79.2 (1). Every continuous map from the real projective plane to the circle is
nullhomotopic. -/
theorem realProjectivePlaneToCircle_nullhomotopic
    (f : C(RealProjectivePlane, Circle)) : f.Nullhomotopic := by
  -- Quotient instances transfer the sphere's connectedness and local path-connectedness to ℝP².
  letI : SimplyConnectedSpace (StandardSphere 2) :=
    simplyConnectedSpace_standardSphere 2 (Nat.le_refl 2)
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2))
      (StandardSphere 2)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty RealProjectivePlane)
  have hcardNe : Nat.card (FundamentalGroup RealProjectivePlane x₀) ≠ 0 := by
    rw [RealProjectivePlane.fundamentalGroup_card]
    norm_num
  letI : Finite (FundamentalGroup RealProjectivePlane x₀) :=
    Nat.finite_of_card_ne_zero hcardNe
  have hmap : FundamentalGroup.map f x₀ = 1 :=
    fundamentalGroupMap_toCircle_eq_one_of_finite f x₀
  obtain ⟨e₀, he₀⟩ := Circle.exp_surjective (f x₀)
  -- The trivial induced map has bottom range, which lies in the covering subgroup of `exp`.
  have hRange :
      (FundamentalGroup.map f x₀).range ≤
        (FundamentalGroup.mapOfEq
          ⟨Circle.exp, Circle.isCoveringMap_exp.continuous⟩ he₀).range := by
    rw [MonoidHom.range_eq_bot_iff.mpr hmap]
    exact bot_le
  obtain ⟨F, hF, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts_of_range_le he₀ hRange
  -- Bundle the pointwise lift identity before using the contractibility of the real line.
  have liftEquation : Circle.exp.comp F = f := by
    apply ContinuousMap.ext
    intro x
    exact congrFun hF.2 x
  have liftNullhomotopic : F.Nullhomotopic := by
    simpa only [ContinuousMap.id_comp] using
      (id_nullhomotopic ℝ).comp_left F
  rw [← liftEquation]
  exact liftNullhomotopic.comp_right Circle.exp

/-- Exercise 79.2 (2). The first projection from the torus to the circle is not
nullhomotopic. -/
theorem torusFst_not_nullhomotopic :
    ¬ (ContinuousMap.fst : C(Torus, Circle)).Nullhomotopic := by
  intro hfst
  let circleSection : C(Circle, Torus) :=
    ContinuousMap.prodMk (ContinuousMap.id Circle) (ContinuousMap.const Circle 1)
  -- Restricting the first projection to its circle section recovers the identity map.
  have hsection :
      (ContinuousMap.fst : C(Torus, Circle)).comp circleSection =
        ContinuousMap.id Circle := by
    apply ContinuousMap.ext
    intro z
    simp only [ContinuousMap.comp_apply, circleSection, ContinuousMap.prod_eval,
      ContinuousMap.fst_apply, ContinuousMap.id_apply]
  have hidNullhomotopic := hfst.comp_left circleSection
  rw [hsection] at hidNullhomotopic
  exact circle_id_not_nullhomotopic hidNullhomotopic
