module

public import Topology_Munkres_2000.Book.Definition_60_3.Quotient
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Covering.Quotient

public section

namespace RealProjectivePlane

/-- Helper for Remark 60.1: the unit sphere in Euclidean three-space. -/
abbrev UnitSphereThree :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- Helper for Remark 60.1: `Bool` acts on the unit sphere by the identity and antipode. -/
noncomputable instance antipodalBoolVAdd : VAdd Bool UnitSphereThree :=
  ⟨fun b x ↦ if b = true then -x else x⟩

/-- Helper for Remark 60.1: the false Boolean fixes every sphere point. -/
@[simp]
lemma false_vadd_sphere (x : UnitSphereThree) : false +ᵥ x = x := by
  -- Unfold the two-element action at its identity element.
  rfl

/-- Helper for Remark 60.1: the true Boolean sends every sphere point to its antipode. -/
@[simp]
lemma true_vadd_sphere (x : UnitSphereThree) : true +ᵥ x = -x := by
  -- Unfold the nonidentity deck transformation.
  rfl

/-- Helper for Remark 60.1: the antipodal Boolean action respects Boolean addition. -/
lemma antipodalBool_add_vadd (b c : Bool) (x : UnitSphereThree) :
    (b + c) +ᵥ x = b +ᵥ c +ᵥ x := by
  -- Check the four elements of the two-element group directly.
  cases b <;> cases c
  · rw [show false + false = false by decide]
    simp
  · rw [show false + true = true by decide]
    simp
  · rw [show true + false = true by decide]
    simp
  · rw [show true + true = false by decide]
    simp

/-- Helper for Remark 60.1: the Boolean identity acts trivially on the sphere. -/
lemma antipodalBool_zero_vadd (x : UnitSphereThree) : (0 : Bool) +ᵥ x = x := by
  -- Boolean zero is the false deck transformation.
  exact false_vadd_sphere x

/-- Helper for Remark 60.1: the identity-antipode operation is an additive action. -/
noncomputable instance antipodalBoolAction : AddAction Bool UnitSphereThree :=
  { add_vadd := antipodalBool_add_vadd
    zero_vadd := antipodalBool_zero_vadd }

/-- Helper for Remark 60.1: every fixed Boolean deck transformation is continuous. -/
lemma continuous_antipodalBoolVAdd (b : Bool) :
    Continuous fun x : UnitSphereThree ↦ b +ᵥ x := by
  -- The two action maps are the identity and continuous negation.
  cases b
  · exact continuous_id
  · exact continuous_neg

/-- Helper for Remark 60.1: the antipodal Boolean action is continuous in the sphere variable. -/
instance antipodalBoolContinuousConstVAdd : ContinuousConstVAdd Bool UnitSphereThree :=
  ⟨continuous_antipodalBoolVAdd⟩

/-- Helper for Remark 60.1: the antipodal Boolean action is free. -/
lemma antipodalBool_right_cancel (b c : Bool) (x : UnitSphereThree)
    (h : b +ᵥ x = c +ᵥ x) : b = c := by
  -- Distinct Boolean transformations would identify a sphere point with its antipode.
  cases b <;> cases c
  · rfl
  · exact False.elim (ne_neg_of_mem_unit_sphere ℝ x h)
  · exact False.elim (ne_neg_of_mem_unit_sphere ℝ x h.symm)
  · rfl

/-- Helper for Remark 60.1: the antipodal Boolean action is cancellative. -/
instance antipodalBoolIsCancelVAdd : IsCancelVAdd Bool UnitSphereThree where
  left_cancel' b x y h := by
    -- Each deck transformation is either the identity or the injective negation map.
    cases b
    · simpa using h
    · simpa using congrArg Neg.neg h
  right_cancel' := antipodalBool_right_cancel

/-- Helper for Remark 60.1: Boolean orbits are precisely equal-or-antipodal pairs. -/
lemma mem_antipodalBoolOrbit_iff (x y : UnitSphereThree) :
    x ∈ AddAction.orbit Bool y ↔ y = x ∨ y = -x := by
  -- Expand the orbit witness and split the two possible deck transformations.
  rw [AddAction.mem_orbit_iff]
  constructor
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inl (by simpa using hb)
    · exact Or.inr (by simpa using congrArg Neg.neg hb)
  · rintro (rfl | rfl)
    · exact ⟨false, by simp⟩
    · exact ⟨true, by simp⟩

/-- Helper for Remark 60.1: the sphere quotient is the covering quotient by the antipodal
Boolean action. -/
lemma quotientMap_isAddQuotientCoveringMap :
    IsAddQuotientCoveringMap quotientMap Bool := by
  -- Match the quotient's explicit fibers with Boolean orbits, then invoke the finite-action API.
  refine quotientMap_isQuotientMap.isAddQuotientCoveringMap_of_properlyDiscontinuousVAdd ?_
  intro x y
  exact (quotientMap_eq_iff x y).trans (mem_antipodalBoolOrbit_iff x y).symm

/-- Helper for Remark 60.1: the antipodal sphere quotient is a covering map. -/
lemma quotientMap_isCoveringMap : IsCoveringMap quotientMap := by
  -- Forget the deck-group structure from the stronger quotient-covering package.
  exact quotientMap_isAddQuotientCoveringMap.isCoveringMap

/-- Helper for Remark 60.1: the total space of the antipodal double cover is connected. -/
lemma unitSphereThree_isConnectedSpace : ConnectedSpace UnitSphereThree := by
  -- The unit sphere in a three-dimensional real vector space is path connected.
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    exact Module.one_lt_rank_of_one_lt_finrank (by norm_num)
  exact Subtype.connectedSpace <| (isPathConnected_sphere hrank
    (0 : EuclideanSpace ℝ (Fin 3)) (show (0 : ℝ) ≤ 1 by norm_num)).isConnected

/-- Helper for Remark 60.1: the unit sphere in Euclidean three-space is nonempty. -/
lemma unitSphereThree_nonempty : Nonempty UnitSphereThree := by
  -- A positive-radius sphere in a nontrivial real normed space contains a point.
  exact (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)).coe_sort

/-- Helper for Remark 60.1: a continuous self-map of the sphere over the projective
quotient is either the identity or the antipodal map. -/
lemma continuous_selfLift_eq_id_or_neg
    (g : UnitSphereThree → UnitSphereThree) (hg : Continuous g)
    (hproj : quotientMap ∘ g = quotientMap) :
    g = id ∨ g = fun x ↦ -x := by
  letI : ConnectedSpace UnitSphereThree := unitSphereThree_isConnectedSpace
  -- Classify the lift at one point using the explicit two-point quotient fiber.
  let x : UnitSphereThree := Classical.choice unitSphereThree_nonempty
  rcases (quotientMap_eq_iff x (g x)).mp (congrFun hproj.symm x) with hx | hx
  · left
    -- Covering-map uniqueness propagates equality with the identity from the base point.
    have hcomp : quotientMap ∘ g = quotientMap ∘ id := by
      simpa [Function.comp_def] using hproj
    exact quotientMap_isCoveringMap.eq_of_comp_eq hg continuous_id hcomp x hx
  · right
    -- The antipodal map is the other lift, and agreement at the base point is global.
    have hcomp : quotientMap ∘ g = quotientMap ∘ fun y ↦ -y := by
      funext y
      exact (congrFun hproj y).trans (quotientMap_neg y).symm
    exact quotientMap_isCoveringMap.eq_of_comp_eq hg continuous_neg hcomp x hx

/-- Helper for Remark 60.1: the antipodal quotient of the sphere has no continuous
right inverse. -/
lemma quotientMap_hasNoContinuousSection :
    ¬ ∃ s : RealProjectivePlane → UnitSphereThree,
      Continuous s ∧ Function.RightInverse s quotientMap := by
  -- A section would produce a self-lift of the quotient map.
  rintro ⟨s, hs, hright⟩
  let g : UnitSphereThree → UnitSphereThree := s ∘ quotientMap
  have hg : Continuous g := hs.comp quotientMap_isCoveringMap.continuous
  have hproj : quotientMap ∘ g = quotientMap := by
    funext x
    exact hright (quotientMap x)
  rcases continuous_selfLift_eq_id_or_neg g hg hproj with hgid | hgneg
  · -- The section identifies antipodal inputs, contradicting the identity lift.
    let x : UnitSphereThree := Classical.choice unitSphereThree_nonempty
    have hsame : g (-x) = g x := by
      simp only [g, Function.comp_apply, quotientMap_neg]
    rw [hgid] at hsame
    exact ne_neg_of_mem_unit_sphere ℝ x hsame.symm
  · -- The same identification also contradicts the antipodal lift.
    let x : UnitSphereThree := Classical.choice unitSphereThree_nonempty
    have hsame : g (-x) = g x := by
      simp only [g, Function.comp_apply, quotientMap_neg]
    rw [hgneg] at hsame
    exact ne_neg_of_mem_unit_sphere ℝ x (by simpa using hsame)

end RealProjectivePlane
