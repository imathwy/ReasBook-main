module

import Topology_Munkres_2000.Book.Definition_9_0_2
import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
import Topology_Munkres_2000.Book.Theorem_58_2
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
public import Topology_Munkres_2000.Book.Exercise_35_4.RadialRetraction
public import Topology_Munkres_2000.Book.Theorem_59_1

public section

universe u

namespace PlaneTwoPunctureCover

/-- The second puncture in the fixed two-puncture cover of the Euclidean plane. -/
noncomputable def secondPuncture : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 0 1

/-- The basepoint in the fixed two-puncture cover of the Euclidean plane. -/
noncomputable def basepoint : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 1 1

/-- The Euclidean plane with the first puncture removed. -/
abbrev U : Set (EuclideanSpace ℝ (Fin 2)) :=
  EuclideanPlane.punctured

/-- The Euclidean plane with the second puncture removed. -/
def V : Set (EuclideanSpace ℝ (Fin 2)) :=
  ({secondPuncture} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ

/-- The chosen basepoint belongs to both sets in the fixed cover. -/
theorem basepoint_mem : basepoint ∈ U ∩ V := by
  -- The two nonmembership claims are detected in the coordinate where the points differ.
  constructor
  · rw [EuclideanPlane.mem_punctured_iff]
    intro hzero
    have hcoordinate := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1) hzero
    norm_num [basepoint, PiLp.single_apply] at hcoordinate
  · rw [V, Set.mem_compl_singleton_iff]
    intro heq
    have hcoordinate := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1) heq
    norm_num [basepoint, secondPuncture, PiLp.single_apply] at hcoordinate

/-- The first member of the fixed cover is open. -/
theorem isOpen_U : IsOpen U := by
  -- Use the owner membership API to identify the opaque punctured-plane set.
  have hUeq : U = ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext x
    simp only [EuclideanPlane.mem_punctured_iff, Set.mem_compl_singleton_iff]
  rw [hUeq]
  exact isOpen_compl_singleton

/-- The second member of the fixed cover is open. -/
theorem isOpen_V : IsOpen V := by
  -- The second member is likewise a singleton complement in a T1 space.
  simpa only [V] using
    (isOpen_compl_singleton :
      IsOpen ({secondPuncture}ᶜ : Set (EuclideanSpace ℝ (Fin 2))))

/-- The two punctured planes cover the Euclidean plane. -/
theorem union_eq_univ : U ∪ V = Set.univ := by
  -- A point equal to the first puncture is distinct from the second; every other point lies in `U`.
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x = 0
  · right
    rw [V, Set.mem_compl_singleton_iff, hx]
    have hsecond : secondPuncture ≠ 0 := by
      intro hzero
      have hcoordinate := congrArg (fun y : EuclideanSpace ℝ (Fin 2) ↦ y 0) hzero
      norm_num [secondPuncture, PiLp.single_apply] at hcoordinate
    exact hsecond.symm
  · left
    exact (EuclideanPlane.mem_punctured_iff x).mpr hx

/-- Helper for Exercise 59.4: the intersection of the two punctured planes is path connected. -/
private theorem isPathConnected_inter :
    IsPathConnected (U ∩ V : Set (EuclideanSpace ℝ (Fin 2))) := by
  -- Identify the intersection with the complement of its two punctures.
  have hset : U ∩ V =
      ({0, secondPuncture} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ := by
    ext x
    rw [Set.mem_inter_iff, EuclideanPlane.mem_punctured_iff]
    simp only [V, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
    tauto
  rw [hset]
  -- A finite set has countable complement, and the Euclidean plane has real rank two.
  have hcount :
      ({0, secondPuncture} : Set (EuclideanSpace ℝ (Fin 2))).Countable :=
    (Set.toFinite
      ({0, secondPuncture} : Set (EuclideanSpace ℝ (Fin 2)))).to_countable
  apply hcount.isPathConnected_compl_of_one_lt_rank
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

/-- The intersection of the two members of the fixed cover is path connected. -/
instance instPathConnectedSpaceInter :
    PathConnectedSpace (U ∩ V : Set (EuclideanSpace ℝ (Fin 2))) :=
  -- Package the proved path-connectedness as the instance required by Theorem 59.1.
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_inter

end PlaneTwoPunctureCover

/-- Exercise 59.4 (a): If the inclusion-induced map from `V` is trivial, then the
inclusion-induced map from `U` is surjective. -/
theorem fundamentalGroupMap_surjective_of_second_eq_one {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace (U ∩ V : Set X)]
    (hVmap : FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩ = 1) :
    Function.Surjective (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩) := by
  -- Theorem 59.1 says that the two image subgroups generate the ambient group.
  have hgenerated :=
    fundamentalGroupMap_range_sup_range_eq_top U V x₀ hx₀ hU hV hcover
  -- Triviality of the second map removes its range from that join.
  have hUrange :
      MonoidHom.range (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩) = ⊤ := by
    simpa only [hVmap, MonoidHom.range_one, sup_bot_eq] using hgenerated
  exact MonoidHom.range_eq_top.mp hUrange

/-- Exercise 59.4 (a): If both inclusion-induced maps are trivial, then the fundamental
group of `X` is trivial. -/
theorem fundamentalGroup_subsingleton_of_inclusionMaps_eq_one {X : Type u}
    [TopologicalSpace X] (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace (U ∩ V : Set X)]
    (hUmap : FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩ = 1)
    (hVmap : FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩ = 1) :
    Subsingleton (FundamentalGroup X x₀) := by
  -- Theorem 59.1 makes the join of the two trivial ranges equal to the top subgroup.
  have hgenerated :=
    fundamentalGroupMap_range_sup_range_eq_top U V x₀ hx₀ hU hV hcover
  have hbotTop : (⊥ : Subgroup (FundamentalGroup X x₀)) = ⊤ := by
    simpa only [hUmap, hVmap, MonoidHom.range_one, sup_idem] using hgenerated
  -- Equality of the bottom and top subgroups is exactly triviality of the ambient group.
  exact Subgroup.subsingleton_iff.mp (subsingleton_iff_bot_eq_top.mp hbotTop)

namespace PlaneTwoPunctureCover

/-- Helper for Exercise 59.4: complex coordinates preserve the unit-sphere predicate
on the Euclidean plane. -/
private lemma euclideanPlaneComplex_mem_unitSphere_iff
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ Metric.sphere (0 : ℂ) 1 := by
  -- Both predicates reduce to the norm-one equation preserved by the linear isometry.
  simp only [Metric.mem_sphere, dist_zero_right]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm ▸ Iff.rfl

/-- Helper for Exercise 59.4: the standard one-sphere is homeomorphic to `Circle`. -/
private noncomputable def standardSphereOneHomeomorphCircle :
    StandardSphere 1 ≃ₜ Circle :=
  -- Restrict the standard Euclidean-plane/complex isometry to the unit spheres.
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    euclideanPlaneComplex_mem_unitSphere_iff

/-- Helper for Exercise 59.4: the punctured Euclidean plane is path connected. -/
private theorem isPathConnected_puncturedEuclideanPlane :
    IsPathConnected {x : EuclideanSpace ℝ (Fin 2) | x ≠ 0} := by
  -- Rewrite the nonzero predicate as a singleton complement and use its rank-two geometry.
  have hset : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) =
      {x : EuclideanSpace ℝ (Fin 2) | x ≠ 0} := by
    ext x
    simp
  rw [← hset]
  apply isPathConnected_compl_singleton_of_one_lt_rank
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

/-- Helper for Exercise 59.4: every based fundamental group of the punctured Euclidean
plane is nontrivial. -/
private theorem fundamentalGroup_puncturedEuclideanSpace_not_subsingleton
    (q : PuncturedEuclideanSpace 1) :
    ¬ Subsingleton (FundamentalGroup (PuncturedEuclideanSpace 1) q) := by
  -- Path connectedness permits comparison of the arbitrary basepoint with a sphere point.
  letI : PathConnectedSpace (PuncturedEuclideanSpace 1) :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_puncturedEuclideanPlane
  obtain ⟨b : StandardSphere 1⟩ :=
    NormedSpace.sphere_nonempty_rclike ℝ
      (E := EuclideanSpace ℝ (Fin 2)) zero_le_one
  let sphereToPuncturedOpposite := MulEquiv.ofBijective
    (((StandardSphere.toPunctured 1)₍b₎)₊)
    (StandardSphere.fundamentalGroupMap_bijective 1 b)
  let sphereToPunctured := MulEquiv.unop sphereToPuncturedOpposite
  let coordinates : FundamentalGroup (PuncturedEuclideanSpace 1) q ≃*
      Multiplicative ℤ :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected q
      (StandardSphere.toPunctured 1 b)).trans
      (sphereToPunctured.symm.trans
        ((standardSphereOneHomeomorphCircle.fundamentalGroupMulEquiv b).trans
          ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
            (standardSphereOneHomeomorphCircle b) 1).trans
              Circle.fundamentalGroupEquivInt)))
  -- Integer coordinates contradict any hypothetical subsingleton structure.
  intro hsub
  have hInt : Subsingleton (Multiplicative ℤ) :=
    coordinates.toEquiv.subsingleton_congr.mp hsub
  exact not_subsingleton_iff_nontrivial.mpr inferInstance hInt

/-- Helper for Exercise 59.4: membership in a singleton complement is equivalent to
nonvanishing after translation by its puncture. -/
private lemma mem_compl_singleton_iff_sub_ne_zero
    (p x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) ↔ x - p ≠ 0 := by
  -- Both sides are the assertion that `x` differs from `p`.
  rw [Set.mem_compl_singleton_iff, sub_ne_zero]

/-- Helper for Exercise 59.4: translation identifies the complement of any planar
point with the standard punctured Euclidean plane. -/
private noncomputable def complementSingletonHomeomorphPunctured
    (p : EuclideanSpace ℝ (Fin 2)) :
    ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) ≃ₜ PuncturedEuclideanSpace 1 :=
  -- Restrict translation by `p` using the nonvanishing criterion above.
  (Homeomorph.subRight p).subtype (mem_compl_singleton_iff_sub_ne_zero p)

/-- Helper for Exercise 59.4: the complement of any point in the Euclidean plane has
nontrivial fundamental group at every basepoint. -/
private theorem fundamentalGroup_compl_singleton_not_subsingleton
    (p : EuclideanSpace ℝ (Fin 2))
    (q : ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
    ¬ Subsingleton (FundamentalGroup ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) q) := by
  -- Transport hypothetical triviality through translation to the standard punctured plane.
  intro hsub
  let e := complementSingletonHomeomorphPunctured p
  have htranslated : Subsingleton
      (FundamentalGroup (PuncturedEuclideanSpace 1) (e q)) :=
    (e.fundamentalGroupMulEquiv q).toEquiv.subsingleton_congr.mp hsub
  exact fundamentalGroup_puncturedEuclideanSpace_not_subsingleton (e q) htranslated

/-- Helper for Exercise 59.4: the owner-defined punctured Euclidean plane is
homeomorphic to `PuncturedEuclideanSpace 1`. -/
private noncomputable def euclideanPlanePuncturedHomeomorphPunctured :
    EuclideanPlane.punctured ≃ₜ PuncturedEuclideanSpace 1 :=
  -- Restrict the identity using the owner API for punctured-plane membership.
  (Homeomorph.refl (EuclideanSpace ℝ (Fin 2))).subtype
    EuclideanPlane.mem_punctured_iff

/-- Helper for Exercise 59.4: the owner-defined punctured Euclidean plane has
nontrivial fundamental group at every basepoint. -/
private theorem fundamentalGroup_euclideanPlanePunctured_not_subsingleton
    (q : EuclideanPlane.punctured) :
    ¬ Subsingleton (FundamentalGroup EuclideanPlane.punctured q) := by
  -- Transport triviality through the owner-level subtype homeomorphism.
  intro hsub
  let e := euclideanPlanePuncturedHomeomorphPunctured
  have htranslated : Subsingleton
      (FundamentalGroup (PuncturedEuclideanSpace 1) (e q)) :=
    (e.fundamentalGroupMulEquiv q).toEquiv.subsingleton_congr.mp hsub
  exact fundamentalGroup_puncturedEuclideanSpace_not_subsingleton (e q) htranslated

/-- The inclusion-induced map from the first punctured plane in the fixed cover is trivial. -/
theorem firstMap_eq_one :
    FundamentalGroup.mapOfSubtype U ⟨basepoint, basepoint_mem.1⟩ = 1 := by
  -- The ambient Euclidean plane is contractible, so the two maps agree pointwise there.
  ext g
  exact Subsingleton.elim _ _

/-- The inclusion-induced map from the second punctured plane in the fixed cover is trivial. -/
theorem secondMap_eq_one :
    FundamentalGroup.mapOfSubtype V ⟨basepoint, basepoint_mem.2⟩ = 1 := by
  -- The same ambient triviality identifies every image with the identity element.
  ext g
  exact Subsingleton.elim _ _

/-- The first punctured plane in the fixed cover has nontrivial fundamental group. -/
theorem fundamentalGroup_U_not_subsingleton :
    ¬ Subsingleton (FundamentalGroup U ⟨basepoint, basepoint_mem.1⟩) := by
  -- Use the punctured-plane owner interface rather than unfolding its opaque definition.
  exact fundamentalGroup_euclideanPlanePunctured_not_subsingleton
    ⟨basepoint, basepoint_mem.1⟩

/-- The second punctured plane in the fixed cover has nontrivial fundamental group. -/
theorem fundamentalGroup_V_not_subsingleton :
    ¬ Subsingleton (FundamentalGroup V ⟨basepoint, basepoint_mem.2⟩) := by
  -- Specialize the same result to the translated puncture.
  exact fundamentalGroup_compl_singleton_not_subsingleton secondPuncture
    ⟨basepoint, basepoint_mem.2⟩

/-- Exercise 59.4 (b): The fixed two-puncture cover gives an example in which both
inclusion-induced maps are trivial, while neither member of the cover has trivial
fundamental group. -/
theorem example_spec :
    FundamentalGroup.mapOfSubtype U ⟨basepoint, basepoint_mem.1⟩ = 1 ∧
      FundamentalGroup.mapOfSubtype V ⟨basepoint, basepoint_mem.2⟩ = 1 ∧
      ¬ Subsingleton (FundamentalGroup U ⟨basepoint, basepoint_mem.1⟩) ∧
      ¬ Subsingleton (FundamentalGroup V ⟨basepoint, basepoint_mem.2⟩) :=
  ⟨firstMap_eq_one, secondMap_eq_one, fundamentalGroup_U_not_subsingleton,
    fundamentalGroup_V_not_subsingleton⟩

end PlaneTwoPunctureCover
