module

public import Topology_Munkres_2000.Book.Definition_61_3.SimpleClosedCurve
public import Topology_Munkres_2000.Book.Exercise_35_4.RadialRetraction
public import Topology_Munkres_2000.Book.Corollary_58_6
public import Topology_Munkres_2000.Book.Lemma_55_3
public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
public import Topology_Munkres_2000.Book.Lemma_61_1
public import Topology_Munkres_2000.Book.Lemma_61_2
public import Topology_Munkres_2000.Book.Lemma_62_2
public import Topology_Munkres_2000.Book.Proposition_61_1.Stereographic
public import Topology_Munkres_2000.Book.Theorem_52_4.Functoriality
public import Topology_Munkres_2000.Book.Theorem_9_0_1.BorsukNoRetraction
public import Mathlib.Topology.Connected.Basic

public section

open Set

universe u v

/-- Helper for Exercise 62.4: on a simple closed curve, a continuous map is
nullhomotopic exactly when its induced fundamental-group map is trivial. -/
lemma nullhomotopic_iff_fundamentalGroupMap_eq_one_of_isSimpleClosedCurve
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [Topology.IsSimpleClosedCurve X] (h : C(X, Y)) (x : X) :
    h.Nullhomotopic ↔ FundamentalGroup.map h x = 1 := by
  constructor
  · intro hNull
    -- Corollary 58.6 gives the result in Munkres's left-to-right convention;
    -- injectivity of `MonoidHom.op` returns to mathlib's convention.
    exact MonoidHom.op.injective
      (fundamentalGroupMap_eq_one_of_nullhomotopic h x hNull)
  · intro hMap
    classical
    -- First identify the Euclidean unit sphere with the boundary of the closed unit disk.
    have sphereNorm (z : StandardSphere 1) :
        ‖(z : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using z.property
    have sphereMemClosedBall (z : StandardSphere 1) :
        (z : EuclideanSpace ℝ (Fin 2)) ∈
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_eq (sphereNorm z)
    let toDiskBoundary (z : StandardSphere 1) : StandardSphere.boundary 1 :=
      ⟨⟨z, sphereMemClosedBall z⟩,
        (StandardSphere.mem_boundary_iff_norm_eq 1 _).mpr (sphereNorm z)⟩
    have diskBoundaryMemSphere (z : StandardSphere.boundary 1) :
        (z.1 : EuclideanSpace ℝ (Fin 2)) ∈
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      exact (StandardSphere.mem_boundary_iff_norm_eq 1 z.1).mp z.property
    let fromDiskBoundary (z : StandardSphere.boundary 1) : StandardSphere 1 :=
      ⟨z.1, diskBoundaryMemSphere z⟩
    have toDiskBoundaryContinuous : Continuous toDiskBoundary := by
      exact (continuous_subtype_val.subtype_mk _).subtype_mk _
    have fromDiskBoundaryContinuous : Continuous fromDiskBoundary := by
      exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have diskBoundaryLeftInverse :
        Function.LeftInverse fromDiskBoundary toDiskBoundary := by
      intro z
      apply Subtype.ext
      rfl
    have diskBoundaryRightInverse :
        Function.RightInverse fromDiskBoundary toDiskBoundary := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      rfl
    let sphereBoundaryEquiv : StandardSphere 1 ≃ₜ StandardSphere.boundary 1 :=
      { toFun := toDiskBoundary
        invFun := fromDiskBoundary
        left_inv := diskBoundaryLeftInverse
        right_inv := diskBoundaryRightInverse
        continuous_toFun := toDiskBoundaryContinuous
        continuous_invFun := fromDiskBoundaryContinuous }
    -- Parametrize the source by `∂𝔻 2`, aligning its basepoint with `x`.
    let diskCircleEquiv : ULift.{u} (StandardSphere 1) ≃ₜ Circle :=
      Homeomorph.ulift.trans
        (sphereBoundaryEquiv.trans closedUnitDiskBoundaryHomeomorphCircle)
    obtain ⟨circleEquiv⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := X)
    let boundaryEquiv : ULift.{u} (StandardSphere 1) ≃ₜ X :=
      diskCircleEquiv.trans circleEquiv.symm
    let boundaryMap : C(ULift.{u} (StandardSphere 1), X) := boundaryEquiv
    let boundaryPoint : ULift.{u} (StandardSphere 1) := boundaryEquiv.symm x
    have hMapLeft : (h₍ x₎)₊ = 1 := by
      exact congrArg MonoidHom.op hMap
    have hBasepoint : boundaryMap boundaryPoint = x :=
      boundaryEquiv.apply_symm_apply x
    have hMapAtBoundary : (h₍(boundaryMap boundaryPoint)₎)₊ = 1 := by
      rw [hBasepoint]
      exact hMapLeft
    have hCompositeMapLeft :
        ((h.comp boundaryMap)₍ boundaryPoint₎)₊ = 1 := by
      rw [FundamentalGroup.LeftToRight.map_comp]
      rw [hMapAtBoundary]
      exact MonoidHom.one_comp _
    have hCompositeMap :
        FundamentalGroup.map (h.comp boundaryMap)
          boundaryPoint = 1 := by
      exact MonoidHom.op.injective hCompositeMapLeft
    have hCompositeNull :
        (h.comp boundaryMap).Nullhomotopic :=
      (nullhomotopic_iff_fundamentalGroupMap_eq_one
        (h.comp boundaryMap) boundaryPoint).mpr
          hCompositeMap
    -- Precomposing once more by the inverse parametrization recovers `h`.
    have hBack :=
      hCompositeNull.comp_left (boundaryEquiv.symm : C(X, ULift.{u} (StandardSphere 1)))
    have hBackMap :
        (h.comp boundaryMap).comp
            (boundaryEquiv.symm : C(X, ULift.{u} (StandardSphere 1))) = h := by
      ext z
      exact congrArg h (boundaryEquiv.apply_symm_apply z)
    rwa [hBackMap] at hBack

namespace PuncturedPlaneMap

/-- Helper for Exercise 62.4: a compact embedding in the punctured plane is
nullhomotopic exactly when the origin component of its ambient complement is unbounded. -/
lemma nullhomotopic_iff_originComponent_unbounded
    {A : Type u} [TopologicalSpace A] [CompactSpace A]
    (f : C(A, EuclideanPlane.punctured)) (hf : Function.Injective f) :
    f.Nullhomotopic ↔
      ¬ Bornology.IsBounded
        (connectedComponentIn
          (Set.range (fun x : A ↦ (f x : EuclideanSpace ℝ (Fin 2))))ᶜ 0) := by
  classical
  -- Choose the point at infinity and let `a` be the spherical point over the planar origin.
  obtain ⟨bValue, hbValue⟩ :=
    (NormedSpace.sphere_nonempty
      (E := EuclideanSpace ℝ (Fin 3)) (x := 0) (r := 1)).mpr zero_le_one
  let b : StandardSphere 2 := ⟨bValue, hbValue⟩
  let stereographic := StandardSphere.puncturedHomeomorphPlane b
  let a : StandardSphere 2 :=
    (stereographic.symm (0 : EuclideanSpace ℝ (Fin 2)) : StandardSphere 2)
  -- The inverse chart sends every nonzero planar point away from both `a` and `b`.
  have inverseMem (z : EuclideanPlane.punctured) :
      (stereographic.symm (z : EuclideanSpace ℝ (Fin 2)) : StandardSphere 2) ∈
        ({a, b}ᶜ : Set (StandardSphere 2)) := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro hzOrigin
      have hSubtype : stereographic.symm (z : EuclideanSpace ℝ (Fin 2)) =
          stereographic.symm (0 : EuclideanSpace ℝ (Fin 2)) := by
        apply Subtype.ext
        exact hzOrigin
      have hzZero : (z : EuclideanSpace ℝ (Fin 2)) = 0 :=
        stereographic.symm.injective hSubtype
      have hzNonzero : (z : EuclideanSpace ℝ (Fin 2)) ≠ 0 :=
        (EuclideanPlane.mem_punctured_iff _).mp z.property
      exact hzNonzero hzZero
    · exact (stereographic.symm (z : EuclideanSpace ℝ (Fin 2))).property
  have inverseContinuous : Continuous (fun z : EuclideanPlane.punctured ↦
      (⟨(stereographic.symm (z : EuclideanSpace ℝ (Fin 2)) : StandardSphere 2),
        inverseMem z⟩ : ({a, b}ᶜ : Set (StandardSphere 2)))) := by
    -- Continuity is inherited from the inverse stereographic chart and subtype coercions.
    exact (continuous_subtype_val.comp
      (stereographic.symm.continuous.comp continuous_subtype_val)).subtype_mk _
  let inverse : C(EuclideanPlane.punctured,
      ({a, b}ᶜ : Set (StandardSphere 2))) :=
    ⟨fun z ↦ ⟨(stereographic.symm (z : EuclideanSpace ℝ (Fin 2)) : StandardSphere 2),
      inverseMem z⟩, inverseContinuous⟩
  -- Conversely, a point avoiding both punctures belongs to the chart domain and projects nonzero.
  have chartDomainMem (z : ({a, b}ᶜ : Set (StandardSphere 2))) :
      (z : StandardSphere 2) ∈ ({b}ᶜ : Set (StandardSphere 2)) := by
    have hz : (z : StandardSphere 2) ≠ a ∧ (z : StandardSphere 2) ≠ b := by
      simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
        using z.property
    exact hz.2
  have projectionMem (z : ({a, b}ᶜ : Set (StandardSphere 2))) :
      stereographic ⟨z, chartDomainMem z⟩ ∈ EuclideanPlane.punctured := by
    have hNonzero : stereographic ⟨z, chartDomainMem z⟩ ≠ 0 := by
      intro hzZero
      have hChart : (⟨z, chartDomainMem z⟩ : ({b}ᶜ : Set (StandardSphere 2))) =
          stereographic.symm (0 : EuclideanSpace ℝ (Fin 2)) := by
        apply stereographic.injective
        simpa only [Homeomorph.apply_symm_apply] using hzZero
      have hza : (z : StandardSphere 2) = a := congrArg Subtype.val hChart
      have hz : (z : StandardSphere 2) ≠ a ∧ (z : StandardSphere 2) ≠ b := by
        simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
          using z.property
      exact hz.1 hza
    exact (EuclideanPlane.mem_punctured_iff _).mpr hNonzero
  have projectionContinuous : Continuous (fun z : ({a, b}ᶜ : Set (StandardSphere 2)) ↦
      (⟨stereographic ⟨z, chartDomainMem z⟩, projectionMem z⟩ :
        EuclideanPlane.punctured)) := by
    -- Restrict the chart to the twice-punctured sphere, then restrict its codomain.
    have hToChart : Continuous (fun z : ({a, b}ᶜ : Set (StandardSphere 2)) ↦
        (⟨z, chartDomainMem z⟩ : ({b}ᶜ : Set (StandardSphere 2)))) :=
      continuous_subtype_val.subtype_mk _
    exact (stereographic.continuous.comp hToChart).subtype_mk _
  let projection : C(({a, b}ᶜ : Set (StandardSphere 2)),
      EuclideanPlane.punctured) :=
    ⟨fun z ↦ ⟨stereographic ⟨z, chartDomainMem z⟩, projectionMem z⟩,
      projectionContinuous⟩
  have projectionInverse :
      projection.comp inverse = ContinuousMap.id EuclideanPlane.punctured := by
    -- The chart and inverse chart cancel at the underlying planar point.
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    exact stereographic.apply_symm_apply (z : EuclideanSpace ℝ (Fin 2))
  let F : C(A, ({a, b}ᶜ : Set (StandardSphere 2))) := inverse.comp f
  have F_coe (x : A) :
      (F x : StandardSphere 2) =
        (stereographic.symm (f x : EuclideanSpace ℝ (Fin 2)) : StandardSphere 2) := by
    rfl
  have projectF : projection.comp F = f := by
    -- Associativity exposes the preceding inverse law.
    calc
      projection.comp F = (projection.comp inverse).comp f := by
        exact (ContinuousMap.comp_assoc projection inverse f).symm
      _ = (ContinuousMap.id EuclideanPlane.punctured).comp f := by rw [projectionInverse]
      _ = f := ContinuousMap.id_comp f
  have nullhomotopic_iff_lift : f.Nullhomotopic ↔ F.Nullhomotopic := by
    constructor
    · intro hNull
      exact hNull.comp_right inverse
    · intro hNull
      have hProjected := hNull.comp_right projection
      rwa [projectF] at hProjected
  have hFInjective : Function.Injective F := by
    -- Injectivity descends through the injective inverse chart to the original embedding.
    intro x y hxy
    apply hf
    apply Subtype.ext
    apply stereographic.symm.injective
    apply Subtype.ext
    have hSphere := congrArg (fun z : ({a, b}ᶜ : Set (StandardSphere 2)) ↦
      (z : StandardSphere 2)) hxy
    rw [F_coe x, F_coe y] at hSphere
    exact hSphere
  let K : Set (StandardSphere 2) :=
    Set.range (fun x : A ↦ (F x : StandardSphere 2))
  let R : Set (EuclideanSpace ℝ (Fin 2)) :=
    Set.range (fun x : A ↦ (f x : EuclideanSpace ℝ (Fin 2)))
  have hKCompact : IsCompact K := by
    -- Compactness of the source makes the lifted spherical image compact.
    exact isCompact_range (continuous_subtype_val.comp F.continuous)
  have hFAvoidsA (x : A) : (F x : StandardSphere 2) ≠ a := by
    have hx : (F x : StandardSphere 2) ≠ a ∧ (F x : StandardSphere 2) ≠ b := by
      simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
        using (F x).property
    exact hx.1
  have hFAvoidsB (x : A) : (F x : StandardSphere 2) ≠ b := by
    have hx : (F x : StandardSphere 2) ≠ a ∧ (F x : StandardSphere 2) ≠ b := by
      simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
        using (F x).property
    exact hx.2
  have haK : a ∉ K := by
    rintro ⟨x, hx⟩
    exact hFAvoidsA x hx
  have hbK : b ∉ K := by
    rintro ⟨x, hx⟩
    exact hFAvoidsB x hx
  have hImageK : stereographic '' (Subtype.val ⁻¹' K) = R := by
    -- The chart sends the lifted range back to the original planar range.
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx⟩, rfl⟩
      refine ⟨x, ?_⟩
      have hz : z = stereographic.symm (f x : EuclideanSpace ℝ (Fin 2)) := by
        apply Subtype.ext
        exact hx.symm.trans (F_coe x)
      rw [hz, stereographic.apply_symm_apply]
    · rintro ⟨x, rfl⟩
      refine ⟨stereographic.symm (f x : EuclideanSpace ℝ (Fin 2)), ?_,
        stereographic.apply_symm_apply _⟩
      exact ⟨x, rfl⟩
  let U : Set (StandardSphere 2) := connectedComponentIn Kᶜ a
  have hUComponent : IsConnectedComponentIn Kᶜ U :=
    IsConnectedComponentIn.of_mem haK
  have haU : a ∈ U := mem_connectedComponentIn haK
  have hZeroImageU :
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ stereographic '' (Subtype.val ⁻¹' U) := by
    -- The point `a` lies in `U` and its chart coordinate is the planar origin.
    refine ⟨stereographic.symm (0 : EuclideanSpace ℝ (Fin 2)), ?_,
      stereographic.apply_symm_apply _⟩
    change (stereographic.symm (0 : EuclideanSpace ℝ (Fin 2)) : StandardSphere 2) ∈ U
    exact haU
  constructor
  · intro hNull
    -- Borsuk's lemma places infinity in `U`; Lemma 61.1 then makes its image unbounded.
    have hbU : b ∈ U :=
      borsukLemma a b F hFInjective (nullhomotopic_iff_lift.mp hNull)
    obtain ⟨hImageComponent, hImageUnbounded⟩ :=
      puncturedSphere_componentImage_unbounded K U b stereographic hKCompact
        hUComponent hbU
    rw [hImageK] at hImageComponent
    have hImageU := hImageComponent.eq_connectedComponentIn hZeroImageU
    rw [hImageU] at hImageUnbounded
    exact hImageUnbounded
  · intro hUnbounded
    -- If infinity were outside `U`, Lemma 61.1 would make the same planar component bounded.
    have hbU : b ∈ U := by
      by_contra hbU
      obtain ⟨hImageComponent, hImageBounded⟩ :=
        puncturedSphere_componentImage_bounded K U b stereographic hKCompact hbK
          hUComponent hbU
      rw [hImageK] at hImageComponent
      have hImageU := hImageComponent.eq_connectedComponentIn hZeroImageU
      rw [hImageU] at hImageBounded
      exact hUnbounded hImageBounded
    have hLiftNull : F.Nullhomotopic := nulhomotopyLemma a b F hbU
    exact nullhomotopic_iff_lift.mpr hLiftNull

end PuncturedPlaneMap

/-- Helper for Exercise 62.4: if the origin lies in the unbounded component of the complement of a
simple closed curve in the punctured Euclidean plane, then the inclusion-induced
fundamental-group homomorphism is trivial. -/
theorem fundamentalGroupMap_eq_one_of_originComponent_unbounded
    (C : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve C]
    (hC : C ⊆ EuclideanPlane.punctured) (c : C)
    (h_unbounded : ¬ Bornology.IsBounded (connectedComponentIn Cᶜ 0)) :
    FundamentalGroup.mapOfSubset hC c = 1 := by
  -- Transfer compactness from the circle model and name the punctured-plane inclusion.
  obtain ⟨circleEquiv⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  letI : CompactSpace C := circleEquiv.symm.compactSpace
  let inclusion : C(C, EuclideanPlane.punctured) := ContinuousMap.inclusion hC
  have inclusionInjective : Function.Injective inclusion := Set.inclusion_injective hC
  have inclusionRange :
      Set.range (fun x : C ↦ (inclusion x : EuclideanSpace ℝ (Fin 2))) = C := by
    -- Forgetting the two subtype layers leaves precisely the original curve.
    ext z
    constructor
    · rintro ⟨x, hx⟩
      rw [← hx]
      exact x.property
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
  have inclusionNull : inclusion.Nullhomotopic := by
    -- The planar criterion turns the assumed unbounded component into a contraction.
    apply (PuncturedPlaneMap.nullhomotopic_iff_originComponent_unbounded
      inclusion inclusionInjective).mpr
    rwa [inclusionRange]
  -- The circle-domain adapter converts the contraction into triviality of the induced map.
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion]
  exact
    (nullhomotopic_iff_fundamentalGroupMap_eq_one_of_isSimpleClosedCurve inclusion c).mp
      inclusionNull

/-- Helper for Exercise 62.4: if the origin lies in the bounded component of the complement of a
simple closed curve in the punctured Euclidean plane, then the inclusion-induced
fundamental-group homomorphism is nontrivial. -/
theorem fundamentalGroupMap_ne_one_of_originComponent_bounded
    (C : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve C]
    (hC : C ⊆ EuclideanPlane.punctured) (c : C)
    (h_bounded : Bornology.IsBounded (connectedComponentIn Cᶜ 0)) :
    FundamentalGroup.mapOfSubset hC c ≠ 1 := by
  -- As above, use the circle model to supply compactness for the planar criterion.
  obtain ⟨circleEquiv⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  letI : CompactSpace C := circleEquiv.symm.compactSpace
  let inclusion : C(C, EuclideanPlane.punctured) := ContinuousMap.inclusion hC
  have inclusionInjective : Function.Injective inclusion := Set.inclusion_injective hC
  have inclusionRange :
      Set.range (fun x : C ↦ (inclusion x : EuclideanSpace ℝ (Fin 2))) = C := by
    -- The ambient range of the inclusion is exactly `C`.
    ext z
    constructor
    · rintro ⟨x, hx⟩
      rw [← hx]
      exact x.property
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
  intro hMap
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion] at hMap
  have inclusionNull : inclusion.Nullhomotopic :=
    (nullhomotopic_iff_fundamentalGroupMap_eq_one_of_isSimpleClosedCurve inclusion c).mpr
      hMap
  have inclusionUnbounded :=
    (PuncturedPlaneMap.nullhomotopic_iff_originComponent_unbounded
      inclusion inclusionInjective).mp inclusionNull
  rw [inclusionRange] at inclusionUnbounded
  exact inclusionUnbounded h_bounded

/-- Exercise 62.4. The inclusion of a simple closed curve into the punctured Euclidean
plane induces the trivial fundamental-group homomorphism exactly when the component of
the origin in the complement of the curve is unbounded. -/
theorem fundamentalGroupMap_eq_one_iff_originComponent_unbounded
    (C : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve C]
    (hC : C ⊆ EuclideanPlane.punctured) (c : C) :
    FundamentalGroup.mapOfSubset hC c = 1 ↔
      ¬ Bornology.IsBounded (connectedComponentIn Cᶜ 0) := by
  constructor
  · intro h_map h_bounded
    exact fundamentalGroupMap_ne_one_of_originComponent_bounded C hC c h_bounded h_map
  · exact fundamentalGroupMap_eq_one_of_originComponent_unbounded C hC c
