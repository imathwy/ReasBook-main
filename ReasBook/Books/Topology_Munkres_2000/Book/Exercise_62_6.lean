module

public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Topology_Munkres_2000.Book.Definition_25_1.ComponentIn
public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Homotopy.Contractible

import all Topology_Munkres_2000.Book.Definition_35_1.Retraction
import all Topology_Munkres_2000.Book.Definition_55_2.Sphere
import Topology_Munkres_2000.Book.Theorem_62_1
import Topology_Munkres_2000.Book.Lemma_62_1
import Topology_Munkres_2000.Book.Exercise_62_2

public section

open Set

universe u

namespace StandardSphere

/-- Helper for Exercise 62.6: the ambient Euclidean space defining
`StandardSphere n` has dimension `n + 1`. -/
private lemma finrank_standardSphereAmbient (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by
  -- Euclidean coordinates are indexed by `Fin (n + 1)`.
  simp

/-- Helper for Exercise 62.6: the dimension fact used by the generic
stereographic chart on `StandardSphere n`. -/
instance standardSphereAmbientFinrankFact (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_standardSphereAmbient n⟩

/-- Helper for Exercise 62.6: stereographic projection identifies a punctured
standard `n`-sphere with `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def puncturedHomeomorphEuclidean
    (n : ℕ) (p : StandardSphere n) :
    ({p}ᶜ : Set (StandardSphere n)) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  ((Homeomorph.setCongr (stereographic'_source p).symm).trans
    (stereographic' n p).toHomeomorphSourceTarget).trans
      ((Homeomorph.setCongr (stereographic'_target p)).trans (Homeomorph.Set.univ _))

/-- Helper for Exercise 62.6: `puncturedHomeomorphEuclidean` agrees pointwise
with stereographic projection. -/
@[simp] theorem puncturedHomeomorphEuclidean_apply
    (n : ℕ) (p : StandardSphere n) (x : ({p}ᶜ : Set (StandardSphere n))) :
    puncturedHomeomorphEuclidean n p x = stereographic' n p x := by
  -- The set-congruence maps only adjust the source and target subtype spellings.
  rfl

end StandardSphere

/-- Helper for Exercise 62.6: a punctured-space homeomorphism exchanges the
preimages of a set and its complement. -/
private lemma image_preimage_compl_eq_compl_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (C : Set X) (b : X) (h : ({b}ᶜ : Set X) ≃ₜ Y) :
    h '' (Subtype.val ⁻¹' Cᶜ) = (h '' (Subtype.val ⁻¹' C))ᶜ := by
  -- Surjectivity supplies the unique representative of each target point.
  ext y
  obtain ⟨x, rfl⟩ := h.surjective y
  constructor
  · rintro ⟨z, hz, hzx⟩ ⟨w, hw, hwx⟩
    have hzw : z = w := h.injective (hzx.trans hwx.symm)
    exact hz (hzw ▸ hw)
  · intro hx
    refine ⟨x, ?_, rfl⟩
    intro hxC
    exact hx ⟨x, hxC, rfl⟩

/-- Helper for Exercise 62.6: a complement component omitting the chart point
becomes a bounded component under the punctured-sphere chart. -/
private lemma puncturedSphereComponentImageBoundedOfAvoidsPuncture
    (d : ℕ) (C U : Set (StandardSphere (d + 1)))
    (b : StandardSphere (d + 1))
    (h : ({b}ᶜ : Set (StandardSphere (d + 1))) ≃ₜ
      EuclideanSpace ℝ (Fin (d + 1)))
    (hC : IsCompact C) (hb : b ∉ C)
    (hU : IsConnectedComponentIn Cᶜ U) (hbU : b ∉ U) :
    IsConnectedComponentIn (h '' (Subtype.val ⁻¹' C))ᶜ
        (h '' (Subtype.val ⁻¹' U)) ∧
      Bornology.IsBounded (h '' (Subtype.val ⁻¹' U)) := by
  letI : LocallyPathConnectedSpace (StandardSphere (d + 1)) :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin (d + 1))) (StandardSphere (d + 1))
  -- The component of `b` is open and therefore separates `b` from the closure
  -- of the distinct component `U`.
  have hCopen : IsOpen Cᶜ := hC.isClosed.isOpen_compl
  have hbC : b ∈ Cᶜ := hb
  let B := connectedComponentIn Cᶜ b
  have hBcomponent : IsConnectedComponentIn Cᶜ B :=
    IsConnectedComponentIn.of_mem hbC
  have hBopen : IsOpen B := by
    rw [hBcomponent.eq_connectedComponentIn (mem_connectedComponentIn hbC)]
    exact hCopen.connectedComponentIn
  have hUB : U ≠ B := by
    intro hEq
    exact hbU (hEq ▸ mem_connectedComponentIn hbC)
  have hdisjoint : Disjoint U B := by
    rw [Set.disjoint_left]
    intro x hxU hxB
    apply hUB
    calc
      U = connectedComponentIn Cᶜ x := hU.eq_connectedComponentIn hxU
      _ = B := (hBcomponent.eq_connectedComponentIn hxB).symm
  have hdisjointClosure : Disjoint (closure U) B :=
    hdisjoint.closure_left hBopen
  have hbClosure : b ∉ closure U := by
    intro hbcl
    exact Set.disjoint_left.mp hdisjointClosure hbcl (mem_connectedComponentIn hbC)
  have hclosureSubset : closure U ⊆ ({b}ᶜ : Set (StandardSphere (d + 1))) := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hxb
    exact hbClosure (hxb ▸ hx)
  have hcompactClosure : IsCompact (closure U) := isClosed_closure.isCompact
  have hcompactPreimage : IsCompact (Subtype.val ⁻¹' closure U :
      Set ({b}ᶜ : Set (StandardSphere (d + 1)))) := by
    rw [Topology.IsEmbedding.isCompact_iff Topology.IsEmbedding.subtypeVal]
    simpa [Subtype.image_preimage_coe, inter_eq_right.mpr hclosureSubset] using
      hcompactClosure
  have hcompactImage : IsCompact (h '' (Subtype.val ⁻¹' closure U)) :=
    hcompactPreimage.image h.continuous
  have hbounded : Bornology.IsBounded (h '' (Subtype.val ⁻¹' U)) :=
    hcompactImage.isBounded.subset (image_mono (preimage_mono subset_closure))
  -- Since `U` omits `b`, its punctured preimage is still connected and maximal.
  have hPconnected : IsConnected
      (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere (d + 1)))) := by
    apply hU.isConnected.preimage_of_isOpenMap Subtype.val_injective
      isOpen_compl_singleton.isOpenMap_subtype_val
    intro x hx
    have hxb : x ∈ ({b}ᶜ : Set (StandardSphere (d + 1))) := by
      intro hxb
      exact hbU (hxb ▸ hx)
    exact ⟨⟨x, hxb⟩, rfl⟩
  obtain ⟨x, hxP⟩ := hPconnected.nonempty
  have hxC : x ∈ Subtype.val ⁻¹' Cᶜ := hU.subset hxP
  have hPeq : (Subtype.val ⁻¹' U :
      Set ({b}ᶜ : Set (StandardSphere (d + 1)))) =
      connectedComponentIn (Subtype.val ⁻¹' Cᶜ) x := by
    apply Set.Subset.antisymm
    · exact hPconnected.isPreconnected.subset_connectedComponentIn hxP
        (preimage_mono hU.subset)
    · intro y hy
      have hImageConnected : IsPreconnected
          (Subtype.val '' connectedComponentIn (Subtype.val ⁻¹' Cᶜ) x) :=
        isPreconnected_connectedComponentIn.image Subtype.val
          continuous_subtype_val.continuousOn
      have hImageSubset : Subtype.val '' connectedComponentIn
          (Subtype.val ⁻¹' Cᶜ) x ⊆ Cᶜ := by
        rintro z ⟨w, hw, rfl⟩
        exact connectedComponentIn_subset (Subtype.val ⁻¹' Cᶜ) x hw
      have hImageInU : Subtype.val '' connectedComponentIn
          (Subtype.val ⁻¹' Cᶜ) x ⊆ U := by
        rw [hU.eq_connectedComponentIn hxP]
        exact hImageConnected.subset_connectedComponentIn
          (mem_image_of_mem Subtype.val (mem_connectedComponentIn hxC)) hImageSubset
      exact hImageInU ⟨y, hy, rfl⟩
  have hImageEq : h '' (Subtype.val ⁻¹' U) =
      connectedComponentIn (h '' (Subtype.val ⁻¹' Cᶜ)) (h x) := by
    rw [hPeq]
    exact h.image_connectedComponentIn hxC
  rw [image_preimage_compl_eq_compl_image C b h] at hImageEq
  have hImageComponent : IsConnectedComponentIn
      (h '' (Subtype.val ⁻¹' C))ᶜ (h '' (Subtype.val ⁻¹' U)) := by
    rw [hImageEq]
    apply IsConnectedComponentIn.of_mem
    rw [← image_preimage_compl_eq_compl_image C b h]
    exact mem_image_of_mem h hxC
  exact ⟨hImageComponent, hbounded⟩

/-- Helper for Exercise 62.6: adjoining a complement component to the omitted
closed set gives a closed subset of the ambient space. -/
private lemma isClosed_componentUnion {E : Type*} [TopologicalSpace E]
    (K U : Set E) (hK : IsClosed K) (hU : IsConnectedComponentIn Kᶜ U) :
    IsClosed (U ∪ K) := by
  -- Express the relative component through an ambient connected component.
  obtain ⟨x, hxU⟩ := hU.nonempty
  have hxK : x ∈ Kᶜ := hU.subset hxU
  rw [hU.eq_connectedComponentIn hxU, ← isOpen_compl_iff]
  have hRelativeOpen :
      IsOpen ((connectedComponent (⟨x, hxK⟩ : {y : E // y ∉ K}) :
        Set {y : E // y ∉ K})ᶜ) :=
    isClosed_connectedComponent.isOpen_compl
  have hAmbientOpen :
      IsOpen (Subtype.val '' ((connectedComponent
        (⟨x, hxK⟩ : {y : E // y ∉ K}) : Set {y : E // y ∉ K})ᶜ)) :=
    hK.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap _ hRelativeOpen
  convert hAmbientOpen using 1
  ext y
  constructor
  · intro hy
    have hyK : y ∉ K := by
      intro hyK
      exact hy (Or.inr hyK)
    refine ⟨⟨y, hyK⟩, ?_, rfl⟩
    intro hyComponent
    apply hy
    apply Or.inl
    rw [connectedComponentIn_eq_image hxK]
    exact ⟨⟨y, hyK⟩, hyComponent, rfl⟩
  · rintro ⟨z, hzComponent, rfl⟩ hy
    rcases hy with hyU | hyKmem
    · rw [connectedComponentIn_eq_image hxK] at hyU
      obtain ⟨w, hw, hwz⟩ := hyU
      have hwEq : w = z := Subtype.ext hwz
      exact hzComponent (hwEq ▸ hw)
    · exact z.property hyKmem

/-- Helper for Exercise 62.6: a nullhomotopic identity map on a closed
Euclidean set extends over its union with a complement component. -/
private lemma existsNullhomotopicComponentUnionExtension
    (d : ℕ) (K U : Set (EuclideanSpace ℝ (Fin d)))
    (p : EuclideanSpace ℝ (Fin d)) (hK : IsClosed K)
    (j : C(K, ({p}ᶜ : Set (EuclideanSpace ℝ (Fin d)))))
    (hjNull : j.Nullhomotopic)
    (hjId : ∀ x, (j x : EuclideanSpace ℝ (Fin d)) = x) :
    ∃ k : C({x : EuclideanSpace ℝ (Fin d) // x ∈ U ∪ K},
        ({p}ᶜ : Set (EuclideanSpace ℝ (Fin d)))),
      ∀ x : K, (k ⟨x, Or.inr x.property⟩ : EuclideanSpace ℝ (Fin d)) = x := by
  -- Regard `K` as the closed subspace of the union carrying the given map.
  let KInUnion : Set {x : EuclideanSpace ℝ (Fin d) // x ∈ U ∪ K} :=
    {x | (x : EuclideanSpace ℝ (Fin d)) ∈ K}
  have hKInUnionClosed : IsClosed KInUnion :=
    hK.preimage continuous_subtype_val
  have hToKContinuous : Continuous (fun x : KInUnion ↦
      (⟨(x : EuclideanSpace ℝ (Fin d)), x.property⟩ : K)) := by
    fun_prop
  let toK : C(KInUnion, K) :=
    ⟨fun x ↦ ⟨x, x.property⟩, hToKContinuous⟩
  let jOnUnion : C(KInUnion, ({p}ᶜ : Set (EuclideanSpace ℝ (Fin d)))) :=
    j.comp toK
  have hjOnUnionNull : jOnUnion.Nullhomotopic := hjNull.comp_left toK
  obtain ⟨k, hk, -⟩ :=
    existsNullhomotopicExtension isOpen_compl_singleton hKInUnionClosed
      jOnUnion hjOnUnionNull
  refine ⟨k, ?_⟩
  -- Evaluate the restriction equality on the original closed set.
  intro x
  let xu : {y : EuclideanSpace ℝ (Fin d) // y ∈ U ∪ K} :=
    ⟨x, Or.inr x.property⟩
  let xk : KInUnion := ⟨xu, x.property⟩
  have hkx : k xu = jOnUnion xk :=
    congrFun (congrArg DFunLike.coe hk) xk
  exact congrArg Subtype.val hkx |>.trans (hjId x)

/-- Helper for Exercise 62.6: a puncture-avoiding map on a component union
that is the identity on the closed part pastes with the ambient identity. -/
private lemma existsPunctureAvoidingMapEqOnCompl
    (d : ℕ) (K U : Set (EuclideanSpace ℝ (Fin d)))
    (p : EuclideanSpace ℝ (Fin d)) (hpU : p ∈ U) (hUOpen : IsOpen U)
    (hUnionClosed : IsClosed (U ∪ K))
    (k : C({x : EuclideanSpace ℝ (Fin d) // x ∈ U ∪ K},
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin d)))))
    (hkId : ∀ x : K,
      (k ⟨x, Or.inr x.property⟩ : EuclideanSpace ℝ (Fin d)) = x) :
    ∃ h : C(EuclideanSpace ℝ (Fin d),
        ({p}ᶜ : Set (EuclideanSpace ℝ (Fin d)))),
      Set.EqOn (fun x ↦ (h x : EuclideanSpace ℝ (Fin d))) id Uᶜ := by
  classical
  -- Paste the extension on `U ∪ K` with the identity on `Uᶜ`.
  let g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x ↦
    if hx : x ∈ U ∪ K then k ⟨x, hx⟩ else x
  have hgUnion : ContinuousOn g (U ∪ K) := by
    rw [continuousOn_iff_continuous_restrict]
    have hRestrict : (U ∪ K).restrict g =
        fun x ↦ (k x : EuclideanSpace ℝ (Fin d)) := by
      funext x
      exact dif_pos x.property
    rw [hRestrict]
    exact continuous_subtype_val.comp (map_continuous k)
  have hgComplEq : Set.EqOn g id Uᶜ := by
    intro x hx
    by_cases hxUnion : x ∈ U ∪ K
    · have hxK : x ∈ K := hxUnion.resolve_left hx
      have hgx : g x = (k ⟨x, hxUnion⟩ : EuclideanSpace ℝ (Fin d)) :=
        dif_pos hxUnion
      rw [hgx]
      have hSubtype :
          (⟨x, hxUnion⟩ : {y : EuclideanSpace ℝ (Fin d) // y ∈ U ∪ K}) =
            ⟨x, Or.inr hxK⟩ := by
        apply Subtype.ext
        rfl
      rw [hSubtype]
      exact hkId ⟨x, hxK⟩
    · exact dif_neg hxUnion
  have hgCompl : ContinuousOn g Uᶜ := continuousOn_id.congr hgComplEq
  have hgContinuousOn : ContinuousOn g ((U ∪ K) ∪ Uᶜ) :=
    hgUnion.union_of_isClosed hgCompl hUnionClosed hUOpen.isClosed_compl
  have hCover : (U ∪ K) ∪ Uᶜ = Set.univ := by
    ext x
    by_cases hx : x ∈ U
    · simp [hx]
    · simp [hx]
  have hgContinuous : Continuous g := by
    rw [hCover] at hgContinuousOn
    exact continuousOn_univ.mp hgContinuousOn
  have hgAvoids : ∀ x, g x ∈ ({p}ᶜ : Set (EuclideanSpace ℝ (Fin d))) := by
    intro x
    by_cases hxUnion : x ∈ U ∪ K
    · have hgx : g x = (k ⟨x, hxUnion⟩ : EuclideanSpace ℝ (Fin d)) :=
        dif_pos hxUnion
      rw [hgx]
      exact (k ⟨x, hxUnion⟩).property
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro hxp
      apply hxUnion
      have hgIdentity : g x = x := dif_neg hxUnion
      have hxp' : x = p := hgIdentity.symm.trans hxp
      exact Or.inl (hxp' ▸ hpU)
  have hContinuous : Continuous (fun x ↦
      (⟨g x, hgAvoids x⟩ : ({p}ᶜ : Set (EuclideanSpace ℝ (Fin d))))) :=
    hgContinuous.subtype_mk _
  let h : C(EuclideanSpace ℝ (Fin d),
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin d)))) :=
    ⟨fun x ↦ ⟨g x, hgAvoids x⟩, hContinuous⟩
  refine ⟨h, ?_⟩
  -- The ambient specification is inherited from the pasted function.
  intro x hx
  exact hgComplEq hx

/-- Helper for Exercise 62.6: radial normalization of a puncture-avoiding map
that fixes the unit sphere gives a retraction of the closed unit ball. -/
private lemma punctureAvoidingMapFixedOnUnitSphereIsRetract
    (d : ℕ)
    (h : C(EuclideanSpace ℝ (Fin (d + 1)),
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hFix : ∀ x, x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 →
      (h x : EuclideanSpace ℝ (Fin (d + 1))) = x) :
    Set.IsRetract (StandardSphere.boundary d) := by
  -- Normalize the nonzero image of each point of the closed ball.
  have hNormalizeContinuous : Continuous (fun x : ClosedUnitBall d ↦
      NormedSpace.normalize (h x : EuclideanSpace ℝ (Fin (d + 1)))) := by
    unfold NormedSpace.normalize
    have hAmbientContinuous : Continuous (fun x : ClosedUnitBall d ↦
        (h x : EuclideanSpace ℝ (Fin (d + 1)))) :=
      continuous_subtype_val.comp (map_continuous h |>.comp continuous_subtype_val)
    have hNormContinuous : Continuous (fun x : ClosedUnitBall d ↦
        ‖(h x : EuclideanSpace ℝ (Fin (d + 1)))‖) :=
      continuous_norm.comp hAmbientContinuous
    have hNormNe : ∀ x : ClosedUnitBall d,
        ‖(h x : EuclideanSpace ℝ (Fin (d + 1)))‖ ≠ 0 := by
      intro x hx
      exact (h x).property (norm_eq_zero.mp hx)
    exact (hNormContinuous.inv₀ hNormNe).smul hAmbientContinuous
  have hNormalizeNorm : ∀ x : ClosedUnitBall d,
      ‖NormedSpace.normalize (h x : EuclideanSpace ℝ (Fin (d + 1)))‖ = 1 := by
    intro x
    apply NormedSpace.norm_normalize
    exact (h x).property
  have hNormalizeClosedBall : ∀ x : ClosedUnitBall d,
      NormedSpace.normalize (h x : EuclideanSpace ℝ (Fin (d + 1))) ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 := by
    intro x
    rw [Metric.mem_closedBall, dist_zero_right, hNormalizeNorm]
  have hToClosedBallContinuous : Continuous (fun x : ClosedUnitBall d ↦
      (⟨NormedSpace.normalize (h x : EuclideanSpace ℝ (Fin (d + 1))),
        hNormalizeClosedBall x⟩ : ClosedUnitBall d)) :=
    hNormalizeContinuous.subtype_mk _
  let r : C(ClosedUnitBall d, StandardSphere.boundary d) :=
    ⟨fun x ↦ ⟨⟨NormedSpace.normalize
      (h x : EuclideanSpace ℝ (Fin (d + 1))), hNormalizeClosedBall x⟩,
      hNormalizeNorm x⟩, hToClosedBallContinuous.subtype_mk _⟩
  rw [Set.isRetract_iff]
  refine ⟨r, ?_⟩
  -- On the boundary, both the given map and radial normalization fix the point.
  rintro ⟨x, hxNorm⟩
  rw [StandardSphere.boundary, Set.mem_setOf_eq] at hxNorm
  apply Subtype.ext
  apply Subtype.ext
  have hxSphere : (x : EuclideanSpace ℝ (Fin (d + 1))) ∈
      Metric.sphere 0 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hxNorm
  simp only [r, ContinuousMap.coe_mk]
  rw [hFix x hxSphere]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one hxNorm

/-- Helper for Exercise 62.6: the no-retraction hypothesis forbids a
puncture-avoiding perturbation of the identity supported in a bounded set. -/
private lemma notExistsCompactlySupportedPunctureAvoidingMap
    (d : ℕ) (hNoRetract : ¬ Set.IsRetract (StandardSphere.boundary d))
    (p : EuclideanSpace ℝ (Fin (d + 1)))
    (U : Set (EuclideanSpace ℝ (Fin (d + 1))))
    (hU : Bornology.IsBounded U) :
    ¬ ∃ h : C(EuclideanSpace ℝ (Fin (d + 1)),
        ({p}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      Set.EqOn (fun x ↦ (h x : EuclideanSpace ℝ (Fin (d + 1)))) id Uᶜ := by
  rintro ⟨h, hEq⟩
  -- Translate the puncture to zero and dilate beyond the bounded support.
  obtain ⟨R, hRPositive, hUSubset⟩ := hU.subset_ball_lt 0 p
  have hRNe : R ≠ 0 := ne_of_gt hRPositive
  have hNormalizedAvoids : ∀ x : EuclideanSpace ℝ (Fin (d + 1)),
      R⁻¹ • ((h (p + R • x) : EuclideanSpace ℝ (Fin (d + 1))) - p) ∈
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))) := by
    intro x
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hx
    have hDifferenceZero :
        (h (p + R • x) : EuclideanSpace ℝ (Fin (d + 1))) - p = 0 :=
      (smul_eq_zero.mp hx).resolve_left (inv_ne_zero hRNe)
    exact (h (p + R • x)).property (sub_eq_zero.mp hDifferenceZero)
  have hNormalizedContinuous : Continuous (fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦
      (⟨R⁻¹ • ((h (p + R • x) : EuclideanSpace ℝ (Fin (d + 1))) - p),
        hNormalizedAvoids x⟩ :
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))))) := by
    fun_prop
  let normalized : C(EuclideanSpace ℝ (Fin (d + 1)),
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    ⟨fun x ↦ ⟨R⁻¹ • ((h (p + R • x) : EuclideanSpace ℝ (Fin (d + 1))) - p),
      hNormalizedAvoids x⟩, hNormalizedContinuous⟩
  have hNormalizedFix : ∀ x, x ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 →
      (normalized x : EuclideanSpace ℝ (Fin (d + 1))) = x := by
    intro x hxSphere
    have hxNorm : ‖x‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hxSphere
    have hAffineOutside : p + R • x ∈ Uᶜ := by
      rw [Set.mem_compl_iff]
      intro hxU
      have hxBall := hUSubset hxU
      rw [Metric.mem_ball, dist_eq_norm] at hxBall
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hRPositive, hxNorm, mul_one] at hxBall
      exact (lt_irrefl R) hxBall
    have hIdentity :
        (h (p + R • x) : EuclideanSpace ℝ (Fin (d + 1))) = p + R • x :=
      hEq hAffineOutside
    simp only [normalized, ContinuousMap.coe_mk]
    rw [hIdentity, add_sub_cancel_left, ← mul_smul, inv_mul_cancel₀ hRNe, one_smul]
  exact hNoRetract
    (punctureAvoidingMapFixedOnUnitSphereIsRetract d normalized hNormalizedFix)

/-- Exercise 62.6 (1). If the standard `(n - 1)`-sphere is not a retract of the
standard `n`-ball, then the Borsuk lemma holds for the standard `n`-sphere. -/
theorem borsukLemma_of_sphereNotRetractOfBall (n : ℕ) (hn : 0 < n)
    (h_noRetract : ¬ Set.IsRetract (StandardSphere.boundary (n - 1)))
    {A : Type u} [TopologicalSpace A] [CompactSpace A] (a b : StandardSphere n)
    (f : C(A, ({a, b}ᶜ : Set (StandardSphere n))))
    (hf_injective : Function.Injective f) (hf_nullhomotopic : f.Nullhomotopic) :
    b ∈ connectedComponentIn
      (Set.range (fun x : A ↦ (f x : StandardSphere n)))ᶜ a := by
  -- Positive dimension writes the sphere as `StandardSphere (d + 1)`, whose
  -- punctured chart has the same dimension as the assumed ball.
  cases n with
  | zero =>
      exact False.elim (Nat.lt_irrefl 0 hn)
  | succ d =>
    have hNoRetract : ¬ Set.IsRetract (StandardSphere.boundary d) := by
      rw [Nat.succ_sub_one] at h_noRetract
      exact h_noRetract
    -- Coincident punctures require only membership in the image complement.
    by_cases hab : a = b
    · subst b
      apply mem_connectedComponentIn
      rintro ⟨x, hx⟩
      have hForbidden : (f x : StandardSphere (d + 1)) ∈
          ({a, a} : Set (StandardSphere (d + 1))) := by
        simp [hx]
      exact (f x).2 hForbidden
    -- Control the component containing `a` through stereographic projection.
    let K : Set (StandardSphere (d + 1)) :=
      Set.range (fun x : A ↦ (f x : StandardSphere (d + 1)))
    have hKCompact : IsCompact K :=
      isCompact_range (continuous_subtype_val.comp (map_continuous f))
    have haK : a ∉ K := by
      rintro ⟨x, hx⟩
      have hForbidden : (f x : StandardSphere (d + 1)) ∈
          ({a, b} : Set (StandardSphere (d + 1))) := by
        simp [hx]
      exact (f x).2 hForbidden
    have hbK : b ∉ K := by
      rintro ⟨x, hx⟩
      have hForbidden : (f x : StandardSphere (d + 1)) ∈
          ({a, b} : Set (StandardSphere (d + 1))) := by
        simp [hx]
      exact (f x).2 hForbidden
    let U : Set (StandardSphere (d + 1)) := connectedComponentIn Kᶜ a
    have hUComponent : IsConnectedComponentIn Kᶜ U :=
      IsConnectedComponentIn.of_mem haK
    by_contra hbU
    let stereographic :=
      StandardSphere.puncturedHomeomorphEuclidean (d + 1) b
    obtain ⟨hEuclideanComponent, hEuclideanBounded⟩ :=
      puncturedSphereComponentImageBoundedOfAvoidsPuncture
        d K U b stereographic hKCompact hbK hUComponent hbU
    -- Transport the compact embedding through the chart, puncturing at the
    -- image of `a`.
    have haPunctured : a ∈ ({b}ᶜ : Set (StandardSphere (d + 1))) := by
      simp [hab]
    let aInPunctured : ({b}ᶜ : Set (StandardSphere (d + 1))) :=
      ⟨a, haPunctured⟩
    let p : EuclideanSpace ℝ (Fin (d + 1)) := stereographic aInPunctured
    have hAvoidB : ∀ x : ({a, b}ᶜ : Set (StandardSphere (d + 1))),
        (x : StandardSphere (d + 1)) ∈ ({b}ᶜ : Set (StandardSphere (d + 1))) := by
      intro x
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hxb
      have hForbidden : (x : StandardSphere (d + 1)) ∈
          ({a, b} : Set (StandardSphere (d + 1))) := by
        simp [hxb]
      exact x.property hForbidden
    have hToPuncturedContinuous : Continuous
        (fun x : ({a, b}ᶜ : Set (StandardSphere (d + 1))) ↦
          (⟨x, hAvoidB x⟩ : ({b}ᶜ : Set (StandardSphere (d + 1))))) := by
      fun_prop
    let toPunctured : C(({a, b}ᶜ : Set (StandardSphere (d + 1))),
        ({b}ᶜ : Set (StandardSphere (d + 1)))) :=
      ⟨fun x ↦ ⟨x, hAvoidB x⟩, hToPuncturedContinuous⟩
    have hTransportAvoids : ∀ x : ({a, b}ᶜ : Set (StandardSphere (d + 1))),
        stereographic (toPunctured x) ∈
          ({p}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))) := by
      intro x
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hx
      have hxSphere : (x : StandardSphere (d + 1)) = a :=
        congrArg Subtype.val (stereographic.injective hx)
      have hForbidden : (x : StandardSphere (d + 1)) ∈
          ({a, b} : Set (StandardSphere (d + 1))) := by
        simp [hxSphere]
      exact x.property hForbidden
    have hTransportContinuous : Continuous
        (fun x : ({a, b}ᶜ : Set (StandardSphere (d + 1))) ↦
          (⟨stereographic (toPunctured x), hTransportAvoids x⟩ :
            ({p}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))))) := by
      fun_prop
    let transport : C(({a, b}ᶜ : Set (StandardSphere (d + 1))),
        ({p}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
      ⟨fun x ↦ ⟨stereographic (toPunctured x), hTransportAvoids x⟩,
        hTransportContinuous⟩
    let q : C(A, ({p}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
      transport.comp f
    have hqInjective : Function.Injective q := by
      intro x y hxy
      apply hf_injective
      apply Subtype.ext
      have hAmbient : (q x : EuclideanSpace ℝ (Fin (d + 1))) = q y :=
        congrArg (fun z : ({p}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))) ↦
          (z : EuclideanSpace ℝ (Fin (d + 1)))) hxy
      have hPunctured : toPunctured (f x) = toPunctured (f y) :=
        stereographic.injective hAmbient
      exact congrArg (fun z : ({b}ᶜ : Set (StandardSphere (d + 1))) ↦
        (z : StandardSphere (d + 1))) hPunctured
    have hqNullhomotopic : q.Nullhomotopic :=
      hf_nullhomotopic.comp_right transport
    let euclideanK : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
      Set.range (fun x : A ↦ (q x : EuclideanSpace ℝ (Fin (d + 1))))
    let euclideanU : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
      stereographic '' (Subtype.val ⁻¹' U)
    have hEuclideanRange : euclideanK =
        stereographic '' (Subtype.val ⁻¹' K) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨toPunctured (f x), ?_, ?_⟩
        · exact ⟨x, rfl⟩
        · rfl
      · rintro ⟨z, hzK, rfl⟩
        obtain ⟨x, hx⟩ := hzK
        refine ⟨x, ?_⟩
        simp only [q, transport, toPunctured, ContinuousMap.comp_apply,
          ContinuousMap.coe_mk]
        exact congrArg stereographic (Subtype.ext hx)
    have hEuclideanComponent' : IsConnectedComponentIn euclideanKᶜ euclideanU := by
      rwa [hEuclideanRange]
    have hEuclideanBounded' : Bornology.IsBounded euclideanU :=
      hEuclideanBounded
    have hpEuclideanU : p ∈ euclideanU := by
      refine ⟨aInPunctured, ?_, rfl⟩
      exact mem_connectedComponentIn haK
    have hEuclideanKClosed : IsClosed euclideanK :=
      (isCompact_range
        (continuous_subtype_val.comp (map_continuous q))).isClosed
    have hEuclideanUOpen : IsOpen euclideanU := by
      obtain ⟨x, hx⟩ := hEuclideanComponent'.nonempty
      rw [hEuclideanComponent'.eq_connectedComponentIn hx]
      exact hEuclideanKClosed.isOpen_compl.connectedComponentIn
    -- Nullhomotopy supplies the extension; pasting it to the identity produces
    -- the boundedly supported perturbation forbidden by `hNoRetract`.
    obtain ⟨j, hjId, hjNull⟩ :=
      existsNullhomotopicAmbientRangeInclusion
        ({p}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1))))
        q hqInjective hqNullhomotopic
    obtain ⟨k, hkId⟩ :=
      existsNullhomotopicComponentUnionExtension (d + 1) euclideanK euclideanU
        p hEuclideanKClosed j hjNull hjId
    obtain ⟨h, hEq⟩ :=
      existsPunctureAvoidingMapEqOnCompl (d + 1) euclideanK euclideanU p
        hpEuclideanU hEuclideanUOpen
        (isClosed_componentUnion euclideanK euclideanU hEuclideanKClosed
          hEuclideanComponent') k hkId
    exact notExistsCompactlySupportedPunctureAvoidingMap d hNoRetract p
      euclideanU hEuclideanBounded' ⟨h, hEq⟩

/-- Exercise 62.6 (2). If the standard `(n - 1)`-sphere is not a retract of the
standard `n`-ball, then every compact contractible subspace of the standard
`n`-sphere has preconnected complement. -/
theorem compactContractible_not_separates_sphere (n : ℕ) (hn : 0 < n)
    (h_noRetract : ¬ Set.IsRetract (StandardSphere.boundary (n - 1)))
    (A : Set (StandardSphere n)) [CompactSpace A] [ContractibleSpace A] :
    ¬ A.Separates := by
  -- Apply the generalized Borsuk lemma to the subtype inclusion for each pair
  -- of points in the complement.
  have complement_preconnected : IsPreconnected Aᶜ := by
    apply isPreconnected_of_mem_connectedComponentIn
    intro a ha b hb
    have inclusion_mem : ∀ x : A,
        (x : StandardSphere n) ∈ ({a, b}ᶜ : Set (StandardSphere n)) := by
      intro x
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun hxa ↦ ha (hxa ▸ x.property),
        fun hxb ↦ hb (hxb ▸ x.property)⟩
    have hInclusionContinuous : Continuous
        (fun x : A ↦ (⟨x, inclusion_mem x⟩ :
          ({a, b}ᶜ : Set (StandardSphere n)))) :=
      continuous_subtype_val.subtype_mk _
    let inclusion : C(A, ({a, b}ᶜ : Set (StandardSphere n))) :=
      ⟨fun x ↦ ⟨x, inclusion_mem x⟩, hInclusionContinuous⟩
    have inclusion_injective : Function.Injective inclusion := by
      intro x y hxy
      have hxyVal : (x : StandardSphere n) = y :=
        congrArg (fun z : ({a, b}ᶜ : Set (StandardSphere n)) ↦
          (z : StandardSphere n)) hxy
      exact Subtype.ext hxyVal
    have inclusion_nullhomotopic : inclusion.Nullhomotopic := by
      simpa only [ContinuousMap.comp_id] using
        (id_nullhomotopic A).comp_right inclusion
    have inclusion_range :
        Set.range (fun x : A ↦ (inclusion x : StandardSphere n)) = A := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact x.property
      · intro hz
        exact ⟨⟨z, hz⟩, rfl⟩
    rw [← inclusion_range]
    exact borsukLemma_of_sphereNotRetractOfBall n hn h_noRetract a b inclusion
      inclusion_injective inclusion_nullhomotopic
  have complement_preconnectedSpace :
      PreconnectedSpace (Aᶜ : Set (StandardSphere n)) :=
    Subtype.preconnectedSpace complement_preconnected
  -- A separating set has a complement that is not preconnected.
  intro hA
  exact (Set.separates_iff.mp hA) complement_preconnectedSpace

/- Exercise 62.6 (3). The stated separation hypotheses imply Brouwer's
invariance of domain theorem in dimension `n`; the repository already exposes
that theorem directly in its canonical assumption-free form. -/
#check invarianceOfDomain

end
