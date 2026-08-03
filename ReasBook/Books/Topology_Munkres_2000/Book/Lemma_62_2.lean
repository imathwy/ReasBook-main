module

import Topology_Munkres_2000.Book.Lemma_62_1
import Topology_Munkres_2000.Book.Lemma_61_1
import Topology_Munkres_2000.Book.Lemma_62_2.NoRetraction
import Topology_Munkres_2000.Book.Proposition_61_1.Stereographic
import Topology_Munkres_2000.Book.Theorem_55_2

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Homotopy.Contractible

public section

open Set

universe u

/-- Helper for Lemma 62.2: a nullhomotopic compact embedding induces the
ambient inclusion on its range. -/
lemma existsNullhomotopicAmbientRangeInclusion {X : Type u} {E : Type*}
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace E] [T2Space E]
    (Y : Set E) (f : C(X, Y)) (hf_injective : Function.Injective f)
    (hf_nullhomotopic : f.Nullhomotopic) :
    ∃ j : C(Set.range (fun x : X ↦ (f x : E)), Y),
      (∀ x, (j x : E) = x) ∧ j.Nullhomotopic := by
  -- View the ambient-valued map as an embedding onto its range.
  let ambient : C(X, E) :=
    ⟨fun x ↦ (f x : E), continuous_subtype_val.comp (map_continuous f)⟩
  have hAmbientInjective : Function.Injective ambient := by
    intro x y hxy
    apply hf_injective
    exact Subtype.ext hxy
  have hEmbedding : Topology.IsEmbedding ambient :=
    ((map_continuous ambient).isClosedEmbedding hAmbientInjective).isEmbedding
  let rangeHomeomorph : X ≃ₜ Set.range (fun x : X ↦ (f x : E)) :=
    hEmbedding.toHomeomorph
  let inverse : C(Set.range (fun x : X ↦ (f x : E)), X) :=
    ⟨rangeHomeomorph.symm, rangeHomeomorph.symm.continuous⟩
  let j : C(Set.range (fun x : X ↦ (f x : E)), Y) := f.comp inverse
  refine ⟨j, ?_, hf_nullhomotopic.comp_left inverse⟩
  -- The inverse parametrization recovers the unique point over each range value.
  intro x
  exact congrArg Subtype.val (rangeHomeomorph.apply_symm_apply x)

/-- Helper for Lemma 62.2: adjoining the omitted closed set to one component of
its complement gives a closed subset of the ambient space. -/
private lemma isClosed_componentUnion {E : Type*} [TopologicalSpace E]
    (K U : Set E) (hK : IsClosed K) (hU : IsConnectedComponentIn Kᶜ U) :
    IsClosed (U ∪ K) := by
  -- Express the relative component as the image of an ambient connected component.
  obtain ⟨x, hxU⟩ := hU.nonempty
  have hxK : x ∈ Kᶜ := hU.subset hxU
  rw [hU.eq_connectedComponentIn hxU, ← isOpen_compl_iff]
  have hRelativeOpen :
      IsOpen ((connectedComponent (⟨x, hxK⟩ : {y : E // y ∉ K}) :
        Set {y : E // y ∉ K})ᶜ) :=
    isClosed_connectedComponent.isOpen_compl
  have hAmbientOpen :
      IsOpen (Subtype.val '' ((connectedComponent (⟨x, hxK⟩ : {y : E // y ∉ K}) :
        Set {y : E // y ∉ K})ᶜ)) :=
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

/-- Helper for Lemma 62.2: a nullhomotopic identity map on a closed planar set
extends over its union with a disjoint complement component. -/
private lemma existsNullhomotopicComponentUnionExtension
    (K U : Set (EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2)) (hK : IsClosed K)
    (j : C(K, ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))))
    (hjNull : j.Nullhomotopic) (hjId : ∀ x, (j x : EuclideanSpace ℝ (Fin 2)) = x) :
    ∃ k : C({x : EuclideanSpace ℝ (Fin 2) // x ∈ U ∪ K},
        ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))),
      ∀ x : K, (k ⟨x, Or.inr x.property⟩ : EuclideanSpace ℝ (Fin 2)) = x := by
  -- Regard `K` as the closed subspace of the union on which the given map is defined.
  let KInUnion : Set {x : EuclideanSpace ℝ (Fin 2) // x ∈ U ∪ K} :=
    {x | (x : EuclideanSpace ℝ (Fin 2)) ∈ K}
  have hKInUnionClosed : IsClosed KInUnion :=
    hK.preimage continuous_subtype_val
  have hToKContinuous : Continuous (fun x : KInUnion ↦
      (⟨(x : EuclideanSpace ℝ (Fin 2)), x.property⟩ : K)) := by
    fun_prop
  let toK : C(KInUnion, K) :=
    ⟨fun x ↦ ⟨x, x.property⟩, hToKContinuous⟩
  let jOnUnion : C(KInUnion, ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    j.comp toK
  have hjOnUnionNull : jOnUnion.Nullhomotopic :=
    hjNull.comp_left toK
  obtain ⟨k, hk, -⟩ :=
    existsNullhomotopicExtension isOpen_compl_singleton hKInUnionClosed jOnUnion hjOnUnionNull
  refine ⟨k, ?_⟩
  -- Evaluate the restriction equation at each point of `K` and forget subtypes.
  intro x
  let xu : {y : EuclideanSpace ℝ (Fin 2) // y ∈ U ∪ K} :=
    ⟨x, Or.inr x.property⟩
  let xk : KInUnion := ⟨xu, x.property⟩
  have hkx : k xu = jOnUnion xk := by
    exact congrFun (congrArg DFunLike.coe hk) xk
  exact congrArg Subtype.val hkx |>.trans (hjId x)

/-- Helper for Lemma 62.2: a puncture-avoiding map on a component union that
is the identity on the closed boundary set pastes with the ambient identity. -/
private lemma existsPunctureAvoidingMapEqOnCompl
    (K U : Set (EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2)) (hpU : p ∈ U) (hUOpen : IsOpen U)
    (_hUK : U ⊆ Kᶜ) (hUnionClosed : IsClosed (U ∪ K))
    (k : C({x : EuclideanSpace ℝ (Fin 2) // x ∈ U ∪ K},
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))))
    (hkId : ∀ x : K, (k ⟨x, Or.inr x.property⟩ : EuclideanSpace ℝ (Fin 2)) = x) :
    ∃ h : C(EuclideanSpace ℝ (Fin 2),
        ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))),
      Set.EqOn (fun x ↦ (h x : EuclideanSpace ℝ (Fin 2))) id Uᶜ := by
  classical
  -- Paste the extension on `U ∪ K` with the identity on the closed complement of `U`.
  let g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun x ↦
    if hx : x ∈ U ∪ K then k ⟨x, hx⟩ else x
  have hgUnion : ContinuousOn g (U ∪ K) := by
    rw [continuousOn_iff_continuous_restrict]
    have hRestrict : (U ∪ K).restrict g =
        fun x ↦ (k x : EuclideanSpace ℝ (Fin 2)) := by
      funext x
      exact dif_pos x.property
    rw [hRestrict]
    exact continuous_subtype_val.comp (map_continuous k)
  have hgComplEq : Set.EqOn g id Uᶜ := by
    intro x hx
    by_cases hxUnion : x ∈ U ∪ K
    · have hxK : x ∈ K := hxUnion.resolve_left hx
      rw [show g x = (k ⟨x, hxUnion⟩ : EuclideanSpace ℝ (Fin 2)) by
        exact dif_pos hxUnion]
      have hSubtype :
          (⟨x, hxUnion⟩ : {y : EuclideanSpace ℝ (Fin 2) // y ∈ U ∪ K}) =
            ⟨x, Or.inr hxK⟩ := by
        exact Subtype.ext rfl
      rw [hSubtype]
      exact hkId ⟨x, hxK⟩
    · exact dif_neg hxUnion
  have hgCompl : ContinuousOn g Uᶜ := by
    exact continuousOn_id.congr hgComplEq
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
  have hgAvoids : ∀ x, g x ∈ ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro x
    by_cases hxUnion : x ∈ U ∪ K
    · rw [show g x = (k ⟨x, hxUnion⟩ : EuclideanSpace ℝ (Fin 2)) by
        exact dif_pos hxUnion]
      exact (k ⟨x, hxUnion⟩).property
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro hxp
      apply hxUnion
      have hgIdentity : g x = x := dif_neg hxUnion
      have hxp' : x = p := hgIdentity.symm.trans hxp
      exact Or.inl (hxp' ▸ hpU)
  have hContinuous : Continuous (fun x ↦
      (⟨g x, hgAvoids x⟩ : ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2))))) := by
    exact hgContinuous.subtype_mk _
  let h : C(EuclideanSpace ℝ (Fin 2),
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    ⟨fun x ↦ ⟨g x, hgAvoids x⟩, hContinuous⟩
  refine ⟨h, ?_⟩
  -- The ambient specification is inherited directly from the pasted function.
  intro x hx
  exact hgComplEq hx

/-- Lemma 62.2 (Borsuk lemma). Let `a` and `b` be points of the standard
2-sphere. If a continuous injective map from a compact space into the sphere
with `a` and `b` removed is nullhomotopic, then `a` and `b` lie in the same
connected component of the complement of its image. -/
theorem borsukLemma {A : Type u} [TopologicalSpace A] [CompactSpace A]
    (a b : StandardSphere 2) (f : C(A, ({a, b}ᶜ : Set (StandardSphere 2))))
    (hf_injective : Function.Injective f) (hf_nullhomotopic : f.Nullhomotopic) :
    b ∈ connectedComponentIn
      (Set.range (fun x : A ↦ (f x : StandardSphere 2)))ᶜ a := by
  -- If the two punctures coincide, membership in the complement is enough.
  by_cases hab : a = b
  · subst b
    apply mem_connectedComponentIn
    rintro ⟨x, hx⟩
    exact (f x).2 (by simp [hx])
  -- Work with the compact sphere image and the component containing `a`.
  let K : Set (StandardSphere 2) := Set.range (fun x : A ↦ (f x : StandardSphere 2))
  have hKCompact : IsCompact K := by
    exact isCompact_range (continuous_subtype_val.comp (map_continuous f))
  have haK : a ∉ K := by
    rintro ⟨x, hx⟩
    exact (f x).2 (by simp [hx])
  have hbK : b ∉ K := by
    rintro ⟨x, hx⟩
    exact (f x).2 (by simp [hx])
  let U : Set (StandardSphere 2) := connectedComponentIn Kᶜ a
  have hUComponent : IsConnectedComponentIn Kᶜ U :=
    IsConnectedComponentIn.of_mem haK
  -- If `b` is not in this component, stereographic projection makes it bounded.
  by_contra hbU
  let stereographic := StandardSphere.puncturedHomeomorphPlane b
  obtain ⟨hPlanarComponent, hPlanarBounded⟩ :=
    puncturedSphere_componentImage_bounded K U b stereographic hKCompact hbK
      hUComponent hbU
  have haPunctured : a ∈ ({b}ᶜ : Set (StandardSphere 2)) := by
    simp [hab]
  let aInPunctured : ({b}ᶜ : Set (StandardSphere 2)) := ⟨a, haPunctured⟩
  let p : EuclideanSpace ℝ (Fin 2) := stereographic aInPunctured
  have hAvoidB : ∀ x : ({a, b}ᶜ : Set (StandardSphere 2)),
      (x : StandardSphere 2) ∈ ({b}ᶜ : Set (StandardSphere 2)) := by
    intro x
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hxb
    exact x.property (by simp [hxb])
  have hToPuncturedContinuous : Continuous (fun x : ({a, b}ᶜ : Set (StandardSphere 2)) ↦
      (⟨x, hAvoidB x⟩ : ({b}ᶜ : Set (StandardSphere 2)))) := by
    fun_prop
  let toPunctured : C(({a, b}ᶜ : Set (StandardSphere 2)),
      ({b}ᶜ : Set (StandardSphere 2))) :=
    ⟨fun x ↦ ⟨x, hAvoidB x⟩, hToPuncturedContinuous⟩
  have hTransportAvoids : ∀ x : ({a, b}ᶜ : Set (StandardSphere 2)),
      stereographic (toPunctured x) ∈ ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro x
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hx
    have hxSphere : (x : StandardSphere 2) = a := by
      exact congrArg Subtype.val (stereographic.injective hx)
    exact x.property (by simp [hxSphere])
  let transport : C(({a, b}ᶜ : Set (StandardSphere 2)),
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    ⟨fun x ↦ ⟨stereographic (toPunctured x), hTransportAvoids x⟩, by fun_prop⟩
  let q : C(A, ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) := transport.comp f
  have hqInjective : Function.Injective q := by
    intro x y hxy
    apply hf_injective
    apply Subtype.ext
    have hPunctured : toPunctured (f x) = toPunctured (f y) :=
      stereographic.injective (congrArg Subtype.val hxy)
    exact congrArg (fun z : ({b}ᶜ : Set (StandardSphere 2)) ↦
      (z : StandardSphere 2)) hPunctured
  have hqNullhomotopic : q.Nullhomotopic := hf_nullhomotopic.comp_right transport
  let planarK : Set (EuclideanSpace ℝ (Fin 2)) :=
    Set.range (fun x : A ↦ (q x : EuclideanSpace ℝ (Fin 2)))
  let planarU : Set (EuclideanSpace ℝ (Fin 2)) :=
    stereographic '' (Subtype.val ⁻¹' U)
  have hPlanarRange : planarK = stereographic '' (Subtype.val ⁻¹' K) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨toPunctured (f x), ?_, ?_⟩
      · exact ⟨x, rfl⟩
      · rfl
    · rintro ⟨z, hzK, rfl⟩
      obtain ⟨x, hx⟩ := hzK
      refine ⟨x, ?_⟩
      simp only [q, transport, toPunctured, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      exact congrArg stereographic (Subtype.ext hx)
  have hPlanarComponent' : IsConnectedComponentIn planarKᶜ planarU := by
    rwa [hPlanarRange]
  have hPlanarBounded' : Bornology.IsBounded planarU := hPlanarBounded
  have hpPlanarU : p ∈ planarU := by
    refine ⟨aInPunctured, ?_, rfl⟩
    exact mem_connectedComponentIn haK
  have hPlanarKClosed : IsClosed planarK := by
    exact (isCompact_range (continuous_subtype_val.comp (map_continuous q))).isClosed
  have hPlanarUOpen : IsOpen planarU := by
    obtain ⟨x, hx⟩ := hPlanarComponent'.nonempty
    rw [hPlanarComponent'.eq_connectedComponentIn hx]
    exact hPlanarKClosed.isOpen_compl.connectedComponentIn
  obtain ⟨j, hjId, hjNull⟩ :=
    existsNullhomotopicAmbientRangeInclusion ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))
      q hqInjective hqNullhomotopic
  obtain ⟨k, hkId⟩ :=
    existsNullhomotopicComponentUnionExtension planarK planarU p hPlanarKClosed j hjNull hjId
  obtain ⟨h, hEq⟩ :=
    existsPunctureAvoidingMapEqOnCompl planarK planarU p hpPlanarU hPlanarUOpen
      hPlanarComponent'.subset (isClosed_componentUnion planarK planarU hPlanarKClosed
        hPlanarComponent') k hkId
  exact notExistsPunctureAvoidingMapEqOnComplBounded p planarU hPlanarBounded'
    ⟨h, hEq⟩
