module

public import Topology_Munkres_2000.Book.Definition_25_1.ComponentIn
public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

public section

open Set

/-- Helper for Lemma 61.1: a homeomorphism from the complement of `b` sends the
preimage of `Cᶜ` onto the complement of the image of the preimage of `C`. -/
private lemma image_preimage_compl_eq_compl_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (C : Set X) (b : X) (h : ({b}ᶜ : Set X) ≃ₜ Y) :
    h '' (Subtype.val ⁻¹' Cᶜ) = (h '' (Subtype.val ⁻¹' C))ᶜ := by
  -- Surjectivity supplies the unique punctured-domain representative of a target point.
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

/-- Helper for Lemma 61.1: a component of an open subset of the standard
two-sphere is open. -/
private lemma isOpen_componentIn_standardSphere
    {S U : Set (StandardSphere 2)} (hS : IsOpen S)
    (hU : IsConnectedComponentIn S U) : IsOpen U := by
  -- The sphere's charted-space structure transfers local path-connectedness from the plane.
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) (StandardSphere 2)
  obtain ⟨x, hxU⟩ := hU.nonempty
  rw [hU.eq_connectedComponentIn hxU]
  exact hS.connectedComponentIn

/-- Helper for Lemma 61.1: the image of a component avoiding the puncture is bounded. -/
private lemma image_preimage_component_isBounded
    (C U : Set (StandardSphere 2)) (b : StandardSphere 2)
    (h : ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) (hb : b ∉ C)
    (hU : IsConnectedComponentIn Cᶜ U) (hbU : b ∉ U) :
    Bornology.IsBounded (h '' (Subtype.val ⁻¹' U)) := by
  -- Openness of the component containing `b` separates `b` from the closure of `U`.
  have hCopen : IsOpen Cᶜ := hC.isClosed.isOpen_compl
  have hUopen : IsOpen U := isOpen_componentIn_standardSphere hCopen hU
  have hbC : b ∈ Cᶜ := hb
  let B := connectedComponentIn Cᶜ b
  have hBcomponent : IsConnectedComponentIn Cᶜ B :=
    IsConnectedComponentIn.of_mem hbC
  have hBopen : IsOpen B := isOpen_componentIn_standardSphere hCopen hBcomponent
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
  have hdisjointClosure : Disjoint (closure U) B := hdisjoint.closure_left hBopen
  have hbClosure : b ∉ closure U := by
    intro hbcl
    exact Set.disjoint_left.mp hdisjointClosure hbcl (mem_connectedComponentIn hbC)
  have hclosureSubset : closure U ⊆ ({b}ᶜ : Set (StandardSphere 2)) := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hxb
    exact hbClosure (hxb ▸ hx)
  have hcompactClosure : IsCompact (closure U) := isClosed_closure.isCompact
  have hcompactPreimage : IsCompact (Subtype.val ⁻¹' closure U :
      Set ({b}ᶜ : Set (StandardSphere 2))) := by
    rw [Topology.IsEmbedding.isCompact_iff Topology.IsEmbedding.subtypeVal]
    simpa [Subtype.image_preimage_coe, inter_eq_right.mpr hclosureSubset] using hcompactClosure
  have hcompactImage : IsCompact (h '' (Subtype.val ⁻¹' closure U)) :=
    hcompactPreimage.image h.continuous
  -- The desired image is contained in this compact image of the closure.
  exact hcompactImage.isBounded.subset (image_mono (preimage_mono subset_closure))

/-- Helper for Lemma 61.1: if a complement component contains the puncture,
then the complement of its punctured image is compact. -/
private lemma isCompact_compl_image_preimage_component
    (C U : Set (StandardSphere 2)) (b : StandardSphere 2)
    (h : ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) (hU : IsConnectedComponentIn Cᶜ U) (hbU : b ∈ U) :
    IsCompact ((h '' (Subtype.val ⁻¹' U))ᶜ) := by
  -- The component is open, so its complement is compact in the compact sphere.
  have hCopen : IsOpen Cᶜ := hC.isClosed.isOpen_compl
  have hUopen : IsOpen U := isOpen_componentIn_standardSphere hCopen hU
  have hcompactCompl : IsCompact Uᶜ := hUopen.isClosed_compl.isCompact
  have hcomplSubset : Uᶜ ⊆ ({b}ᶜ : Set (StandardSphere 2)) := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff] at hx ⊢
    intro hxb
    exact hx (hxb ▸ hbU)
  have hcompactPreimage : IsCompact (Subtype.val ⁻¹' Uᶜ :
      Set ({b}ᶜ : Set (StandardSphere 2))) := by
    rw [Topology.IsEmbedding.isCompact_iff Topology.IsEmbedding.subtypeVal]
    simpa [Subtype.image_preimage_coe, inter_eq_right.mpr hcomplSubset] using hcompactCompl
  have hcompactImage : IsCompact (h '' (Subtype.val ⁻¹' Uᶜ)) :=
    hcompactPreimage.image h.continuous
  -- Surjectivity identifies this compact image with the complement of the component image.
  have hcomplement : h '' (Subtype.val ⁻¹' Uᶜ) =
      (h '' (Subtype.val ⁻¹' U))ᶜ :=
    image_preimage_compl_eq_compl_image U b h
  rwa [hcomplement] at hcompactImage

/-- Helper for Lemma 61.1: a subset of an unbounded normed space with bounded
complement cannot itself be bounded. -/
private lemma not_isBounded_of_isBounded_compl
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {S : Set E} (hSc : Bornology.IsBounded Sᶜ) : ¬ Bornology.IsBounded S := by
  -- Boundedness of both pieces would make the entire normed space bounded.
  intro hS
  have huniv : Bornology.IsBounded (Set.univ : Set E) := by
    rw [← union_compl_self S]
    exact hS.union hSc
  exact NormedSpace.unbounded_univ ℝ E huniv

/-- Helper for Lemma 61.1: distinct connected components of the same subset are disjoint. -/
private lemma disjoint_of_isConnectedComponentIn_of_ne
    {X : Type*} [TopologicalSpace X] {S U V : Set X}
    (hU : IsConnectedComponentIn S U) (hV : IsConnectedComponentIn S V)
    (hne : U ≠ V) : Disjoint U V := by
  -- A common point would identify both components with its canonical component.
  rw [Set.disjoint_left]
  intro x hxU hxV
  apply hne
  calc
    U = connectedComponentIn S x := hU.eq_connectedComponentIn hxU
    _ = V := (hV.eq_connectedComponentIn hxV).symm

/-- Helper for Lemma 61.1: deleting a point preserves connectedness when it has a
connected punctured neighborhood inside the original connected set. -/
private lemma isConnected_sdiff_singleton_of_connected_punctured_nhds
    {X : Type*} [TopologicalSpace X] [T1Space X] {U W : Set X} {b : X}
    (hU : IsConnected U) (hbU : b ∈ U) (hW : W ∈ nhds b) (hWU : W ⊆ U)
    (hWconn : IsConnected (W \ {b})) : IsConnected (U \ {b}) := by
  -- The punctured neighborhood supplies nonemptiness after deletion.
  have hpunctureSubset : W \ {b} ⊆ U \ {b} :=
    sdiff_subset_sdiff hWU (Subset.refl _)
  refine ⟨hWconn.nonempty.mono hpunctureSubset, ?_⟩
  intro A B hA hB hcover hAn hBn
  -- It suffices to rule out a separation of the punctured set.
  by_contra hmeet
  have hdisjointWithin : Disjoint (U \ {b} ∩ A) (U \ {b} ∩ B) := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact hmeet ⟨x, hxA.1, hxA.2, hxB.2⟩
  have hWcover : W \ {b} ⊆ A ∪ B := hpunctureSubset.trans hcover
  have hWside : W \ {b} ⊆ A ∨ W \ {b} ⊆ B := by
    by_cases hWA : ((W \ {b}) ∩ A).Nonempty
    · by_cases hWB : ((W \ {b}) ∩ B).Nonempty
      · obtain ⟨x, hxW, hxAB⟩ := hWconn.isPreconnected A B hA hB hWcover hWA hWB
        exact False.elim (hmeet ⟨x, hpunctureSubset hxW, hxAB.1, hxAB.2⟩)
      · exact Or.inl fun x hxW ↦ by
          rcases hWcover hxW with hxA | hxB
          · exact hxA
          · exact False.elim (hWB ⟨x, hxW, hxB⟩)
    · exact Or.inr fun x hxW ↦ by
        rcases hWcover hxW with hxA | hxB
        · exact False.elim (hWA ⟨x, hxW, hxA⟩)
        · exact hxB
  obtain ⟨V, hVW, hVopen, hbV⟩ := mem_nhds_iff.mp hW
  rcases hWside with hWA | hWB
  · -- Adding `V` to the `A` side and deleting `b` from `B` separates `U`.
    have hUcover : U ⊆ (A ∪ V) ∪ (B \ {b}) := by
      intro x hxU
      by_cases hxb : x = b
      · exact Or.inl (Or.inr (hxb ▸ hbV))
      · rcases hcover ⟨hxU, hxb⟩ with hxA | hxB
        · exact Or.inl (Or.inl hxA)
        · exact Or.inr ⟨hxB, hxb⟩
    have hleft : (U ∩ (A ∪ V)).Nonempty :=
      ⟨b, hbU, Or.inr hbV⟩
    have hright : (U ∩ (B \ {b})).Nonempty := by
      obtain ⟨x, hxU, hxB⟩ := hBn
      exact ⟨x, hxU.1, hxB, hxU.2⟩
    obtain ⟨x, hxU, hxLeft, hxRight⟩ := hU.isPreconnected
      (A ∪ V) (B \ {b}) (hA.union hVopen) (hB.sdiff isClosed_singleton)
      hUcover hleft hright
    rcases hxLeft with hxA | hxV
    · exact hmeet ⟨x, ⟨hxU, hxRight.2⟩, hxA, hxRight.1⟩
    · exact hmeet ⟨x, ⟨hxU, hxRight.2⟩, hWA ⟨hVW hxV, hxRight.2⟩, hxRight.1⟩
  · -- The same construction with the roles of `A` and `B` reversed closes the other case.
    have hUcover : U ⊆ (B ∪ V) ∪ (A \ {b}) := by
      intro x hxU
      by_cases hxb : x = b
      · exact Or.inl (Or.inr (hxb ▸ hbV))
      · rcases hcover ⟨hxU, hxb⟩ with hxA | hxB
        · exact Or.inr ⟨hxA, hxb⟩
        · exact Or.inl (Or.inl hxB)
    have hleft : (U ∩ (B ∪ V)).Nonempty :=
      ⟨b, hbU, Or.inr hbV⟩
    have hright : (U ∩ (A \ {b})).Nonempty := by
      obtain ⟨x, hxU, hxA⟩ := hAn
      exact ⟨x, hxU.1, hxA, hxU.2⟩
    obtain ⟨x, hxU, hxLeft, hxRight⟩ := hU.isPreconnected
      (B ∪ V) (A \ {b}) (hB.union hVopen) (hA.sdiff isClosed_singleton)
      hUcover hleft hright
    rcases hxLeft with hxB | hxV
    · exact hmeet ⟨x, ⟨hxU, hxRight.2⟩, hxRight.1, hxB⟩
    · exact hmeet ⟨x, ⟨hxU, hxRight.2⟩, hxRight.1, hWB ⟨hVW hxV, hxRight.2⟩⟩

/-- Helper for Lemma 61.1: every point of an open subset of the standard
two-sphere has a connected punctured neighborhood contained in that subset. -/
private lemma exists_connected_punctured_nhds_standardSphere
    {U : Set (StandardSphere 2)} {b : StandardSphere 2}
    (hU : IsOpen U) (hbU : b ∈ U) :
    ∃ W ∈ nhds b, W ⊆ U ∧ IsConnected (W \ {b}) := by
  -- Choose a small Euclidean ball in the chart image of `U`.
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) b b
  have hchartNhds : chartAt (EuclideanSpace ℝ (Fin 2)) b ''
      (U ∩ (chartAt (EuclideanSpace ℝ (Fin 2)) b).source) ∈ nhds c := by
    apply (chartAt (EuclideanSpace ℝ (Fin 2)) b).image_mem_nhds
      (mem_chart_source (EuclideanSpace ℝ (Fin 2)) b)
    exact Filter.inter_mem (hU.mem_nhds hbU) (chart_source_mem_nhds (EuclideanSpace ℝ (Fin 2)) b)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hchartNhds
  let e := (OpenPartialHomeomorph.univBall c r).trans
    (chartAt (EuclideanSpace ℝ (Fin 2)) b).symm
  let W := e '' Set.univ
  have hesource : e.source = Set.univ := by
    ext x
    simp only [e, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.univBall_source,
      mem_inter_iff, mem_univ, true_and, mem_preimage]
    have hxball : OpenPartialHomeomorph.univBall c r x ∈ Metric.ball c r := by
      rw [← OpenPartialHomeomorph.univBall_target c hr]
      exact (OpenPartialHomeomorph.univBall c r).map_source (by simp)
    let z := (hrsub hxball).choose
    have hz := (hrsub hxball).choose_spec
    rw [← hz.2]
    exact iff_true_intro ((chartAt (EuclideanSpace ℝ (Fin 2)) b).map_source hz.1.2)
  have hezero : e 0 = b := by
    simp only [e, OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.univBall_apply_zero, c]
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) b).left_inv
      (mem_chart_source (EuclideanSpace ℝ (Fin 2)) b)
  have hWnhds : W ∈ nhds b := by
    rw [← hezero]
    exact e.image_mem_nhds (hesource ▸ Set.mem_univ 0) Filter.univ_mem
  have hWU : W ⊆ U := by
    rintro y ⟨x, -, hxy⟩
    have hxball : OpenPartialHomeomorph.univBall c r x ∈ Metric.ball c r := by
      rw [← OpenPartialHomeomorph.univBall_target c hr]
      exact (OpenPartialHomeomorph.univBall c r).map_source (by simp)
    let z := (hrsub hxball).choose
    have hz := (hrsub hxball).choose_spec
    have hzEq : e x = z := by
      calc
        e x = (chartAt (EuclideanSpace ℝ (Fin 2)) b).symm
            (OpenPartialHomeomorph.univBall c r x) := rfl
        _ = (chartAt (EuclideanSpace ℝ (Fin 2)) b).symm
            (chartAt (EuclideanSpace ℝ (Fin 2)) b z) := congrArg _ hz.2.symm
        _ = z := (chartAt (EuclideanSpace ℝ (Fin 2)) b).left_inv hz.1.2
    rw [← hxy, hzEq]
    exact hz.1.1
  have hpuncture : W \ {b} = e '' (Set.univ \ {0}) := by
    change (e '' Set.univ) \ {b} = e '' (Set.univ \ {0})
    rw [Set.image_sdiff]
    · rw [image_singleton, hezero]
    · intro x y hxy
      apply e.injOn (hesource ▸ Set.mem_univ x) (hesource ▸ Set.mem_univ y) hxy
  have hplanePuncture : IsConnected
      ((Set.univ : Set (EuclideanSpace ℝ (Fin 2))) \ {0}) := by
    have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
      rw [← Module.finrank_eq_rank]
      norm_num
    have hset : (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) \ {0} = ({0}ᶜ) := by
      ext x
      simp only [mem_sdiff, mem_univ, true_and, mem_singleton_iff, mem_compl_iff]
    rw [hset]
    exact isConnected_compl_singleton_of_one_lt_rank hrank
      (0 : EuclideanSpace ℝ (Fin 2))
  have hWconn : IsConnected (W \ {b}) := by
    rw [hpuncture]
    exact hplanePuncture.image e
      (e.continuousOn.mono fun x _ ↦ hesource ▸ Set.mem_univ x)
  exact ⟨W, hWnhds, hWU, hWconn⟩

/-- Helper for Lemma 61.1: an open connected subset of the standard two-sphere
remains connected when viewed inside the sphere punctured at one point. -/
private lemma isConnected_preimage_openConnected_standardSphere
    {U : Set (StandardSphere 2)} {b : StandardSphere 2}
    (hUopen : IsOpen U) (hU : IsConnected U) :
    IsConnected (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2))) := by
  by_cases hbU : b ∈ U
  · -- The local chart gives the punctured neighborhood required by the deletion lemma.
    obtain ⟨W, hWnhds, hWU, hWconn⟩ :=
      exists_connected_punctured_nhds_standardSphere hUopen hbU
    have hpunctured : IsConnected (U \ {b}) :=
      isConnected_sdiff_singleton_of_connected_punctured_nhds
        hU hbU hWnhds hWU hWconn
    have hpreimage : (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2))) =
        Subtype.val ⁻¹' (U \ {b}) := by
      ext x
      constructor
      · intro hx
        exact ⟨hx, x.property⟩
      · exact fun hx ↦ hx.1
    rw [hpreimage]
    apply hpunctured.preimage_of_isOpenMap Subtype.val_injective
      isOpen_compl_singleton.isOpenMap_subtype_val
    intro x hx
    exact ⟨⟨x, hx.2⟩, rfl⟩
  · -- If `b` is absent already, the subtype preimage is simply a copy of `U`.
    apply hU.preimage_of_isOpenMap Subtype.val_injective
      isOpen_compl_singleton.isOpenMap_subtype_val
    intro x hx
    exact ⟨⟨x, hbU ∘ fun hxb ↦ hxb ▸ hx⟩, rfl⟩

/-- Helper for Lemma 61.1: puncturing a component of `Cᶜ` at `b` and applying
the chart produces a connected component of the planar complement. -/
private lemma isConnectedComponentIn_image_preimage
    (C U : Set (StandardSphere 2)) (b : StandardSphere 2)
    (h : ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) (_hb : b ∉ C) (hU : IsConnectedComponentIn Cᶜ U) :
    IsConnectedComponentIn (h '' (Subtype.val ⁻¹' C))ᶜ
      (h '' (Subtype.val ⁻¹' U)) := by
  -- First identify the punctured component canonically inside the punctured complement.
  have hCopen : IsOpen Cᶜ := hC.isClosed.isOpen_compl
  have hUopen : IsOpen U := isOpen_componentIn_standardSphere hCopen hU
  have hPconnected : IsConnected
      (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2))) :=
    isConnected_preimage_openConnected_standardSphere hUopen hU.isConnected
  obtain ⟨x, hxP⟩ := hPconnected.nonempty
  have hxC : x ∈ Subtype.val ⁻¹' Cᶜ := hU.subset hxP
  have hPeq : (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2))) =
      connectedComponentIn (Subtype.val ⁻¹' Cᶜ) x := by
    apply Set.Subset.antisymm
    · exact hPconnected.isPreconnected.subset_connectedComponentIn hxP
        (preimage_mono hU.subset)
    · intro y hy
      have hImageConnected : IsPreconnected
          (Subtype.val '' connectedComponentIn (Subtype.val ⁻¹' Cᶜ) x) :=
        isPreconnected_connectedComponentIn.image Subtype.val continuous_subtype_val.continuousOn
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
  have hPcomponent : IsConnectedComponentIn
      (Subtype.val ⁻¹' Cᶜ : Set ({b}ᶜ : Set (StandardSphere 2)))
      (Subtype.val ⁻¹' U) := by
    rw [hPeq]
    exact IsConnectedComponentIn.of_mem hxC
  -- The homeomorphism transports that canonical component, and the complement identity
  -- puts the ambient set in the required planar normal form.
  have hImageEq : h '' (Subtype.val ⁻¹' U) =
      connectedComponentIn (h '' (Subtype.val ⁻¹' Cᶜ)) (h x) := by
    rw [hPeq]
    exact h.image_connectedComponentIn hxC
  rw [image_preimage_compl_eq_compl_image C b h] at hImageEq
  rw [hImageEq]
  exact IsConnectedComponentIn.of_mem (by
    rw [← image_preimage_compl_eq_compl_image C b h]
    exact mem_image_of_mem h hxC)

/-- Helper for Lemma 61.1: deleting the chart point induces an equivalence
between the connected components of the spherical and planar complements. -/
private lemma nonempty_connectedComponents_equiv_puncturedComplement
    (C : Set (StandardSphere 2)) (b : StandardSphere 2)
    (h : ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) (_hb : b ∉ C) :
    Nonempty (ConnectedComponents (Cᶜ : Set (StandardSphere 2)) ≃
      ConnectedComponents ((h '' (Subtype.val ⁻¹' C))ᶜ :
        Set (EuclideanSpace ℝ (Fin 2)))) := by
  -- The puncture inclusion meets every component and has connected intersection with each one.
  classical
  let P := (Subtype.val ⁻¹' Cᶜ : Set ({b}ᶜ : Set (StandardSphere 2)))
  let Q := (Cᶜ : Set (StandardSphere 2))
  let j : P → Q := fun x ↦ ⟨x.1.1, x.2⟩
  have hj : Continuous j := by
    change Continuous (fun x : P ↦ (⟨x.1.1, x.2⟩ : Q))
    have hval : Continuous (fun x : P ↦ x.1.1 : P → StandardSphere 2) := by
      fun_prop
    exact hval.subtype_mk fun x ↦ x.2
  have hjbij : Function.Bijective hj.connectedComponentsMap := by
    constructor
    · -- Equality after inclusion means the representatives lie in one spherical component;
      -- its puncture is connected, so they were already equal in `π₀(P)`.
      intro a₁ a₂ ha
      obtain ⟨x₁, rfl⟩ := ConnectedComponents.surjective_coe a₁
      obtain ⟨x₂, rfl⟩ := ConnectedComponents.surjective_coe a₂
      rw [Continuous.connectedComponentsMap_mk, Continuous.connectedComponentsMap_mk] at ha
      rw [ConnectedComponents.coe_eq_coe'] at ha ⊢
      have hsame : x₁.1.1 ∈ connectedComponentIn Cᶜ x₂.1.1 := by
        rw [connectedComponentIn_eq_image (F := Cᶜ) (x := x₂.1.1) x₂.2]
        exact ⟨j x₁, ha, rfl⟩
      have hUopen : IsOpen (connectedComponentIn Cᶜ x₂.1.1) :=
        isOpen_componentIn_standardSphere hC.isClosed.isOpen_compl
          (IsConnectedComponentIn.of_mem x₂.2)
      have hPconn : IsConnected (Subtype.val ⁻¹' connectedComponentIn Cᶜ x₂.1.1 :
          Set ({b}ᶜ : Set (StandardSphere 2))) :=
        isConnected_preimage_openConnected_standardSphere hUopen
          (isConnected_connectedComponentIn_iff.mpr x₂.2)
      have hsubsetP : Subtype.val ⁻¹' connectedComponentIn Cᶜ x₂.1.1 ⊆ P :=
        preimage_mono (connectedComponentIn_subset Cᶜ x₂.1.1)
      have hx₁ : x₁.1 ∈ Subtype.val ⁻¹' connectedComponentIn Cᶜ x₂.1.1 := hsame
      have hx₂ : x₂.1 ∈ Subtype.val ⁻¹' connectedComponentIn Cᶜ x₂.1.1 :=
        mem_connectedComponentIn x₂.2
      have hPopen : IsOpen P := by
        exact hC.isClosed.isOpen_compl.preimage continuous_subtype_val
      have hinsideP : IsConnected
          (Subtype.val ⁻¹' (Subtype.val ⁻¹' connectedComponentIn Cᶜ x₂.1.1) : Set P) := by
        apply hPconn.preimage_of_isOpenMap Subtype.val_injective hPopen.isOpenMap_subtype_val
        intro y hy
        exact ⟨⟨y, hsubsetP hy⟩, rfl⟩
      exact hinsideP.isPreconnected.subset_connectedComponent hx₂ hx₁
    · -- Every spherical component has a nonempty puncture, which supplies a preimage class.
      intro a
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
      have hUopen : IsOpen (connectedComponentIn Cᶜ x.1) :=
        isOpen_componentIn_standardSphere hC.isClosed.isOpen_compl
          (IsConnectedComponentIn.of_mem x.2)
      have hPconn : IsConnected (Subtype.val ⁻¹' connectedComponentIn Cᶜ x.1 :
          Set ({b}ᶜ : Set (StandardSphere 2))) :=
        isConnected_preimage_openConnected_standardSphere hUopen
          (isConnected_connectedComponentIn_iff.mpr x.2)
      obtain ⟨y, hy⟩ := hPconn.nonempty
      have hyC : y.1 ∈ Cᶜ := connectedComponentIn_subset Cᶜ x.1 hy
      let yp : P := ⟨y, hyC⟩
      refine ⟨ConnectedComponents.mk yp, ?_⟩
      rw [Continuous.connectedComponentsMap_mk, ConnectedComponents.coe_eq_coe']
      rw [connectedComponentIn_eq_image x.2] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have hzEq : z = j yp := Subtype.ext hzy
      exact hzEq ▸ hz
  let eP : ConnectedComponents P ≃ ConnectedComponents Q :=
    Equiv.ofBijective hj.connectedComponentsMap hjbij
  -- Restrict `h` to the two complements and use its canonical equivalence on components.
  have hhiff : ∀ x : ({b}ᶜ : Set (StandardSphere 2)), x ∈ P ↔
      h x ∈ (h '' (Subtype.val ⁻¹' C))ᶜ := by
    intro x
    rw [← image_preimage_compl_eq_compl_image C b h]
    exact ⟨fun hx ↦ mem_image_of_mem h hx, fun hx ↦ by
      obtain ⟨y, hy, hxy⟩ := hx
      exact h.injective hxy ▸ hy⟩
  let hP : P ≃ₜ ((h '' (Subtype.val ⁻¹' C))ᶜ :
      Set (EuclideanSpace ℝ (Fin 2))) := h.subtype hhiff
  have hfiber : ∀ y, IsConnected ((hP : P → _) ⁻¹' {y}) := by
    intro y
    have hsingleton : (hP : P → _) ⁻¹' {y} = {hP.symm y} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      exact ⟨fun hxy ↦ hP.injective (hxy.trans (hP.apply_symm_apply y).symm),
        fun hxy ↦ hxy ▸ hP.apply_symm_apply y⟩
    rw [hsingleton]
    exact isConnected_singleton
  let eH : ConnectedComponents P ≃
      ConnectedComponents ((h '' (Subtype.val ⁻¹' C))ᶜ :
        Set (EuclideanSpace ℝ (Fin 2))) :=
    (hP.isQuotientMap.isCoinducing.connectedComponentsHomeomorph hfiber).toEquiv
  exact ⟨eP.symm.trans eH⟩

/-- Lemma 61.1 (1): Under a homeomorphism from the two-sphere punctured at `b`
to the plane, a component of `Cᶜ` not containing `b` maps to a bounded component
of the complement of the image of `C`. -/
theorem puncturedSphere_componentImage_bounded
    (C U : Set (StandardSphere 2)) (b : StandardSphere 2)
    (h : ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) (hb : b ∉ C)
    (hU : IsConnectedComponentIn Cᶜ U) (hbU : b ∉ U) :
    IsConnectedComponentIn (h '' (Subtype.val ⁻¹' C))ᶜ
      (h '' (Subtype.val ⁻¹' U)) ∧
      Bornology.IsBounded (h '' (Subtype.val ⁻¹' U)) := by
  -- Component transport gives the first conclusion; compact closure gives boundedness.
  exact ⟨isConnectedComponentIn_image_preimage C U b h hC hb hU,
    image_preimage_component_isBounded C U b h hC hb hU hbU⟩

/-- Lemma 61.1 (2): Under a homeomorphism from the two-sphere punctured at `b`
to the plane, the punctured component of `Cᶜ` containing `b` maps to an
unbounded component of the complement of the image of `C`. -/
theorem puncturedSphere_componentImage_unbounded
    (C U : Set (StandardSphere 2)) (b : StandardSphere 2)
    (h : ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) (hU : IsConnectedComponentIn Cᶜ U) (hbU : b ∈ U) :
    IsConnectedComponentIn (h '' (Subtype.val ⁻¹' C))ᶜ
      (h '' (Subtype.val ⁻¹' U)) ∧
      ¬ Bornology.IsBounded (h '' (Subtype.val ⁻¹' U)) := by
  -- Membership in the component supplies the omitted hypothesis `b ∉ C`.
  have hb : b ∉ C := hU.subset hbU
  have hcompactCompl := isCompact_compl_image_preimage_component C U b h hC hU hbU
  exact ⟨isConnectedComponentIn_image_preimage C U b h hC hb hU,
    not_isBounded_of_isBounded_compl hcompactCompl.isBounded⟩

/-- Lemma 61.1 (3): The image of the punctured component containing `b` is the
unique unbounded component: every other component of the plane complement is
bounded. -/
theorem puncturedSphere_otherComponent_bounded
    (C U : Set (StandardSphere 2)) (b : StandardSphere 2)
    (h : ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) (hU : IsConnectedComponentIn Cᶜ U) (hbU : b ∈ U)
    (V : Set (EuclideanSpace ℝ (Fin 2)))
    (hV : IsConnectedComponentIn (h '' (Subtype.val ⁻¹' C))ᶜ V)
    (hne : V ≠ h '' (Subtype.val ⁻¹' U)) :
    Bornology.IsBounded V := by
  -- Once the distinguished image is known to be a component, every other component
  -- lies in its compact complement.
  have hb : b ∉ C := hU.subset hbU
  have hcompactCompl := isCompact_compl_image_preimage_component C U b h hC hU hbU
  have hImageComponent : IsConnectedComponentIn (h '' (Subtype.val ⁻¹' C))ᶜ
      (h '' (Subtype.val ⁻¹' U)) :=
    isConnectedComponentIn_image_preimage C U b h hC hb hU
  have hdisjoint := disjoint_of_isConnectedComponentIn_of_ne hV hImageComponent hne
  exact hcompactCompl.isBounded.subset (Set.disjoint_left.mp hdisjoint)

/-- Lemma 61.1 (4): The punctured-sphere homeomorphism preserves the number of
components of the complement of a compact subset. -/
theorem puncturedSphere_complement_componentCount
    (C : Set (StandardSphere 2)) (b : StandardSphere 2)
    (h : ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) (hb : b ∉ C) (n : ℕ)
    (hn : C.SeparatesInto n) :
    (h '' (Subtype.val ⁻¹' C)).SeparatesInto n := by
  -- The component equivalence transports the defining cardinal equality.
  obtain ⟨e⟩ := nonempty_connectedComponents_equiv_puncturedComplement C b h hC hb
  rw [separatesInto_iff] at hn ⊢
  rw [← Cardinal.mk_congr e]
  exact hn
