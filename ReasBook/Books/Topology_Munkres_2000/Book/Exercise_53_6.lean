module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Separation.CompletelyRegular

public section

universe u v

namespace IsCoveringMap

variable {E : Type u} {B : Type v}

open Filter Set Topology

/-- Helper for Exercise 53.6: finiteness of an equation fiber gives finiteness of
the corresponding singleton preimage. -/
private theorem finite_preimage_singleton {p : E → B} {b : B}
    [Finite {e : E // p e = b}] : Finite (p ⁻¹' {b}) := by
  have heq : p ⁻¹' {b} = {e : E | p e = b} := by
    ext e
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  rw [Set.finite_coe_iff, heq]
  exact Set.finite_coe_iff.mp (inferInstance : Finite {e : E // p e = b})

variable [TopologicalSpace E] [TopologicalSpace B]

/-- Helper for Exercise 53.6: every point of a covering space lies in an open sheet
that maps bijectively onto an open set, and closed subsets of the base lift to closed
subsets of that sheet. -/
private lemma exists_sheet {p : E → B} (hp : IsCoveringMap p) (x : E) :
    ∃ U : Set B, ∃ V : Set E,
      p x ∈ U ∧ x ∈ V ∧ IsOpen U ∧ IsOpen V ∧ V.InjOn p ∧ p '' V = U ∧
        ∀ C : Set B, IsClosed C → C ⊆ U → IsClosed (p ⁻¹' C ∩ V) := by
  -- Fix an evenly covered neighborhood and the sheet coordinate of `x`.
  obtain ⟨hdiscrete, U, hxU, hU, hpU, H, hH⟩ := hp (p x)
  let i : p ⁻¹' {p x} := (H ⟨x, hxU⟩).2
  let W : Set (p ⁻¹' U) := (Prod.snd ∘ H) ⁻¹' {i}
  let V : Set E := Subtype.val '' W
  have hWopen : IsOpen W := by
    exact (isOpen_discrete {i}).preimage (continuous_snd.comp H.continuous)
  have hWclosed : IsClosed W := by
    exact (isClosed_discrete {i}).preimage (continuous_snd.comp H.continuous)
  have hxV : x ∈ V := by
    refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    exact rfl
  have hVopen : IsOpen V := by
    exact hpU.isOpenMap_subtype_val W hWopen
  have hVinj : V.InjOn p := by
    rintro a ⟨a', ha'W, rfl⟩ b ⟨b', hb'W, rfl⟩ hab
    change (H a').2 = i at ha'W
    change (H b').2 = i at hb'W
    exact congrArg Subtype.val (H.injective (Prod.ext
      (Subtype.ext (hH a' |>.trans (hab.trans (hH b').symm)))
      (ha'W.trans hb'W.symm)))
  have hpV : p '' V = U := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨e, heW, rfl⟩, rfl⟩
      exact hH e ▸ (H e).1.2
    · intro b hbU
      let e : p ⁻¹' U := H.symm (⟨b, hbU⟩, i)
      have heW : e ∈ W := by
        simp only [W, Function.comp_apply, Set.mem_preimage, Set.mem_singleton_iff, e,
          H.apply_symm_apply]
      refine ⟨e, ⟨e, heW, rfl⟩, ?_⟩
      exact (hH e).symm.trans (congrArg (fun z ↦ z.1.1) (H.apply_symm_apply (⟨b, hbU⟩, i)))
  -- A closed sheet in the subspace `p ⁻¹' U` is cut out by a closed set of `E`.
  obtain ⟨A, hAclosed, hA⟩ := isClosed_induced_iff.mp hWclosed
  have hclosedLift (C : Set B) (hC : IsClosed C) (hCU : C ⊆ U) :
      IsClosed (p ⁻¹' C ∩ V) := by
    have heq : p ⁻¹' C ∩ V = p ⁻¹' C ∩ A := by
      ext e
      constructor
      · rintro ⟨heC, e', he'W, rfl⟩
        have he'A : e' ∈ Subtype.val ⁻¹' A := hA.symm ▸ he'W
        exact ⟨heC, he'A⟩
      · rintro ⟨heC, heA⟩
        have heU : p e ∈ U := hCU heC
        refine ⟨heC, ⟨e, heU⟩, ?_, rfl⟩
        have heA' : (⟨e, heU⟩ : p ⁻¹' U) ∈ Subtype.val ⁻¹' A := heA
        exact hA ▸ heA'
    rw [heq]
    exact (hC.preimage hp.continuous).inter hAclosed
  exact ⟨U, V, hxU, hxV, hU, hVopen, hVinj, hpV, hclosedLift⟩

/-- Helper for Exercise 53.6: regularity lifts along a covering map. -/
private theorem regularSpace {p : E → B} (hp : IsCoveringMap p) [RegularSpace B] :
    RegularSpace E := by
  -- Shrink a neighborhood inside one sheet, shrink its image to a closed base
  -- neighborhood, and lift that closed neighborhood back to the chosen sheet.
  refine RegularSpace.of_exists_mem_nhds_isClosed_subset fun x s hs ↦ ?_
  obtain ⟨U, V, hpxU, hxV, hU, hV, hinj, hpV, hclosed⟩ := exists_sheet hp x
  obtain ⟨O, hOs, hO, hxO⟩ := mem_nhds_iff.mp (Filter.inter_mem hs (hV.mem_nhds hxV))
  have hpOopen : IsOpen (p '' O) := hp.isOpenMap O hO
  have hpxO : p x ∈ p '' O := ⟨x, hxO, rfl⟩
  obtain ⟨C, hCnhds, hCclosed, hCpO⟩ :=
    exists_mem_nhds_isClosed_subset (hpOopen.mem_nhds hpxO)
  have hCU : C ⊆ U := hCpO.trans (Set.image_mono (hOs.trans Set.inter_subset_right)) |>.trans_eq hpV
  refine ⟨p ⁻¹' C ∩ V, Filter.inter_mem (hp.continuous.continuousAt hCnhds)
    (hV.mem_nhds hxV), hclosed C hCclosed hCU, ?_⟩
  rintro y ⟨hyC, hyV⟩
  obtain ⟨z, hzO, hpz⟩ := hCpO hyC
  have hzV : z ∈ V := hOs hzO |>.2
  have hyz : y = z := hinj hyV hzV hpz.symm
  exact hyz ▸ (hOs hzO).1

/-- Helper for Exercise 53.6: complete regularity lifts along a covering map. -/
private theorem completelyRegularSpace {p : E → B} (hp : IsCoveringMap p)
    [CompletelyRegularSpace B] : CompletelyRegularSpace E := by
  -- Build a closed lifted neighborhood disjoint from the prescribed closed set.
  rw [completelyRegularSpace_iff]
  intro x K hK hxK
  obtain ⟨U, V, hpxU, hxV, hU, hV, hinj, hpV, hclosed⟩ := exists_sheet hp x
  have hVK : V ∩ Kᶜ ∈ 𝓝 x := Filter.inter_mem (hV.mem_nhds hxV) (hK.isOpen_compl.mem_nhds hxK)
  obtain ⟨O, hOVK, hO, hxO⟩ := mem_nhds_iff.mp hVK
  have hpOopen : IsOpen (p '' O) := hp.isOpenMap O hO
  have hpxO : p x ∈ p '' O := ⟨x, hxO, rfl⟩
  obtain ⟨C, hCnhds, hCclosed, hCpO⟩ :=
    exists_mem_nhds_isClosed_subset (hpOopen.mem_nhds hpxO)
  have hCU : C ⊆ U := hCpO.trans (Set.image_mono (hOVK.trans Set.inter_subset_left)) |>.trans_eq hpV
  let D : Set E := p ⁻¹' C ∩ V
  have hDclosed : IsClosed D := hclosed C hCclosed hCU
  have hxC : p x ∈ C := mem_of_mem_nhds hCnhds
  have hxD : x ∈ D := ⟨hxC, hxV⟩
  have hDK : Disjoint D K := by
    refine Set.disjoint_left.mpr fun y hyD hyK ↦ ?_
    obtain ⟨z, hzO, hpz⟩ := hCpO hyD.1
    have hzV : z ∈ V := (hOVK hzO).1
    have hyz : y = z := hinj hyD.2 hzV hpz.symm
    exact (hOVK hzO).2 (hyz ▸ hyK)
  have hpxInterior : p x ∈ interior C := mem_interior_iff_mem_nhds.mpr hCnhds
  obtain ⟨g, hgcontinuous, hgx, hgoutside⟩ :=
    CompletelyRegularSpace.completely_regular_isOpen (p x) (interior C) isOpen_interior hpxInterior
  classical
  let f : E → Set.Icc (0 : ℝ) 1 := D.piecewise (g ∘ p) 1
  -- On the frontier of the closed lifted neighborhood, the base point is outside
  -- `interior C`, so the two branches of the piecewise function agree.
  have hfrontier : ∀ y ∈ frontier D, (g ∘ p) y = 1 := by
    intro y hy
    apply hgoutside
    intro hypy
    have hyD : y ∈ D := hDclosed.closure_eq ▸ frontier_subset_closure hy
    have hopen : IsOpen (p ⁻¹' interior C ∩ V) :=
      (isOpen_interior.preimage hp.continuous).inter hV
    have hsubset : p ⁻¹' interior C ∩ V ⊆ D :=
      Set.inter_subset_inter (Set.preimage_mono interior_subset) Set.Subset.rfl
    have hyInterior : y ∈ interior D :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hopen.mem_nhds ⟨hypy, hyD.2⟩) hsubset)
    exact Set.disjoint_left.mp disjoint_interior_frontier hyInterior hy
  have hfcontinuous : Continuous f := by
    exact hgcontinuous.comp hp.continuous |>.piecewise hfrontier continuous_const
  refine ⟨f, hfcontinuous, ?_, ?_⟩
  · simpa only [f, Set.piecewise_eq_of_mem (s := D) (f := g ∘ p) (g := 1) hxD,
      Function.comp_apply] using hgx
  · intro y hyK
    have hyD : y ∉ D := fun hyD ↦ Set.disjoint_left.mp hDK hyD hyK
    simp only [f, Set.piecewise_eq_of_notMem (s := D) (f := g ∘ p) (g := 1) hyD]

/-- Helper for Exercise 53.6: a covering map with finite fibers is closed. -/
private theorem isClosedMap_of_finite_fiber {p : E → B} (hp : IsCoveringMap p)
    [∀ b : B, Finite {e : E // p e = b}] : IsClosedMap p := by
  classical
  -- Use the evenly covered neighborhoods as an open cover of the target.
  choose U hbU hU hpU H hH using fun b : B ↦ (hp b).2
  let cover : B → TopologicalSpace.Opens B := fun b ↦ ⟨U b, hU b⟩
  have hcover : TopologicalSpace.IsOpenCover cover := by
    refine TopologicalSpace.IsOpenCover.of_sets (v := U) hU ?_
    apply Set.eq_univ_of_forall
    intro b
    exact Set.mem_iUnion.mpr ⟨b, hbU b⟩
  rw [hcover.isClosedMap_iff_restrictPreimage]
  intro b
  letI : Finite (p ⁻¹' {b}) := finite_preimage_singleton
  have hmap : (U b).restrictPreimage p = Prod.fst ∘ H b := by
    funext e
    exact Subtype.ext (hH b e).symm
  rw [hmap]
  exact isClosedMap_fst_of_compactSpace.comp (H b).isClosedMap

/-- Exercise 53.6 (1). If the base of a covering map is Hausdorff, then its total
space is Hausdorff. -/
theorem t2Space {p : E → B} (hp : IsCoveringMap p) [T2Space B] : T2Space E := by
  -- Points in one fiber are separated by the covering-map separation property;
  -- points in distinct fibers are separated by inverse images from the Hausdorff base.
  constructor
  intro x y hxy
  by_cases hpxy : p x = p y
  · exact hp.isSeparatedMap x y hpxy hxy
  · obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hpxy
    exact ⟨p ⁻¹' U, p ⁻¹' V, hU.preimage hp.continuous, hV.preimage hp.continuous,
      hxU, hyV, Set.disjoint_left.mpr fun z hzU hzV ↦ Set.disjoint_left.mp hUV hzU hzV⟩

/-- Companion to Exercise 53.6 (2). If the base of a covering map is regular in Munkres's sense,
then its total space is regular in the same sense. -/
theorem t3Space {p : E → B} (hp : IsCoveringMap p) [T3Space B] : T3Space E := by
  -- Combine lifted regularity with the Hausdorff (hence T₀) result above.
  letI : T2Space E := hp.t2Space
  letI : RegularSpace E := regularSpace hp
  exact inferInstance

/-- Companion to Exercise 53.6 (3). If the base of a covering map is completely regular in
Munkres's sense, then its total space is completely regular in the same sense. -/
theorem t35Space {p : E → B} (hp : IsCoveringMap p) [T35Space B] : T35Space E := by
  -- Combine the lifted separating functions with the Hausdorff (hence T₀) result.
  letI : T2Space E := hp.t2Space
  letI : CompletelyRegularSpace E := completelyRegularSpace hp
  exact @T35Space.mk E _ inferInstance inferInstance

/-- Companion to Exercise 53.6 (4). If the base of a covering map is locally compact, then its
total space is locally compact. Together with `IsCoveringMap.t2Space`, this gives
the locally compact Hausdorff assertion. -/
theorem locallyCompactSpace {p : E → B} (hp : IsCoveringMap p) [LocallyCompactSpace B] :
    LocallyCompactSpace E := by
  -- Work in a local source chart, transfer local compactness across its
  -- source-target homeomorphism, and map the resulting compact neighborhood to `E`.
  refine ⟨fun x n hn ↦ ?_⟩
  obtain ⟨e, hxe, hep⟩ := hp.isLocalHomeomorph x
  letI : LocallyCompactSpace e.target := e.open_target.locallyCompactSpace
  letI : LocallyCompactSpace e.source :=
    e.toHomeomorphSourceTarget.locallyCompactSpace_iff.mpr inferInstance
  have hnSource : Subtype.val ⁻¹' n ∈ 𝓝 (⟨x, hxe⟩ : e.source) :=
    continuous_subtype_val.continuousAt hn
  obtain ⟨K, hKnhds, hKn, hKcompact⟩ := local_compact_nhds hnSource
  refine ⟨Subtype.val '' K, e.open_source.isOpenMap_subtype_val.image_mem_nhds hKnhds,
    ?_, hKcompact.image continuous_subtype_val⟩
  rintro _ ⟨y, hyK, rfl⟩
  exact hKn hyK

/-- Companion to Exercise 53.6 (5). If the base of a covering map is compact and every fiber is
finite, then its total space is compact. -/
theorem compactSpace_of_finite_fiber {p : E → B} (hp : IsCoveringMap p) [CompactSpace B]
    [∀ b : B, Finite {e : E // p e = b}] : CompactSpace E := by
  -- Finite fibers are compact, while the preceding local trivialization argument
  -- makes the covering closed; hence it is proper and pulls back compact `univ`.
  have hproper : IsProperMap p := by
    rw [isProperMap_iff_isClosedMap_and_compact_fibers]
    refine ⟨hp.continuous, isClosedMap_of_finite_fiber hp, fun b ↦ ?_⟩
    letI : Finite (p ⁻¹' {b}) := finite_preimage_singleton
    exact isCompact_iff_compactSpace.mpr inferInstance
  refine ⟨?_⟩
  simpa only [Set.preimage_univ] using hproper.isCompact_preimage (K := Set.univ) isCompact_univ

end IsCoveringMap
