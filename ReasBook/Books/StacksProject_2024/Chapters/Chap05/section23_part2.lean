import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.Spectral.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_23_12 (from Chap05) -/
open CategoryTheory CategoryTheory.Limits Opposite Set TopologicalSpace

universe u

noncomputable section

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (F : Iᵒᵖ ⥤ TopCat.{u})
variable [∀ i : Iᵒᵖ, T0Space (F.obj i)]
variable [∀ i : Iᵒᵖ, QuasiSober (F.obj i)]

/-- Helper for Lemma 5.23.12: a compatible family of stage points determines a point of the
explicit inverse-limit cone `TopCat.limitCone F`. -/
def limit_cone_point_of_compatible_family
    (x : ∀ i : Iᵒᵖ, F.obj i)
    (hx : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), F.map f (x i) = x j) :
    (TopCat.limitCone F).pt :=
  ⟨x, fun {_ _} f ↦ hx f⟩

/-- Helper for Lemma 5.23.12: an irreducible closed subset of the explicit inverse limit has a
generic point obtained from the compatible family of stage generic points. -/
lemma generic_point_of_irreducible_closed_limit
    {Z : Set (TopCat.limitCone F).pt} (hZ_irred : IsIrreducible Z) (hZ_closed : IsClosed Z) :
    ∃ ξ : (TopCat.limitCone F).pt, IsGenericPoint ξ Z := by
  let C := TopCat.limitCone F
  have hC : IsLimit C := TopCat.limitConeIsLimit F
  have hπ {i j : Iᵒᵖ} (f : i ⟶ j) (x : C.pt) :
      C.π.app j x = F.map f (C.π.app i x) := by
    rw [← CategoryTheory.comp_apply]
    exact congrArg (fun g : C.pt ⟶ F.obj j ↦ g x) (C.w f).symm
  have hImage_irred (i : Iᵒᵖ) : IsIrreducible (C.π.app i '' Z) :=
    hZ_irred.image (C.π.app i) (C.π.app i).hom.continuous.continuousOn
  let ξi : ∀ i : Iᵒᵖ, F.obj i := fun i ↦ (hImage_irred i).genericPoint
  have hξi : ∀ i : Iᵒᵖ, IsGenericPoint (ξi i) (closure (C.π.app i '' Z)) := by
    intro i
    simpa [ξi] using (hImage_irred i).isGenericPoint_genericPoint_closure
  have hmap_image {i j : Iᵒᵖ} (f : i ⟶ j) :
      F.map f '' (C.π.app i '' Z) = C.π.app j '' Z := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, hπ f z⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨C.π.app i z, ⟨z, hz, rfl⟩, (hπ f z).symm⟩
  have hξ_compatible : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), F.map f (ξi i) = ξi j := by
    intro i j f
    have hImageGeneric :
        IsGenericPoint (F.map f (ξi i)) (closure (C.π.app j '' Z)) := by
      have htmp := (hξi i).image (F.map f).hom.continuous
      have hclosure :
          closure (F.map f '' closure (C.π.app i '' Z)) = closure (C.π.app j '' Z) := by
        rw [closure_image_closure (F.map f).hom.continuous]
        simpa using congrArg closure (hmap_image (f := f))
      exact hclosure ▸ htmp
    exact IsGenericPoint.eq hImageGeneric (hξi j)
  let ξ : C.pt :=
    limit_cone_point_of_compatible_family (F := F) ξi (fun {i j} f ↦ hξ_compatible f)
  have hξ_mem_closure : ξ ∈ closure Z := by
    -- Expand an arbitrary neighborhood of `ξ` into a union of stage pullbacks, then use the stage
    -- generic point to find a point of `Z` in that same stage pullback.
    rw [mem_closure_iff]
    intro U hU hξU
    let Uo : Opens C.pt := ⟨U, hU⟩
    obtain ⟨W, hW⟩ := open_eq_iUnion_preimage_of_isLimit (F := F) (C := C) hC Uo
    have hξUo : ξ ∈ (Uo : Set C.pt) := by
      simpa [Uo] using hξU
    have hξUnionSet : ξ ∈ ⋃ i, C.π.app i ⁻¹' (W i : Set (F.obj i)) := by
      rwa [hW] at hξUo
    rcases mem_iUnion.1 hξUnionSet with ⟨i, hξWi⟩
    have hξiWi : ξi i ∈ (W i : Set (F.obj i)) := by
      simpa [ξ, limit_cone_point_of_compatible_family] using hξWi
    have hStageMeet :
        (closure (C.π.app i '' Z) ∩ (W i : Set (F.obj i))).Nonempty :=
      ((hξi i).mem_open_set_iff (W i).isOpen).1 hξiWi
    rcases hStageMeet with ⟨y, hyClosure, hyWi⟩
    rcases mem_closure_iff.1 hyClosure (W i : Set (F.obj i)) (W i).isOpen hyWi with
      ⟨w, hwWi, hwImage⟩
    rcases hwImage with ⟨z, hz, rfl⟩
    refine ⟨z, ?_, hz⟩
    have hzUnion : z ∈ ⋃ i, C.π.app i ⁻¹' (W i : Set (F.obj i)) := by
      exact mem_iUnion.2 ⟨i, by simpa using hwWi⟩
    have hzUo : z ∈ (Uo : Set C.pt) := by
      rwa [hW]
    simpa [Uo] using hzUo
  have hξ_mem : ξ ∈ Z := by
    simpa [hZ_closed.closure_eq] using hξ_mem_closure
  have hξ_specializes : ∀ ⦃z : C.pt⦄, z ∈ Z → ξ ⤳ z := by
    intro z hz
    -- Expand a neighborhood of `z` into stage pullbacks. The chosen stage pullback contains a
    -- point of the stage image of `Z`, hence also the stage generic point, so `ξ` lies in it.
    rw [specializes_iff_forall_open]
    intro U hU hzU
    let Uo : Opens C.pt := ⟨U, hU⟩
    obtain ⟨W, hW⟩ := open_eq_iUnion_preimage_of_isLimit (F := F) (C := C) hC Uo
    have hzUo : z ∈ (Uo : Set C.pt) := by
      simpa [Uo] using hzU
    have hzUnionSet : z ∈ ⋃ i, C.π.app i ⁻¹' (W i : Set (F.obj i)) := by
      rwa [hW] at hzUo
    rcases mem_iUnion.1 hzUnionSet with ⟨i, hzWi⟩
    have hStageMeet :
        (closure (C.π.app i '' Z) ∩ (W i : Set (F.obj i))).Nonempty := by
      exact ⟨C.π.app i z, subset_closure ⟨z, hz, rfl⟩, hzWi⟩
    have hξiWi : ξi i ∈ (W i : Set (F.obj i)) :=
      ((hξi i).mem_open_set_iff (W i).isOpen).2 hStageMeet
    have hξUnion : ξ ∈ ⋃ i, C.π.app i ⁻¹' (W i : Set (F.obj i)) := by
      exact mem_iUnion.2 ⟨i, by simpa [ξ, limit_cone_point_of_compatible_family] using hξiWi⟩
    have hξUo : ξ ∈ (Uo : Set C.pt) := by
      rwa [hW]
    simpa [Uo] using hξUo
  have hclosure_subset : closure ({ξ} : Set C.pt) ⊆ Z :=
    hZ_closed.closure_subset_iff.mpr (by simpa using (singleton_subset_iff.mpr hξ_mem))
  refine ⟨ξ, ?_⟩
  -- The specialization criterion identifies `Z` with the closure of the singleton `{ξ}`.
  rw [isGenericPoint_iff_specializes]
  intro z
  constructor
  · intro hz
    exact hclosure_subset (specializes_iff_mem_closure.mp hz)
  · intro hz
    exact hξ_specializes hz

/-- Helper for Lemma 5.23.12: index the basic opens on the explicit limit cone by a stage together
with an open subset of that stage. -/
private def projection_preimage_basis (C : Cone F) :
    (Σ i : Iᵒᵖ, Opens (F.obj i)) → Set C.pt :=
  fun p ↦ C.π.app p.1 ⁻¹' (p.2 : Set (F.obj p.1))

/-- Helper for Lemma 5.23.12: projection pullbacks of stage opens form the canonical basis on the
explicit inverse-limit cone. -/
lemma isTopologicalBasis_projection_preimages :
    IsTopologicalBasis
      (Set.range (projection_preimage_basis (F := F) (TopCat.limitCone F))) := by
  let C := TopCat.limitCone F
  -- Rewrite the sigma-indexed family into the existential form expected by the mathlib owner.
  rw [show Set.range (projection_preimage_basis (F := F) C) =
      {W : Set C.pt | ∃ (j : Iᵒᵖ) (U : Set (F.obj j)), IsOpen U ∧ W = C.π.app j ⁻¹' U} by
      ext W
      constructor
      · rintro ⟨⟨j, U⟩, rfl⟩
        exact ⟨j, (U : Set (F.obj j)), U.isOpen, rfl⟩
      · rintro ⟨j, U, hU, rfl⟩
        exact ⟨⟨j, ⟨U, hU⟩⟩, rfl⟩]
  simpa using
    (TopCat.isTopologicalBasis_cofiltered_limit.{u, u, u} F C (TopCat.limitConeIsLimit F)
      (fun j ↦ {U : Set (F.obj j) | IsOpen U})
      (fun _ ↦ isTopologicalBasis_opens)
      (fun _ ↦ isOpen_univ)
      (fun _ _ _ hU₁ hU₂ ↦ hU₁.inter hU₂)
      (fun _ _ f _ hU ↦ hU.preimage (F.map f).hom.continuous))

/-- Helper for Lemma 5.23.12: the identity on compatible families is continuous from the inverse
limit built from the discrete stage topologies to the original inverse limit. -/
noncomputable def continuous_discrete_stage_limit_to_original_limit :
    (TopCat.limitCone (F ⋙ forget TopCat ⋙ TopCat.discrete)).pt ⟶ (TopCat.limitCone F).pt := by
  let C := TopCat.limitCone F
  let D := TopCat.limitCone (F ⋙ forget TopCat ⋙ TopCat.discrete)
  have hC : IsLimit C := TopCat.limitConeIsLimit F
  have hle : D.pt.str ≤ C.pt.str := by
    -- Route correction: compare the two limit topologies by checking continuity of each original
    -- stage projection out of the finer discrete-stage limit.
    rw [TopCat.induced_of_isLimit C hC]
    refine le_iInf ?_
    intro i
    exact (continuous_iff_le_induced).1 <| by
      letI : DiscreteTopology ↥((F ⋙ forget TopCat ⋙ TopCat.discrete).obj i) := by
        change DiscreteTopology ↥(TopCat.discrete.obj ↥(F.obj i))
        infer_instance
      -- Every subset is open on the discrete stage, so the original stage projection is
      -- continuous from the discrete-stage limit.
      rw [continuous_def]
      intro V hV
      let V' : Set ((F ⋙ forget TopCat ⋙ TopCat.discrete).obj i) := V
      have hV' : IsOpen V' := isOpen_discrete V'
      simpa [V'] using (D.π.app i).hom.continuous.isOpen_preimage _ hV'
  have hcont : @Continuous D.pt C.pt D.pt.str C.pt.str (fun x ↦ (x : C.pt)) := by
    rw [continuous_iff_le_induced]
    change D.pt.str ≤ induced id C.pt.str
    rw [induced_id]
    exact hle
  exact TopCat.ofHom ⟨fun x ↦ (x : C.pt), hcont⟩

/-- Helper for Lemma 5.23.12: every basic projection pullback is compact, by viewing the same
compatible-family set with the finer inverse-limit topology coming from discrete finite stages. -/
lemma projection_preimage_isCompact_via_discrete_stage_limit
    [∀ i : Iᵒᵖ, Finite (F.obj i)] (i : Iᵒᵖ) (U : Opens (F.obj i)) :
    IsCompact (((TopCat.limitCone F).π.app i) ⁻¹' (U : Set (F.obj i))) := by
  let C := TopCat.limitCone F
  let G := F ⋙ forget TopCat ⋙ TopCat.discrete
  let D := TopCat.limitCone G
  let f : D.pt ⟶ C.pt := continuous_discrete_stage_limit_to_original_limit (F := F)
  have hproj (x : D.pt) : C.π.app i (f x) = D.π.app i x := rfl
  haveI : CompactSpace ↥D.pt := by
    -- The discrete-stage system is a diagram of finite discrete compact Hausdorff spaces.
    haveI : ∀ j : Iᵒᵖ, CompactSpace ↥(G.obj j) := by
      intro j
      letI : Finite ↥(G.obj j) := by
        change Finite ↥(F.obj j)
        infer_instance
      infer_instance
    haveI : ∀ j : Iᵒᵖ, T2Space ↥(G.obj j) := by
      intro j
      letI : DiscreteTopology ↥(G.obj j) := by
        change DiscreteTopology ↥(TopCat.discrete.obj ↥(F.obj j))
        infer_instance
      infer_instance
    letI : CompactSpace ↥((limit.cone G).pt) := by
      simpa using (compactSpace_limit_of_compactSpace_t2Space G)
    let e :=
      TopCat.homeoOfIso
        (IsLimit.conePointUniqueUpToIso (TopCat.limitConeIsLimit G) (limit.isLimit G))
    simpa [D] using e.symm.compactSpace
  let s : Set (G.obj i) := ((U : Set (F.obj i)) : Set (G.obj i))
  have hCompactDiscrete : IsCompact ((D.π.app i) ⁻¹' s) := by
    letI : DiscreteTopology ↥(G.obj i) := by
      change DiscreteTopology ↥(TopCat.discrete.obj ↥(F.obj i))
      infer_instance
    -- In the discrete-stage limit the same basic set is closed, hence compact.
    have hClosed : IsClosed ((D.π.app i) ⁻¹' s : Set D.pt) :=
      (isClosed_discrete s).preimage (D.π.app i).hom.continuous
    exact hClosed.isCompact
  have hImage :
      (f '' ((D.π.app i) ⁻¹' s : Set D.pt)) = ((C.π.app i) ⁻¹' (U : Set (F.obj i)) : Set C.pt) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_preimage.2 <| by
        simpa [s, hproj y] using (mem_preimage.1 hy)
    · intro hx
      refine ⟨x, ?_, ?_⟩
      · exact mem_preimage.2 <| by
          simpa [s, hproj x] using (mem_preimage.1 hx)
      · show (f x : C.pt) = x
        rfl
  -- The comparison map is the identity on the compatible-family set, so its image is exactly the
  -- original basic open.
  convert hCompactDiscrete.image f.hom.continuous using 1
  exact hImage.symm

/-- Helper for Lemma 5.23.12: the intersection of two basis opens is again a single basis open
after passing to a common upper-bound stage in the directed system. -/
lemma projection_preimage_inter_eq
    (i j : Iᵒᵖ) (Ui : Opens (F.obj i)) (Uj : Opens (F.obj j)) :
    ∃ (k : Iᵒᵖ) (_ : k ⟶ i) (_ : k ⟶ j) (Uk : Opens (F.obj k)),
      (((TopCat.limitCone F).π.app i) ⁻¹' (Ui : Set (F.obj i))) ∩
          (((TopCat.limitCone F).π.app j) ⁻¹' (Uj : Set (F.obj j))) =
        ((TopCat.limitCone F).π.app k) ⁻¹' (Uk : Set (F.obj k)) := by
  let C := TopCat.limitCone F
  have hπ {a b : Iᵒᵖ} (h : a ⟶ b) (x : C.pt) :
      C.π.app b x = F.map h (C.π.app a x) := by
    rw [← CategoryTheory.comp_apply]
    exact congrArg (fun m : C.pt ⟶ F.obj b ↦ m x) (C.w h).symm
  -- Directedness lets us compare both stage conditions at one common stage.
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.unop j.unop
  let k' : Iᵒᵖ := Opposite.op k
  let f : k' ⟶ i := Quiver.Hom.op (homOfLE hik)
  let g : k' ⟶ j := Quiver.Hom.op (homOfLE hjk)
  let Uk : Opens (F.obj k') := Opens.comap (F.map f).hom Ui ⊓ Opens.comap (F.map g).hom Uj
  refine ⟨k', f, g, Uk, ?_⟩
  ext x
  constructor
  · rintro ⟨hxi, hxj⟩
    refine mem_preimage.2 ?_
    constructor
    · have hxi' : C.π.app i x ∈ (Ui : Set (F.obj i)) := hxi
      rwa [hπ f x] at hxi'
    · have hxj' : C.π.app j x ∈ (Uj : Set (F.obj j)) := hxj
      rwa [hπ g x] at hxj'
  · intro hx
    have hxpair :
        x ∈ (C.π.app k') ⁻¹' ((Opens.comap (F.map f).hom Ui : Opens (F.obj k')) : Set (F.obj k')) ∩
          (C.π.app k') ⁻¹' ((Opens.comap (F.map g).hom Uj : Opens (F.obj k')) : Set (F.obj k')) := by
      simpa [Uk] using hx
    constructor
    · refine mem_preimage.2 ?_
      have hleft : F.map f (C.π.app k' x) ∈ (Ui : Set (F.obj i)) := hxpair.1
      rwa [hπ f x]
    · refine mem_preimage.2 ?_
      have hright : F.map g (C.π.app k' x) ∈ (Uj : Set (F.obj j)) := hxpair.2
      rwa [hπ g x]

-- Proof sketch: the source proof splits into two pieces. The sobriety part is implemented below by
-- constructing the compatible family of stage generic points. The remaining compact-open basis
-- comparison still needs the discrete-limit compactness bridge.
/-- Lemma 5.23.12: the inverse limit of a directed inverse system of finite sober topological
spaces is a spectral topological space. -/
theorem spectralSpace_of_limit_finite_sober_inverse_system
    [∀ i : Iᵒᵖ, Finite (F.obj i)] :
    SpectralSpace ↥(limit F) := by
  classical
  let C := TopCat.limitCone F
  -- Route correction: work on the explicit cone point first; the sobriety heart is already
  -- available from `generic_point_of_irreducible_closed_limit`.
  letI : T0Space C.pt := by
    change T0Space { u : ∀ j : Iᵒᵖ, F.obj j |
      ∀ {i j : Iᵒᵖ} (f : i ⟶ j), F.map f (u i) = u j }
    infer_instance
  letI : QuasiSober C.pt :=
    { sober := fun {Z} hZ_irred hZ_closed ↦
        generic_point_of_irreducible_closed_limit (F := F) hZ_irred hZ_closed }
  let i₀ : Iᵒᵖ := Opposite.op (Classical.choice ‹Nonempty I›)
  letI : CompactSpace C.pt := CompactSpace.mk <| by
    -- Taking the top open on any stage identifies the whole inverse limit with one basis element.
    simpa using
      (projection_preimage_isCompact_via_discrete_stage_limit (F := F) i₀ (⊤ : Opens (F.obj i₀)))
  let b := projection_preimage_basis (F := F) C
  have hBasis : IsTopologicalBasis (Set.range b) :=
    isTopologicalBasis_projection_preimages (F := F)
  have hCompactBasis : ∀ p : Σ i : Iᵒᵖ, Opens (F.obj i), IsCompact (b p) := by
    rintro ⟨i, U⟩
    -- Each basis open inherits compactness from the discrete-stage comparison space.
    simpa [b, projection_preimage_basis] using
      (projection_preimage_isCompact_via_discrete_stage_limit (F := F) i U)
  have hCompactInter :
      ∀ p q : Σ i : Iᵒᵖ, Opens (F.obj i), IsCompact (b p ∩ b q) := by
    rintro ⟨i, Ui⟩ ⟨j, Uj⟩
    obtain ⟨k, _, _, Uk, hEq⟩ := projection_preimage_inter_eq (F := F) i j Ui Uj
    -- Directedness rewrites every basis intersection to one basis open upstairs.
    have hbEq : b ⟨i, Ui⟩ ∩ b ⟨j, Uj⟩ = b ⟨k, Uk⟩ := by
      simpa [b, projection_preimage_basis] using hEq
    rw [hbEq]
    simpa [b, projection_preimage_basis] using
      (projection_preimage_isCompact_via_discrete_stage_limit (F := F) k Uk)
  letI : PrespectralSpace C.pt :=
    PrespectralSpace.of_isTopologicalBasis' hBasis hCompactBasis
  letI : QuasiSeparatedSpace C.pt :=
    QuasiSeparatedSpace.of_isTopologicalBasis hBasis hCompactInter
  letI : SpectralSpace C.pt :=
    { toT0Space := inferInstance
      toCompactSpace := inferInstance
      toQuasiSober := inferInstance
      toQuasiSeparatedSpace := inferInstance
      toPrespectralSpace := inferInstance }
  let e :=
    TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso (TopCat.limitConeIsLimit F) (limit.isLimit F))
  -- Transport the spectral ingredients from the explicit owner cone to the abstract categorical
  -- limit object.
  letI : T0Space ↥(limit F) := e.t0Space
  letI : CompactSpace ↥(limit F) := e.compactSpace
  letI : QuasiSober ↥(limit F) := e.symm.isOpenEmbedding.quasiSober
  letI : QuasiSeparatedSpace ↥(limit F) := e.symm.isOpenEmbedding.quasiSeparatedSpace
  letI : PrespectralSpace ↥(limit F) := e.symm.isOpenEmbedding.prespectralSpace
  exact SpectralSpace.mk

end

/-! ### Lemma_5_23_13 (from Chap05) -/
universe u v

open CategoryTheory Limits Opposite
open Set TopologicalSpace Topology

/- Domain-style sampling for spectral Sierpinski-product embeddings:
- primary domain: spectral spaces, constructible topology, and a compact-open Sierpinski-product
  map;
- sampled owner declarations:
  `SpectralSpace`,
  `CompactOpens`,
  `IsSpectralMap.isClosed_range_constructibleTopology`,
  `spectralSpace_subtype_of_isClosed_constructibleTopology`;
- best owner abstraction: the primitive owner data for the reverse direction are an embedding
  `f : X → ι → Prop` together with constructible-topology closedness of its range, while the
  forward spectral witness is the compact-open characteristic map indexed by `CompactOpens X`;
- primitive-vs-derived split: the embedding and range-closedness are the source-facing primitive
  data, while the existential packaging of a witness is derived API.

Layer triage:
- `source-facing`: Lemma 5.23.13, the existential embedding characterization of spectral spaces;
- `core/canonical`: `SpectralSpace`, `constructibleTopology`, `CompactOpens`, and the Sierpinski
  function space `ι → Prop`;
- `bridge/view`: the constructible-closed range bridge for spectral maps, the spectral-subspace
  bridge for constructibly closed subspaces, and the inverse-limit comparison from finite
  coordinate systems to the full Sierpinski product.
-/

section

variable (X : Type u) [TopologicalSpace X]

/-- Helper for Lemma 5.23.13: an open subset of the Sierpinski space containing `False` is the
whole space. -/
private theorem open_subset_prop_eq_univ {s : Set Prop} (hs : IsOpen s) (hFalse : False ∈ s) :
    s = Set.univ := by
  have h : s ∈ 𝓝 False := hs.mem_nhds hFalse
  simpa using h

/-- Helper for Lemma 5.23.13: an open subset of the Sierpinski space containing `True` but not
`False` is exactly `{True}`. -/
private theorem open_subset_prop_eq_singleton_true {s : Set Prop} (hs : IsOpen s)
    (hTrue : True ∈ s) (hFalse : False ∉ s) : s = ({True} : Set Prop) := by
  ext p
  by_cases hp : p
  · simpa [hp] using hTrue
  · have h : s ∈ 𝓝 True := hs.mem_nhds hTrue
    simpa [nhds_true, hp, hFalse] using h

/-- Helper for Lemma 5.23.13: the two-point Sierpinski space is quasi-sober. -/
private theorem quasiSoberProp : QuasiSober Prop := by
  refine ⟨?_⟩
  intro S hS hSclosed
  by_cases hTrue : True ∈ S
  · -- A closed irreducible subset containing `True` must also contain `False`, hence is `univ`.
    have hFalse : False ∈ S := by
      have hsub : closure ({True} : Set Prop) ⊆ S :=
        hSclosed.closure_subset_iff.mpr (by simpa using hTrue)
      have hmem : False ∈ closure ({True} : Set Prop) := by
        simp
      exact hsub hmem
    use True
    have hUniv : S = Set.univ := by
      ext p
      by_cases hp : p <;> simp [hp, hTrue, hFalse]
    simpa [hUniv] using (show IsGenericPoint True (Set.univ : Set Prop) by
      rw [isGenericPoint_def]
      ext p
      by_cases hp : p <;> simp [hp])
  · -- Otherwise irreducibility forces the closed subset to be exactly `{False}`.
    have hFalse : False ∈ S := by
      rcases hS.1 with ⟨x, hx⟩
      by_cases hxTrue : x
      · have hxEq : x = True := propext (iff_true_intro hxTrue)
        exact (hTrue <| by simpa [hxEq] using hx).elim
      · have hxEq : x = False := propext (iff_false_intro hxTrue)
        simpa [hxEq] using hx
    use False
    have hSingleton : S = ({False} : Set Prop) := by
      ext p
      by_cases hp : p <;> simp [hp, hTrue, hFalse]
    simpa [hSingleton] using (show IsGenericPoint False ({False} : Set Prop) by
      rw [isGenericPoint_def]
      ext p
      by_cases hp : p <;> simp [hp])

/-- Helper for Lemma 5.23.13: the Sierpinski space itself is spectral. -/
private theorem spectralSpaceProp : SpectralSpace Prop := by
  letI : QuasiSober Prop := quasiSoberProp
  exact SpectralSpace.mk

/-- Helper for Lemma 5.23.13: every finite product of the Sierpinski space is spectral. -/
private theorem spectralSpaceFiniteSierpinskiProduct {α : Type v} [Finite α] :
    SpectralSpace (α → Prop) := by
  classical
  -- Build finite products by repeatedly splitting off one coordinate with `Option`.
  refine Finite.induction_empty_option (P := fun β => SpectralSpace (β → Prop)) ?_ ?_ ?_ α
  · intro β γ e hβ
    let hHomeo : (γ → Prop) ≃ₜ (β → Prop) := by
      simpa using (Homeomorph.piCongrLeft (Y := fun _ : β => Prop) e.symm)
    letI : SpectralSpace (β → Prop) := hβ
    letI : CompactSpace (γ → Prop) := hHomeo.symm.compactSpace
    exact hHomeo.isOpenEmbedding.spectralSpace
  · let hHomeo : (PEmpty → Prop) ≃ₜ PUnit := Homeomorph.homeomorphOfUnique _ _
    letI : SpectralSpace PUnit := SpectralSpace.mk
    letI : CompactSpace (PEmpty → Prop) := hHomeo.symm.compactSpace
    exact hHomeo.isOpenEmbedding.spectralSpace
  · intro β _ hβ
    let e₁ : (Option β → Prop) ≃ₜ ((i : {x : Option β // x = none}) → Prop) ×
        ((i : {x : Option β // x ≠ none}) → Prop) :=
      Homeomorph.piEquivPiSubtypeProd (fun x : Option β => x = none) (fun _ => Prop)
    let eSome : {x : Option β // x ≠ none} ≃ β :=
      { toFun := fun x =>
          Option.get x.1 (Option.isSome_iff_exists.mpr (Option.ne_none_iff_exists'.1 x.2))
        invFun := fun b => ⟨some b, by simp⟩
        left_inv := by
          intro x
          apply Subtype.ext
          have hmem := Option.get_mem (o := x.1)
            (Option.isSome_iff_exists.mpr (Option.ne_none_iff_exists'.1 x.2))
          simpa [Option.mem_def] using hmem
        right_inv := by
          intro b
          simp }
    let e₂ :
        ((i : {x : Option β // x = none}) → Prop) × ((i : {x : Option β // x ≠ none}) → Prop) ≃ₜ
          Prop × (β → Prop) := by
      refine Homeomorph.prodCongr (Homeomorph.funUnique _ _) ?_
      simpa using (Homeomorph.piCongrLeft (Y := fun _ : β => Prop) eSome)
    let hHomeo : (Option β → Prop) ≃ₜ Prop × (β → Prop) := e₁.trans e₂
    letI : SpectralSpace Prop := spectralSpaceProp
    letI : SpectralSpace (β → Prop) := hβ
    letI : SpectralSpace (Prop × (β → Prop)) := inferInstance
    letI : CompactSpace (Option β → Prop) := hHomeo.symm.compactSpace
    exact hHomeo.isOpenEmbedding.spectralSpace

/-- Helper for Lemma 5.23.13: the finite-coordinate restriction system over `Finset ι`. -/
noncomputable def finiteRestrictionDiagram (ι : Type v) : (Finset ι)ᵒᵖ ⥤ TopCat where
  obj s := TopCat.of (s.unop → Prop)
  map {s t} h := TopCat.ofHom
    { toFun := fun f x => f ⟨x, (show t.unop ≤ s.unop from h.unop.down.down) x.2⟩
      continuous_toFun := continuous_pi fun x => continuous_apply _ }
  map_id s := by
    ext f x
    rfl
  map_comp {a b c} f g := by
    ext u x
    rfl

/-- Helper for Lemma 5.23.13: compatible finite-coordinate families are exactly full Sierpinski
functions. -/
noncomputable def compatibleFamilyHomeomorph (ι : Type v) :
    ↥(TopCat.limitCone (finiteRestrictionDiagram ι)).pt ≃ₜ (ι → Prop) where
  toFun u i := u.1 (Opposite.op ({i} : Finset ι)) ⟨i, by simp⟩
  invFun g := ⟨fun s x => g x.1, by intro i j f; funext x; rfl⟩
  left_inv := by
    intro u
    -- Read the value on a finite stage from its singleton restriction using compatibility.
    apply Subtype.ext
    funext s
    funext x
    let h : s ⟶ Opposite.op ({x.1} : Finset ι) := by
      exact Quiver.Hom.op ⟨PLift.up <| by simpa using x.2⟩
    have hcompat := congrFun (u.2 h) ⟨x.1, by simp⟩
    simpa [finiteRestrictionDiagram, h] using hcompat.symm
  right_inv := by
    intro g
    funext i
    rfl
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    have hstage :
        Continuous fun u : ↥(TopCat.limitCone (finiteRestrictionDiagram ι)).pt =>
          u.1 (Opposite.op ({i} : Finset ι)) :=
      (continuous_apply (Opposite.op ({i} : Finset ι))).comp continuous_subtype_val
    exact (continuous_apply (⟨i, by simp⟩ : ({x // x ∈ ({i} : Finset ι)}))).comp hstage
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_pi fun s => continuous_pi fun x => continuous_apply x.1)
      (fun g i j f => by funext x; rfl)

/-- Helper for Lemma 5.23.13: arbitrary products of the Sierpinski space are spectral. -/
private theorem spectralSpaceSierpinskiProduct {ι : Type v} : SpectralSpace (ι → Prop) := by
  classical
  let F := finiteRestrictionDiagram ι
  letI : ∀ i : (Finset ι)ᵒᵖ, SpectralSpace (F.obj i) := by
    intro i
    change SpectralSpace (i.unop → Prop)
    exact spectralSpaceFiniteSierpinskiProduct
  letI : ∀ i : (Finset ι)ᵒᵖ, T0Space (F.obj i) := by
    intro i
    change T0Space (i.unop → Prop)
    infer_instance
  letI : ∀ i : (Finset ι)ᵒᵖ, Finite (F.obj i) := by
    intro i
    change Finite (i.unop → Prop)
    infer_instance
  have hLimit : SpectralSpace ↥(limit F) :=
    spectralSpace_of_limit_finite_sober_inverse_system (F := F)
  let eLimit : ↥(TopCat.limitCone F).pt ≃ₜ ↥(limit F) :=
    TopCat.homeoOfIso (IsLimit.conePointUniqueUpToIso (TopCat.limitConeIsLimit F) (limit.isLimit F))
  let e : ↥(limit F) ≃ₜ (ι → Prop) := eLimit.symm.trans (compatibleFamilyHomeomorph ι)
  letI : SpectralSpace ↥(limit F) := hLimit
  letI : CompactSpace (ι → Prop) := e.compactSpace
  exact e.symm.isOpenEmbedding.spectralSpace

/-- Helper for Lemma 5.23.13: the finite `true`-cylinder in a Sierpinski product. -/
private def trueCylinder {ι : Type v} (s : Finset ι) : Set (ι → Prop) :=
  {f | ∀ i ∈ s, f i}

/-- Helper for Lemma 5.23.13: finite `true`-cylinders are open in a Sierpinski product. -/
private theorem trueCylinder_isOpen {ι : Type v} (s : Finset ι) : IsOpen (trueCylinder s) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [trueCylinder]
  | cons i s hs ih =>
      have hiOpen : IsOpen ((fun f : ι → Prop => f i) ⁻¹' ({True} : Set Prop)) :=
        isOpen_singleton_true.preimage (continuous_apply i)
      simpa [trueCylinder, hs, Set.setOf_and] using hiOpen.inter ih

/-- Helper for Lemma 5.23.13: finite `true`-cylinders are compact. -/
private theorem trueCylinder_isCompact {ι : Type v} (s : Finset ι) : IsCompact (trueCylinder s) := by
  classical
  let e₁ : (ι → Prop) ≃ₜ ((i : {x // x ∈ s}) → Prop) × ((i : {x // x ∉ s}) → Prop) :=
    Homeomorph.piEquivPiSubtypeProd (fun i : ι => i ∈ s) (fun _ => Prop)
  let A : Set ((i : {x // x ∈ s}) → Prop) := {g | ∀ x, g x}
  have hACompact : IsCompact A := (Set.toFinite _).isCompact
  have himage : e₁ '' trueCylinder s = A ×ˢ (Set.univ : Set ((i : {x // x ∉ s}) → Prop)) := by
    ext p
    constructor
    · rintro ⟨f, hf, rfl⟩
      constructor
      · intro x
        exact hf x.1 x.2
      · simp
    · rintro ⟨hpA, hpU⟩
      refine ⟨e₁.symm p, ?_, by simp⟩
      intro i hi
      have hcoord : (e₁.symm p) i = p.1 ⟨i, hi⟩ := by
        simpa [e₁, hi]
      rw [hcoord]
      exact hpA ⟨i, hi⟩
  rw [e₁.isEmbedding.isCompact_iff]
  simpa [himage] using hACompact.prod isCompact_univ

/-- Helper for Lemma 5.23.13: finite `true`-cylinders form a basis of a Sierpinski product. -/
private theorem trueCylinder_isTopologicalBasis {ι : Type v} :
    IsTopologicalBasis (Set.range (trueCylinder : Finset ι → Set (ι → Prop))) := by
  classical
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro s hs
    rcases hs with ⟨t, rfl⟩
    exact trueCylinder_isOpen t
  · intro x u hx hu
    -- Convert a general product-basis neighborhood to the equivalent finite `true`-cylinder.
    obtain ⟨v, hv, hxv, hvu⟩ :=
      (isTopologicalBasis_pi (fun _ : ι => isTopologicalBasis_opens)).exists_subset_of_mem_open hx hu
    rcases hv with ⟨U, F, hUopen, rfl⟩
    let t : Finset ι := F.filter fun i => U i = ({True} : Set Prop)
    refine ⟨trueCylinder t, ⟨t, rfl⟩, ?_, ?_⟩
    · intro i hi
      have hit : i ∈ F := (Finset.mem_filter.1 hi).1
      have hEq : U i = ({True} : Set Prop) := (Finset.mem_filter.1 hi).2
      have hxi : x i ∈ U i := by
        have : ∀ i ∈ F, x i ∈ U i := by
          simpa [Set.pi_def] using hxv
        exact this i hit
      simpa [hEq] using hxi
    · intro y hy
      apply hvu
      have hy' : ∀ i ∈ F, y i ∈ U i := by
        intro i hi
        by_cases hEq : U i = ({True} : Set Prop)
        · have hit : i ∈ t := by
            simpa [t, hEq] using hi
          have hyi : y i := hy i hit
          simpa [hEq] using hyi
        · have hFalse : False ∈ U i := by
            by_contra hFalse
            have hxi : x i ∈ U i := by
              have : ∀ i ∈ F, x i ∈ U i := by
                simpa [Set.pi_def] using hxv
              exact this i hi
            have hTrue : True ∈ U i := by
              by_cases hxiTrue : x i
              · simpa [hxiTrue] using hxi
              · exact (hFalse <| by simpa [hxiTrue] using hxi).elim
            have : U i = ({True} : Set Prop) :=
              open_subset_prop_eq_singleton_true (hUopen i hi) hTrue hFalse
            exact hEq this
          have hUniv : U i = Set.univ := open_subset_prop_eq_univ (hUopen i hi) hFalse
          simpa [hUniv]
      simpa [Set.pi_def] using hy'

/-- Helper for Lemma 5.23.13: the compact-open characteristic map into a Sierpinski product. -/
private def compactOpenSierpinskiMap (X : Type u) [TopologicalSpace X] :
    C(X, CompactOpens X → Prop) where
  toFun x U := x ∈ (U : Set X)
  continuous_toFun := by
    rw [continuous_pi_iff]
    intro U
    exact continuous_Prop.2 U.isOpen

/-- Helper for Lemma 5.23.13: compact opens already recover the topology through Sierpinski
coordinates. -/
private theorem compactOpenSierpinskiMap_isInducing (X : Type u) [TopologicalSpace X]
    [PrespectralSpace X] : IsInducing (compactOpenSierpinskiMap X) := by
  refine .mk ?_
  apply le_antisymm
  · exact continuous_iff_le_induced.1 (compactOpenSierpinskiMap X).continuous
  · let B : Set (Set X) := {U : Set X | IsOpen U ∧ IsCompact U}
    have hOpen :
        ∀ s ∈ B,
          IsOpen[TopologicalSpace.induced (compactOpenSierpinskiMap X) inferInstance] s := by
      intro s hs
      rcases hs with ⟨hsOpen, hsCompact⟩
      let U : CompactOpens X := ⟨⟨s, hsCompact⟩, hsOpen⟩
      have hTargetOpen :
          IsOpen[Pi.topologicalSpace]
            ((fun g : CompactOpens X → Prop => g U) ⁻¹' ({True} : Set Prop)) :=
        isOpen_singleton_true.preimage (continuous_apply U)
      have hPreOpen :
          IsOpen[TopologicalSpace.induced (compactOpenSierpinskiMap X) inferInstance]
            ((fun x : X => compactOpenSierpinskiMap X x) ⁻¹'
              ((fun g : CompactOpens X → Prop => g U) ⁻¹' ({True} : Set Prop))) := by
        rw [isOpen_induced_iff]
        exact ⟨_, hTargetOpen, rfl⟩
      simpa [compactOpenSierpinskiMap] using hPreOpen
    have hgen :
        TopologicalSpace.induced (compactOpenSierpinskiMap X) inferInstance ≤
          TopologicalSpace.generateFrom B :=
      le_generateFrom hOpen
    exact hgen.trans (PrespectralSpace.isTopologicalBasis (X := X)).eq_generateFrom.ge

/-- Helper for Lemma 5.23.13: the compact-open characteristic map is injective on a spectral
space. -/
private theorem compactOpenSierpinskiMap_injective (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] : Function.Injective (compactOpenSierpinskiMap X) := by
  intro x y hxy
  apply Inseparable.eq
  rw [← IsInducing.inseparable_iff (compactOpenSierpinskiMap_isInducing X), hxy]

/-- Helper for Lemma 5.23.13: the compact-open characteristic map is an embedding. -/
private theorem compactOpenSierpinskiMap_isEmbedding (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] : IsEmbedding (compactOpenSierpinskiMap X) :=
  .mk (compactOpenSierpinskiMap_isInducing X) (compactOpenSierpinskiMap_injective X)

/-- Helper for Lemma 5.23.13: finite intersections of compact opens are open. -/
private theorem compactOpen_inter_isOpen {X : Type u} [TopologicalSpace X]
    (s : Finset (CompactOpens X)) : IsOpen (⋂ U ∈ s, (U : Set X)) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons U s hU ih =>
      simpa [hU] using U.isOpen.inter ih

/-- Helper for Lemma 5.23.13: finite intersections of compact opens remain compact in a
quasi-separated space. -/
private theorem compactOpen_inter_isCompact {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [QuasiSeparatedSpace X] (s : Finset (CompactOpens X)) :
    IsCompact (⋂ U ∈ s, (U : Set X)) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using (isCompact_univ : IsCompact (Set.univ : Set X))
  | cons U s hU ih =>
      have hsOpen : IsOpen (⋂ V ∈ s, (V : Set X)) := compactOpen_inter_isOpen s
      simpa [hU] using U.isCompact.inter_of_isOpen ih U.isOpen hsOpen

/-- Helper for Lemma 5.23.13: the preimage of a finite `true`-cylinder is the corresponding finite
intersection of compact opens. -/
private theorem preimage_compactOpenSierpinskiMap_trueCylinder {X : Type u} [TopologicalSpace X]
    (s : Finset (CompactOpens X)) :
    (compactOpenSierpinskiMap X) ⁻¹' trueCylinder s = ⋂ U ∈ s, (U : Set X) := by
  ext x
  simp [compactOpenSierpinskiMap, trueCylinder]

/-- Helper for Lemma 5.23.13: the compact-open characteristic map is spectral. -/
private theorem compactOpenSierpinskiMap_isSpectralMap (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] : IsSpectralMap (compactOpenSierpinskiMap X) := by
  classical
  let f := compactOpenSierpinskiMap X
  refine ⟨f.continuous, ?_⟩
  intro s hsOpen hsCompact
  let b : Set (Finset (CompactOpens X)) := {t | trueCylinder t ⊆ s}
  -- Cover the compact open target set by basis cylinders that already lie inside it.
  have hcover : s ⊆ ⋃ t ∈ b, trueCylinder t := by
    intro y hy
    obtain ⟨v, ⟨t, rfl⟩, hyv, hvs⟩ :=
      (trueCylinder_isTopologicalBasis (ι := CompactOpens X)).isOpen_iff.mp hsOpen y hy
    exact mem_iUnion.2 ⟨t, mem_iUnion.2 ⟨hvs, hyv⟩⟩
  obtain ⟨b', hb'b, hb'finite, hs_sub⟩ :=
    hsCompact.elim_finite_subcover_image (b := b) (c := trueCylinder)
      (fun t ht => trueCylinder_isOpen t) hcover
  have hsub' : ⋃ t ∈ b', trueCylinder t ⊆ s := by
    intro y hy
    rcases mem_iUnion.1 hy with ⟨t, hy⟩
    rcases mem_iUnion.1 hy with ⟨ht, hyt⟩
    exact hb'b ht hyt
  have hEq : s = ⋃ t ∈ b', trueCylinder t := subset_antisymm hs_sub hsub'
  have hpreEq : f ⁻¹' s = ⋃ t ∈ b', f ⁻¹' trueCylinder t := by
    ext x
    simp [hEq]
  rw [hpreEq]
  exact hb'finite.isCompact_biUnion fun t ht => by
    rw [preimage_compactOpenSierpinskiMap_trueCylinder]
    exact compactOpen_inter_isCompact t

-- Proof sketch: for the forward implication, use the compact-open characteristic map
-- `X → CompactOpens X → Prop`; it is an embedding because compact opens form a basis, and it is
-- spectral because compact opens in the codomain are finite unions of finite coordinate cylinders.
-- For the reverse implication, show that every Sierpinski product is spectral by comparing it with
-- the inverse limit of its finite-coordinate restriction system, then transfer spectrality back
-- from the constructibly closed range via the embedding homeomorphism.
/-- Lemma 5.23.13: a space is spectral if and only if it embeds into a product of copies of the
Sierpinski space `Prop` with range closed in the constructible topology on that product. -/
theorem spectralSpace_iff_exists_sierpinski_product_embedding_closed_in_constructible_topology :
    SpectralSpace X ↔
      ∃ (ι : Type u) (f : C(X, ι → Prop)),
        IsEmbedding f ∧
          IsClosed[constructibleTopology (ι → Prop)] (range f) := by
  constructor
  · intro hX
    letI : SpectralSpace X := hX
    letI : SpectralSpace (CompactOpens X → Prop) := spectralSpaceSierpinskiProduct
    -- The source proof uses quasi-compact opens as coordinates, which is exactly `CompactOpens X`.
    refine
      ⟨CompactOpens X, compactOpenSierpinskiMap X, compactOpenSierpinskiMap_isEmbedding X, ?_⟩
    exact (compactOpenSierpinskiMap_isSpectralMap X).isClosed_range_constructibleTopology
  · rintro ⟨ι, f, hf, hclosed⟩
    letI : SpectralSpace (ι → Prop) := spectralSpaceSierpinskiProduct
    have hRangeSpectral : SpectralSpace (range f) :=
      spectralSpace_subtype_of_isClosed_constructibleTopology hclosed
    have hpre : (f ⁻¹' range f : Set X) = Set.univ := by
      ext x
      simp
    let ePre : (f ⁻¹' range f) ≃ₜ range f :=
      hf.homeomorphOfSubsetRange (s := range f) (by intro y hy; exact hy)
    let eRange : (Set.univ : Set X) ≃ₜ range f := by
      -- The embedding identifies `X` with its range because the preimage of the range is `univ`.
      exact (Homeomorph.setCongr hpre.symm).trans ePre
    let e : X ≃ₜ range f := (Homeomorph.Set.univ X).symm.trans eRange
    letI : SpectralSpace (range f) := hRangeSpectral
    letI : CompactSpace X := e.symm.compactSpace
    exact e.isOpenEmbedding.spectralSpace

end

/-! ### Lemma_5_23_14 (from Chap05) -/
open CategoryTheory Limits Opposite Set TopologicalSpace Topology

universe u

noncomputable section

section

variable (X : Type u) [TopologicalSpace X]

/-- Helper for Lemma 5.23.14: arbitrary Sierpinski products are spectral. -/
private theorem spectralSpace_sierpinskiProduct (ι : Type u) : SpectralSpace (ι → Prop) := by
  -- Reuse Lemma `5.23.13` with the identity embedding of the product into itself.
  refine
    (spectralSpace_iff_exists_sierpinski_product_embedding_closed_in_constructible_topology
      (X := ι → Prop)).2 ?_
  refine ⟨ι, ContinuousMap.id (ι → Prop), ?_, ?_⟩
  · simpa using (show Topology.IsEmbedding (fun x : ι → Prop => x) from Topology.IsEmbedding.id)
  · simp

/-- Helper for Lemma 5.23.14: the single-coordinate `true` cylinder is compact. -/
private theorem coordinate_true_isCompact {ι : Type u} [DecidableEq ι] (i : ι) :
    IsCompact ({x : ι → Prop | x i = True} : Set (ι → Prop)) := by
  -- Split off the chosen coordinate and identify the cylinder with `{True} × univ`.
  let e₁ : (ι → Prop) ≃ₜ ((j : {x : ι // x = i}) → Prop) × ((j : {x : ι // x ≠ i}) → Prop) :=
    Homeomorph.piEquivPiSubtypeProd (fun j : ι => j = i) (fun _ => Prop)
  let e₂ :
      ((j : {x : ι // x = i}) → Prop) × ((j : {x : ι // x ≠ i}) → Prop) ≃ₜ
        Prop × ((j : {x : ι // x ≠ i}) → Prop) :=
    Homeomorph.prodCongr (Homeomorph.funUnique {x : ι // x = i} Prop) (Homeomorph.refl _)
  let e : (ι → Prop) ≃ₜ Prop × ((j : {x : ι // x ≠ i}) → Prop) := e₁.trans e₂
  have himage :
      e '' ({x : ι → Prop | x i = True} : Set (ι → Prop)) =
        ({True} : Set Prop) ×ˢ (Set.univ : Set ((j : {x : ι // x ≠ i}) → Prop)) := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor
      · simpa [e, e₁, e₂] using hx
      · simp
    · rintro ⟨hp, -⟩
      refine ⟨e.symm p, ?_, by simp [e]⟩
      simpa [e, e₁, e₂] using hp
  rw [e.isEmbedding.isCompact_iff]
  simpa [himage] using (isCompact_singleton.prod isCompact_univ)

/-- Helper for Lemma 5.23.14: the single-coordinate `true` cylinder is constructible. -/
private theorem coordinate_true_isConstructible {ι : Type u} [DecidableEq ι]
    [SpectralSpace (ι → Prop)] (i : ι) :
    IsConstructible ({x : ι → Prop | x i = True} : Set (ι → Prop)) := by
  -- Compact-open cylinders are constructible in a spectral space.
  have hOpen : IsOpen ({x : ι → Prop | x i = True} : Set (ι → Prop)) := by
    have hpre :
        IsOpen (((fun x : ι → Prop => x i) : (ι → Prop) → Prop) ⁻¹' ({True} : Set Prop)) :=
      isOpen_singleton_true.preimage (continuous_apply i)
    simpa using hpre
  exact (coordinate_true_isCompact (i := i)).isConstructible hOpen

/-- Helper for Lemma 5.23.14: fixing one coordinate is patch-closed in a Sierpinski product. -/
private theorem coordinate_value_isClosed_patch {ι : Type u} [DecidableEq ι]
    [SpectralSpace (ι → Prop)] (i : ι) (b : Prop) :
    IsClosed[constructibleTopology (ι → Prop)] ({x : ι → Prop | x i = b} : Set (ι → Prop)) := by
  by_cases hb : b
  · have hb' : b = True := propext (iff_true_intro hb)
    simpa [hb'] using
      (isClopen_constructibleTopology_of_isConstructible
        (coordinate_true_isConstructible (i := i))).1
  · have hclosed :
        IsClosed[constructibleTopology (ι → Prop)] ({x : ι → Prop | x i = False} : Set
          (ι → Prop)) := by
      have hopenTrue :
          IsOpen[constructibleTopology (ι → Prop)] ({x : ι → Prop | x i = True} : Set
            (ι → Prop)) :=
        (isClopen_constructibleTopology_of_isConstructible
          (coordinate_true_isConstructible (i := i))).2
      have hclosedCompl :
          IsClosed[constructibleTopology (ι → Prop)]
            (({x : ι → Prop | x i = True} : Set (ι → Prop))ᶜ) := by
        let _ : TopologicalSpace (ι → Prop) := constructibleTopology (ι → Prop)
        exact hopenTrue.isClosed_compl
      convert hclosedCompl using 1
      ext x
      simp
    have hb' : b = False := propext (iff_false_intro hb)
    simpa [hb'] using hclosed

/-- Helper for Lemma 5.23.14: a finite coordinate pattern is patch-closed in a Sierpinski
product. -/
private theorem finite_coordinate_match_isClosed_patch {ι : Type u} [DecidableEq ι]
    [SpectralSpace (ι → Prop)]
    (s : Finset ι) (a : s → Prop) :
    IsClosed[constructibleTopology (ι → Prop)] ({x : ι → Prop | ∀ i : s, x i.1 = a i} : Set
      (ι → Prop)) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      simpa using (isClosed_univ : IsClosed[constructibleTopology (ι → Prop)] (Set.univ : Set
        (ι → Prop)))
  | cons i s hi hs =>
      -- Separate the new coordinate from the previously fixed finite pattern.
      let aTail : s → Prop := fun j => a ⟨j.1, by simp [j.2]⟩
      have hEq :
          ({x : ι → Prop | ∀ j : Finset.cons i s hi, x j.1 = a j} : Set (ι → Prop)) =
            ({x : ι → Prop | x i = a ⟨i, by simp⟩} ∩
              {x : ι → Prop | ∀ j : s, x j.1 = aTail j}) := by
        ext x
        constructor
        · intro hx
          constructor
          · exact hx ⟨i, by simp⟩
          · intro j
            exact hx ⟨j.1, by simp [j.2]⟩
        · rintro ⟨hHead, hTail⟩ j
          by_cases hj : j.1 = i
          · have hji : j = ⟨i, by simp⟩ := Subtype.ext hj
            simpa [hji] using hHead
          · exact hTail ⟨j.1, by simpa [Finset.mem_cons, hj] using j.2⟩
      rw [hEq]
      have hHeadClosed :
          IsClosed[constructibleTopology (ι → Prop)] ({x : ι → Prop | x i = a ⟨i, by simp⟩} :
            Set (ι → Prop)) :=
        coordinate_value_isClosed_patch (i := i) (b := a ⟨i, by simp⟩)
      have hTailClosed :
          IsClosed[constructibleTopology (ι → Prop)] ({x : ι → Prop | ∀ j : s, x j.1 = aTail j} :
            Set (ι → Prop)) :=
        hs aTail
      let _ : TopologicalSpace (ι → Prop) := constructibleTopology (ι → Prop)
      exact hHeadClosed.inter hTailClosed

/-- Helper for Lemma 5.23.14: every finite `T₀` space is quasi-sober. -/
private theorem quasiSober_of_finite_t0 (Y : Type u) [TopologicalSpace Y] [Finite Y] [T0Space Y] :
    QuasiSober Y := by
  -- Pass to the irreducible closed subset as a finite `T₀` subspace and choose a point whose
  -- singleton is open there; irreducibility then forces that singleton to be dense.
  refine (quasiSober_iff Y).2 ?_
  intro S hS hSclosed
  rcases hS.1 with ⟨x0, hx0⟩
  letI : Nonempty S := ⟨⟨x0, hx0⟩⟩
  letI : Finite S := inferInstance
  letI : T0Space S := inferInstance
  letI : PreirreducibleSpace S := Subtype.preirreducibleSpace hS.isPreirreducible
  obtain ⟨x, hxOpen⟩ := exists_open_singleton_of_finite (X := S)
  have hDense : Dense ({x} : Set S) := hxOpen.dense (Set.singleton_nonempty x)
  have hClosureSubtype : closure ({x} : Set S) = Set.univ := by
    simpa [dense_iff_closure_eq] using hDense
  have hsubset : S ⊆ closure ({x.1} : Set Y) := by
    intro y hy
    have hySub : (⟨y, hy⟩ : S) ∈ closure ({x} : Set S) := by
      simp [hClosureSubtype]
    simpa using (closure_subtype (x := ⟨y, hy⟩) (s := ({x} : Set S))).1 hySub
  have hsuperset : closure ({x.1} : Set Y) ⊆ S :=
    hSclosed.closure_subset_iff.mpr (by
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact x.2)
  refine ⟨x.1, ?_⟩
  -- The ambient closure of the chosen point is exactly the original irreducible closed subset.
  rw [isGenericPoint_def]
  exact subset_antisymm hsuperset hsubset

-- Proof sketch: for the forward implication, use Lemma `5.23.13` to identify `X` with a
-- constructibly closed subset of a Sierpinski product, then replace that closed subset by the
-- inverse system of its finite-coordinate images. For the reverse implication, convert the given
-- `Jᵒᵈ`-diagram to a `Jᵒᵖ`-diagram via `orderDualEquivalence`, apply Lemma `5.23.12`, and
-- transport spectrality back across the resulting homeomorphisms.
/-- Lemma 5.23.14: a topological space is spectral if and only if it is homeomorphic to the limit
of a directed inverse system of finite sober topological spaces. -/
theorem spectralSpace_iff_homeomorphic_directed_limit_finite_sober :
    SpectralSpace X ↔
      ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirectedOrder J)
        (F : Jᵒᵈ ⥤ TopCat.{u}) (_ : ∀ j : Jᵒᵈ, Finite (F.obj j))
        (_ : ∀ j : Jᵒᵈ, T0Space (F.obj j)),
        Nonempty (X ≃ₜ ↥(limit F)) := by
  constructor
  · intro hX
    classical
    letI : SpectralSpace X := hX
    rcases
      (spectralSpace_iff_exists_sierpinski_product_embedding_closed_in_constructible_topology
        (X := X)).1 hX with
      ⟨ι, f, hf, hclosed⟩
    letI : SpectralSpace (ι → Prop) := spectralSpace_sierpinskiProduct ι
    let E : Set (ι → Prop) := Set.range f
    have hpre : (f ⁻¹' E : Set X) = Set.univ := by
      ext x
      simp [E]
    let ePre : (f ⁻¹' E) ≃ₜ E :=
      hf.homeomorphOfSubsetRange (s := E) (by intro y hy; exact hy)
    let eRange : (Set.univ : Set X) ≃ₜ E := by
      -- The embedding identifies `X` with its range in the Sierpinski product.
      exact (Homeomorph.setCongr hpre.symm).trans ePre
    let eX : X ≃ₜ E := (Homeomorph.Set.univ X).symm.trans eRange
    letI : SpectralSpace E := spectralSpace_subtype_of_isClosed_constructibleTopology hclosed
    let G : (Finset ι)ᵒᵖ ⥤ TopCat.{u} := by
      refine
        { obj := fun s =>
            TopCat.of (Set.range (fun x : E => fun i : s.unop => x.1 i.1))
          map := fun {s t} h =>
            TopCat.ofHom
              { toFun := fun a => by
                  refine ⟨fun i => a.1 ⟨i.1, (show t.unop ≤ s.unop from h.unop.down.down) i.2⟩, ?_⟩
                  rcases a.2 with ⟨x, hx⟩
                  refine ⟨x, ?_⟩
                  ext i
                  simpa [hx] using
                    congrFun hx ⟨i.1, (show t.unop ≤ s.unop from h.unop.down.down) i.2⟩
                continuous_toFun := by
                  refine Continuous.subtype_mk ?_ ?_
                  exact
                    continuous_pi fun i =>
                      (continuous_apply
                          (⟨i.1, (show t.unop ≤ s.unop from h.unop.down.down) i.2⟩ : s.unop)).comp
                        continuous_subtype_val }
          map_id := by
            intro s
            ext a i
            rfl
          map_comp := by
            intro a b c g h
            ext u i
            rfl }
    let forgetLimitCone :
        (TopCat.limitCone G).pt → (TopCat.limitCone (finiteRestrictionDiagram ι)).pt :=
      fun u => by
        refine ⟨(fun s => (u.1 s).1), ?_⟩
        intro s t h
        simpa [G] using congrArg Subtype.val (u.2 h)
    have hforgetLimitCone :
        Continuous forgetLimitCone := by
      -- Forget only the range witnesses; the underlying stage tuples vary continuously.
      refine Continuous.subtype_mk ?_ ?_
      exact
        continuous_pi fun s =>
          continuous_subtype_val.comp ((continuous_apply s).comp continuous_subtype_val)
    have realize_limitCone_point :
        ∀ u : (TopCat.limitCone G).pt, compatibleFamilyHomeomorph ι (forgetLimitCone u) ∈ E := by
      intro u
      let v : (TopCat.limitCone (finiteRestrictionDiagram ι)).pt := forgetLimitCone u
      let M : Finset ι → Set (ι → Prop) :=
        fun s ↦ E ∩ {x : ι → Prop | ∀ i : s, x i.1 = (v.1 (Opposite.op s)) i}
      have hM_closed_patch :
          ∀ s : Finset ι, IsClosed[constructibleTopology (ι → Prop)] (M s) := by
        intro s
        have hMatchClosed :
            IsClosed[constructibleTopology (ι → Prop)]
              ({x : ι → Prop | ∀ i : s, x i.1 = (v.1 (Opposite.op s)) i} : Set (ι → Prop)) :=
          finite_coordinate_match_isClosed_patch s (v.1 (Opposite.op s))
        let _ : TopologicalSpace (ι → Prop) := constructibleTopology (ι → Prop)
        exact hclosed.inter hMatchClosed
      have hM_nonempty : ∀ s : Finset ι, (M s).Nonempty := by
        intro s
        rcases (u.1 (Opposite.op s)).2 with ⟨x, hx⟩
        refine ⟨x.1, x.2, ?_⟩
        intro i
        simpa [v, forgetLimitCone] using congrFun hx i
      have hM_directed : Directed (· ⊇ ·) M := by
        intro s t
        refine ⟨s ∪ t, ?_, ?_⟩
        · intro x hx
          constructor
          · exact hx.1
          · intro i
            let hst : Opposite.op (s ∪ t) ⟶ Opposite.op s := by
              exact Quiver.Hom.op ⟨PLift.up <| Finset.subset_union_left⟩
            have hcompat := congrArg Subtype.val (u.2 hst)
            have hi :
                (v.1 (Opposite.op (s ∪ t))) ⟨i.1, by
                  exact Finset.mem_union.mpr (Or.inl i.2)⟩ =
                  (v.1 (Opposite.op s)) i := by
              simpa [v, forgetLimitCone, G, hst] using congrFun hcompat i
            exact (hx.2 ⟨i.1, by exact Finset.mem_union.mpr (Or.inl i.2)⟩).trans hi
        · intro x hx
          constructor
          · exact hx.1
          · intro i
            let hst : Opposite.op (s ∪ t) ⟶ Opposite.op t := by
              exact Quiver.Hom.op ⟨PLift.up <| Finset.subset_union_right⟩
            have hcompat := congrArg Subtype.val (u.2 hst)
            have hi :
                (v.1 (Opposite.op (s ∪ t))) ⟨i.1, by
                  exact Finset.mem_union.mpr (Or.inr i.2)⟩ =
                  (v.1 (Opposite.op t)) i := by
              simpa [v, forgetLimitCone, G, hst] using congrFun hcompat i
            exact (hx.2 ⟨i.1, by exact Finset.mem_union.mpr (Or.inr i.2)⟩).trans hi
      have hM_compact_patch :
          ∀ s : Finset ι, @IsCompact (ι → Prop) (constructibleTopology (ι → Prop)) (M s) := by
        have hPatchCompact :
            @CompactSpace (ι → Prop) (constructibleTopology (ι → Prop)) :=
          (constructibleTopology_compactSpace_of_spectralSpace :
            @CompactSpace (ι → Prop) (constructibleTopology (ι → Prop)))
        intro s
        letI : TopologicalSpace (ι → Prop) := constructibleTopology (ι → Prop)
        letI : CompactSpace (ι → Prop) := hPatchCompact
        exact (hM_closed_patch s).isCompact
      obtain ⟨x, hx⟩ :=
        Set.nonempty_iInter.mp <|
          @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
            (ι → Prop) (constructibleTopology (ι → Prop)) (Finset ι) inferInstance M
            hM_directed hM_nonempty hM_compact_patch hM_closed_patch
      have hxEq :
          x = compatibleFamilyHomeomorph ι v := by
        funext i
        exact (hx ({i} : Finset ι)).2 ⟨i, by simp⟩
      have hxE : x ∈ E := (hx ∅).1
      simpa [v] using hxEq ▸ hxE
    let forwardLimitCone : E → (TopCat.limitCone G).pt :=
      fun x =>
        ⟨fun s => ⟨fun i => x.1 i.1, ⟨x, rfl⟩⟩, by
          intro s t h
          apply Subtype.ext
          funext i
          rfl⟩
    have hforwardLimitCone : Continuous forwardLimitCone := by
      -- Each stage is given by finite coordinate restriction of the ambient Sierpinski point.
      refine Continuous.subtype_mk ?_ ?_
      exact
        continuous_pi fun s =>
          Continuous.subtype_mk
            (continuous_pi fun i => (continuous_apply i.1).comp continuous_subtype_val)
            (fun x => ⟨x, rfl⟩)
    let reverseLimitCone : (TopCat.limitCone G).pt → E :=
      fun u => ⟨compatibleFamilyHomeomorph ι (forgetLimitCone u), realize_limitCone_point u⟩
    have hreverseLimitCone : Continuous reverseLimitCone := by
      -- Recover the global Sierpinski point from the singleton coordinates of the compatible
      -- family, then use the realization lemma to place it back in `E`.
      refine Continuous.subtype_mk ?_ ?_
      exact (compatibleFamilyHomeomorph ι).continuous_toFun.comp hforgetLimitCone
    have hforward_reverse :
        Function.LeftInverse reverseLimitCone forwardLimitCone := by
      intro x
      apply Subtype.ext
      have hforgetX :
          forgetLimitCone (forwardLimitCone x) = (compatibleFamilyHomeomorph ι).symm x.1 := by
        apply Subtype.ext
        funext s
        rfl
      simpa [reverseLimitCone, hforgetX] using (compatibleFamilyHomeomorph ι).right_inv x.1
    have hreverse_forward :
        Function.RightInverse reverseLimitCone forwardLimitCone := by
      intro u
      apply Subtype.ext
      funext s
      apply Subtype.ext
      funext i
      have hcompat :
          (compatibleFamilyHomeomorph ι).symm
              ((compatibleFamilyHomeomorph ι) (forgetLimitCone u)) =
            forgetLimitCone u :=
        (compatibleFamilyHomeomorph ι).left_inv (forgetLimitCone u)
      exact congrArg (fun v => v.1 s i) hcompat
    let eLimitCone : E ≃ₜ (TopCat.limitCone G).pt :=
      { toFun := forwardLimitCone
        invFun := reverseLimitCone
        left_inv := hforward_reverse
        right_inv := hreverse_forward
        continuous_toFun := hforwardLimitCone
        continuous_invFun := hreverseLimitCone }
    let eG : E ≃ₜ ↥(limit G) :=
      eLimitCone.trans
        (TopCat.homeoOfIso
          (IsLimit.conePointUniqueUpToIso (TopCat.limitConeIsLimit G) (limit.isLimit G)))
    let F : (Finset ι)ᵒᵈ ⥤ TopCat.{u} :=
      (CategoryTheory.orderDualEquivalence (Finset ι)).functor ⋙ G
    let eOrder : ↥(limit F) ≃ₜ ↥(limit G) :=
      (TopCat.homeoOfIso
        (HasLimit.isoOfEquivalence (CategoryTheory.orderDualEquivalence (Finset ι)).symm
          (Iso.refl G))).symm
    refine
      ⟨Finset ι, inferInstance, inferInstance, inferInstance, F, ?_, ?_,
        ⟨eX.trans (eG.trans eOrder.symm)⟩⟩
    · intro j
      simpa [F] using
        (inferInstance :
          Finite (G.obj ((CategoryTheory.orderDualEquivalence (Finset ι)).functor.obj j)))
    · intro j
      simpa [F] using
        (inferInstance :
          T0Space (G.obj ((CategoryTheory.orderDualEquivalence (Finset ι)).functor.obj j)))
  · rintro ⟨J, _, _, _, F, hFinite, hT0, ⟨e⟩⟩
    let G : Jᵒᵖ ⥤ TopCat.{u} := (CategoryTheory.orderDualEquivalence J).inverse ⋙ F
    letI : ∀ j : Jᵒᵖ, Finite (G.obj j) := by
      intro j
      simpa [G] using hFinite ((CategoryTheory.orderDualEquivalence J).inverse.obj j)
    letI : ∀ j : Jᵒᵖ, T0Space (G.obj j) := by
      intro j
      simpa [G] using hT0 ((CategoryTheory.orderDualEquivalence J).inverse.obj j)
    letI : ∀ j : Jᵒᵖ, QuasiSober (G.obj j) := by
      intro j
      exact quasiSober_of_finite_t0 (G.obj j)
    have hLimitG : SpectralSpace ↥(limit G) :=
      spectralSpace_of_limit_finite_sober_inverse_system (F := G)
    let eLimit :
        ↥(limit F) ≃ₜ ↥(limit G) :=
      (TopCat.homeoOfIso
        (HasLimit.isoOfEquivalence
          (CategoryTheory.orderDualEquivalence J).symm
          (Iso.refl G))).symm
    have hLimitF : SpectralSpace ↥(limit F) := by
      letI : SpectralSpace ↥(limit G) := hLimitG
      letI : CompactSpace ↥(limit F) := eLimit.symm.compactSpace
      exact eLimit.isOpenEmbedding.spectralSpace
    letI : SpectralSpace ↥(limit F) := hLimitF
    letI : CompactSpace X := e.symm.compactSpace
    exact e.isOpenEmbedding.spectralSpace

end

/-! ### Lemma_5_23_15 (from Chap05) -/
universe u

open TopologicalSpace Topology

/-
Domain-style sampling for soberification and spectral transfer:
- primary domain: soberification via `IrreducibleCloseds X`, viewed through the lattice of open
  subsets;
- sampled owner declarations:
  `toIrreducibleCloseds_opensComap_bijective`,
  `TopologicalSpace.Opens.comap`,
  `PrespectralSpace.isBasis_opens`,
  `QuasiSeparatedSpace.inter_isCompact`;
- best owner abstraction: the key owner here is the order isomorphism on opens induced by
  `toIrreducibleCloseds`; compactness, Noetherianity, prespectrality, quasi-separatedness, and
  spectrality of `IrreducibleCloseds X` are all derived API transported across that owner;
- primitive-vs-derived split: the primitive data for this file is only the open-lattice
  equivalence; the various topological typeclass instances are derived from it and should not be
  packaged as separate wrapper data.

Layer triage:
- `source-facing`: the Stacks claims that soberification preserves quasi-compactness, the compact
  open basis, quasi-separatedness, and Noetherianity;
- `core/canonical`: `Opens`, `CompactSpace`, `NoetherianSpace`, `PrespectralSpace`,
  `QuasiSeparatedSpace`, and `SpectralSpace`;
- `bridge/view`: `toIrreducibleCloseds` and the induced order isomorphism on opens.
-/

section

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Lemma 5.23.15: compactness of an open subset of the soberification follows from
compactness of its pullback along `toIrreducibleCloseds`. -/
lemma isCompact_of_isCompact_comap_toIrreducibleCloseds
    (V : Opens (IrreducibleCloseds X))
    (hV : IsCompact
      ((((Opens.comap (toIrreducibleCloseds : C(X, IrreducibleCloseds X))) V : Opens X) :
        Set X))) :
    IsCompact (V : Set (IrreducibleCloseds X)) := by
  -- Pull back an arbitrary open cover of `V` to the corresponding open of `X`.
  rw [isCompact_iff_finite_subcover]
  intro ι U hUo hcover
  let f : C(X, IrreducibleCloseds X) := toIrreducibleCloseds
  let Uo : ι → Opens (IrreducibleCloseds X) := fun i ↦ ⟨U i, hUo i⟩
  have hcover_comap :
      ((((Opens.comap f) V : Opens X) : Set X)) ⊆
        ⋃ i, ((((Opens.comap f) (Uo i) : Opens X) : Set X)) := by
    intro x hx
    have hxV : f x ∈ (V : Set (IrreducibleCloseds X)) := by
      simpa [Opens.mem_comap] using hx
    rcases Set.mem_iUnion.1 (hcover hxV) with ⟨i, hxi⟩
    exact Set.mem_iUnion.2 ⟨i, by simpa [Uo, Opens.mem_comap] using hxi⟩
  obtain ⟨t, ht⟩ :=
    hV.elim_finite_subcover
      (fun i ↦ ((((Opens.comap f) (Uo i) : Opens X) : Set X)))
      (fun i ↦ ((Opens.comap f) (Uo i)).isOpen)
      hcover_comap
  let W : Opens (IrreducibleCloseds X) := ⨆ i : {i // i ∈ t}, Uo i.1
  have hcomap_le' :
      (Opens.comap f) V ≤ ⨆ i : {i // i ∈ t}, (Opens.comap f) (Uo i.1) := by
    -- Reindex the finite subcover by the subtype associated to the chosen `Finset`.
    intro x hx
    rcases Set.mem_iUnion₂.1 (ht hx) with ⟨i, hi, hxi⟩
    exact Opens.mem_iSup.2 ⟨⟨i, hi⟩, hxi⟩
  have hcomapW :
      (Opens.comap f) W = ⨆ i : {i // i ∈ t}, (Opens.comap f) (Uo i.1) := by
    ext x
    simp [W]
  have hcomap_le : (Opens.comap f) V ≤ (Opens.comap f) W := by
    rw [hcomapW]
    exact hcomap_le'
  have hV_le_W : V ≤ W := by
    -- Injectivity of `Opens.comap` reflects the inclusion after packaging it as an inf-equality.
    have hinj := (toIrreducibleCloseds_opensComap_bijective (X := X)).1
    apply inf_eq_left.mp
    apply hinj
    calc
      (Opens.comap f) (V ⊓ W) = (Opens.comap f) V ⊓ (Opens.comap f) W := by simp
      _ = (Opens.comap f) V := inf_eq_left.mpr hcomap_le
  -- Push the finite source-side cover back to the original cover of `V`.
  refine ⟨t, ?_⟩
  intro Z hZ
  have hZW : Z ∈ W := hV_le_W hZ
  rcases Opens.mem_iSup.1 hZW with ⟨i, hZi⟩
  exact Set.mem_iUnion₂.2 ⟨i.1, i.2, hZi⟩

/-- Helper for Lemma 5.23.15: a compact open of `X` yields a compact basic open on the
soberification. -/
lemma basicOpen_isCompact (U : Opens X) (hU : IsCompact (U : Set X)) :
    IsCompact (IrreducibleCloseds.basicOpen U) := by
  -- Rewrite the pulled-back basic open as `U`, then invoke compactness transfer.
  let V : Opens (IrreducibleCloseds X) :=
    ⟨IrreducibleCloseds.basicOpen U, (isOpen_iff_exists_basicOpen).2 ⟨U, rfl⟩⟩
  have hpre :
      ((((Opens.comap (toIrreducibleCloseds : C(X, IrreducibleCloseds X))) V : Opens X) :
        Set X)) = U := by
    simpa [V, Opens.coe_comap] using preimage_basicOpen_toIrreducibleClosedsFun (X := X) U
  have hcomap : IsCompact ((((Opens.comap
      (toIrreducibleCloseds : C(X, IrreducibleCloseds X))) V : Opens X) : Set X)) := by
    rw [hpre]
    exact hU
  simpa [V] using isCompact_of_isCompact_comap_toIrreducibleCloseds (X := X) V hcomap

/-- Helper for Lemma 5.23.15: compact basic opens coming from `CompactOpens X` form a
topological basis on the soberification. -/
lemma isTopologicalBasis_compact_basicOpen [PrespectralSpace X] :
    IsTopologicalBasis
      (Set.range fun U : CompactOpens X ↦ IrreducibleCloseds.basicOpen U.toOpens) := by
  -- Transport the compact-open neighborhood basis from `X` through `basicOpen`.
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨U, rfl⟩
    exact (isOpen_iff_exists_basicOpen).2 ⟨U.toOpens, rfl⟩
  · intro Z s hZ hs
    obtain ⟨U, rfl⟩ := (isOpen_iff_exists_basicOpen).1 hs
    rcases hZ with ⟨x, hxZ, hxU⟩
    obtain ⟨K, hK, hxK, hKU⟩ :=
      (PrespectralSpace.isTopologicalBasis (X := X)).exists_subset_of_mem_open hxU U.isOpen
    let Kc : CompactOpens X := ⟨⟨K, hK.2⟩, hK.1⟩
    refine ⟨IrreducibleCloseds.basicOpen Kc.toOpens, ⟨Kc, rfl⟩, ?_, ?_⟩
    · exact ⟨x, hxZ, hxK⟩
    · exact IrreducibleCloseds.basicOpen_mono hKU

/-- Helper for Lemma 5.23.15: intersections of compact basic opens on the soberification are
compact once `X` is quasi-separated. -/
lemma compact_inter_compact_basicOpen [QuasiSeparatedSpace X] (U V : CompactOpens X) :
    IsCompact (IrreducibleCloseds.basicOpen U.toOpens ∩ IrreducibleCloseds.basicOpen V.toOpens) := by
  -- Identify the target intersection with the basic open of the source-side compact
  -- intersection.
  have hUV :
      IsCompact (((U.toOpens ⊓ V.toOpens : Opens X) : Set X)) := by
    exact
      QuasiSeparatedSpace.inter_isCompact (U : Set X) (V : Set X)
        U.toOpens.isOpen U.isCompact V.toOpens.isOpen V.isCompact
  simpa [IrreducibleCloseds.basicOpen_inf] using
    basicOpen_isCompact (X := X) (U := U.toOpens ⊓ V.toOpens) hUV

-- Proof sketch: the soberification map induces a bijection on opens. Since this bijection commutes
-- with arbitrary unions, quasi-compactness of the soberification space transfers across it, so
-- compactness of `X` gives compactness of `IrreducibleCloseds X`.
/-- Lemma 5.23.15 (1): if `X` is quasi-compact, then the soberification space
`IrreducibleCloseds X` is quasi-compact. In Lean this is the canonical `CompactSpace`
instance. -/
instance irreducibleCloseds_compactSpace [CompactSpace X] :
    CompactSpace (IrreducibleCloseds X) := by
  -- Apply compactness transfer to the universal open `⊤`.
  apply (isCompact_univ_iff).1
  have htop : IsCompact
      ((((Opens.comap (toIrreducibleCloseds : C(X, IrreducibleCloseds X))) ⊤ : Opens X) :
        Set X)) := by
    simpa using (CompactSpace.isCompact_univ : IsCompact (Set.univ : Set X))
  simpa using
    isCompact_of_isCompact_comap_toIrreducibleCloseds
      (X := X) (V := (⊤ : Opens (IrreducibleCloseds X))) htop

-- Proof sketch: the open-bijection property of the soberification map transfers compact opens and
-- their pairwise intersections from `X` to `IrreducibleCloseds X`. Together with the quasi-sober
-- and `T₀` structure from Lemma 5.8.16 and compactness from part (1), this yields a spectral
-- structure on `IrreducibleCloseds X`.
/-- Lemma 5.23.15 (2): if `X` is quasi-compact, has a basis of quasi-compact opens, and the
intersection of two quasi-compact opens is quasi-compact, then `IrreducibleCloseds X` is
spectral. The textbook hypotheses are expressed canonically by
`[CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]`. -/
instance irreducibleCloseds_spectralSpace [CompactSpace X] [PrespectralSpace X]
    [QuasiSeparatedSpace X] : SpectralSpace (IrreducibleCloseds X) := by
  -- Build the prespectral and quasi-separated structures from compact basic opens.
  let hPrespectral : PrespectralSpace (IrreducibleCloseds X) :=
    PrespectralSpace.of_isTopologicalBasis
      (isTopologicalBasis_compact_basicOpen (X := X))
      (by
        rintro _ ⟨U, rfl⟩
        exact basicOpen_isCompact (X := X) U.toOpens U.isCompact)
  let hQuasiSeparated : QuasiSeparatedSpace (IrreducibleCloseds X) :=
    QuasiSeparatedSpace.of_isTopologicalBasis
      (isTopologicalBasis_compact_basicOpen (X := X))
      (compact_inter_compact_basicOpen (X := X))
  -- The soberification already carries `T₀` and quasi-sober structures from Lemma 5.8.16.
  exact
    @SpectralSpace.mk (IrreducibleCloseds X) inferInstance inferInstance inferInstance inferInstance
      hQuasiSeparated hPrespectral

-- Proof sketch: the soberification map gives a bijection on opens, so the ascending chain
-- condition on open subsets transfers from `X` to `IrreducibleCloseds X`.
/-- The soberification space `IrreducibleCloseds X` of a Noetherian space is again Noetherian. -/
instance irreducibleCloseds_noetherianSpace [NoetherianSpace X] :
    NoetherianSpace (IrreducibleCloseds X) := by
  -- Noetherianity is equivalent to compactness of every open, which transfers across `c⁻¹`.
  rw [TopologicalSpace.noetherianSpace_iff_opens]
  intro V
  have hV : IsCompact
      ((((Opens.comap (toIrreducibleCloseds : C(X, IrreducibleCloseds X))) V : Opens X) :
        Set X)) := NoetherianSpace.isCompact _
  exact isCompact_of_isCompact_comap_toIrreducibleCloseds (X := X) V hV

-- Proof sketch: combine the transferred Noetherianity of `IrreducibleCloseds X` with the
-- quasi-sober and `T₀` properties from Lemma 5.8.16. Mathlib's Noetherian-space instances provide
-- compactness, a basis of compact opens, and quasi-separatedness, so `IrreducibleCloseds X` is
-- spectral as well.
/-- Lemma 5.23.15 (3): if `X` is Noetherian, then `IrreducibleCloseds X` is a Noetherian
spectral space. -/
theorem irreducibleCloseds_noetherian_and_spectral [NoetherianSpace X] :
    NoetherianSpace (IrreducibleCloseds X) ∧ SpectralSpace (IrreducibleCloseds X) := by
  exact ⟨inferInstance, inferInstance⟩

end
