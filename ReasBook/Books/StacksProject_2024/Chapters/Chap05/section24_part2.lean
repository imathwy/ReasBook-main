import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_24_5 (from Chap05) -/
open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

universe u v

noncomputable section

section

variable {I : Type u} [Category.{v} I] [IsCofiltered I]
variable {F : I ⥤ TopCat.{max u v}} [∀ i : I, SpectralSpace ↥(F.obj i)]
variable {C : Cone F}

/- Domain-style sampling for cofiltered limits of spectral spaces:
- primary domain: inverse limits in `TopCat` of spectral spaces with spectral transition maps;
- sampled owner declarations:
  `SpectralSpace`,
  `IsSpectralMap`,
  `TopCat.isTopologicalBasis_cofiltered_limit`,
  `compact_open_eq_preimage_of_isLimit`;
- best owner abstraction: the cone-level spectrality theorem for an arbitrary limiting cone, with
  the chosen categorical limit treated only as derived inference support;
- primitive data: a cofiltered diagram `F`, spectral structures on the stages, a limiting cone
  `C`, and spectrality of the transition maps;
- derived API: spectrality of the limiting cone point and spectrality of its projection maps.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that an inverse limit of spectral spaces with spectral
  transition maps is spectral, together with the projection-map corollary;
- `core/canonical`: `SpectralSpace` and `IsSpectralMap` on the limiting cone data;
- `bridge/view`: the chosen-limit specialization, which should remain only an instance and not a
  second named owner theorem.
-/

/-- Helper for Lemma 5.24.5: at stage `j`, keep only the points whose image in the fixed stage `i`
lies in the chosen compact open along every arrow `j ⟶ i`. -/
private def stagewise_pullback_family (i : I) (U : CompactOpens (F.obj i)) (j : I) :
    Set (F.obj j) :=
  ⋂ a : j ⟶ i, (F.map a) ⁻¹' (U : Set (F.obj i))

/-- Helper for Lemma 5.24.5: the stagewise pullback family is constructibly closed because each
member is the pullback of a compact open along a spectral map. -/
private theorem stagewise_pullback_family_closed
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a))
    (i : I) (U : CompactOpens (F.obj i)) (j : I) :
    IsClosed[constructibleTopology (F.obj j)] (stagewise_pullback_family (F := F) i U j) := by
  -- Compact opens are clopen for the constructible topology on a spectral space.
  have hU_closed : IsClosed[constructibleTopology (F.obj i)] (U : Set (F.obj i)) := by
    exact (isClopen_constructibleTopology_of_isConstructible
      (U.isCompact.isConstructible U.isOpen)).1
  -- Intersect the constructibly closed pullbacks over all arrows `j ⟶ i`.
  dsimp [stagewise_pullback_family]
  refine @isClosed_iInter (F.obj j) (j ⟶ i) (constructibleTopology (F.obj j))
    (fun a ↦ (F.map a) ⁻¹' (U : Set (F.obj i))) ?_
  intro a
  exact @IsClosed.preimage (F.obj j) (F.obj i)
    (constructibleTopology (F.obj j)) (constructibleTopology (F.obj i))
    (F.map a) (hF a).continuous_constructibleTopology _ hU_closed

/-- Helper for Lemma 5.24.5: the stagewise pullback family is stable under the transition maps. -/
private theorem stagewise_pullback_family_mapsTo
    (i : I) (U : CompactOpens (F.obj i)) {j k : I} (a : j ⟶ k) :
    Set.MapsTo (F.map a)
      (stagewise_pullback_family (F := F) i U j)
      (stagewise_pullback_family (F := F) i U k) := by
  -- A point satisfying all arrows out of `j` still satisfies all arrows out of `k` after
  -- precomposing with `a`.
  intro x hx
  refine mem_iInter.2 fun b ↦ ?_
  have hx' :
      x ∈ (F.map (a ≫ b)) ⁻¹' (U : Set (F.obj i)) := by
    exact mem_iInter.1 hx (a ≫ b)
  change F.map b (F.map a x) ∈ (U : Set (F.obj i))
  simpa [stagewise_pullback_family, Functor.map_comp] using hx'

/-- Helper for Lemma 5.24.5: forgetting the subtype coordinate gives a natural transformation from
the stable-subset diagram back to the ambient diagram. -/
private def stagewise_pullback_forget_hom
    (i : I) (U : CompactOpens (F.obj i))
    (hZ_maps :
      ∀ ⦃j k : I⦄ (a : j ⟶ k), Set.MapsTo (F.map a)
        (stagewise_pullback_family (F := F) i U j)
        (stagewise_pullback_family (F := F) i U k)) :
    (F.stableSubsetDiagram (stagewise_pullback_family (F := F) i U) hZ_maps) ⟶ F where
  app j := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  naturality {X Y} f := by
    -- Both sides are the same restricted ambient map on points.
    ext x
    rfl

/-- Helper for Lemma 5.24.5: the pullback of a stage compact open to the explicit limit cone is
compact, by realizing it as the image of a compact limit of a stable-subset diagram. -/
private theorem projection_preimage_isCompact_of_compact_open
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a))
    (i : I) (U : CompactOpens (F.obj i)) :
    IsCompact (((TopCat.limitCone F).π.app i) ⁻¹' (U : Set (F.obj i))) := by
  let Z := stagewise_pullback_family (F := F) i U
  have hZ_closed : ∀ j : I, IsClosed[constructibleTopology (F.obj j)] (Z j) := by
    intro j
    exact stagewise_pullback_family_closed (F := F) hF i U j
  have hZ_maps :
      ∀ ⦃j k : I⦄ (a : j ⟶ k), Set.MapsTo (F.map a) (Z j) (Z k) := by
    intro j k a
    exact stagewise_pullback_family_mapsTo (F := F) i U a
  let D := F.stableSubsetDiagram Z hZ_maps
  have hCompactLimit : CompactSpace ↥(limit D) :=
    compactSpace_limit_of_constructibleClosed_stableSubsetDiagram
      (F := F) (Z := Z) (hF := hF) (hZ_closed := hZ_closed) (hZ_maps := hZ_maps)
  let e :=
    TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso (limit.isLimit D) (TopCat.limitConeIsLimit D))
  letI : CompactSpace ↥((limit.cone D).pt) := by
    simpa using hCompactLimit
  letI : CompactSpace ↥((TopCat.limitCone D).pt) := by
    exact e.compactSpace
  let α := stagewise_pullback_forget_hom (F := F) i U hZ_maps
  let c : Cone F := (Cone.postcompose α).obj (TopCat.limitCone D)
  let f : (TopCat.limitCone D).pt ⟶ (TopCat.limitCone F).pt :=
    (TopCat.limitConeIsLimit F).lift c
  have hImage :
      f '' (Set.univ : Set (TopCat.limitCone D).pt) =
        ((TopCat.limitCone F).π.app i) ⁻¹' (U : Set (F.obj i)) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      refine mem_preimage.2 ?_
      have hfπ :
          (TopCat.limitCone F).π.app i (f y) = c.π.app i y := by
        simpa [f] using
          congrArg
            (fun g : (TopCat.limitCone D).pt ⟶ F.obj i ↦ g y)
            ((TopCat.limitConeIsLimit F).fac c i)
      have hyi : c.π.app i y ∈ (U : Set (F.obj i)) := by
        change (((TopCat.limitCone D).π.app i y).1 : F.obj i) ∈ (U : Set (F.obj i))
        have hyi' :
            ((TopCat.limitCone D).π.app i y).1 ∈ Z i :=
          ((TopCat.limitCone D).π.app i y).2
        simpa [Z, stagewise_pullback_family, Functor.map_id] using
          (mem_iInter.1 hyi' (𝟙 i))
      rw [hfπ]
      exact hyi
    · intro hx
      let yComp : ∀ j : I, D.obj j := fun j ↦
        ⟨(TopCat.limitCone F).π.app j x, by
          refine mem_iInter.2 fun a ↦ ?_
          change F.map a ((TopCat.limitCone F).π.app j x) ∈ (U : Set (F.obj i))
          have hπ :
              (TopCat.limitCone F).π.app i x =
                F.map a ((TopCat.limitCone F).π.app j x) := by
            rw [← CategoryTheory.comp_apply]
            exact congrArg
              (fun g : (TopCat.limitCone F).pt ⟶ F.obj i ↦ g x)
              ((TopCat.limitCone F).w a).symm
          exact hπ ▸ mem_preimage.1 hx⟩
      have hyCompat :
          ∀ ⦃j k : I⦄ (a : j ⟶ k), D.map a (yComp j) = yComp k := by
        intro j k a
        apply Subtype.ext
        change F.map a ((TopCat.limitCone F).π.app j x) = (TopCat.limitCone F).π.app k x
        rw [← CategoryTheory.comp_apply]
        exact congrArg
          (fun g : (TopCat.limitCone F).pt ⟶ F.obj k ↦ g x)
          ((TopCat.limitCone F).w a)
      let y : (TopCat.limitCone D).pt := ⟨yComp, fun {_ _} a ↦ hyCompat a⟩
      refine ⟨y, trivial, ?_⟩
      apply Subtype.ext
      funext j
      have hfπ :
          (TopCat.limitCone F).π.app j (f y) = c.π.app j y := by
        simpa [f] using
          congrArg
            (fun g : (TopCat.limitCone D).pt ⟶ F.obj j ↦ g y)
            ((TopCat.limitConeIsLimit F).fac c j)
      change (TopCat.limitCone F).π.app j (f y) = (TopCat.limitCone F).π.app j x
      rw [hfπ]
      rfl
  -- The stable-subset limit is compact, and its image is exactly the desired pullback subset.
  rw [← hImage]
  exact isCompact_univ.image f.hom.continuous

/-- Helper for Lemma 5.24.5: index the compact-open basic neighborhoods on the explicit limit cone
by a stage together with a stage compact open. -/
private def projection_preimage_basis :
    (Σ i : I, CompactOpens (F.obj i)) → Set (TopCat.limitCone F).pt :=
  fun p ↦ (TopCat.limitCone F).π.app p.1 ⁻¹' (p.2 : Set (F.obj p.1))

/-- Helper for Lemma 5.24.5: projection pullbacks of stage compact opens form a topological basis
on the explicit limit cone. -/
private theorem projection_preimage_compact_open_basis
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) :
    IsTopologicalBasis (Set.range (projection_preimage_basis (F := F))) := by
  let C := TopCat.limitCone F
  let T : ∀ j : I, Set (Set (F.obj j)) := fun j ↦ {U : Set (F.obj j) | IsOpen U ∧ IsCompact U}
  have hT_basis : ∀ j : I, IsTopologicalBasis (T j) := by
    intro j
    simpa [T] using (PrespectralSpace.isTopologicalBasis (X := F.obj j))
  have hT_univ : ∀ j : I, Set.univ ∈ T j := by
    intro j
    exact ⟨isOpen_univ, isCompact_univ⟩
  have hT_inter :
      ∀ j : I, ∀ U V : Set (F.obj j), U ∈ T j → V ∈ T j → U ∩ V ∈ T j := by
    intro j U V hU hV
    exact ⟨hU.1.inter hV.1, hU.2.inter_of_isOpen hV.2 hU.1 hV.1⟩
  have hBasisAux :
      IsTopologicalBasis {W : Set C.pt | ∃ j, ∃ V ∈ T j, W = C.π.app j ⁻¹' V} :=
    TopCat.isTopologicalBasis_cofiltered_limit.{max u v, u, v} F C (TopCat.limitConeIsLimit F)
      T
      hT_basis hT_univ hT_inter
      (fun _ _ a U hU ↦ by
        change IsOpen ((F.map a) ⁻¹' U) ∧ IsCompact ((F.map a) ⁻¹' U)
        exact ⟨hU.1.preimage (hF a).continuous, (hF a).isCompact_preimage_of_isOpen hU.1 hU.2⟩)
  have hRange :
      Set.range (projection_preimage_basis (F := F)) =
        {W : Set C.pt | ∃ (j : I) (U : Set (F.obj j)),
          IsOpen U ∧ IsCompact U ∧ W = C.π.app j ⁻¹' U} := by
    ext W
    constructor
    · rintro ⟨⟨j, U⟩, rfl⟩
      exact ⟨j, (U : Set (F.obj j)), U.isOpen, U.isCompact, rfl⟩
    · rintro ⟨j, U, hU_open, hU_compact, rfl⟩
      exact ⟨⟨j, ⟨⟨U, hU_compact⟩, hU_open⟩⟩, rfl⟩
  -- Rewrite the existential basis returned by the owner theorem into the sigma-indexed family.
  rw [hRange]
  simpa [T, and_assoc] using hBasisAux

/-- Helper for Lemma 5.24.5: a basis intersection is again a single projection pullback on a
common refinement stage. -/
private theorem projection_preimage_inter_eq
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a))
    (i j : I) (Ui : CompactOpens (F.obj i)) (Uj : CompactOpens (F.obj j)) :
    ∃ (k : I) (_ : k ⟶ i) (_ : k ⟶ j) (Uk : CompactOpens (F.obj k)),
      (((TopCat.limitCone F).π.app i) ⁻¹' (Ui : Set (F.obj i))) ∩
          (((TopCat.limitCone F).π.app j) ⁻¹' (Uj : Set (F.obj j))) =
        ((TopCat.limitCone F).π.app k) ⁻¹' (Uk : Set (F.obj k)) := by
  let C := TopCat.limitCone F
  have hπ {a b : I} (f : a ⟶ b) (x : C.pt) :
      C.π.app b x = F.map f (C.π.app a x) := by
    rw [← CategoryTheory.comp_apply]
    exact congrArg (fun m : C.pt ⟶ F.obj b ↦ m x) (C.w f).symm
  obtain ⟨k, a, b, _⟩ := IsCofilteredOrEmpty.cone_objs i j
  have hUk_open :
      IsOpen (((F.map a) ⁻¹' (Ui : Set (F.obj i))) ∩
        ((F.map b) ⁻¹' (Uj : Set (F.obj j))) : Set (F.obj k)) := by
    exact (Ui.isOpen.preimage (hF a).continuous).inter (Uj.isOpen.preimage (hF b).continuous)
  have hUk_compact :
      IsCompact (((F.map a) ⁻¹' (Ui : Set (F.obj i))) ∩
        ((F.map b) ⁻¹' (Uj : Set (F.obj j))) : Set (F.obj k)) := by
    exact ((hF a).isCompact_preimage_of_isOpen Ui.isOpen Ui.isCompact).inter_of_isOpen
      ((hF b).isCompact_preimage_of_isOpen Uj.isOpen Uj.isCompact)
      (Ui.isOpen.preimage (hF a).continuous) (Uj.isOpen.preimage (hF b).continuous)
  let Uk : CompactOpens (F.obj k) := ⟨⟨_, hUk_compact⟩, hUk_open⟩
  refine ⟨k, a, b, Uk, ?_⟩
  ext x
  constructor
  · intro hx
    refine mem_preimage.2 ?_
    constructor
    · have hleft : C.π.app i x ∈ (Ui : Set (F.obj i)) := mem_preimage.1 hx.1
      change F.map a (C.π.app k x) ∈ (Ui : Set (F.obj i))
      exact (hπ a x).symm ▸ hleft
    · have hright : C.π.app j x ∈ (Uj : Set (F.obj j)) := mem_preimage.1 hx.2
      change F.map b (C.π.app k x) ∈ (Uj : Set (F.obj j))
      exact (hπ b x).symm ▸ hright
  · intro hx
    constructor
    · refine mem_preimage.2 ?_
      have hleft : F.map a (C.π.app k x) ∈ (Ui : Set (F.obj i)) := (mem_preimage.1 hx).1
      exact hπ a x ▸ hleft
    · refine mem_preimage.2 ?_
      have hright : F.map b (C.π.app k x) ∈ (Uj : Set (F.obj j)) := (mem_preimage.1 hx).2
      exact hπ b x ▸ hright

/-- Helper for Lemma 5.24.5: an irreducible closed subset of the explicit limit cone has a
generic point obtained from the compatible family of the stage generic points. -/
private theorem generic_point_of_irreducible_closed_limit
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a))
    {Z : Set (TopCat.limitCone F).pt}
    (hZ_irred : IsIrreducible Z) (hZ_closed : IsClosed Z) :
    ∃ ξ : (TopCat.limitCone F).pt, IsGenericPoint ξ Z := by
  let C := TopCat.limitCone F
  have hπ {i j : I} (f : i ⟶ j) (x : C.pt) :
      C.π.app j x = F.map f (C.π.app i x) := by
    rw [← CategoryTheory.comp_apply]
    exact congrArg (fun g : C.pt ⟶ F.obj j ↦ g x) (C.w f).symm
  have hBasis : IsTopologicalBasis (Set.range (projection_preimage_basis (F := F))) :=
    projection_preimage_compact_open_basis (F := F) hF
  have hImage_irred (i : I) : IsIrreducible (C.π.app i '' Z) :=
    hZ_irred.image (C.π.app i) (C.π.app i).hom.continuous.continuousOn
  let ξi : ∀ i : I, F.obj i := fun i ↦ (hImage_irred i).genericPoint
  have hξi :
      ∀ i : I, IsGenericPoint (ξi i) (closure (C.π.app i '' Z)) := by
    intro i
    simpa [ξi] using (hImage_irred i).isGenericPoint_genericPoint_closure
  have hmap_image {i j : I} (f : i ⟶ j) :
      F.map f '' (C.π.app i '' Z) = C.π.app j '' Z := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, hπ f z⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨C.π.app i z, ⟨z, hz, rfl⟩, (hπ f z).symm⟩
  have hξ_compatible : ∀ {i j : I} (f : i ⟶ j), F.map f (ξi i) = ξi j := by
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
    ⟨ξi, fun {_ _} f ↦ hξ_compatible f⟩
  have hξ_mem_closure : ξ ∈ closure Z := by
    -- Any open neighborhood of `ξ` contains a basis neighborhood of the form `π_i ⁻¹(Ui)`.
    rw [mem_closure_iff]
    intro U hU hξU
    obtain ⟨B, hB, hξB, hBU⟩ := hBasis.exists_subset_of_mem_open hξU hU
    rcases hB with ⟨⟨i, Ui⟩, rfl⟩
    have hξiUi : ξi i ∈ (Ui : Set (F.obj i)) := by
      simpa [ξ, projection_preimage_basis] using hξB
    have hStageMeet :
        (closure (C.π.app i '' Z) ∩ (Ui : Set (F.obj i))).Nonempty :=
      ((hξi i).mem_open_set_iff Ui.isOpen).1 hξiUi
    rcases hStageMeet with ⟨y, hyClosure, hyUi⟩
    rcases mem_closure_iff.1 hyClosure (Ui : Set (F.obj i)) Ui.isOpen hyUi with
      ⟨w, hwUi, hwImage⟩
    rcases hwImage with ⟨z, hz, rfl⟩
    refine ⟨z, ?_, hz⟩
    exact hBU (by simpa [projection_preimage_basis] using hwUi)
  have hξ_mem : ξ ∈ Z := by
    simpa [hZ_closed.closure_eq] using hξ_mem_closure
  have hξ_specializes : ∀ ⦃z : C.pt⦄, z ∈ Z → ξ ⤳ z := by
    intro z hz
    -- Basis neighborhoods of `z` already meet the stage image of `Z`, hence they contain `ξ`.
    rw [specializes_iff_forall_open]
    intro U hU hzU
    obtain ⟨B, hB, hzB, hBU⟩ := hBasis.exists_subset_of_mem_open hzU hU
    rcases hB with ⟨⟨i, Ui⟩, rfl⟩
    have hStageMeet :
        (closure (C.π.app i '' Z) ∩ (Ui : Set (F.obj i))).Nonempty := by
      exact ⟨C.π.app i z, subset_closure ⟨z, hz, rfl⟩, by
        simpa [projection_preimage_basis] using hzB⟩
    have hξiUi : ξi i ∈ (Ui : Set (F.obj i)) :=
      ((hξi i).mem_open_set_iff Ui.isOpen).2 hStageMeet
    have hξB : ξ ∈ C.π.app i ⁻¹' (Ui : Set (F.obj i)) := by
      simpa [ξ, projection_preimage_basis] using hξiUi
    exact hBU hξB
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

/-- Helper for Lemma 5.24.5: the explicit limit cone of the diagram is spectral. -/
private theorem explicit_spectralSpace_of_cofiltered_spectral_diagram
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) :
    SpectralSpace ↥((TopCat.limitCone F).pt) := by
  classical
  let C := TopCat.limitCone F
  have hCompactLimit : CompactSpace ↥(limit F) :=
    compactSpace_limit_of_spectralSpaceDiagram (F := F) hF
  let e :=
    TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (TopCat.limitConeIsLimit F))
  letI : CompactSpace ↥((limit.cone F).pt) := by
    simpa using hCompactLimit
  letI : T0Space C.pt := by
    change T0Space { u : ∀ j : I, F.obj j |
      ∀ {i j : I} (f : i ⟶ j), F.map f (u i) = u j }
    infer_instance
  letI : CompactSpace C.pt := by
    exact e.compactSpace
  letI : QuasiSober C.pt :=
    { sober := fun {Z} hZ_irred hZ_closed ↦
        generic_point_of_irreducible_closed_limit (F := F) hF hZ_irred hZ_closed }
  let b := projection_preimage_basis (F := F)
  have hBasis : IsTopologicalBasis (Set.range b) :=
    projection_preimage_compact_open_basis (F := F) hF
  have hCompactBasis : ∀ p : Σ i : I, CompactOpens (F.obj i), IsCompact (b p) := by
    rintro ⟨i, U⟩
    -- Each basis element is compact by the stable-subset limit comparison above.
    simpa [b, projection_preimage_basis] using
      projection_preimage_isCompact_of_compact_open (F := F) hF i U
  have hCompactInter :
      ∀ p q : Σ i : I, CompactOpens (F.obj i), IsCompact (b p ∩ b q) := by
    rintro ⟨i, Ui⟩ ⟨j, Uj⟩
    obtain ⟨k, _, _, Uk, hEq⟩ :=
      projection_preimage_inter_eq (F := F) hF i j Ui Uj
    have hbEq : b ⟨i, Ui⟩ ∩ b ⟨j, Uj⟩ = b ⟨k, Uk⟩ := by
      simpa [b, projection_preimage_basis] using hEq
    rw [hbEq]
    simpa [b, projection_preimage_basis] using
      projection_preimage_isCompact_of_compact_open (F := F) hF k Uk
  letI : PrespectralSpace C.pt :=
    PrespectralSpace.of_isTopologicalBasis' hBasis hCompactBasis
  letI : QuasiSeparatedSpace C.pt :=
    QuasiSeparatedSpace.of_isTopologicalBasis hBasis hCompactInter
  exact
    { toT0Space := inferInstance
      toCompactSpace := inferInstance
      toQuasiSober := inferInstance
      toQuasiSeparatedSpace := inferInstance
      toPrespectralSpace := inferInstance }

/-- Helper for Lemma 5.24.5: a homeomorphism is spectral because preimages of compact sets are
images under the continuous inverse. -/
private theorem isSpectralMap_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : IsSpectralMap e := by
  refine ⟨e.continuous, fun s _ hs_compact ↦ ?_⟩
  have hpreimage : e ⁻¹' s = e.symm '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [hpreimage]
  exact hs_compact.image e.symm.continuous

/-- Helper for Lemma 5.24.5: each projection from the explicit limit cone is spectral. -/
private theorem isSpectralMap_explicit_projection_of_cofiltered_spectral_diagram
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) (i : I) :
    IsSpectralMap ((TopCat.limitCone F).π.app i) := by
  let C := TopCat.limitCone F
  letI : SpectralSpace C.pt :=
    explicit_spectralSpace_of_cofiltered_spectral_diagram (F := F) hF
  refine ⟨(C.π.app i).hom.continuous, fun s hs_open hs_compact ↦ ?_⟩
  let U : CompactOpens (F.obj i) := ⟨⟨s, hs_compact⟩, hs_open⟩
  simpa [U] using projection_preimage_isCompact_of_compact_open (F := F) hF i U

-- Proof sketch: first prove spectrality for the explicit limit cone `TopCat.limitCone F` by
-- combining the compactness theorem of Lemma `5.24.1` with the compact-open basis and the
-- compatible-family generic-point construction; then transport the resulting spectral structure to
-- the arbitrary limiting cone point `C.pt`.
/-- Lemma 5.24.5: the inverse limit of a cofiltered diagram of spectral spaces with spectral
transition maps is a spectral topological space. -/
theorem spectralSpace_of_isLimit_of_cofiltered_spectral_diagram (hC : IsLimit C)
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) :
    SpectralSpace ↥C.pt := by
  let C₀ := TopCat.limitCone F
  letI : SpectralSpace ↥C₀.pt :=
    explicit_spectralSpace_of_cofiltered_spectral_diagram (F := F) hF
  let e :=
    TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso (TopCat.limitConeIsLimit F) hC)
  -- Transport the spectral ingredients across the canonical homeomorphism from the explicit limit
  -- cone to the chosen limiting cone.
  letI : T0Space C.pt := e.t0Space
  letI : CompactSpace C.pt := e.compactSpace
  letI : QuasiSober C.pt := e.symm.isOpenEmbedding.quasiSober
  letI : QuasiSeparatedSpace C.pt := e.symm.isOpenEmbedding.quasiSeparatedSpace
  letI : PrespectralSpace C.pt := e.symm.isOpenEmbedding.prespectralSpace
  exact SpectralSpace.mk

-- Proof sketch: compare the chosen limiting cone to the explicit limit cone, note that the
-- comparison homeomorphism is spectral, and compose it with the already-proved spectral
-- projection on the explicit cone.
/-- Each projection from a limiting cone of a cofiltered diagram of spectral spaces is a spectral
map. -/
theorem isSpectralMap_projection_of_isLimit_of_cofiltered_spectral_diagram
    (hC : IsLimit C) (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) (i : I) :
    IsSpectralMap (C.π.app i) := by
  let e :=
    TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso hC (TopCat.limitConeIsLimit F))
  have hHomeo : IsSpectralMap e :=
    isSpectralMap_homeomorph e
  have hExplicit : IsSpectralMap ((TopCat.limitCone F).π.app i) :=
    isSpectralMap_explicit_projection_of_cofiltered_spectral_diagram (F := F) hF i
  have hComp : IsSpectralMap (((TopCat.limitCone F).π.app i) ∘ e) :=
    hExplicit.comp hHomeo
  have hEq : (C.π.app i : C.pt → F.obj i) = ((TopCat.limitCone F).π.app i) ∘ e := by
    funext x
    simpa [Function.comp] using
      congrArg (fun g : C.pt ⟶ F.obj i ↦ g x)
        (IsLimit.conePointUniqueUpToIso_hom_comp hC (TopCat.limitConeIsLimit F) i)
  simpa [hEq, Function.comp] using hComp

instance
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) :
    SpectralSpace ↥(limit F) :=
  spectralSpace_of_isLimit_of_cofiltered_spectral_diagram (limit.isLimit F) hF

end

/-! ### Lemma_5_24_6 (from Chap05) -/
universe u v w

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits

section

variable {J : Type v} [Category.{w} J] [IsCofiltered J]
variable {F : J ⥤ TopCat.{max v w}} [∀ j : J, SpectralSpace (F.obj j)]

/- Domain-style sampling for Lemma 5.24.6:
- primary domain: cofiltered inverse limits of spectral spaces, with descent of quasi-compact
  opens and eventual stagewise inclusion;
- inspected owner-level declarations:
  `open_eq_preimage_of_isLimit_of_isConstructible`,
  `constructible_eq_preimage_of_isLimit`,
  `limit_projection_preimage_subset_iff_exists_stage_preimage_subset`,
  `spectralSpace_of_isLimit_of_cofiltered_spectral_diagram`;
- best owner abstraction first: the spectral/constructible descent owner for part `(1)` is
  `open_eq_preimage_of_isLimit_of_isConstructible`, whose output already lives in
  `CompactOpens`; `limit_projection_preimage_subset_iff_exists_stage_preimage_subset` is the
  chapter-level owner for eventual stagewise inclusion in part `(2)`;
- primitive data: the cofiltered spectral diagram and the limit-side or stagewise `CompactOpens`;
- derived API: part `(1)` as the chosen-limit specialization of open constructible descent, then
  the common-refinement inclusion criterion and the finite union/intersection descent statements.

Source/core/bridge triage:
- `source-facing`: the numbered Lemma 5.24.6 statements about quasi-compact opens on the chosen
  inverse limit and their eventual stagewise behavior;
- `core/canonical`: `Topology.IsConstructible` together with `CompactOpens` and the chapter 5.24
  cofiltered-limit descent owners;
- `bridge/view`: part `(1)` is the chosen-limit specialization of
  `open_eq_preimage_of_isLimit_of_isConstructible`, turning a limit-side `CompactOpens` object into
  its stagewise `CompactOpens` ancestor.

The finite-family parts are stated over an arbitrary `Fintype` rather than `Fin n`: the source
mathematics uses only finiteness, so the `Fin n` encoding would be presentation-level bookkeeping
rather than primitive data.
-/

-- Proof sketch: first descend the limit-side compact open to a single stage open via
-- `compact_open_eq_preimage_of_isLimit`, then refine that stage open by compact-open basis pieces
-- and use compactness of the limit-side subset to keep only finitely many of them.
/-- Lemma 5.24.6 (1): every quasi-compact open subset of the inverse limit of a cofiltered diagram
of spectral spaces with spectral transition maps is the pullback of a quasi-compact open subset
from some stage. -/
theorem compact_open_eq_preimage_of_limit
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (W : CompactOpens ↥(limit F)) :
    ∃ (i : J) (Wi : CompactOpens (F.obj i)),
      (W : Set ↥(limit F)) = (limit.π F i) ⁻¹' (Wi : Set (F.obj i)) := by
  let _ := hF
  let C : Cone F := limit.cone F
  have hC : IsLimit C := by
    simpa [C] using limit.isLimit F
  obtain ⟨i, U, hU⟩ := compact_open_eq_preimage_of_isLimit (F := F) (C := C) hC (by
    simpa [C] using W)
  have hU' : (W : Set ↥(limit F)) = (limit.π F i) ⁻¹' (U : Set (F.obj i)) := by
    simpa [C] using hU
  let S : Set (Set (F.obj i)) := {s | IsOpen s ∧ IsCompact s ∧ s ⊆ (U : Set (F.obj i))}
  have hU_eq : (U : Set (F.obj i)) = ⋃₀ S := by
    simpa [S, and_left_comm, and_assoc] using
      (PrespectralSpace.isTopologicalBasis (X := F.obj i)).open_eq_sUnion' U.isOpen
  let V : {s : Set (F.obj i) // s ∈ S} → CompactOpens (F.obj i) :=
    fun s ↦ ⟨⟨s.1, s.2.2.1⟩, s.2.1⟩
  have hOpen : ∀ s : {s : Set (F.obj i) // s ∈ S},
      IsOpen ((limit.π F i) ⁻¹' (V s : Set (F.obj i))) := by
    intro s
    exact (V s).isOpen.preimage (limit.π F i).hom.continuous
  have hCover : (W : Set ↥(limit F)) ⊆ ⋃ s : {s : Set (F.obj i) // s ∈ S},
      (limit.π F i) ⁻¹' (V s : Set (F.obj i)) := by
    intro x hx
    rw [hU'] at hx
    change (limit.π F i) x ∈ (U : Set (F.obj i)) at hx
    rw [hU_eq] at hx
    rcases mem_sUnion.1 hx with ⟨s, hsS, hsx⟩
    exact mem_iUnion.2 ⟨⟨s, hsS⟩, hsx⟩
  obtain ⟨t, ht⟩ := W.isCompact.elim_finite_subcover
    (fun s : {s : Set (F.obj i) // s ∈ S} ↦ (limit.π F i) ⁻¹' (V s : Set (F.obj i))) hOpen hCover
  let Wi : CompactOpens (F.obj i) := t.sup V
  refine ⟨i, Wi, ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : x ∈ ⋃ s ∈ t, (limit.π F i) ⁻¹' (V s : Set (F.obj i)) := by
      have htx := ht hx
      rw [Set.mem_iUnion] at htx
      rcases htx with ⟨s, htx⟩
      rw [Set.mem_iUnion] at htx
      rcases htx with ⟨hs, hsx⟩
      exact mem_iUnion.2 ⟨s, mem_iUnion.2 ⟨hs, hsx⟩⟩
    simpa [Wi, CompactOpens.coe_finsetSup] using hx'
  · intro hx
    have hx' : x ∈ ⋃ s ∈ t, (limit.π F i) ⁻¹' (V s : Set (F.obj i)) := by
      simpa [Wi, CompactOpens.coe_finsetSup] using hx
    rw [hU']
    rw [Set.mem_preimage]
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨s, hx'⟩
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨hs, hsx⟩
    exact s.2.2.2 hsx

/-- Helper for Lemma 5.24.6: pulling back along a limit projection can be rewritten through any
refining stage map. -/
private theorem limit_projection_preimage_eq_stage_preimage
    {J : Type v} [Category.{w} J] {F : J ⥤ TopCat.{max v w}}
    {i k : J} (a : k ⟶ i) (S : Set (F.obj i)) :
    (limit.π F i) ⁻¹' S = (limit.π F k) ⁻¹' ((F.map a) ⁻¹' S) := by
  -- The limit cone relation identifies the `i`-coordinate with the `k`-coordinate followed by `a`.
  ext x
  constructor
  · intro hx
    change F.map a ((limit.π F k) x) ∈ S
    have hπ : F.map a ((limit.π F k) x) = (limit.π F i) x := by
      exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F a)) x
    simpa [hπ] using hx
  · intro hx
    change F.map a ((limit.π F k) x) ∈ S at hx
    have hπ : F.map a ((limit.π F k) x) = (limit.π F i) x := by
      exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F a)) x
    simpa [hπ] using hx

/-- Helper for Lemma 5.24.6: compact opens are constructibly closed on a spectral space. -/
private theorem compact_open_isClosed_constructibleTopology
    {X : Type*} [TopologicalSpace X] [SpectralSpace X] (U : CompactOpens X) :
    IsClosed[constructibleTopology X] (U : Set X) := by
  -- Compact opens are constructible, hence clopen for the constructible topology.
  exact (isClopen_constructibleTopology_of_isConstructible
    (U.isCompact.isConstructible U.isOpen)).1

/-- Helper for Lemma 5.24.6: compact opens are constructibly open on a spectral space. -/
private theorem compact_open_isOpen_constructibleTopology
    {X : Type*} [TopologicalSpace X] [SpectralSpace X] (U : CompactOpens X) :
    IsOpen[constructibleTopology X] (U : Set X) := by
  -- Compact opens are constructible, hence clopen for the constructible topology.
  exact (isClopen_constructibleTopology_of_isConstructible
    (U.isCompact.isConstructible U.isOpen)).2

/-- Helper for Lemma 5.24.6: inverse image commutes with the finite `CompactOpens` supremum
packaged by `Finset.univ.sup`. -/
private theorem preimage_finset_sup_eq_iUnion
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι] (f : X → Y) (V : ι → CompactOpens Y) :
    f ⁻¹' ((Finset.univ.sup V : CompactOpens Y) : Set Y) = ⋃ t, f ⁻¹' (V t : Set Y) := by
  classical
  -- Membership in the finite supremum is exactly membership in one of the finitely many opens.
  ext x
  simp [CompactOpens.coe_finsetSup]

/-- Helper for Lemma 5.24.6: inverse image commutes with the finite `CompactOpens` infimum
packaged by `Finset.univ.inf`. -/
private theorem preimage_finset_inf_eq_iInter
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SpectralSpace Y]
    {ι : Type*} [Fintype ι] (f : X → Y) (V : ι → CompactOpens Y) :
    f ⁻¹' ((Finset.univ.inf V : CompactOpens Y) : Set Y) = ⋂ t, f ⁻¹' (V t : Set Y) := by
  classical
  -- Unfold the finite infimum inductively and rewrite each step as an intersection preimage.
  have haux :
      ∀ s : Finset ι,
        f ⁻¹' ((s.inf V : CompactOpens Y) : Set Y) = ⋂ t ∈ s, f ⁻¹' (V t : Set Y) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        ext x
        simp
    | insert a s ha hs =>
        ext x
        simp [Finset.inf_insert, hs, CompactOpens.coe_inf]
  simpa using haux Finset.univ

-- Proof sketch: specialize
-- `limit_projection_preimage_subset_iff_exists_stage_preimage_subset` from Lemma `5.24.3` to the
-- constructibly closed set `Ui` and the constructibly open set `Uj`, then use cofilteredness to
-- compare the two stage indices on a common refinement.
/-- Lemma 5.24.6 (2): if the pullback of a quasi-compact open from one stage is contained in the
pullback of a quasi-compact open from another stage, then this inclusion already holds after
pullback to some common refinement stage. -/
theorem exists_common_refinement_of_preimage_subset
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : J} (Ui : CompactOpens (F.obj i)) (Uj : CompactOpens (F.obj j))
    (hsub : (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) ⊆
      (limit.π F j) ⁻¹' (Uj : Set (F.obj j))) :
    ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j),
      (F.map a) ⁻¹' (Ui : Set (F.obj i)) ⊆ (F.map b) ⁻¹' (Uj : Set (F.obj j)) := by
  have hF' : ∀ ⦃j k : J⦄ (a : j ⟶ k), IsSpectralMap (F.map a) := fun {_ _} a ↦ hF a
  obtain ⟨k₀, a₀, b₀, _⟩ := IsCofilteredOrEmpty.cone_objs i j
  let Ei : Set (F.obj k₀) := (F.map a₀) ⁻¹' (Ui : Set (F.obj i))
  let Fj : Set (F.obj k₀) := (F.map b₀) ⁻¹' (Uj : Set (F.obj j))
  have hEi_closed : IsClosed[constructibleTopology (F.obj k₀)] Ei := by
    -- Pull the constructibly closed compact open `Ui` back along the spectral transition map.
    dsimp [Ei]
    exact @IsClosed.preimage (F.obj k₀) (F.obj i)
      (constructibleTopology (F.obj k₀)) (constructibleTopology (F.obj i))
      (F.map a₀) (hF a₀).continuous_constructibleTopology _ <|
        compact_open_isClosed_constructibleTopology Ui
  have hFj_open : IsOpen[constructibleTopology (F.obj k₀)] Fj := by
    -- Pull the constructibly open compact open `Uj` back along the spectral transition map.
    dsimp [Fj]
    exact @IsOpen.preimage (F.obj k₀) (F.obj j)
      (constructibleTopology (F.obj k₀)) (constructibleTopology (F.obj j))
      (F.map b₀) (hF b₀).continuous_constructibleTopology _ <|
        compact_open_isOpen_constructibleTopology Uj
  have hsub_k₀ : (limit.π F k₀) ⁻¹' Ei ⊆ (limit.π F k₀) ⁻¹' Fj := by
    -- Rewrite the original limit-side inclusion on the common refinement stage `k₀`.
    intro x hx
    have hx' : x ∈ (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) := by
      simpa [Ei, limit_projection_preimage_eq_stage_preimage] using hx
    have hx'' : x ∈ (limit.π F j) ⁻¹' (Uj : Set (F.obj j)) := hsub hx'
    simpa [Fj, limit_projection_preimage_eq_stage_preimage] using hx''
  obtain ⟨k, c, hc⟩ :=
    (limit_projection_preimage_subset_iff_exists_stage_preimage_subset
      (X := F) (i := k₀) (E := Ei) (F := Fj)
      hF' hEi_closed hFj_open).mp hsub_k₀
  refine ⟨k, c ≫ a₀, c ≫ b₀, ?_⟩
  -- Compose the single-stage inclusion obtained at `k₀` with the chosen refinement arrow.
  simpa [Ei, Fj, Functor.map_comp, Set.preimage_preimage] using hc

-- Proof sketch: descend the quasi-compact open on the limit to one stage by part `(1)`, then use
-- part `(2)` to descend each inclusion in the finite union and cofilteredness to dominate the
-- resulting finite set of stages by a single refinement.
/-- Lemma 5.24.6 (3): if the pullback of a quasi-compact open from a stage is a finite union of
pullbacks of quasi-compact opens from the same stage, then after pulling back along some morphism
to that stage the corresponding finite union identity already holds there. -/
theorem exists_stage_of_preimage_eq_iUnion
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : J} {ι : Type u} [Fintype ι] (Ui : CompactOpens (F.obj i))
    (V : ι → CompactOpens (F.obj i))
    (hcover : (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) =
      ⋃ t, (limit.π F i) ⁻¹' (V t : Set (F.obj i))) :
    ∃ (j : J) (a : j ⟶ i),
      (F.map a) ⁻¹' (Ui : Set (F.obj i)) = ⋃ t, (F.map a) ⁻¹' (V t : Set (F.obj i)) := by
  classical
  have hF' : ∀ ⦃j k : J⦄ (a : j ⟶ k), IsSpectralMap (F.map a) := fun {_ _} a ↦ hF a
  let _ := hF
  let Wsup : CompactOpens (F.obj i) := Finset.univ.sup V
  have hWsup_preimage :
      (limit.π F i) ⁻¹' (Wsup : Set (F.obj i)) =
        ⋃ t, (limit.π F i) ⁻¹' (V t : Set (F.obj i)) := by
    -- The finite family is compressed into one compact open via `sup`.
    unfold Wsup
    exact preimage_finset_sup_eq_iUnion (f := limit.π F i) V
  have hUi_to_Wsup :
      (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) ⊆
        (limit.π F i) ⁻¹' (Wsup : Set (F.obj i)) := by
    -- The limit-side equality gives one inclusion immediately.
    intro x hx
    rw [hcover] at hx
    exact hWsup_preimage.symm ▸ hx
  have hWsup_to_Ui :
      (limit.π F i) ⁻¹' (Wsup : Set (F.obj i)) ⊆
        (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) := by
    -- The reverse inclusion is the same equality read backwards.
    intro x hx
    rw [hWsup_preimage] at hx
    exact hcover.symm ▸ hx
  have hUi_closed : IsClosed[constructibleTopology (F.obj i)] (Ui : Set (F.obj i)) := by
    exact compact_open_isClosed_constructibleTopology Ui
  have hUi_open : IsOpen[constructibleTopology (F.obj i)] (Ui : Set (F.obj i)) := by
    exact compact_open_isOpen_constructibleTopology Ui
  have hWsup_closed : IsClosed[constructibleTopology (F.obj i)] (Wsup : Set (F.obj i)) := by
    exact compact_open_isClosed_constructibleTopology Wsup
  have hWsup_open : IsOpen[constructibleTopology (F.obj i)] (Wsup : Set (F.obj i)) := by
    exact compact_open_isOpen_constructibleTopology Wsup
  obtain ⟨j₁, a₁, ha₁⟩ :=
    (limit_projection_preimage_subset_iff_exists_stage_preimage_subset
      (X := F) (i := i) (E := (Ui : Set (F.obj i))) (F := (Wsup : Set (F.obj i)))
      hF' hUi_closed hWsup_open).mp hUi_to_Wsup
  obtain ⟨j₂, a₂, ha₂⟩ :=
    (limit_projection_preimage_subset_iff_exists_stage_preimage_subset
      (X := F) (i := i) (E := (Wsup : Set (F.obj i))) (F := (Ui : Set (F.obj i)))
      hF' hWsup_closed hUi_open).mp hWsup_to_Ui
  obtain ⟨j, b₁, b₂, hb⟩ := IsCofiltered.cospan a₁ a₂
  have hleft :
      (F.map (b₁ ≫ a₁)) ⁻¹' (Ui : Set (F.obj i)) ⊆
        (F.map (b₁ ≫ a₁)) ⁻¹' (Wsup : Set (F.obj i)) := by
    -- Pull the first eventual inclusion back to the common cospan stage.
    simpa [Functor.map_comp, Set.preimage_preimage] using Set.preimage_mono ha₁
  have hright :
      (F.map (b₁ ≫ a₁)) ⁻¹' (Wsup : Set (F.obj i)) ⊆
        (F.map (b₁ ≫ a₁)) ⁻¹' (Ui : Set (F.obj i)) := by
    -- Pull the second eventual inclusion back and rewrite along the commuting square.
    simpa [hb, Functor.map_comp, Set.preimage_preimage] using Set.preimage_mono ha₂
  refine ⟨j, b₁ ≫ a₁, ?_⟩
  -- After both inclusions are descended to one stage, rewrite the finite supremum as a union.
  calc
    (F.map (b₁ ≫ a₁)) ⁻¹' (Ui : Set (F.obj i)) =
        (F.map (b₁ ≫ a₁)) ⁻¹' (Wsup : Set (F.obj i)) :=
      Set.Subset.antisymm hleft hright
    _ = ⋃ t, (F.map (b₁ ≫ a₁)) ⁻¹' (V t : Set (F.obj i)) := by
      unfold Wsup
      exact preimage_finset_sup_eq_iUnion (f := F.map (b₁ ≫ a₁)) V

-- Proof sketch: argue exactly as in part `(3)`, replacing finite unions by finite intersections
-- and using that inverse images commute with intersections.
/-- Lemma 5.24.6 (4): if the pullback of a quasi-compact open from a stage is a finite
intersection of pullbacks of quasi-compact opens from the same stage, then after pulling back
along some morphism to that stage the corresponding finite intersection identity already holds
there. -/
theorem exists_stage_of_preimage_eq_iInter
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : J} {ι : Type u} [Fintype ι] (Ui : CompactOpens (F.obj i))
    (V : ι → CompactOpens (F.obj i))
    (hcover : (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) =
      ⋂ t, (limit.π F i) ⁻¹' (V t : Set (F.obj i))) :
    ∃ (j : J) (a : j ⟶ i),
      (F.map a) ⁻¹' (Ui : Set (F.obj i)) = ⋂ t, (F.map a) ⁻¹' (V t : Set (F.obj i)) := by
  classical
  have hF' : ∀ ⦃j k : J⦄ (a : j ⟶ k), IsSpectralMap (F.map a) := fun {_ _} a ↦ hF a
  let _ := hF
  let Winf : CompactOpens (F.obj i) := Finset.univ.inf V
  have hWinf_preimage :
      (limit.π F i) ⁻¹' (Winf : Set (F.obj i)) =
        ⋂ t, (limit.π F i) ⁻¹' (V t : Set (F.obj i)) := by
    -- The finite family is compressed into one compact open via `inf`.
    simpa [Winf] using preimage_finset_inf_eq_iInter (f := limit.π F i) V
  have hUi_to_Winf :
      (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) ⊆
        (limit.π F i) ⁻¹' (Winf : Set (F.obj i)) := by
    -- The limit-side equality gives one inclusion immediately.
    intro x hx
    rw [hcover] at hx
    exact hWinf_preimage.symm ▸ hx
  have hWinf_to_Ui :
      (limit.π F i) ⁻¹' (Winf : Set (F.obj i)) ⊆
        (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) := by
    -- The reverse inclusion is the same equality read backwards.
    intro x hx
    rw [hWinf_preimage] at hx
    exact hcover.symm ▸ hx
  have hUi_closed : IsClosed[constructibleTopology (F.obj i)] (Ui : Set (F.obj i)) := by
    exact compact_open_isClosed_constructibleTopology Ui
  have hUi_open : IsOpen[constructibleTopology (F.obj i)] (Ui : Set (F.obj i)) := by
    exact compact_open_isOpen_constructibleTopology Ui
  have hWinf_closed : IsClosed[constructibleTopology (F.obj i)] (Winf : Set (F.obj i)) := by
    exact compact_open_isClosed_constructibleTopology Winf
  have hWinf_open : IsOpen[constructibleTopology (F.obj i)] (Winf : Set (F.obj i)) := by
    exact compact_open_isOpen_constructibleTopology Winf
  obtain ⟨j₁, a₁, ha₁⟩ :=
    (limit_projection_preimage_subset_iff_exists_stage_preimage_subset
      (X := F) (i := i) (E := (Ui : Set (F.obj i))) (F := (Winf : Set (F.obj i)))
      hF' hUi_closed hWinf_open).mp hUi_to_Winf
  obtain ⟨j₂, a₂, ha₂⟩ :=
    (limit_projection_preimage_subset_iff_exists_stage_preimage_subset
      (X := F) (i := i) (E := (Winf : Set (F.obj i))) (F := (Ui : Set (F.obj i)))
      hF' hWinf_closed hUi_open).mp hWinf_to_Ui
  obtain ⟨j, b₁, b₂, hb⟩ := IsCofiltered.cospan a₁ a₂
  have hleft :
      (F.map (b₁ ≫ a₁)) ⁻¹' (Ui : Set (F.obj i)) ⊆
        (F.map (b₁ ≫ a₁)) ⁻¹' (Winf : Set (F.obj i)) := by
    -- Pull the first eventual inclusion back to the common cospan stage.
    simpa [Functor.map_comp, Set.preimage_preimage] using Set.preimage_mono ha₁
  have hright :
      (F.map (b₁ ≫ a₁)) ⁻¹' (Winf : Set (F.obj i)) ⊆
        (F.map (b₁ ≫ a₁)) ⁻¹' (Ui : Set (F.obj i)) := by
    -- Pull the second eventual inclusion back and rewrite along the commuting square.
    simpa [hb, Functor.map_comp, Set.preimage_preimage] using Set.preimage_mono ha₂
  refine ⟨j, b₁ ≫ a₁, ?_⟩
  -- After both inclusions are descended to one stage, rewrite the finite infimum as an
  -- intersection.
  calc
    (F.map (b₁ ≫ a₁)) ⁻¹' (Ui : Set (F.obj i)) =
        (F.map (b₁ ≫ a₁)) ⁻¹' (Winf : Set (F.obj i)) :=
      Set.Subset.antisymm hleft hright
    _ = ⋂ t, (F.map (b₁ ≫ a₁)) ⁻¹' (V t : Set (F.obj i)) := by
      simpa [Winf] using preimage_finset_inf_eq_iInter (f := F.map (b₁ ≫ a₁)) V

end

/-! ### Lemma_5_24_7 (from Chap05) -/
universe u v

noncomputable section

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits
open TopologicalSpace.Opens

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

/-- Helper for Lemma 5.24.7: every open subset of a spectral space is open for the constructible
topology. -/
private theorem isOpen_constructibleTopology_of_isOpen {s : Set X} (hs : IsOpen s) :
    IsOpen[constructibleTopology X] s := by
  -- The compact-open basis of a spectral space consists of constructible-topology open sets.
  refine PrespectralSpace.isTopologicalBasis.isOpen_induction ?_ ?_ hs
  · intro U hU
    exact hU.2.isOpen_constructibleTopology_of_isOpen hU.1
  · intro S hS
    let _ : TopologicalSpace X := constructibleTopology X
    exact isOpen_sUnion fun U hU ↦ hS U hU

/-- Helper for Lemma 5.24.7: every constructible-topology open neighborhood contains a
constructible neighborhood of each of its points. -/
private theorem exists_constructible_subset_of_mem_open_constructibleTopology
    {U : Set X} (hU : IsOpen[constructibleTopology X] U) {x : X} (hx : x ∈ U) :
    ∃ C : Set X, IsConstructible C ∧ x ∈ C ∧ C ⊆ U := by
  -- Route correction: instead of separating by later chapter API, induct directly on the
  -- `GenerateOpen` presentation of the constructible topology.
  change TopologicalSpace.GenerateOpen (constructibleTopologySubbasis X) U at hU
  induction hU generalizing x with
  | basic s hs =>
      rcases hs with hs | hs
      · -- A compact open subbasic set is already constructible.
        exact ⟨s, hs.2.isConstructible hs.1, hx, subset_rfl⟩
      · -- The complementary subbasic sets are complements of compact opens, hence constructible.
        have hs_compl_constructible : IsConstructible sᶜ := by
          exact hs.2.isConstructible hs.1.isOpen_compl
        exact ⟨s, by simpa using hs_compl_constructible.compl, hx, subset_rfl⟩
  | univ =>
      -- The whole space is constructible because a spectral space is quasi-compact.
      exact ⟨univ, isCompact_univ.isConstructible isOpen_univ, by simp, subset_rfl⟩
  | inter s t hs ht ihs iht =>
      rcases hx with ⟨hxS, hxT⟩
      rcases ihs hxS with ⟨Cs, hCs_constructible, hxCs, hCs_subset⟩
      rcases iht hxT with ⟨Ct, hCt_constructible, hxCt, hCt_subset⟩
      -- Intersect the two constructible neighborhoods supplied by the induction hypotheses.
      exact
        ⟨Cs ∩ Ct, hCs_constructible.inter hCt_constructible, ⟨hxCs, hxCt⟩,
          Set.inter_subset_inter hCs_subset hCt_subset⟩
  | sUnion S hS ih =>
      rcases Set.mem_sUnion.mp hx with ⟨V, hV, hxV⟩
      rcases ih V hV hxV with ⟨C, hC, hxC, hCU⟩
      -- A point of a union already lies in one stage, so keep the stagewise constructible witness.
      exact ⟨C, hC, hxC, hCU.trans (Set.subset_sUnion_of_mem hV)⟩

/-- In a spectral space, a subset is closed in the constructible topology exactly when it admits
the source-style presentation as an intersection of constructible subsets. -/
theorem isClosed_constructibleTopology_iff_eq_sInter_constructible (W : Set X) :
    IsClosed[constructibleTopology X] W ↔
      ∃ S : Set (Set X), (∀ Z ∈ S, IsConstructible Z) ∧ W = ⋂₀ S := by
  constructor
  · intro hW
    let S : Set (Set X) := { Z : Set X | IsConstructible Z ∧ W ⊆ Z }
    refine ⟨S, fun Z hZ ↦ hZ.1, ?_⟩
    apply subset_antisymm
    · intro x hx
      exact Set.mem_sInter.2 fun Z hZ ↦ hZ.2 hx
    · intro x hx
      by_contra hxW
      have hW_open : IsOpen[constructibleTopology X] Wᶜ := by
        let _ : TopologicalSpace X := constructibleTopology X
        exact hW.isOpen_compl
      obtain ⟨C, hC, hxC, hCW⟩ :=
        exists_constructible_subset_of_mem_open_constructibleTopology hW_open hxW
      have hC_compl_mem : Cᶜ ∈ S := by
        refine ⟨by simpa using hC.compl, ?_⟩
        intro y hyW hyC
        exact (hCW hyC) hyW
      have hxCcompl : x ∉ Cᶜ := by
        simpa using hxC
      exact hxCcompl (Set.mem_sInter.1 hx _ hC_compl_mem)
  · rintro ⟨S, hS, rfl⟩
    -- Constructible subsets are clopen in the constructible topology, so arbitrary intersections
    -- of them are constructibly closed.
    exact @isClosed_sInter X (constructibleTopology X) S fun Z hZ ↦
      (isClopen_constructibleTopology_of_isConstructible (hS Z hZ)).1

end

section

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for Lemma 5.24.7:
- primary domain: inverse limits in `TopCat` built from compact-open subspaces of a spectral space;
- inspected owner declarations:
  `CompactOpens`,
  `TopCat.nonempty_isLimit_iff_eq_induced`,
  `TopCat.isLimit_of_underlying_limit_of_preimage_basis`,
  `spectralSpace_of_isLimit_of_cofiltered_spectral_diagram`;
- best owner abstraction: the source-facing cone `compactOpenIntersectionCone W S hW`, with the
  chapter-level spectral-limit theorem reused only for the downstream spectrality consequence;
- primitive data: a subset `W`, a family `S : Set (CompactOpens X)`, and the equality
  `W = ⋂ U ∈ S, (U : Set X)`;
- derived API: the limiting-cone theorem and the resulting spectral-space instance on `W`.

Source/core/bridge triage:
- `source-facing`: the explicit cone exhibiting a directed nonempty intersection of compact opens
  as an inverse limit;
- `core/canonical`: `TopCat.nonempty_isLimit_iff_eq_induced` and
  `spectralSpace_of_isLimit_of_cofiltered_spectral_diagram`;
- `bridge/view`: the internal comparison isomorphism from
  `IsLimit.conePointUniqueUpToIso` between the source-facing cone and `TopCat.limitCone`.

No earlier Chapter 5 file provides this exact compact-open intersection cone. The owner-level reuse
point is therefore the canonical `TopCat` limit criterion, not a replacement of the source-facing
cone by a parallel wrapper.
-/

/-- A point of an intersection presentation by compact opens lies in every displayed stage. -/
theorem mem_of_mem_iInter_compactOpens {W : Set X} {S : Set (CompactOpens X)}
    (hW : W = ⋂ U ∈ S, (U : Set X)) {x : X} (hx : x ∈ W) {U : CompactOpens X} (hU : U ∈ S) :
    x ∈ (U : Set X) := by
  rw [hW] at hx
  have hx' : ∀ V ∈ S, x ∈ (V : Set X) := by
    simpa [Set.mem_iInter] using hx
  exact hx' U hU

/-- The open-subspace diagram indexed by a family of compact opens, ordered by reverse inclusion. -/
def compactOpenDiagram (S : Set (CompactOpens X)) : S ⥤ Opens (TopCat.of X) where
  obj U := U.1.toOpens
  map hij := homOfLE hij.le
  map_id U := by
    simp
  map_comp hij hjk := by
    simp

/-- The `TopCat` diagram of compact-open stages attached to an intersection presentation. -/
abbrev compactOpenIntersectionDiagram (S : Set (CompactOpens X)) : S ⥤ TopCat :=
  compactOpenDiagram S ⋙ Opens.toTopCat (TopCat.of X)

private def compactOpenIntersectionConeApp
    (W : Set X) (S : Set (CompactOpens X)) (hW : W = ⋂ U ∈ S, (U : Set X)) (U : S) :
    TopCat.of W ⟶ (compactOpenIntersectionDiagram S).obj U :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, mem_of_mem_iInter_compactOpens hW x.2 U.2⟩,
      continuous_subtype_val.subtype_mk
        (fun x ↦ mem_of_mem_iInter_compactOpens hW x.2 U.2)⟩

/-- The canonical cone from an intersection subtype to the diagram of the corresponding compact
open subspaces. -/
def compactOpenIntersectionCone
    (W : Set X) (S : Set (CompactOpens X)) (hW : W = ⋂ U ∈ S, (U : Set X)) :
    Cone (compactOpenIntersectionDiagram S) where
  pt := TopCat.of W
  π :=
    { app := compactOpenIntersectionConeApp W S hW
      naturality := by
        intro U V hUV
        ext x
        rfl }

private theorem induced_compactOpenIntersectionConeApp
    (W : Set X) (S : Set (CompactOpens X)) (hW : W = ⋂ U ∈ S, (U : Set X)) (U : S) :
    TopologicalSpace.induced (compactOpenIntersectionConeApp W S hW U)
      ((compactOpenIntersectionDiagram S).obj U).str = (TopCat.of W).str := by
  change TopologicalSpace.induced (compactOpenIntersectionConeApp W S hW U)
      (TopologicalSpace.induced Subtype.val inferInstance) =
    TopologicalSpace.induced Subtype.val inferInstance
  rw [induced_compose]
  rfl

private theorem val_eq_of_section_of_compactOpenIntersectionDiagram
    (S : Set (CompactOpens X)) (hDirected : DirectedOn (· ≥ ·) S)
    (s : ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).sections) (U V : S) :
    ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) U).1 =
      ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) V).1 := by
  obtain ⟨Z, hZS, hZU, hZV⟩ := hDirected U.1 U.2 V.1 V.2
  let Z' : S := ⟨Z, hZS⟩
  have hZU_eq :
      (((compactOpenIntersectionDiagram S).map (show Z' ⟶ U from homOfLE hZU))
        ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) Z')) =
      (s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) U :=
    s.2 (show Z' ⟶ U from homOfLE hZU)
  have hZV_eq :
      (((compactOpenIntersectionDiagram S).map (show Z' ⟶ V from homOfLE hZV))
        ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) Z')) =
      (s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) V :=
    s.2 (show Z' ⟶ V from homOfLE hZV)
  have hZU_val :
      Subtype.val
          (((compactOpenIntersectionDiagram S).map (show Z' ⟶ U from homOfLE hZU))
            ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) Z')) =
        Subtype.val
          ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) U) := by
    simpa [compactOpenIntersectionDiagram, compactOpenDiagram] using congrArg Subtype.val hZU_eq
  have hZV_val :
      Subtype.val
          (((compactOpenIntersectionDiagram S).map (show Z' ⟶ V from homOfLE hZV))
            ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) Z')) =
        Subtype.val
          ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) V) := by
    simpa [compactOpenIntersectionDiagram, compactOpenDiagram] using congrArg Subtype.val hZV_eq
  exact hZU_val.symm.trans hZV_val

private def isLimit_compactOpenIntersectionCone_of_directed_forget
    (W : Set X) (S : Set (CompactOpens X)) (hS_nonempty : S.Nonempty)
    (hW : W = ⋂ U ∈ S, (U : Set X)) (hDirected : DirectedOn (· ≥ ·) S) :
    IsLimit ((forget TopCat).mapCone (compactOpenIntersectionCone W S hW)) := by
  classical
  let F : S ⥤ Type _ := (compactOpenIntersectionDiagram S) ⋙ forget TopCat
  refine Classical.choice <| (Types.isLimit_iff_bijective_sectionOfCone _).2 ?_
  let U₀ : S := Classical.choice hS_nonempty.to_subtype
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hU₀ :
        ((Types.sectionOfCone ((forget TopCat).mapCone (compactOpenIntersectionCone W S hW)) x).1 U₀) =
          ((Types.sectionOfCone ((forget TopCat).mapCone (compactOpenIntersectionCone W S hW))
            y).1 U₀) := by
      exact congrArg (fun t ↦ t.1 U₀) hxy
    apply Subtype.ext
    simpa only [Types.sectionOfCone, Functor.mapCone_pt, compactOpenIntersectionCone,
      compactOpenIntersectionConeApp] using congrArg Subtype.val hU₀
  · intro s
    let x : X := ((s : ∀ U : S, F.obj U) U₀).1
    have hx_mem : ∀ V : CompactOpens X, V ∈ S → x ∈ (V : Set X) := by
      intro V hV
      have hUV :
          x = ((s : ∀ U : S, F.obj U) ⟨V, hV⟩).1 := by
        simpa [F, x] using
          val_eq_of_section_of_compactOpenIntersectionDiagram S hDirected s U₀ ⟨V, hV⟩
      exact hUV ▸ ((s : ∀ U : S, F.obj U) ⟨V, hV⟩).2
    have hxW : x ∈ W := by
      rw [hW]
      simpa [Set.mem_iInter] using hx_mem
    refine ⟨⟨x, hxW⟩, ?_⟩
    apply Subtype.ext
    funext V
    apply Subtype.ext
    change x = ((s : ∀ U : S, F.obj U) V).1
    simpa [F, x] using
      val_eq_of_section_of_compactOpenIntersectionDiagram S hDirected s U₀ V

private theorem compactOpenIntersectionCone_pt_eq_iInf_induced
    (W : Set X) (S : Set (CompactOpens X)) (hS_nonempty : S.Nonempty)
    (hW : W = ⋂ U ∈ S, (U : Set X)) :
    (compactOpenIntersectionCone W S hW).pt.str =
      ⨅ U : S, ((compactOpenIntersectionDiagram S).obj U).str.induced
        ((compactOpenIntersectionCone W S hW).π.app U) := by
  classical
  let U₀ : S := Classical.choice hS_nonempty.to_subtype
  have hinduced :
      ∀ U : S,
        ((compactOpenIntersectionDiagram S).obj U).str.induced
            ((compactOpenIntersectionCone W S hW).π.app U) =
          (compactOpenIntersectionCone W S hW).pt.str := by
    intro U
    simpa [compactOpenIntersectionCone] using induced_compactOpenIntersectionConeApp W S hW U
  apply le_antisymm
  · exact le_iInf fun U ↦ (hinduced U).ge
  · exact (iInf_le (fun U : S ↦
      ((compactOpenIntersectionDiagram S).obj U).str.induced
        ((compactOpenIntersectionCone W S hW).π.app U)) U₀).trans (hinduced U₀).le

/-- Lemma 5.24.7 (b): a directed nonempty intersection of quasi-compact opens is the inverse
limit of the associated diagram of open subspaces, expressed by the canonical cone. -/
def isLimit_compactOpenIntersectionCone_of_directed
    (W : Set X) (S : Set (CompactOpens X)) (hS_nonempty : S.Nonempty)
    (hW : W = ⋂ U ∈ S, (U : Set X)) (hDirected : DirectedOn (· ≥ ·) S) :
    IsLimit (compactOpenIntersectionCone W S hW) := by
  classical
  let hforget :=
    isLimit_compactOpenIntersectionCone_of_directed_forget W S hS_nonempty hW hDirected
  exact Classical.choice <|
    (TopCat.nonempty_isLimit_iff_eq_induced (compactOpenIntersectionCone W S hW) hforget).2
      (compactOpenIntersectionCone_pt_eq_iInf_induced W S hS_nonempty hW)

end

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

-- Proof sketch: compare the five clauses by the Stacks argument. Constructible-topology closedness
-- gives quasi-compactness via the compact constructible topology; quasi-compact generalizing
-- subsets are sets of specializations of quasi-compact subsets and hence intersections of
-- quasi-compact opens; finite-intersection refinements package such intersections into a directed
-- family of compact opens.
/-- A subset presented as an intersection of constructible subsets. -/
def constructibleIntersectionPresentation (W : Set X) : Prop :=
  ∃ S : Set (Set X), (∀ Z ∈ S, IsConstructible Z) ∧ W = ⋂₀ S

/-- Lemma 5.24.7 (1): `W` is an intersection of constructible subsets and is stable under
generalization. -/
def compactGeneralizingClause1 (W : Set X) : Prop :=
  constructibleIntersectionPresentation W ∧ StableUnderGeneralization W

/-- Lemma 5.24.7 (2): `W` is quasi-compact and is stable under generalization. -/
def compactGeneralizingClause2 (W : Set X) : Prop :=
  IsCompact W ∧ StableUnderGeneralization W

/-- Lemma 5.24.7 (3): `W` is the set of points specializing to a quasi-compact subset. -/
def compactGeneralizingClause3 (W : Set X) : Prop :=
  ∃ E : Set X, IsCompact E ∧ W = nhdsKer E

/-- Lemma 5.24.7 (4): `W` is an intersection of quasi-compact open subsets. -/
def compactGeneralizingClause4 (W : Set X) : Prop :=
  ∃ S : Set (CompactOpens X), W = ⋂ U ∈ S, (U : Set X)

/-- A subset is the directed intersection of the displayed family of compact open subsets. -/
def IsDirectedCompactOpenIntersection
    (W : Set X) (S : Set (CompactOpens X)) : Prop :=
  W = ⋂ U ∈ S, (U : Set X) ∧ DirectedOn (· ≥ ·) S

/-- Lemma 5.24.7 (5): `W` is the intersection of a directed nonempty family of quasi-compact
open subsets. -/
def compactGeneralizingClause5 (W : Set X) : Prop :=
  ∃ S : Set (CompactOpens X), S.Nonempty ∧ IsDirectedCompactOpenIntersection W S

/-- Helper for Lemma 5.24.7: the specialization closure `nhdsKer E` of a compact subset is the
intersection of all compact opens containing that subset. -/
private theorem nhdsKer_eq_iInter_compactOpens_of_isCompact (E : Set X) (hE : IsCompact E) :
    nhdsKer E = ⋂ U ∈ { V : CompactOpens X | E ⊆ (V : Set X) }, (U : Set X) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_iInter]
    intro U
    rw [Set.mem_iInter]
    intro hEU
    have hx_singleton : ({x} : Set X) ⊆ nhdsKer E := by
      simpa [Set.singleton_subset_iff] using hx
    exact (subset_nhdsKer_iff.mp hx_singleton) (U : Set X) U.isOpen hEU (by simp)
  · intro hx
    -- To prove `x ∈ nhdsKer E`, it suffices to check every open neighborhood of `E`.
    rw [← Set.singleton_subset_iff, subset_nhdsKer_iff]
    intro O hO hEO
    obtain ⟨V, hV_compact, hV_open, hEV, hVO⟩ :=
      PrespectralSpace.exists_isCompact_and_isOpen_between hE hO hEO
    let K : CompactOpens X := ⟨⟨V, hV_compact⟩, hV_open⟩
    have hxK : x ∈ (K : Set X) := by
      have hx' :
          ∀ U : CompactOpens X, U ∈ { V : CompactOpens X | E ⊆ (V : Set X) } →
            x ∈ (U : Set X) := by
        simpa [Set.mem_iInter] using hx
      exact hx' K hEV
    exact Set.singleton_subset_iff.2 (hVO hxK)

-- Proof sketch: prove the TFAE chain from the Stacks argument, using
-- `isClosed_constructibleTopology_iff_eq_sInter_constructible` to pass between constructible
-- presentations and constructible-topology closedness, and then the compact-open intersection
-- criteria developed above.
/-- The five clause predicates attached to Lemma 5.24.7 are equivalent. -/
theorem compact_generalizing_subset_tfae (W : Set X) :
    List.TFAE
      [ compactGeneralizingClause1 W,
        compactGeneralizingClause2 W,
        compactGeneralizingClause3 W,
        compactGeneralizingClause4 W,
        compactGeneralizingClause5 W ] :=
  by
  tfae_have 1 → 2 := by
    rintro ⟨hPresentation, hGen⟩
    have hPatchClosed : IsClosed[constructibleTopology X] W := by
      exact (isClosed_constructibleTopology_iff_eq_sInter_constructible W).2 hPresentation
    have hPatchCompact : @IsCompact X (constructibleTopology X) W := by
      exact
        @IsClosed.isCompact X (constructibleTopology X)
          W constructibleTopology_compactSpace_of_spectralSpace hPatchClosed
    have hContToOriginal : @Continuous X X (constructibleTopology X) ‹TopologicalSpace X› id := by
      rw [continuous_def]
      intro s hs
      exact isOpen_constructibleTopology_of_isOpen hs
    -- Transport compactness back to the original topology along the identity map.
    refine ⟨by
      simpa using
        @IsCompact.image X X (constructibleTopology X) ‹TopologicalSpace X› W id
          hPatchCompact hContToOriginal, hGen⟩
  tfae_have 2 → 3 := by
    rintro ⟨hCompact, hGen⟩
    refine ⟨W, hCompact, ?_⟩
    apply subset_antisymm
    · exact subset_nhdsKer
    · intro x hx
      rcases mem_nhdsKer_iff_specializes.mp hx with ⟨y, hyW, hxy⟩
      exact hGen hxy hyW
  tfae_have 3 → 5 := by
    rintro ⟨E, hE, rfl⟩
    let S : Set (CompactOpens X) := { U : CompactOpens X | E ⊆ (U : Set X) }
    refine ⟨S, ?_, ?_⟩
    · exact ⟨⊤, by simp [S]⟩
    · refine ⟨nhdsKer_eq_iInter_compactOpens_of_isCompact E hE, ?_⟩
      intro U hU V hV
      refine ⟨U ⊓ V, ?_, inf_le_left, inf_le_right⟩
      intro x hx
      simpa [CompactOpens.coe_inf] using ⟨hU hx, hV hx⟩
  tfae_have 5 → 4 := by
    rintro ⟨S, _hS, hWS⟩
    exact ⟨S, hWS.1⟩
  tfae_have 4 → 1 := by
    rintro ⟨S, hW⟩
    let T : Set (Set X) := Set.range fun U : S ↦ ((U.1 : CompactOpens X) : Set X)
    refine ⟨?_, ?_⟩
    · refine ⟨T, ?_, ?_⟩
      · intro Z hZ
        rcases hZ with ⟨U, rfl⟩
        exact U.1.isCompact.isConstructible U.1.isOpen
      · ext x
        rw [hW]
        simp [T, Set.mem_iInter]
    · intro x y hxy hy
      rw [hW] at hy ⊢
      have hy' : ∀ V : CompactOpens X, V ∈ S → x ∈ (V : Set X) := by
        simpa [Set.mem_iInter] using hy
      exact
        Set.mem_iInter.2 fun V ↦
          Set.mem_iInter.2 fun hV ↦
            V.isOpen.stableUnderGeneralization hxy (hy' V hV)
  tfae_finish

/-- Lemma 5.24.7 (a): a directed nonempty intersection of quasi-compact opens in a spectral
space is spectral. -/
theorem spectralSpace_of_compactOpenDirectedIntersection
    (W : Set X) (S : Set (CompactOpens X)) (hS_nonempty : S.Nonempty)
    (hW : W = ⋂ U ∈ S, (U : Set X)) (hDirected : DirectedOn (· ≥ ·) S) :
    SpectralSpace W := by
  letI : Nonempty S := hS_nonempty.to_subtype
  letI : IsCodirectedOrder S :=
    directedOn_univ_iff.mp fun U _ V _ ↦ by
      obtain ⟨Z, hZS, hZU, hZV⟩ := hDirected U.1 U.2 V.1 V.2
      exact ⟨⟨Z, hZS⟩, trivial, hZU, hZV⟩
  letI (U : S) : SpectralSpace ↥((compactOpenIntersectionDiagram S).obj U) := by
    letI : CompactSpace ↥((Opens.toTopCat (TopCat.of X)).obj U.1.toOpens) := by
      change CompactSpace ↥(U.1.toOpens)
      exact isCompact_iff_compactSpace.mp U.1.isCompact
    let V : Opens (TopCat.of X) := U.1.toOpens
    have hOpenEmbedding : IsOpenEmbedding (Opens.inclusion' V) :=
      Opens.isOpenEmbedding V
    exact hOpenEmbedding.spectralSpace
  have hF : ∀ ⦃U V : S⦄ (hUV : U ⟶ V), IsSpectralMap ((compactOpenIntersectionDiagram S).map hUV) := by
    intro U V hUV
    have hOpenEmbedding :
        IsOpenEmbedding ((compactOpenIntersectionDiagram S).map hUV) := by
      simpa [compactOpenIntersectionDiagram, compactOpenDiagram] using
        (Opens.isOpenEmbedding_of_le (show U.1.toOpens ≤ V.1.toOpens from hUV.le))
    refine ⟨hOpenEmbedding.continuous, fun T hT_open hT_comp ↦ ?_⟩
    have hT_retro : IsRetrocompact T :=
      (QuasiSeparatedSpace.isRetrocompact_iff_isCompact hT_open).2 hT_comp
    have hpre_retro :
        IsRetrocompact (((compactOpenIntersectionDiagram S).map hUV) ⁻¹' T) :=
      hT_retro.preimage_of_isOpenEmbedding hOpenEmbedding
    exact
      (QuasiSeparatedSpace.isRetrocompact_iff_isCompact
        (hT_open.preimage hOpenEmbedding.continuous)).1 hpre_retro
  haveI : SpectralSpace ↥((TopCat.limitCone (compactOpenIntersectionDiagram S)).pt) :=
    spectralSpace_of_isLimit_of_cofiltered_spectral_diagram
      (TopCat.limitConeIsLimit (compactOpenIntersectionDiagram S)) hF
  have e : W ≃ₜ ↥((TopCat.limitCone (compactOpenIntersectionDiagram S)).pt) := by
    simpa [compactOpenIntersectionCone] using
      TopCat.homeoOfIso
        (IsLimit.conePointUniqueUpToIso
          (isLimit_compactOpenIntersectionCone_of_directed W S hS_nonempty hW hDirected)
          (TopCat.limitConeIsLimit (compactOpenIntersectionDiagram S)))
  letI : CompactSpace W := e.symm.compactSpace
  exact e.isOpenEmbedding.spectralSpace

-- Proof sketch: intersect each stage `U ∈ S` with the closed complement of the ambient open
-- neighborhood; the resulting constructible subsets have empty intersection in the spectral
-- complement, so quasi-compactness of the constructible topology yields one stage already
-- contained in the neighborhood.
/-- Any open neighborhood of a directed nonempty compact-open intersection contains one stage of
the presentation. -/
theorem exists_stage_subset_of_isOpen_of_compactOpenDirectedIntersection
    (W : Set X) (S : Set (CompactOpens X)) (hS_nonempty : S.Nonempty)
    (hW : W = ⋂ U ∈ S, (U : Set X)) (hDirected : DirectedOn (· ≥ ·) S) {U : Set X}
    (hU : IsOpen U) (hWU : W ⊆ U) :
    ∃ V : CompactOpens X, V ∈ S ∧ (V : Set X) ⊆ U := by
  let Z : Set X := Uᶜ
  have hZ_closed_patch : IsClosed[constructibleTopology X] Z := by
    exact @IsOpen.isClosed_compl X (constructibleTopology X) U
      (isOpen_constructibleTopology_of_isOpen hU)
  let _ : SpectralSpace Z := spectralSpace_subtype_of_isClosed_constructibleTopology hZ_closed_patch
  let T : { V : CompactOpens X // V ∈ S } → Set Z := fun V ↦ Subtype.val ⁻¹' (V.1 : Set X)
  have hT_closed_patch :
      ∀ V : { V : CompactOpens X // V ∈ S }, IsClosed[constructibleTopology Z] (T V) := by
    intro V
    have hTV_open : IsOpen (T V) := V.1.isOpen.preimage continuous_subtype_val
    have hTV_compact : IsCompact (T V) := by
      have hImageCompact : IsCompact ((V.1 : Set X) ∩ Z) := by
        simpa [Z, Set.inter_comm] using V.1.isCompact.inter_right hU.isClosed_compl
      rw [Subtype.isCompact_iff]
      simpa [T, Set.image_preimage_eq_inter_range, Subtype.range_val, Set.inter_assoc,
        Set.inter_comm, Set.inter_left_comm] using hImageCompact
    have hTV_constructible : IsConstructible (T V) := hTV_compact.isConstructible hTV_open
    exact (isClopen_constructibleTopology_of_isConstructible hTV_constructible).1
  have hInter_empty : (⋂ V, T V) = (∅ : Set Z) := by
    ext z
    constructor
    · intro hz
      have hz_all : ∀ V : CompactOpens X, V ∈ S → (z : X) ∈ (V : Set X) := by
        intro V hV
        exact Set.mem_iInter.1 hz ⟨V, hV⟩
      have hzW : (z : X) ∈ W := by
        rw [hW]
        simpa [Set.mem_iInter] using hz_all
      exact (z.2 (hWU hzW)).elim
    · simp
  have hFinite_empty :
      ∃ t : Finset { V : CompactOpens X // V ∈ S }, (⋂ V ∈ t, T V) = (∅ : Set Z) := by
    have hPatchCompactZ : @CompactSpace Z (constructibleTopology Z) :=
      constructibleTopology_compactSpace_of_spectralSpace
    have hEmpty' : ((Set.univ : Set Z) ∩ ⋂ V, T V) = (∅ : Set Z) := by
      simp [hInter_empty]
    letI : TopologicalSpace Z := constructibleTopology Z
    letI : CompactSpace Z := hPatchCompactZ
    obtain ⟨t, ht⟩ :=
      (show IsCompact (Set.univ : Set Z) from isCompact_univ).elim_finite_subfamily_closed T
        (fun i ↦ show IsClosed (T i) from hT_closed_patch i) hEmpty'
    exact ⟨t, by simpa using ht⟩
  obtain ⟨t, ht⟩ := hFinite_empty
  have hRefine :
      ∀ t : Finset { V : CompactOpens X // V ∈ S },
        ∃ V : CompactOpens X, V ∈ S ∧ ∀ i ∈ t, V ≤ i.1 := by
    intro t
    classical
    induction t using Finset.induction_on with
    | empty =>
        rcases hS_nonempty with ⟨V, hV⟩
        exact ⟨V, hV, by intro i hi; simp at hi⟩
    | @insert i t hi ih =>
        rcases ih with ⟨V, hVS, hVle⟩
        obtain ⟨W', hW'S, hW'i, hW'V⟩ := hDirected i.1 i.2 V hVS
        refine ⟨W', hW'S, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjt
        · exact hW'i
        · exact hW'V.trans (hVle j hjt)
  obtain ⟨V, hVS, hVle⟩ := hRefine t
  have hTV_empty : T ⟨V, hVS⟩ = (∅ : Set Z) := by
    ext z
    constructor
    · intro hz
      have hzFinite : z ∈ ⋂ i ∈ t, T i := by
        refine Set.mem_iInter.2 fun i ↦ Set.mem_iInter.2 fun hi ↦ ?_
        exact hVle i hi hz
      have : False := by
        simp [ht] at hzFinite
      exact this.elim
    · simp
  refine ⟨V, hVS, ?_⟩
  intro x hxV
  by_contra hxU
  have hxTrace : (⟨x, hxU⟩ : Z) ∈ T ⟨V, hVS⟩ := hxV
  simp [hTV_empty] at hxTrace

end
