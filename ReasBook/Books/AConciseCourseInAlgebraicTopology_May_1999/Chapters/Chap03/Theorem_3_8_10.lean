import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Separation.Connected
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Example_3_1_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_7_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Corollary_3_7_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_8_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Proposition_3_8_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_8_10.ConnectedCovering

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open scoped FundamentalGroup

variable {B : Type u} [TopologicalSpace B]

namespace IsUniversalCoveringMap

variable {E : Type u} [TopologicalSpace E] [LocPathConnectedSpace E] {p : C(E, B)}

/-- The fundamental group of the base acts on a universal cover through deck transformations. -/
noncomputable instance universalCoverDeckMulAction
    [hp : IsUniversalCoveringMap p] (e : E) :
    MulAction (FundamentalGroup B (p e)) E :=
  MulAction.compHom E
    ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm.toMonoidHom)

private noncomputable abbrev universalCoverDeckMulActionOf
    (hp : IsUniversalCoveringMap p) (e : E) :
    MulAction (FundamentalGroup B (p e)) E :=
  letI : IsUniversalCoveringMap p := hp
  universalCoverDeckMulAction e

/-- The deck action of `π₁(B, p e)` is evaluation of the corresponding deck transformation. -/
theorem universalCoverDeck_smul_def
    [hp : IsUniversalCoveringMap p] (e : E) (γ : FundamentalGroup B (p e)) (x : E) :
    γ • x =
      ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ) • x := rfl

/-- Deck transformations coming from `π₁(B, p e)` preserve the universal-cover projection. -/
theorem universalCoverDeck_smul_proj
    [hp : IsUniversalCoveringMap p] (e : E) (γ : FundamentalGroup B (p e)) (x : E) :
    p (γ • x) = p x := by
  have hcomm :=
    congrArg (fun f : TopCat.of E ⟶ TopCat.of B ↦ f.hom x)
      (Over.w ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ).hom)
  simpa [ContinuousMap.comp_apply, universalCoverDeck_smul_def] using hcomm

/-- Each deck transformation of a universal cover acts by a homeomorphism, so the induced
fundamental-group action is continuous in each group variable. -/
-- Proof sketch: transport the continuous deck-transformation action of
-- `CoveringSpaceAut p` along the canonical group isomorphism with `π₁(B, p e)`.
instance universalCoverDeckContinuousConstSMul
    [hp : IsUniversalCoveringMap p] (e : E) :
    ContinuousConstSMul (FundamentalGroup B (p e)) E := by
  refine ⟨?_⟩
  intro γ
  -- Transport continuity of the corresponding deck transformation along the universal-cover
  -- automorphism/fundamental-group identification.
  simpa [universalCoverDeck_smul_def] using
    ((((coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ).hom.left.hom).continuous :
      Continuous fun x : E ↦
        ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ) • x)

/-- Helper for Theorem 3.8.10: the transported deck action of `π₁(B, p e)` on the universal
cover is free, so equality of two translates at one point forces equality of the deck elements. -/
instance universalCoverDeck_isCancelSMul
    [hp : IsUniversalCoveringMap p] (e : E) :
    IsCancelSMul (FundamentalGroup B (p e)) E := by
  refine
    { right_cancel' := ?_ }
  intro γ₁ γ₂ x hγ
  let α₁ : CoveringSpaceAut p :=
    (coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ₁
  let α₂ : CoveringSpaceAut p :=
    (coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ₂
  have hα :
      α₁.hom.left.hom x = α₂.hom.left.hom x := by
    simpa [α₁, α₂, universalCoverDeck_smul_def] using hγ
  let x₀ : p ⁻¹' {p x} := ⟨x, rfl⟩
  let y₀ : p ⁻¹' {p x} := ⟨α₁.hom.left.hom x, by
    have hproj : p (α₁.hom.left.hom x) = p x := by
      have hcomm := congrArg (fun f : TopCat.of E ⟶ TopCat.of B ↦ f.hom x) (Over.w α₁.hom)
      simpa [ContinuousMap.comp_apply] using hcomm
    simpa [x₀] using hproj⟩
  have hsub :
      (FundamentalGroup.mapOfEq p x₀.2).range ≤
        (FundamentalGroup.mapOfEq p y₀.2).range := by
    rw [hp.fundamentalGroup_mapOfEq_range_eq_bot x₀]
    exact bot_le
  rcases
    (IsPathConnectedCoveringMap.existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
      hp.isPathConnectedCoveringMap (p x) x₀ y₀).2 hsub with
    ⟨h₀, hh₀, huniq⟩
  have hα₁ : α₁.hom.left.hom x = y₀.1 := rfl
  have hα₂ : α₂.hom.left.hom x = y₀.1 := by
    simpa [y₀] using hα.symm
  have hEq : α₁.hom = α₂.hom := by
    exact (huniq α₁.hom hα₁).trans (huniq α₂.hom hα₂).symm
  have hIso : α₁ = α₂ := by
    apply CategoryTheory.Iso.ext
    simpa using hEq
  have hγeq := congrArg (coveringSpaceAutMulEquivFundamentalGroup hp e) hIso
  simpa [α₁, α₂] using hγeq

/-- Helper for Theorem 3.8.10: around any point of the universal cover there is a single sheet of
an evenly covered neighborhood whose nontrivial deck translates are disjoint from it. -/
theorem universalCoverDeck_exists_nhds_disjoint_image
    [hp : IsUniversalCoveringMap p] (e : E) (x : E) :
    ∃ U ∈ nhds x, ∀ γ : FundamentalGroup B (p e), γ • x ≠ x → Disjoint ((γ • ·) '' U) U := by
  letI : IsCancelSMul (FundamentalGroup B (p e)) E := universalCoverDeck_isCancelSMul e
  let hx := hp.isPathConnectedCoveringMap.2 (p x)
  letI : Nonempty (p ⁻¹' {p x}) := ⟨⟨x, rfl⟩⟩
  letI : DiscreteTopology (p ⁻¹' {p x}) := hx.isEvenlyCovered.1
  let t : Bundle.Trivialization (p ⁻¹' {p x}) p := hx.isEvenlyCovered.toTrivialization
  let U : Set E := t.source ∩ (Prod.snd ∘ t) ⁻¹' {⟨x, rfl⟩}
  have hUopen : IsOpen U := by
    exact t.continuousOn_toFun.isOpen_inter_preimage t.open_source
      (continuous_snd.isOpen_preimage _ <| isOpen_discrete _)
  have hxbase : p x ∈ t.baseSet := hx.isEvenlyCovered.mem_toTrivialization_baseSet
  have hxts : x ∈ t.source := by
    exact t.mem_source.mpr hxbase
  have hxU : x ∈ U := by
    refine ⟨hxts, ?_⟩
    simpa [t, hxts] using hx.isEvenlyCovered.toTrivialization_apply
  refine ⟨U, hUopen.mem_nhds hxU, ?_⟩
  intro γ hγ
  refine Set.disjoint_left.mpr ?_
  intro y hyγ hyU
  rcases hyγ with ⟨z, hzU, rfl⟩
  have hzts : z ∈ t.source := hzU.1
  have hγzts : γ • z ∈ t.source := hyU.1
  have hp_eq : p (γ • z) = p z := universalCoverDeck_smul_proj e γ z
  have hzsnd : (t z).2 = ⟨x, rfl⟩ := by
    simpa [U] using hzU.2
  have hγzsnd : (t (γ • z)).2 = ⟨x, rfl⟩ := by
    simpa [U] using hyU.2
  have ht_eq : t z = t (γ • z) := by
    ext
    ·
      have hfst_z : (t z).1 = p z := t.proj_toFun z hzts
      have hfst_γz : (t (γ • z)).1 = p (γ • z) := t.proj_toFun (γ • z) hγzts
      calc
        (t z).1 = p z := hfst_z
        _ = p (γ • z) := hp_eq.symm
        _ = (t (γ • z)).1 := hfst_γz.symm
    · exact (congrArg Subtype.val hzsnd).trans (congrArg Subtype.val hγzsnd).symm
  have hfix : z = γ • z := t.injOn hzts hγzts ht_eq
  exact hγ <| by
    have hγeq1 : γ = 1 := IsCancelSMul.eq_one_of_smul hfix.symm
    simp [hγeq1]

/-- The orbit space `E / H` of a universal cover by a subgroup of its deck group. -/
noncomputable abbrev universalCoverOrbit
    [IsUniversalCoveringMap p] (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) : Type u :=
  E /[H]

noncomputable instance
    [IsUniversalCoveringMap p] (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    TopologicalSpace (universalCoverOrbit e H) := by
  change TopologicalSpace (E /[H])
  infer_instance

noncomputable instance
    [IsUniversalCoveringMap p] (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    PathConnectedSpace (universalCoverOrbit e H) := by
  change PathConnectedSpace (Quotient (MulAction.orbitRel H E))
  exact Quotient.mk''_surjective.pathConnectedSpace continuous_quotient_mk'

/-- Helper for Theorem 3.8.10: quotienting the universal cover by a subgroup of deck
transformations preserves local path connectedness, because the quotient map is an open quotient
of a locally path-connected space. -/
noncomputable instance
    [IsUniversalCoveringMap p] (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    LocPathConnectedSpace (universalCoverOrbit e H) := by
  let q : E → universalCoverOrbit e H := Quotient.mk''
  exact (isQuotientMap_quotient_mk' : Topology.IsQuotientMap q).locPathConnectedSpace

/-- The canonical orbit class of the chosen point `e` in the quotient `E / H`. -/
noncomputable abbrev universalCoverOrbitPoint
    [IsUniversalCoveringMap p] (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    universalCoverOrbit e H :=
  Quotient.mk'' e

/-- The universal covering projection is constant on orbits of any subgroup of the deck group. -/
-- Proof sketch: points in the same orbit differ by a deck transformation of the universal cover,
-- and every deck transformation lies over the identity on the base.
private theorem universalCoverOrbitProjection_eq_of_orbitRel
    [hp : IsUniversalCoveringMap p] (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {x y : E}
    (hxy : MulAction.orbitRel H E x y) :
    p x = p y := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
  obtain ⟨γ, rfl⟩ := hxy
  exact universalCoverDeck_smul_proj e (γ : FundamentalGroup B (p e)) y

/-- The quotient covering `E / H → B` attached to a subgroup of the deck group of a universal
cover. -/
noncomputable def universalCoverOrbitProjection
    [hp : IsUniversalCoveringMap p] (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    C(universalCoverOrbit e H, B) :=
  ⟨fun q ↦ Quotient.liftOn' q p
      (fun _ _ hxy ↦ universalCoverOrbitProjection_eq_of_orbitRel e H hxy),
    continuous_quot_lift
      (fun _ _ hxy ↦ universalCoverOrbitProjection_eq_of_orbitRel e H hxy)
      p.continuous⟩

/-- The canonical orbit point of `e` lies over the basepoint `p e`. -/
@[simp] theorem universalCoverOrbitProjection_point
    [IsUniversalCoveringMap p] (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    universalCoverOrbitProjection e H (universalCoverOrbitPoint e H) = p e :=
  rfl

/-- Helper for Theorem 3.8.10: the raw quotient map `E → E / H` coming from the subgroup deck
action is itself a path-connected covering map. -/
private theorem universalCoverOrbitQuotientMap_isPathConnectedCoveringMap
    [hp : IsUniversalCoveringMap p] (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    IsPathConnectedCoveringMap (Quotient.mk'' : E → universalCoverOrbit e H) := by
  letI : ContinuousConstSMul (FundamentalGroup B (p e)) E :=
    universalCoverDeckContinuousConstSMul e
  -- Local instance justification (proof-local temporary data): the subgroup action on `E`
  -- inherits continuity from the ambient deck action only for this quotient-cover proof.
  letI : ContinuousConstSMul H E :=
    { continuous_const_smul := fun γ ↦ continuous_const_smul (γ : FundamentalGroup B (p e)) }
  letI : IsCancelSMul (FundamentalGroup B (p e)) E := universalCoverDeck_isCancelSMul e
  -- Local instance justification (proof-local temporary data): the subgroup action on `E`
  -- inherits freeness from the ambient deck action only for this quotient-cover proof.
  letI : IsCancelSMul H E :=
    { right_cancel' := by
        intro γ₁ γ₂ x hγ
        apply Subtype.ext
        exact IsCancelSMul.right_cancel (γ₁ : FundamentalGroup B (p e))
          (γ₂ : FundamentalGroup B (p e)) x hγ }
  let q : E → universalCoverOrbit e H := Quotient.mk''
  have hcoverOn :
      IsCoveringMapOn q (q '' {x | MulAction.stabilizer H x = ⊥}) :=
    (isQuotientMap_quotient_mk' : Topology.IsQuotientMap q).isCoveringMapOn_of_smul_disjoint
      (fun {e₁ e₂} ↦ (Quotient.eq'' : q e₁ = q e₂ ↔ e₁ ∈ MulAction.orbit H e₂))
      (fun x ↦ by
        -- The already-proved disjoint-translate neighborhood for the full deck action restricts
        -- to the subgroup action and gives the sheet-level disjointness required by the quotient
        -- covering criterion.
        have hdisj :
            ∃ U ∈ nhds x,
              ∀ γ : FundamentalGroup B (p e), γ • x ≠ x → Disjoint ((γ • ·) '' U) U :=
          universalCoverDeck_exists_nhds_disjoint_image e x
        rcases hdisj with ⟨U, hU, hUdisj⟩
        refine ⟨U, hU, ?_⟩
        intro γ hγ
        by_contra hfix
        exact hγ.ne_empty <|
          Set.disjoint_iff_inter_eq_empty.mp (hUdisj (γ : FundamentalGroup B (p e)) hfix))
  have hfree : {x : E | MulAction.stabilizer H x = ⊥} = Set.univ := by
    ext x
    simp
  have hsurj : Function.Surjective q := Quotient.mk''_surjective
  have hcover : IsCoveringMap q := by
    rw [isCoveringMap_iff_isCoveringMapOn_univ]
    simpa [hfree, hsurj.range_eq] using hcoverOn
  letI : LocPathConnectedSpace (universalCoverOrbit e H) :=
    (isQuotientMap_quotient_mk' : Topology.IsQuotientMap q).locPathConnectedSpace
  -- Once the quotient map is known to be a covering map, local path connectedness of the orbit
  -- space upgrades it to the source-facing `IsPathConnectedCoveringMap` owner.
  exact IsCoveringMap.isPathConnectedCoveringMap hcover hsurj

/-- Helper for Theorem 3.8.10: factoring the universal covering projection through the subgroup
quotient shows that `E / H → B` is at least a local homeomorphism. -/
private theorem universalCoverOrbitProjection_isLocalHomeomorph
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    IsLocalHomeomorph (universalCoverOrbitProjection e H) := by
  letI : IsUniversalCoveringMap p := hp
  letI : LocPathConnectedSpace E := inferInstance
  letI := universalCoverDeckMulActionOf hp e
  let q : E → universalCoverOrbit e H := Quotient.mk''
  have hcomp : universalCoverOrbitProjection e H ∘ q = p := by
    funext x
    rfl
  have hqCover : IsCoveringMap q :=
    IsPathConnectedCoveringMap.isCoveringMap
      (universalCoverOrbitQuotientMap_isPathConnectedCoveringMap e H)
  have hq :
      IsLocalHomeomorph q :=
    hqCover.isLocalHomeomorph
  have hcompLocal :
      IsLocalHomeomorph (universalCoverOrbitProjection e H ∘ q) := by
    simpa [hcomp] using
      (IsPathConnectedCoveringMap.isCoveringMap hp.isPathConnectedCoveringMap).isLocalHomeomorph
  have hbarOn :
      IsLocalHomeomorphOn (universalCoverOrbitProjection e H) (q '' Set.univ) :=
    hcompLocal.isLocalHomeomorphOn.of_comp_right hq.isLocalHomeomorphOn
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  simpa [q, Quotient.mk''_surjective.range_eq] using hbarOn

theorem baseLocPathConnectedSpace
    (hp : IsUniversalCoveringMap p) :
    LocPathConnectedSpace B := by
  -- The universal covering projection is a surjective quotient map from a locally
  -- path-connected space, so local path connectedness descends to the base.
  exact (hp.isCoveringMap.isQuotientMap hp.surjective).locPathConnectedSpace

/-- Helper for Theorem 3.8.10: a path-connected covering over a locally path-connected base has
locally path-connected total space. -/
theorem IsPathConnectedCoveringMap.locPathConnectedSpace_totalSpace
    {Y : Type u} [TopologicalSpace Y] {q : C(Y, B)}
    [LocPathConnectedSpace B] (hq : IsPathConnectedCoveringMap q) :
    LocPathConnectedSpace Y := by
  rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro y u hu hyu
  rcases hq.2 (q y) with
    ⟨hdisc, V, hyV, hVOpen, hVPath, hpreVOpen, T, hT⟩
  let yV : q ⁻¹' V := ⟨y, hyV⟩
  let ξ₀ : q ⁻¹' ({q y} : Set B) := (T yV).2
  let sheetMap : V → Y := fun v ↦ (T.symm (v, ξ₀)).1
  have hProdOpenEmbedding :
      Topology.IsOpenEmbedding
        ((fun v : V ↦ (v, ξ₀)) : V → V × (q ⁻¹' ({q y} : Set B))) := by
    have hRangeOpen :
        IsOpen
          (Set.range
            (((fun v : V ↦ (v, ξ₀)) : V → V × (q ⁻¹' ({q y} : Set B))))) := by
      have hRange :
          Set.range
              (((fun v : V ↦ (v, ξ₀)) : V → V × (q ⁻¹' ({q y} : Set B)))) =
            Set.univ ×ˢ ({ξ₀} : Set (q ⁻¹' ({q y} : Set B))) := by
        ext x
        constructor
        · rintro ⟨v, rfl⟩
          exact ⟨Set.mem_univ _, rfl⟩
        · rintro ⟨-, hx⟩
          rcases x with ⟨v, ξ⟩
          have hξ : ξ = ξ₀ := by simpa using hx
          cases hξ
          exact ⟨v, rfl⟩
      rw [hRange]
      simpa using
        (isOpen_univ.prod
          (show IsOpen ({ξ₀} : Set (q ⁻¹' ({q y} : Set B))) from isOpen_discrete _))
    exact ⟨isEmbedding_prodMkLeft ξ₀, hRangeOpen⟩
  have hSheetOpenEmbedding : Topology.IsOpenEmbedding sheetMap := by
    simpa [sheetMap, Function.comp] using
      (hpreVOpen.isOpenEmbedding_subtypeVal.comp T.symm.isOpenEmbedding).comp hProdOpenEmbedding
  have hTy :
      T yV = (⟨q y, hyV⟩, ξ₀) := by
    ext
    · simpa using hT yV
    · rfl
  have hySheet : y ∈ Set.range sheetMap := by
    refine ⟨⟨q y, hyV⟩, ?_⟩
    have hSymm : T.symm (⟨q y, hyV⟩, ξ₀) = yV := by
      apply T.injective
      simp [hTy]
    exact congrArg Subtype.val hSymm
  haveI : LocPathConnectedSpace V := hVOpen.locPathConnectedSpace
  let hSheetHomeomorph : V ≃ₜ Set.range sheetMap :=
    (Homeomorph.Set.univ V).symm.trans <|
      (hSheetOpenEmbedding.toIsEmbedding.homeomorphImage Set.univ).trans <|
        Homeomorph.setCongr <| by
          ext z
          constructor
          · rintro ⟨w, -, rfl⟩
            exact ⟨w, rfl⟩
          · rintro ⟨w, rfl⟩
            exact ⟨w, Set.mem_univ _, rfl⟩
  have hSheetSymmOpenEmbedding : Topology.IsOpenEmbedding hSheetHomeomorph.symm :=
    hSheetHomeomorph.symm.isOpenEmbedding
  haveI : LocPathConnectedSpace (Set.range sheetMap) :=
    hSheetSymmOpenEmbedding.locPathConnectedSpace
  let ySheet : Set.range sheetMap := ⟨y, hySheet⟩
  have hpreOpen :
      IsOpen (Subtype.val ⁻¹' u : Set (Set.range sheetMap)) := by
    exact hu.preimage continuous_subtype_val
  have hyPre : ySheet ∈ (Subtype.val ⁻¹' u : Set (Set.range sheetMap)) := hyu
  have hPathNhds :
      pathComponentIn (Subtype.val ⁻¹' u : Set (Set.range sheetMap)) ySheet ∈
        nhds ySheet := by
    exact
      (locPathConnectedSpace_iff_pathComponentIn_mem_nhds.mp inferInstance)
        ySheet _ hpreOpen hyPre
  rcases mem_nhds_iff.mp hPathNhds with ⟨t, htSubset, htOpen, hyt⟩
  have hImageOpen : IsOpen (Subtype.val '' t : Set Y) := by
    simpa using hSheetOpenEmbedding.isOpen_range.isOpenMap_subtype_val _ htOpen
  have hPathImageSubset :
      Subtype.val ''
          pathComponentIn (Subtype.val ⁻¹' u : Set (Set.range sheetMap)) ySheet ⊆
        pathComponentIn u y := by
    intro z hz
    rcases hz with ⟨z', hz', rfl⟩
    have hImagePath :
        IsPathConnected
          (Subtype.val ''
            pathComponentIn (Subtype.val ⁻¹' u : Set (Set.range sheetMap)) ySheet) := by
      exact (isPathConnected_pathComponentIn hyPre).image continuous_subtype_val
    have hyImage :
        y ∈
          Subtype.val ''
            pathComponentIn (Subtype.val ⁻¹' u : Set (Set.range sheetMap)) ySheet := by
      exact ⟨ySheet, mem_pathComponentIn_self hyPre, rfl⟩
    have hImageSubsetU :
        Subtype.val ''
          pathComponentIn (Subtype.val ⁻¹' u : Set (Set.range sheetMap)) ySheet ⊆ u := by
      intro w hw
      rcases hw with ⟨w', hw', rfl⟩
      simpa using pathComponentIn_subset hw'
    exact hImagePath.subset_pathComponentIn hyImage hImageSubsetU ⟨z', hz', rfl⟩
  have hImageSubset :
      (Subtype.val '' t : Set Y) ⊆ pathComponentIn u y := by
    intro z hz
    exact hPathImageSubset (Set.image_mono htSubset hz)
  exact mem_nhds_iff.mpr ⟨Subtype.val '' t, hImageSubset, hImageOpen, ⟨ySheet, hyt, rfl⟩⟩

/-- Helper for Theorem 3.8.10: the quotient projection `E / H → B` is surjective because it still
hits every basepoint represented by the universal cover. -/
private theorem universalCoverOrbitProjection_surjective
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    Function.Surjective (universalCoverOrbitProjection e H) := by
  intro b
  rcases hp.surjective b with ⟨x, rfl⟩
  -- The quotient class of a chosen lift of `b` still projects to `b`.
  exact ⟨Quotient.mk'' x, rfl⟩

/-- Helper for Theorem 3.8.10: a local homeomorphism has discrete fibers, because each fiber maps
locally homeomorphically onto the singleton image `{z}`. -/
theorem IsLocalHomeomorph.discreteTopology_fiber
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    {r : Y → Z} (hr : IsLocalHomeomorph r) (z : Z) :
    DiscreteTopology (r ⁻¹' ({z} : Set Z)) := by
  haveI : Subsingleton (r '' (r ⁻¹' ({z} : Set Z))) :=
    ⟨fun a b ↦ by
      apply Subtype.ext
      rcases a.2 with ⟨xa, hxa, hra⟩
      rcases b.2 with ⟨xb, hxb, hrb⟩
      calc
        (a : Z) = r xa := hra.symm
        _ = z := by simpa using hxa
        _ = r xb := by simpa using hxb.symm
        _ = (b : Z) := hrb⟩
  letI : DiscreteTopology (r '' (r ⁻¹' ({z} : Set Z))) := by
    refine discreteTopology_iff_isOpen_singleton.mpr ?_
    intro a
    have hs : ({a} : Set (r '' (r ⁻¹' ({z} : Set Z)))) = Set.univ := by
      ext b
      simp [Subsingleton.elim b a]
    simp [hs]
  simpa using
    (hr.isLocalHomeomorphOn.discreteTopology_of_image :
      DiscreteTopology (r ⁻¹' ({z} : Set Z)))

/-- Helper for Theorem 3.8.10: the fibers of the orbit-cover projection are discrete, since the
projection is already known to be a local homeomorphism. -/
private theorem universalCoverOrbitProjection_discreteTopology_fiber
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) (z : B) :
    DiscreteTopology ((universalCoverOrbitProjection e H) ⁻¹' ({z} : Set B)) := by
  -- Once the quotient projection is a local homeomorphism, discreteness of each fiber is
  -- immediate from the general local-homeomorphism fiber lemma above.
  exact
    IsLocalHomeomorph.discreteTopology_fiber
      (universalCoverOrbitProjection_isLocalHomeomorph hp e H) z

private abbrev smulWith
    {G X : Type*} [Group G] (act : MulAction G X) :
    G → X → X :=
  @SMul.smul G X act.toSMul

private abbrev orbitQuotient
    {G X : Type*} [Group G] (act : MulAction G X) :=
  Quotient (@MulAction.orbitRel G X _ act)

/-- Helper for Theorem 3.8.10: the subgroup deck action preserves each fiber `p⁻¹ {z}`. -/
private theorem universalCoverDeck_smul_mem_fiber
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) (z : B)
    (γ : H) (x : p ⁻¹' ({z} : Set B)) :
    p
        (smulWith (universalCoverDeckMulActionOf hp e)
          (γ : FundamentalGroup B (p e)) x.1) = z := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  change p ((γ : FundamentalGroup B (p e)) • x.1) = z
  have hproj :
      p ((γ : FundamentalGroup B (p e)) • x.1) = p x.1 := by
    let htop :
        MulAction.orbitRel (⊤ : Subgroup (FundamentalGroup B (p e))) E
          ((γ : FundamentalGroup B (p e)) • x.1) x.1 := by
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨⟨γ, by simp⟩, rfl⟩
    simpa using universalCoverOrbitProjection_eq_of_orbitRel e ⊤ htop
  exact hproj.trans x.2

/-- Helper for Theorem 3.8.10: restricting the deck action of `H` to the fiber `p⁻¹ {z}` gives
the orbit relation used in the quotient-fiber model. -/
private noncomputable abbrev universalCoverDeckFiberMulAction
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) (z : B) :
    MulAction H (p ⁻¹' ({z} : Set B)) :=
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  { smul := fun γ x ↦
      ⟨(γ : FundamentalGroup B (p e)) • x.1,
        universalCoverDeck_smul_mem_fiber hp e H z γ x⟩
    one_smul := fun x ↦ Subtype.ext (one_smul H x.1)
    mul_smul := fun γ₁ γ₂ x ↦ Subtype.ext (mul_smul γ₁ γ₂ x.1) }

/-- Helper for Theorem 3.8.10: the subgroup deck action preserves each restricted preimage
`p⁻¹ V`. -/
private theorem universalCoverDeck_smul_mem_preimage
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) (V : Set B)
    (γ : H) (x : p ⁻¹' V) :
    p
        (smulWith (universalCoverDeckMulActionOf hp e)
          (γ : FundamentalGroup B (p e)) x.1) ∈ V := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  change p ((γ : FundamentalGroup B (p e)) • x.1) ∈ V
  have hproj :
      p ((γ : FundamentalGroup B (p e)) • x.1) = p x.1 := by
    let htop :
        MulAction.orbitRel (⊤ : Subgroup (FundamentalGroup B (p e))) E
          ((γ : FundamentalGroup B (p e)) • x.1) x.1 := by
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨⟨γ, by simp⟩, rfl⟩
    simpa using universalCoverOrbitProjection_eq_of_orbitRel e ⊤ htop
  exact hproj ▸ x.2

/-- Helper for Theorem 3.8.10: restricting the deck action of `H` to `p⁻¹ V` gives the orbit
relation used in the literal preimage of the quotient cover over `V`. -/
private noncomputable abbrev universalCoverDeckPreimageMulAction
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) (V : Set B) :
    MulAction H (p ⁻¹' V) :=
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  { smul := fun γ x ↦
      ⟨(γ : FundamentalGroup B (p e)) • x.1,
        universalCoverDeck_smul_mem_preimage hp e H V γ x⟩
    one_smul := fun x ↦ Subtype.ext (one_smul H x.1)
    mul_smul := fun γ₁ γ₂ x ↦ Subtype.ext (mul_smul γ₁ γ₂ x.1) }

/-- Helper for Theorem 3.8.10: the quotient of the restricted preimage `p⁻¹ V` is homeomorphic
to the actual preimage of `V` under the orbit-cover projection. -/
private noncomputable def universalCoverOrbitProjection_preimageHomeomorph
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hV : IsFundamentalNeighborhood p z V) :
    orbitQuotient (universalCoverDeckPreimageMulAction hp e H V) ≃ₜ
      ((universalCoverOrbitProjection e H) ⁻¹' V) := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  letI := universalCoverDeckPreimageMulAction hp e H V
  letI : ContinuousConstSMul (FundamentalGroup B (p e)) E :=
    universalCoverDeckContinuousConstSMul e
  letI : ContinuousConstSMul H E :=
    { continuous_const_smul := fun γ ↦
        continuous_const_smul (γ : FundamentalGroup B (p e)) }
  have hVOpen : IsOpen V := hV.isOpen
  let q : E → universalCoverOrbit e H := Quotient.mk''
  let s : Set (universalCoverOrbit e H) := (universalCoverOrbitProjection e H) ⁻¹' V
  let qV : p ⁻¹' V → s := fun x ↦
    ⟨q x.1, by
      change p x.1 ∈ V
      exact x.2⟩
  have hqV_isQuot : Topology.IsQuotientMap qV := by
    -- Restrict the ambient quotient map `E → E / H` to the open preimage of `V`.
    simpa [qV, q, s] using
      ((MulAction.isOpenQuotientMap_quotientMk : IsOpenQuotientMap q)).isQuotientMap
        |>.restrictPreimage_isOpen
          ((hVOpen.preimage (universalCoverOrbitProjection e H).continuous))
  have hrel :
      ∀ x y : p ⁻¹' V,
        MulAction.orbitRel H (p ⁻¹' V) x y ↔ Setoid.ker qV x y := by
    intro x y
    constructor
    · intro hxy
      apply Subtype.ext
      rw [Quotient.eq'']
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
      rcases hxy with ⟨γ, hγ⟩
      exact ⟨γ, by simpa using congrArg Subtype.val hγ⟩
    · intro hxy
      change qV x = qV y at hxy
      have hval :
          (Quotient.mk'' x.1 : universalCoverOrbit e H) = Quotient.mk'' y.1 := by
        simpa [qV] using congrArg Subtype.val hxy
      rw [Quotient.eq''] at hval
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      rcases hval with ⟨γ, hγ⟩
      exact ⟨γ, Subtype.ext hγ⟩
  have hrelEq :
      MulAction.orbitRel H (p ⁻¹' V) = Setoid.ker qV := by
    ext x y
    exact hrel x y
  -- Identify the quotient by the orbit relation with the restricted codomain via the universal
  -- property of quotient maps.
  let qVMap : C(p ⁻¹' V, s) := ⟨qV, hqV_isQuot.continuous⟩
  have hker :
      Setoid.ker qVMap = MulAction.orbitRel H (p ⁻¹' V) := by
    simpa [qVMap] using hrelEq.symm
  change Quotient (MulAction.orbitRel H (p ⁻¹' V)) ≃ₜ s
  have hhomeo : Quotient (Setoid.ker qVMap) ≃ₜ s :=
    Topology.IsQuotientMap.homeomorph hqV_isQuot
  exact hker.symm ▸ hhomeo

/-- Helper for Theorem 3.8.10: quotienting the discrete fiber `p⁻¹ {z}` by `H` gives exactly the
fiber of the descended orbit projection over `z`. -/
private noncomputable def universalCoverOrbitProjection_fiberHomeomorph
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) (z : B) :
    orbitQuotient (universalCoverDeckFiberMulAction hp e H z) ≃ₜ
      ((universalCoverOrbitProjection e H) ⁻¹' ({z} : Set B)) := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  letI := universalCoverDeckFiberMulAction hp e H z
  letI : DiscreteTopology (p ⁻¹' ({z} : Set B)) := (hp.isPathConnectedCoveringMap.2 z).1
  letI : DiscreteTopology ((p ⁻¹' ({z} : Set B)) /[H]) := by
    refine discreteTopology_iff_isOpen_singleton.mpr ?_
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    -- The quotient of a discrete fiber is discrete because the orbit of each representative is
    -- open in the source fiber.
    rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
    simp
  letI : DiscreteTopology ((universalCoverOrbitProjection e H) ⁻¹' ({z} : Set B)) :=
    universalCoverOrbitProjection_discreteTopology_fiber hp e H z
  let toFiber : ((p ⁻¹' ({z} : Set B)) /[H]) →
      ((universalCoverOrbitProjection e H) ⁻¹' ({z} : Set B)) :=
    fun q ↦
      Quotient.liftOn' q
        (fun x : p ⁻¹' ({z} : Set B) ↦
          ⟨Quotient.mk'' x.1, by
            exact x.2⟩)
        (fun x y hxy ↦ by
          -- Orbit-related points in the fiber define the same orbit point downstairs.
          apply Subtype.ext
          rw [Quotient.eq'']
          rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy ⊢
          rcases hxy with ⟨γ, hγ⟩
          exact ⟨γ, by simpa using congrArg Subtype.val hγ⟩)
  have htoFiber_bijective : Function.Bijective toFiber := by
    constructor
    · intro q₁ q₂ hq
      refine Quotient.inductionOn₂' q₁ q₂ ?_ hq
      intro x y hxy
      apply Quotient.sound
      have hval :
          (Quotient.mk'' x.1 : universalCoverOrbit e H) = Quotient.mk'' y.1 := by
        simpa using congrArg Subtype.val hxy
      rw [Quotient.eq''] at hval
      change MulAction.orbitRel H (p ⁻¹' ({z} : Set B)) x y
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hval
      rcases hval with ⟨γ, hγ⟩
      exact ⟨γ, Subtype.ext hγ⟩
    · intro y
      rcases y with ⟨q, hq⟩
      rcases Quotient.exists_rep q with ⟨x, rfl⟩
      have hx : p x = z := by
        simpa [universalCoverOrbitProjection] using hq
      refine ⟨Quotient.mk'' ⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      rfl
  refine
    { toEquiv := Equiv.ofBijective toFiber htoFiber_bijective
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

private noncomputable abbrev fundamentalNeighborhoodHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {y : Y} {V : Set Y} (hV : IsFundamentalNeighborhood f y V) :
    f ⁻¹' V ≃ₜ V × (f ⁻¹' ({y} : Set Y)) :=
  Classical.choose hV.exists_preimageHomeomorph

private theorem fundamentalNeighborhoodHomeomorph_fst
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {y : Y} {V : Set Y} (hV : IsFundamentalNeighborhood f y V)
    (x : f ⁻¹' V) :
    ((fundamentalNeighborhoodHomeomorph hV x).1 : Y) = f x :=
  Classical.choose_spec hV.exists_preimageHomeomorph x

/-- Helper for Theorem 3.8.10: in any chosen fundamental-neighborhood chart, the fiber
coordinate of a deck translate is constant across the path-connected base neighborhood. -/
private theorem universalCoverDeck_chart_secondCoord_eq_basepoint
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    [DiscreteTopology (p ⁻¹' ({z} : Set B))]
    (hzV : z ∈ V) (hVPath : IsPathConnected V)
    (T : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({z} : Set B)))
    (_hT : ∀ x, (T x).1.1 = p x)
    (γ : H) (ξ : p ⁻¹' ({z} : Set B)) (v : V) :
    (T
        ⟨smulWith (universalCoverDeckMulActionOf hp e)
            (γ : FundamentalGroup B (p e)) (T.symm (v, ξ)).1,
          universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (v, ξ))⟩).2 =
      (T
        ⟨smulWith (universalCoverDeckMulActionOf hp e)
            (γ : FundamentalGroup B (p e)) (T.symm (⟨z, hzV⟩, ξ)).1,
          universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (⟨z, hzV⟩, ξ))⟩).2 := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  change
    (T
        ⟨(γ : FundamentalGroup B (p e)) • (T.symm (v, ξ)).1,
          universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (v, ξ))⟩).2 =
      (T
        ⟨(γ : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, ξ)).1,
          universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (⟨z, hzV⟩, ξ))⟩).2
  letI : ContinuousConstSMul (FundamentalGroup B (p e)) E :=
    universalCoverDeckContinuousConstSMul e
  let f : V → p ⁻¹' ({z} : Set B) := fun v' ↦
    -- Transport the deck translate through the fixed chart and retain only the fiber coordinate.
    (T
      ⟨(γ : FundamentalGroup B (p e)) • (T.symm (v', ξ)).1,
        universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (v', ξ))⟩).2
  have hf : Continuous f := by
    -- Every ingredient is continuous: the chart inverse, constant deck translation, the chart,
    -- and the fiber-coordinate projection.
    have hpair : Continuous fun v' : V ↦ (v', ξ) :=
      continuous_id.prodMk continuous_const
    have hTsymm : Continuous T.symm := T.symm.continuous
    have hsymm : Continuous fun v' : V ↦ T.symm (v', ξ) :=
      hTsymm.comp hpair
    have hsmul : Continuous fun v' : V ↦
        (γ : FundamentalGroup B (p e)) • (T.symm (v', ξ)).1 := by
      exact
        (continuous_const_smul (γ : FundamentalGroup B (p e))).comp
          (continuous_subtype_val.comp hsymm)
    have hsmul' : Continuous fun v' : V ↦
        (⟨(γ : FundamentalGroup B (p e)) • (T.symm (v', ξ)).1,
          universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (v', ξ))⟩ : p ⁻¹' V) := by
      exact hsmul.subtype_mk fun v' ↦
        universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (v', ξ))
    have hcoord : Continuous fun x : p ⁻¹' V ↦ (T x).2 :=
      continuous_snd.comp T.continuous
    simpa [f] using hcoord.comp hsmul'
  haveI : PathConnectedSpace V := isPathConnected_iff_pathConnectedSpace.mp hVPath
  have hRangePath : IsPathConnected (Set.range f) := by
    -- The image of a path-connected space under a continuous map is path connected.
    simpa [Set.image_univ] using
      (pathConnectedSpace_iff_univ.mp (by infer_instance : PathConnectedSpace V)).image hf
  haveI : PathConnectedSpace (Set.range f) :=
    isPathConnected_iff_pathConnectedSpace.mp hRangePath
  have hRangeSubsingleton : Subsingleton (Set.range f) :=
    PreconnectedSpace.trivial_of_discrete
  have hEq :
      (⟨f v, ⟨v, rfl⟩⟩ : Set.range f) =
        ⟨f ⟨z, hzV⟩, ⟨⟨z, hzV⟩, rfl⟩⟩ :=
    hRangeSubsingleton.elim _ _
  exact congrArg Subtype.val hEq

/- Helper for Theorem 3.8.10: in a chosen chart `T : p⁻¹ V ≃ V × p⁻¹ {z}`, the preimage of
the basepoint pair `(z, ξ)` still lies over `z`. -/
omit [LocPathConnectedSpace E] in
private theorem universalCoverDeck_chart_symm_basepoint_mem_fiber
    {z : B} {V : Set B}
    [DiscreteTopology (p ⁻¹' ({z} : Set B))]
    (hzV : z ∈ V)
    (T : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({z} : Set B)))
    (hT : ∀ x, (T x).1.1 = p x)
    (ξ : p ⁻¹' ({z} : Set B)) :
    p (T.symm (⟨z, hzV⟩, ξ)).1 = z := by
  -- Project the chart inverse back to the base and compare with the chosen first coordinate.
  have hproj :
      ((T (T.symm (⟨z, hzV⟩, ξ))).1 : B) = p (T.symm (⟨z, hzV⟩, ξ)).1 :=
    hT (T.symm (⟨z, hzV⟩, ξ))
  have hpair : T (T.symm (⟨z, hzV⟩, ξ)) = (⟨z, hzV⟩, ξ) :=
    T.apply_symm_apply (⟨z, hzV⟩, ξ)
  calc
    p (T.symm (⟨z, hzV⟩, ξ)).1 = ((T (T.symm (⟨z, hzV⟩, ξ))).1 : B) := hproj.symm
    _ = z := congrArg (fun q : V × (p ⁻¹' ({z} : Set B)) ↦ (q.1 : B)) hpair

/-- Helper for Theorem 3.8.10: transporting the deck action through the basepoint slice of a
chosen chart gives a concrete `H`-action on the reference fiber `p⁻¹ {z}`. -/
private noncomputable abbrev universalCoverDeck_chartFiberMulAction
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hV : IsFundamentalNeighborhood p z V) :
    MulAction H (p ⁻¹' ({z} : Set B)) := by
  classical
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  let hdisc : DiscreteTopology (p ⁻¹' ({z} : Set B)) := hV.discreteTopology_fiber
  let hzV : z ∈ V := hV.mem
  let T : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({z} : Set B)) := fundamentalNeighborhoodHomeomorph hV
  let hT : ∀ x, (T x).1.1 = p x := fundamentalNeighborhoodHomeomorph_fst hV
  letI : DiscreteTopology (p ⁻¹' ({z} : Set B)) := hdisc
  let ρ : H → p ⁻¹' ({z} : Set B) → p ⁻¹' ({z} : Set B) := fun γ ξ ↦
    -- Read off the fiber coordinate of the deck translate of the basepoint slice.
    (T
      ⟨(γ : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, ξ)).1,
        universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (⟨z, hzV⟩, ξ))⟩).2
  have hρ_apply :
      ∀ (γ : H) (ξ : p ⁻¹' ({z} : Set B)),
        T
            ⟨(γ : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, ξ)).1,
              universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (⟨z, hzV⟩, ξ))⟩ =
          (⟨z, hzV⟩, ρ γ ξ) := by
    intro γ ξ
    -- The first coordinate stays at `z` because deck transformations lie over the identity.
    ext
    · have hdeck :
          p ((γ : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, ξ)).1) =
            p (T.symm (⟨z, hzV⟩, ξ)).1 := by
        simpa using
          universalCoverDeck_smul_proj e (γ : FundamentalGroup B (p e))
            (T.symm (⟨z, hzV⟩, ξ)).1
      calc
        ((T
            ⟨(γ : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, ξ)).1,
              universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (⟨z, hzV⟩, ξ))⟩).1 : B) =
            p ((γ : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, ξ)).1) := by
              simpa using
                hT
                  ⟨(γ : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, ξ)).1,
                    universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (⟨z, hzV⟩, ξ))⟩
        _ = p (T.symm (⟨z, hzV⟩, ξ)).1 := hdeck
        _ = z := universalCoverDeck_chart_symm_basepoint_mem_fiber hzV T hT ξ
    · rfl
  refine
    { smul := fun γ ξ ↦ ρ γ ξ
      one_smul := by
        intro ξ
        -- At the identity element the transported action is the original fiber point.
        change ρ (1 : H) ξ = ξ
        have hpoint :
            (⟨(1 : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, ξ)).1,
              universalCoverDeck_smul_mem_preimage hp e H V (1 : H)
                (T.symm (⟨z, hzV⟩, ξ))⟩ : p ⁻¹' V) =
              T.symm (⟨z, hzV⟩, ξ) := by
          apply Subtype.ext
          simp
        simp [ρ]
      mul_smul := by
        intro γ₁ γ₂ ξ
        -- Composition becomes ordinary multiplication after conjugating by the chart slice.
        let x : p ⁻¹' V := T.symm (⟨z, hzV⟩, ξ)
        let y : p ⁻¹' V :=
          ⟨(γ₂ : FundamentalGroup B (p e)) • x.1,
            universalCoverDeck_smul_mem_preimage hp e H V γ₂ x⟩
        have hy : T.symm (⟨z, hzV⟩, (T y).2) = y := by
          apply T.injective
          simpa [ρ, x, y] using (hρ_apply γ₂ ξ).symm
        have hpoint :
            (⟨((γ₁ * γ₂ : H) : FundamentalGroup B (p e)) • x.1,
              universalCoverDeck_smul_mem_preimage hp e H V (γ₁ * γ₂) x⟩ : p ⁻¹' V) =
              ⟨(γ₁ : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, (T y).2)).1,
                universalCoverDeck_smul_mem_preimage hp e H V γ₁
                  (T.symm (⟨z, hzV⟩, (T y).2))⟩ := by
          apply Subtype.ext
          rw [hy]
          simp [x, y, mul_smul]
        calc
          (T
              ⟨((γ₁ * γ₂ : H) : FundamentalGroup B (p e)) • x.1,
                universalCoverDeck_smul_mem_preimage hp e H V (γ₁ * γ₂) x⟩).2 =
              (T
                ⟨(γ₁ : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, (T y).2)).1,
                  universalCoverDeck_smul_mem_preimage hp e H V γ₁
                    (T.symm (⟨z, hzV⟩, (T y).2))⟩).2 := by
                  rw [hpoint]
          _ = ρ γ₁ (ρ γ₂ ξ) := rfl }

/-- Helper for Theorem 3.8.10: the transported action on the discrete chart fiber is
continuous in each subgroup variable. -/
private theorem universalCoverDeck_chartFiberContinuousConstSMul
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hV : IsFundamentalNeighborhood p z V) :
    @ContinuousConstSMul H (p ⁻¹' ({z} : Set B))
      inferInstance (universalCoverDeck_chartFiberMulAction hp e H hV).toSMul := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  -- Local instance justification (proof-local temporary data): the chosen fundamental
  -- neighborhood `hV` supplies the discrete fiber topology only for this local continuity proof.
  letI : DiscreteTopology (p ⁻¹' ({z} : Set B)) := hV.discreteTopology_fiber
  letI := universalCoverDeck_chartFiberMulAction hp e H hV
  refine ⟨fun _ ↦ continuous_of_discreteTopology⟩

/- Helper for Theorem 3.8.10: over a chosen chart, `H` acts trivially on the base coordinate and
by the transported deck action on the fiber coordinate. -/
omit [LocPathConnectedSpace E] in
private theorem universalCoverDeck_chartProduct_one_smul
    (e : E) (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    [MulAction H (p ⁻¹' ({z} : Set B))]
    (x : V × (p ⁻¹' ({z} : Set B))) :
    (x.1, (1 : H) • x.2) = x := by
  -- The chart product action fixes the base coordinate and uses the ordinary identity action on
  -- the fiber coordinate.
  rcases x with ⟨v, ξ⟩
  simp

/- Helper for Theorem 3.8.10: multiplication in the chart product action is computed only on the
fiber coordinate. -/
omit [LocPathConnectedSpace E] in
private theorem universalCoverDeck_chartProduct_mul_smul
    (e : E) (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    [MulAction H (p ⁻¹' ({z} : Set B))]
    (γ₁ γ₂ : H) (x : V × (p ⁻¹' ({z} : Set B))) :
    (x.1, ((γ₁ * γ₂ : H) • x.2)) = (x.1, γ₁ • (γ₂ • x.2)) := by
  -- The base coordinate is unchanged, while the fiber coordinate follows the subgroup action law.
  rcases x with ⟨v, ξ⟩
  simp [mul_smul]

private noncomputable abbrev universalCoverDeck_chartProductMulAction
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hV : IsFundamentalNeighborhood p z V) :
    MulAction H (V × (p ⁻¹' ({z} : Set B))) := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  letI := universalCoverDeck_chartFiberMulAction hp e H hV
  exact
    { smul := fun γ x ↦ (x.1, γ • x.2)
      one_smul := fun x ↦ by
        -- The product action fixes the base coordinate and applies the identity element on the
        -- fiber.
        rcases x with ⟨v, ξ⟩
        exact Prod.ext rfl (one_smul H ξ)
      mul_smul := fun γ₁ γ₂ x ↦ by
        -- Multiplication acts only in the fiber coordinate of the chart.
        rcases x with ⟨v, ξ⟩
        exact Prod.ext rfl (mul_smul γ₁ γ₂ ξ) }

/-- Helper for Theorem 3.8.10: the product action in the descended chart is continuous because
the base coordinate is fixed and the chart fiber is discrete. -/
private theorem universalCoverDeck_chartProductContinuousConstSMul
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hV : IsFundamentalNeighborhood p z V) :
    @ContinuousConstSMul H (V × (p ⁻¹' ({z} : Set B)))
      inferInstance (universalCoverDeck_chartProductMulAction hp e H hV).toSMul := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  letI := universalCoverDeck_chartFiberMulAction hp e H hV
  letI : ContinuousConstSMul H (p ⁻¹' ({z} : Set B)) :=
    universalCoverDeck_chartFiberContinuousConstSMul hp e H hV
  letI := universalCoverDeck_chartProductMulAction hp e H hV
  refine ⟨?_⟩
  intro γ
  -- The base coordinate is fixed, so continuity reduces to continuity of the transported fiber
  -- translate.
  have hcont :
      Continuous fun x : V × (p ⁻¹' ({z} : Set B)) ↦ (x.1, γ • x.2) :=
    continuous_fst.prodMk <| (continuous_const_smul γ).comp continuous_snd
  rw [show (fun x : V × (p ⁻¹' ({z} : Set B)) ↦ γ • x) =
      (fun x : V × (p ⁻¹' ({z} : Set B)) ↦ (x.1, γ • x.2)) by
        rfl]
  exact hcont

/-- Helper for Theorem 3.8.10: once a quotient map `q` is known to identify exactly the classes
of a setoid `r`, the quotient by `r` is homeomorphic to the codomain of `q`. -/
private noncomputable def quotient_homeomorph_of_rel_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : C(X, Y)) (hq : Topology.IsQuotientMap q) (r : Setoid X)
    (hrel : ∀ x y : X, r x y ↔ q x = q y) :
    Quotient r ≃ₜ Y := by
  have hker : Setoid.ker q = r := by
    ext x y
    exact (hrel x y).symm
  -- Repackage the quotient topology through the kernel of `q`.
  exact hker ▸ Topology.IsQuotientMap.homeomorph hq

/-- Helper for Theorem 3.8.10: on a representative, `quotient_homeomorph_of_rel_iff` evaluates
to the original quotient map. -/
private theorem quotient_homeomorph_of_rel_iff_apply_mk
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : C(X, Y)) (hq : Topology.IsQuotientMap q) (r : Setoid X)
    (hrel : ∀ x y : X, r x y ↔ q x = q y) (x : X) :
    quotient_homeomorph_of_rel_iff q hq r hrel (Quotient.mk'' x) = q x := by
  -- Unfold the quotient homeomorphism and reduce it to the kernel quotient map on
  -- representatives.
  have hker : Setoid.ker q = r := by
    ext a b
    exact (hrel a b).symm
  subst hker
  rfl

/-- Helper for Theorem 3.8.10: an equivariant homeomorphism between two explicit actions of the
same group on the same space descends to a homeomorphism between the corresponding orbit
quotients. -/
private noncomputable def quotient_homeomorph_of_equivariant_homeomorph
    {G X Y : Type*} [Group G] [TopologicalSpace X] [TopologicalSpace Y]
    (sourceAct : MulAction G X) (targetAct : MulAction G Y) (s : X ≃ₜ Y)
    (hs : ∀ (γ : G) (x : X),
      s (smulWith sourceAct γ x) = smulWith targetAct γ (s x)) :
    orbitQuotient sourceAct ≃ₜ orbitQuotient targetAct := by
  let q : C(X, orbitQuotient targetAct) :=
    ⟨fun x ↦ Quotient.mk'' (s x), continuous_quotient_mk'.comp s.continuous⟩
  have hqTarget :
      Topology.IsQuotientMap
        (show C(Y, orbitQuotient targetAct) from
          ⟨Quotient.mk'', continuous_quotient_mk'⟩) := by
    simpa using
      (isQuotientMap_quotient_mk' : Topology.IsQuotientMap
        (Quotient.mk'' : Y → orbitQuotient targetAct))
  have hq : Topology.IsQuotientMap q := by
    -- The descended map is the ordinary quotient map composed with the given homeomorphism.
    simpa [q, Function.comp] using Topology.IsQuotientMap.comp hqTarget s.isQuotientMap
  have hrel :
      ∀ x y : X,
        @MulAction.orbitRel G X _ sourceAct x y ↔ q x = q y := by
    intro x y
    constructor
    · intro hxy
      change Quotient.mk'' (s x) = Quotient.mk'' (s y)
      letI := targetAct
      rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      have hxy' : ∃ γ : G, smulWith sourceAct γ y = x := by
        letI := sourceAct
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
        simpa [smulWith] using hxy
      rcases hxy' with ⟨γ, hγ⟩
      refine ⟨γ, ?_⟩
      calc
        smulWith targetAct γ (s y) = s (smulWith sourceAct γ y) := by
          symm
          simpa [smulWith] using hs γ y
        _ = s x := by rw [hγ]
    · intro hxy
      have hxy' : ∃ γ : G, smulWith targetAct γ (s y) = s x := by
        letI := targetAct
        rw [show q x = q y ↔ Quotient.mk'' (s x) = Quotient.mk'' (s y) by rfl] at hxy
        rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
        simpa [smulWith] using hxy
      rcases hxy' with ⟨γ, hγ⟩
      letI := sourceAct
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨γ, ?_⟩
      apply s.injective
      calc
        s (smulWith sourceAct γ y) = smulWith targetAct γ (s y) := by
          simpa [smulWith] using hs γ y
        _ = s x := hγ
  -- Package the orbit-relation/kernel comparison into the quotient homeomorphism.
  exact
    quotient_homeomorph_of_rel_iff q hq
      (@MulAction.orbitRel G X _ sourceAct) hrel

/-- Helper for Theorem 3.8.10: on representatives, the descended quotient-conjugacy map sends
`[x]` to `[s x]`. -/
private theorem quotient_homeomorph_of_equivariant_homeomorph_apply_mk
    {G X Y : Type*} [Group G] [TopologicalSpace X] [TopologicalSpace Y]
    (sourceAct : MulAction G X) (targetAct : MulAction G Y) (s : X ≃ₜ Y)
    (hs : ∀ (γ : G) (x : X),
      s (smulWith sourceAct γ x) = smulWith targetAct γ (s x))
    (x : X) :
    quotient_homeomorph_of_equivariant_homeomorph sourceAct targetAct s hs
        (Quotient.mk'' x) =
      Quotient.mk'' (s x) := by
  let q : C(X, orbitQuotient targetAct) :=
    ⟨fun x ↦ Quotient.mk'' (s x), continuous_quotient_mk'.comp s.continuous⟩
  have hqTarget :
      Topology.IsQuotientMap
        (show C(Y, orbitQuotient targetAct) from
          ⟨Quotient.mk'', continuous_quotient_mk'⟩) := by
    simpa using
      (isQuotientMap_quotient_mk' : Topology.IsQuotientMap
        (Quotient.mk'' : Y → orbitQuotient targetAct))
  have hq : Topology.IsQuotientMap q := by
    simpa [q, Function.comp] using Topology.IsQuotientMap.comp hqTarget s.isQuotientMap
  have hrel :
      ∀ x y : X,
        @MulAction.orbitRel G X _ sourceAct x y ↔ q x = q y := by
    intro x y
    constructor
    · intro hxy
      change Quotient.mk'' (s x) = Quotient.mk'' (s y)
      letI := targetAct
      rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      have hxy' : ∃ γ : G, smulWith sourceAct γ y = x := by
        letI := sourceAct
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
        simpa [smulWith] using hxy
      rcases hxy' with ⟨γ, hγ⟩
      refine ⟨γ, ?_⟩
      calc
        smulWith targetAct γ (s y) = s (smulWith sourceAct γ y) := by
          symm
          simpa [smulWith] using hs γ y
        _ = s x := by rw [hγ]
    · intro hxy
      have hxy' : ∃ γ : G, smulWith targetAct γ (s y) = s x := by
        letI := targetAct
        rw [show q x = q y ↔ Quotient.mk'' (s x) = Quotient.mk'' (s y) by rfl] at hxy
        rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
        simpa [smulWith] using hxy
      rcases hxy' with ⟨γ, hγ⟩
      letI := sourceAct
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨γ, ?_⟩
      apply s.injective
      calc
        s (smulWith sourceAct γ y) = smulWith targetAct γ (s y) := by
          simpa [smulWith] using hs γ y
        _ = s x := hγ
  -- Evaluate the packaged quotient homeomorphism on the chosen representative.
  simpa [quotient_homeomorph_of_equivariant_homeomorph, q] using
    quotient_homeomorph_of_rel_iff_apply_mk q hq
      (@MulAction.orbitRel G X _ sourceAct) hrel x

/-- Helper for Theorem 3.8.10: the chosen chart `T : p⁻¹ V ≃ V × p⁻¹ {z}` intertwines the deck
action on `p⁻¹ V` with the product action that is trivial on `V`. -/
private theorem universalCoverDeck_chartHomeomorph_equivariant
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hV : IsFundamentalNeighborhood p z V) (γ : H) (x : p ⁻¹' V) :
    let T : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({z} : Set B)) := fundamentalNeighborhoodHomeomorph hV
    T (smulWith (universalCoverDeckPreimageMulAction hp e H V) γ x) =
      smulWith (universalCoverDeck_chartProductMulAction hp e H hV) γ (T x) := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  -- Local instance justification (proof-local temporary data): the chosen fundamental
  -- neighborhood `hV` supplies the discrete fiber topology only for this local chart
  -- equivariance proof.
  letI : DiscreteTopology (p ⁻¹' ({z} : Set B)) := hV.discreteTopology_fiber
  letI := universalCoverDeck_chartFiberMulAction hp e H hV
  letI := universalCoverDeck_chartProductMulAction hp e H hV
  let hzV : z ∈ V := hV.mem
  let hVPath : IsPathConnected V := hV.isPathConnected
  let T : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({z} : Set B)) := fundamentalNeighborhoodHomeomorph hV
  let hT : ∀ x, (T x).1.1 = p x := fundamentalNeighborhoodHomeomorph_fst hV
  change
    T
        ⟨(γ : FundamentalGroup B (p e)) • x.1,
          universalCoverDeck_smul_mem_preimage hp e H V γ x⟩ =
      smulWith (universalCoverDeck_chartProductMulAction hp e H hV) γ (T x)
  let xγ : p ⁻¹' V :=
    ⟨(γ : FundamentalGroup B (p e)) • x.1,
      universalCoverDeck_smul_mem_preimage hp e H V γ x⟩
  -- The first chart coordinate stays fixed because every deck transformation preserves `p`.
  have hproj :
      p ((γ : FundamentalGroup B (p e)) • x.1) = p x.1 := by
    simpa using universalCoverDeck_smul_proj e (γ : FundamentalGroup B (p e)) x.1
  change T xγ = ((T x).1, γ • (T x).2)
  apply Prod.ext
  · apply Subtype.ext
    calc
      (((T xγ).1 : V) : B) = p xγ.1 := hT xγ
      _ = p x.1 := hproj
      _ = (((T x).1 : V) : B) := (hT x).symm
  · let v : V := (T x).1
    let ξ : p ⁻¹' ({z} : Set B) := (T x).2
    have hx : T.symm (v, ξ) = x := by
      simp [v, ξ]
    have hleft :
        (T xγ).2 =
          (T
            ⟨(γ : FundamentalGroup B (p e)) • (T.symm (v, ξ)).1,
              universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (v, ξ))⟩).2 := by
      simp [xγ, v, ξ, hx]
    have hright :
        (γ • (T x)).2 =
          (T
            ⟨(γ : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, ξ)).1,
              universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (⟨z, hzV⟩, ξ))⟩).2 := by
      change γ • ξ =
        (T
          ⟨(γ : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, ξ)).1,
            universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (⟨z, hzV⟩, ξ))⟩).2
      rfl
    -- The second coordinate is constant across the base neighborhood, so the transported action
    -- is read off from the basepoint slice.
    exact hleft.trans <|
      (universalCoverDeck_chart_secondCoord_eq_basepoint hp e H hzV hVPath T hT γ ξ v).trans
        hright.symm

/-- Helper for Theorem 3.8.10: quotienting the chosen chart `T : p⁻¹ V ≃ V × p⁻¹ {z}` by the
subgroup action gives a homeomorphism between the two orbit quotients. -/
private noncomputable def universalCoverDeck_chartQuotientHomeomorph
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hV : IsFundamentalNeighborhood p z V) :
    orbitQuotient (universalCoverDeckPreimageMulAction hp e H V) ≃ₜ
      orbitQuotient (universalCoverDeck_chartProductMulAction hp e H hV) := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  letI := universalCoverDeckPreimageMulAction hp e H V
  -- Local instance justification (proof-local temporary data): the chosen fundamental
  -- neighborhood `hV` supplies the discrete fiber topology only for this local quotient-chart
  -- evaluation formula.
  letI : DiscreteTopology (p ⁻¹' ({z} : Set B)) := hV.discreteTopology_fiber
  letI := universalCoverDeck_chartFiberMulAction hp e H hV
  letI : ContinuousConstSMul H (p ⁻¹' ({z} : Set B)) :=
    universalCoverDeck_chartFiberContinuousConstSMul hp e H hV
  letI := universalCoverDeck_chartProductMulAction hp e H hV
  letI : ContinuousConstSMul H (V × (p ⁻¹' ({z} : Set B))) :=
    universalCoverDeck_chartProductContinuousConstSMul hp e H hV
  let T : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({z} : Set B)) := fundamentalNeighborhoodHomeomorph hV
  -- Route correction: descend the chosen chart directly by quotient-conjugacy instead of
  -- rebuilding the quotient homeomorphism from kernels.
  exact
    quotient_homeomorph_of_equivariant_homeomorph
      (universalCoverDeckPreimageMulAction hp e H V)
      (universalCoverDeck_chartProductMulAction hp e H hV)
      T
      (universalCoverDeck_chartHomeomorph_equivariant hp e H hV)

/-- Helper for Theorem 3.8.10: the descended chart quotient sends the class of `y` to the class of
its chosen chart coordinates. -/
private theorem universalCoverDeck_chartQuotientHomeomorph_apply_mk
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hV : IsFundamentalNeighborhood p z V) (y : p ⁻¹' V) :
    let T : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({z} : Set B)) := fundamentalNeighborhoodHomeomorph hV
    universalCoverDeck_chartQuotientHomeomorph hp e H hV (Quotient.mk'' y) =
      Quotient.mk'' (T y) := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  -- Local instance justification (proof-local temporary data): the chosen fundamental
  -- neighborhood `hV` supplies the discrete fiber topology only for this local kernel/orbit
  -- comparison on the product chart.
  letI : DiscreteTopology (p ⁻¹' ({z} : Set B)) := hV.discreteTopology_fiber
  letI := universalCoverDeck_chartFiberMulAction hp e H hV
  letI : ContinuousConstSMul H (p ⁻¹' ({z} : Set B)) :=
    universalCoverDeck_chartFiberContinuousConstSMul hp e H hV
  letI := universalCoverDeck_chartProductMulAction hp e H hV
  letI : ContinuousConstSMul H (V × (p ⁻¹' ({z} : Set B))) :=
    universalCoverDeck_chartProductContinuousConstSMul hp e H hV
  let T : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({z} : Set B)) := fundamentalNeighborhoodHomeomorph hV
  -- Evaluate the quotient-conjugacy homeomorphism on the chosen representative.
  simpa [universalCoverDeck_chartQuotientHomeomorph, T] using
    quotient_homeomorph_of_equivariant_homeomorph_apply_mk
      (universalCoverDeckPreimageMulAction hp e H V)
      (universalCoverDeck_chartProductMulAction hp e H hV)
      T
      (universalCoverDeck_chartHomeomorph_equivariant hp e H hV)
      y

/-- Helper for Theorem 3.8.10: the preimage comparison map sends the class of a restricted lift to
the corresponding literal point in the preimage downstairs. -/
private theorem universalCoverOrbitProjection_preimageHomeomorph_apply_mk
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hV : IsFundamentalNeighborhood p z V) (y : p ⁻¹' V) :
    universalCoverOrbitProjection_preimageHomeomorph hp e H hV (Quotient.mk'' y) =
      ⟨Quotient.mk'' y.1, y.2⟩ := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  letI := universalCoverDeckPreimageMulAction hp e H V
  letI : ContinuousConstSMul (FundamentalGroup B (p e)) E :=
    universalCoverDeckContinuousConstSMul e
  letI : ContinuousConstSMul H E :=
    { continuous_const_smul := fun γ ↦
        continuous_const_smul (γ : FundamentalGroup B (p e)) }
  let hVOpen : IsOpen V := hV.isOpen
  let q : E → universalCoverOrbit e H := Quotient.mk''
  let s : Set (universalCoverOrbit e H) := (universalCoverOrbitProjection e H) ⁻¹' V
  let qV : p ⁻¹' V → s := fun x ↦
    ⟨q x.1, by
      change p x.1 ∈ V
      exact x.2⟩
  have hqV_isQuot : Topology.IsQuotientMap qV := by
    simpa [qV, q, s] using
      ((MulAction.isOpenQuotientMap_quotientMk : IsOpenQuotientMap q)).isQuotientMap
        |>.restrictPreimage_isOpen
          (hVOpen.preimage (universalCoverOrbitProjection e H).continuous)
  let qVMap : C(p ⁻¹' V, s) := ⟨qV, hqV_isQuot.continuous⟩
  have hrel :
      ∀ x y : p ⁻¹' V,
        MulAction.orbitRel H (p ⁻¹' V) x y ↔ qVMap x = qVMap y := by
    intro x y
    constructor
    · intro hxy
      apply Subtype.ext
      change (Quotient.mk'' x.1 : universalCoverOrbit e H) = Quotient.mk'' y.1
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
      rcases hxy with ⟨γ, hγ⟩
      rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨γ, by simpa using congrArg Subtype.val hγ⟩
    · intro hxy
      change qV x = qV y at hxy
      have hval :
          (Quotient.mk'' x.1 : universalCoverOrbit e H) = Quotient.mk'' y.1 := by
        simpa [qV] using congrArg Subtype.val hxy
      rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hval
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      rcases hval with ⟨γ, hγ⟩
      exact ⟨γ, Subtype.ext hγ⟩
  -- Evaluate the quotient-kernel homeomorphism on the chosen representative.
  simpa [universalCoverOrbitProjection_preimageHomeomorph, qVMap, qV, q, s] using
    quotient_homeomorph_of_rel_iff_apply_mk qVMap hqV_isQuot
      (MulAction.orbitRel H (p ⁻¹' V)) hrel y

/-- Helper for Theorem 3.8.10: the orbit relation for the transported product action is exactly
the kernel of the map `(v, ξ) ↦ (v, [ξ])`. -/
private theorem chart_product_orbitRel_iff_ker
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hV : IsFundamentalNeighborhood p z V)
    (x y : V × (p ⁻¹' ({z} : Set B))) :
    let q : V × (p ⁻¹' ({z} : Set B)) →
        V × orbitQuotient (universalCoverDeck_chartFiberMulAction hp e H hV) := fun u ↦
      (u.1, Quotient.mk'' u.2)
    @MulAction.orbitRel H (V × (p ⁻¹' ({z} : Set B))) _
        (universalCoverDeck_chartProductMulAction hp e H hV) x y ↔ Setoid.ker q x y := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  -- Local instance justification (proof-local temporary data): the chosen fundamental
  -- neighborhood `hV` supplies the discrete fiber topology only for this local product-quotient
  -- homeomorphism.
  letI : DiscreteTopology (p ⁻¹' ({z} : Set B)) := hV.discreteTopology_fiber
  letI := universalCoverDeck_chartFiberMulAction hp e H hV
  letI : ContinuousConstSMul H (p ⁻¹' ({z} : Set B)) :=
    universalCoverDeck_chartFiberContinuousConstSMul hp e H hV
  letI := universalCoverDeck_chartProductMulAction hp e H hV
  let q : V × (p ⁻¹' ({z} : Set B)) → V × (((p ⁻¹' ({z} : Set B)) /[H])) := fun u ↦
    (u.1, Quotient.mk'' u.2)
  constructor
  · intro hxy
    change q x = q y
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
    rcases hxy with ⟨γ, hγ⟩
    rw [← hγ]
    rcases y with ⟨v, ξ⟩
    apply Prod.ext
    · rfl
    · apply Quotient.sound
      change MulAction.orbitRel H (p ⁻¹' ({z} : Set B)) ((γ • (v, ξ)).2) ξ
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨γ, rfl⟩
  · intro hxy
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    have hbase : x.1 = y.1 := by
      simpa [q] using congrArg Prod.fst hxy
    have hfiber :
        (Quotient.mk'' x.2 : ((p ⁻¹' ({z} : Set B)) /[H])) = Quotient.mk'' y.2 := by
      simpa [q] using congrArg Prod.snd hxy
    rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hfiber
    rcases hfiber with ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    rcases x with ⟨vx, ξx⟩
    rcases y with ⟨vy, ξy⟩
    simp only at hbase hγ
    subst hbase
    exact Prod.ext rfl hγ

/-- Helper for Theorem 3.8.10: because the product action is trivial on `V`, quotienting
`V × p⁻¹ {z}` should split as the product of `V` with the quotient of the fiber action. -/
private noncomputable def chart_product_quotient_homeomorph
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hV : IsFundamentalNeighborhood p z V) :
    orbitQuotient (universalCoverDeck_chartProductMulAction hp e H hV) ≃ₜ
      V × orbitQuotient (universalCoverDeck_chartFiberMulAction hp e H hV) := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  -- Local instance justification (proof-local temporary data): the chosen fundamental
  -- neighborhood `hV` supplies the discrete fiber topology only for this local product-quotient
  -- evaluation formula.
  letI : DiscreteTopology (p ⁻¹' ({z} : Set B)) := hV.discreteTopology_fiber
  letI := universalCoverDeck_chartFiberMulAction hp e H hV
  letI : ContinuousConstSMul H (p ⁻¹' ({z} : Set B)) :=
    universalCoverDeck_chartFiberContinuousConstSMul hp e H hV
  letI := universalCoverDeck_chartProductMulAction hp e H hV
  let qProd : C(V × (p ⁻¹' ({z} : Set B)), V × (((p ⁻¹' ({z} : Set B)) /[H]))) :=
    ⟨fun u ↦ (u.1, Quotient.mk'' u.2),
      continuous_fst.prodMk (continuous_quotient_mk'.comp continuous_snd)⟩
  have hqProd :
      Topology.IsQuotientMap qProd := by
    -- The product quotient is the identity on the base and the orbit quotient on the fiber.
    simpa [qProd] using
      (IsOpenQuotientMap.id.prodMap
        (MulAction.isOpenQuotientMap_quotientMk :
          IsOpenQuotientMap
            (Quotient.mk (MulAction.orbitRel H (p ⁻¹' ({z} : Set B)))))).isQuotientMap
  -- Package the already-proved orbit-relation/kernel comparison into the desired homeomorphism.
  exact
    quotient_homeomorph_of_rel_iff qProd hqProd
      (MulAction.orbitRel H (V × (p ⁻¹' ({z} : Set B))))
      (chart_product_orbitRel_iff_ker hp e H hV)

/-- Helper for Theorem 3.8.10: quotienting the product chart sends the class of `(v, ξ)` to the
pair `(v, [ξ])`. -/
private theorem chart_product_quotient_homeomorph_apply_mk
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hV : IsFundamentalNeighborhood p z V)
    (u : V × (p ⁻¹' ({z} : Set B))) :
    chart_product_quotient_homeomorph hp e H hV (Quotient.mk'' u) =
      (u.1, Quotient.mk'' u.2) := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  letI : DiscreteTopology (p ⁻¹' ({z} : Set B)) := hV.discreteTopology_fiber
  letI := universalCoverDeck_chartFiberMulAction hp e H hV
  letI : ContinuousConstSMul H (p ⁻¹' ({z} : Set B)) :=
    universalCoverDeck_chartFiberContinuousConstSMul hp e H hV
  letI := universalCoverDeck_chartProductMulAction hp e H hV
  let qProd : C(V × (p ⁻¹' ({z} : Set B)), V × (((p ⁻¹' ({z} : Set B)) /[H]))) :=
    ⟨fun u ↦ (u.1, Quotient.mk'' u.2),
      continuous_fst.prodMk (continuous_quotient_mk'.comp continuous_snd)⟩
  have hqProd :
      Topology.IsQuotientMap qProd := by
    simpa [qProd] using
      (IsOpenQuotientMap.id.prodMap
        (MulAction.isOpenQuotientMap_quotientMk :
          IsOpenQuotientMap
            (Quotient.mk (MulAction.orbitRel H (p ⁻¹' ({z} : Set B)))))).isQuotientMap
  -- Evaluate the product quotient on the chosen representative.
  simpa [chart_product_quotient_homeomorph, qProd] using
    quotient_homeomorph_of_rel_iff_apply_mk qProd hqProd
      (MulAction.orbitRel H (V × (p ⁻¹' ({z} : Set B))))
      (chart_product_orbitRel_iff_ker hp e H hV) u

/-- Helper for Theorem 3.8.10: restricting the chosen chart to the basepoint slice gives a
homeomorphism of the reference fiber with itself. -/
private noncomputable def universalCoverDeck_chartFiberSliceHomeomorph
    {z : B} {V : Set B} [DiscreteTopology (p ⁻¹' ({z} : Set B))]
    (hzV : z ∈ V) (T : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({z} : Set B)))
    (hT : ∀ x, (T x).1.1 = p x) :
    (p ⁻¹' ({z} : Set B)) ≃ₜ (p ⁻¹' ({z} : Set B)) where
  toEquiv :=
    { toFun := fun x ↦
        -- Read off the second coordinate of the chart on the actual fiber point.
        let hx : p x.1 = z := Set.mem_singleton_iff.mp x.2
        (T ⟨x.1, by simpa [hx] using hzV⟩).2
      invFun := fun ξ ↦
        -- Recover the literal fiber point by moving back along the basepoint slice.
        ⟨(T.symm (⟨z, hzV⟩, ξ)).1,
          universalCoverDeck_chart_symm_basepoint_mem_fiber hzV T hT ξ⟩
      left_inv := by
        intro x
        apply Subtype.ext
        let hx : p x.1 = z := Set.mem_singleton_iff.mp x.2
        let xV : p ⁻¹' V := ⟨x.1, by simpa [hx] using hzV⟩
        have hpair : T xV = (⟨z, hzV⟩, (T xV).2) := by
          apply Prod.ext
          · apply Subtype.ext
            calc
              (((T xV).1 : V) : B) = p xV.1 := by simpa using hT xV
              _ = z := by simp [xV, hx]
          · rfl
        have hsymm : T.symm (⟨z, hzV⟩, (T xV).2) = xV := by
          rw [← hpair]
          exact T.symm_apply_apply xV
        simpa [xV] using congrArg Subtype.val hsymm
      right_inv := by
        intro ξ
        let x : p ⁻¹' V := T.symm (⟨z, hzV⟩, ξ)
        have hxEq :
            (⟨x.1, x.2⟩ : p ⁻¹' V) = x := by
          apply Subtype.ext
          rfl
        change
          (T ⟨x.1, x.2⟩).2 = ξ
        rw [hxEq]
        exact congrArg Prod.snd (T.apply_symm_apply (⟨z, hzV⟩, ξ)) }
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- Helper for Theorem 3.8.10: the actual restricted deck action on the discrete fiber has
continuous translates. -/
private theorem universalCoverDeckFiberContinuousConstSMul
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) (z : B) :
    @ContinuousConstSMul H (p ⁻¹' ({z} : Set B))
      inferInstance (universalCoverDeckFiberMulAction hp e H z).toSMul := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  letI := universalCoverDeckFiberMulAction hp e H z
  letI : DiscreteTopology (p ⁻¹' ({z} : Set B)) := (hp.isPathConnectedCoveringMap.2 z).1
  refine ⟨fun _ ↦ continuous_of_discreteTopology⟩

/-- Helper for Theorem 3.8.10: the slice homeomorphism of a chosen trivializing chart conjugates
the literal restricted deck action on `p⁻¹ {z}` to the transported chart-fiber action. -/
private theorem universalCoverDeck_chartFiberSliceHomeomorph_equivariant
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hdisc : DiscreteTopology (p ⁻¹' ({z} : Set B))) (hzV : z ∈ V)
    (T : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({z} : Set B)))
    (hT : ∀ x, (T x).1.1 = p x)
    (γ : H) (ξ : p ⁻¹' ({z} : Set B)) :
    let s : (p ⁻¹' ({z} : Set B)) ≃ₜ (p ⁻¹' ({z} : Set B)) :=
      universalCoverDeck_chartFiberSliceHomeomorph hzV T hT
    s (smulWith (universalCoverDeckFiberMulAction hp e H z) γ ξ) =
      (T
        ⟨smulWith (universalCoverDeckMulActionOf hp e)
            (γ : FundamentalGroup B (p e)) (T.symm (⟨z, hzV⟩, s ξ)).1,
          universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (⟨z, hzV⟩, s ξ))⟩).2 := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  change
    let s : (p ⁻¹' ({z} : Set B)) ≃ₜ (p ⁻¹' ({z} : Set B)) :=
      universalCoverDeck_chartFiberSliceHomeomorph hzV T hT
    s ((universalCoverDeckFiberMulAction hp e H z).smul γ ξ) =
      (T
        ⟨(γ : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, s ξ)).1,
          universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (⟨z, hzV⟩, s ξ))⟩).2
  let s : (p ⁻¹' ({z} : Set B)) ≃ₜ (p ⁻¹' ({z} : Set B)) :=
    universalCoverDeck_chartFiberSliceHomeomorph hzV T hT
  -- The slice map sends a literal fiber point to the chart coordinate of that same point, so
  -- after translating the point upstairs it computes exactly the transported chart action.
  have hs : (T.symm (⟨z, hzV⟩, s ξ)).1 = ξ.1 := by
    exact congrArg Subtype.val (s.left_inv ξ)
  let x₁ : p ⁻¹' V :=
    ⟨(γ : FundamentalGroup B (p e)) • ξ.1,
      by
        have hγz :
            p ((γ : FundamentalGroup B (p e)) • ξ.1) = z :=
          universalCoverDeck_smul_mem_fiber hp e H z γ ξ
        simpa [hγz] using hzV⟩
  let x₂ : p ⁻¹' V :=
    ⟨(γ : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, s ξ)).1,
      universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (⟨z, hzV⟩, s ξ))⟩
  have hx : x₂ = x₁ := by
    apply Subtype.ext
    simp [x₁, x₂, hs]
  have hTx : (T x₂).2 = (T x₁).2 := by
    simp [hx]
  simpa [s, x₁, x₂, universalCoverDeck_chartFiberSliceHomeomorph,
    universalCoverDeckFiberMulAction] using hTx.symm

/-- Helper for Theorem 3.8.10: the transported chart-fiber action is conjugate to the actual deck
action on the reference fiber, so their orbit quotients are homeomorphic. -/
private noncomputable def chartFiberQuotientHomeomorph
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hV : IsFundamentalNeighborhood p z V) :
    orbitQuotient (universalCoverDeck_chartFiberMulAction hp e H hV) ≃ₜ
      ((universalCoverOrbitProjection e H) ⁻¹' ({z} : Set B)) := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  -- Local instance justification (proof-local temporary data): the chosen fundamental
  -- neighborhood `hV` supplies the discrete fiber topology only for this local fiber-quotient
  -- comparison proof.
  letI : DiscreteTopology (p ⁻¹' ({z} : Set B)) := hV.discreteTopology_fiber
  letI := universalCoverDeck_chartFiberMulAction hp e H hV
  letI : ContinuousConstSMul H (p ⁻¹' ({z} : Set B)) :=
    universalCoverDeck_chartFiberContinuousConstSMul hp e H hV
  letI := universalCoverDeckFiberMulAction hp e H z
  letI : ContinuousConstSMul H (p ⁻¹' ({z} : Set B)) :=
    universalCoverDeckFiberContinuousConstSMul hp e H z
  let hzV : z ∈ V := hV.mem
  let T : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({z} : Set B)) := fundamentalNeighborhoodHomeomorph hV
  let hT : ∀ x, (T x).1.1 = p x := fundamentalNeighborhoodHomeomorph_fst hV
  let s : (p ⁻¹' ({z} : Set B)) ≃ₜ (p ⁻¹' ({z} : Set B)) :=
    universalCoverDeck_chartFiberSliceHomeomorph hzV T hT
  let hconj :
      Quotient (@MulAction.orbitRel H (p ⁻¹' ({z} : Set B)) _
        (universalCoverDeck_chartFiberMulAction hp e H hV)) ≃ₜ
        Quotient (@MulAction.orbitRel H (p ⁻¹' ({z} : Set B)) _
          (universalCoverDeckFiberMulAction hp e H z)) :=
    quotient_homeomorph_of_equivariant_homeomorph
      (universalCoverDeck_chartFiberMulAction hp e H hV)
      (universalCoverDeckFiberMulAction hp e H z)
      s.symm
      (by
        intro γ ξ
        let sourceSmul : H → p ⁻¹' ({z} : Set B) → p ⁻¹' ({z} : Set B) := fun γ ξ ↦ by
          letI := universalCoverDeck_chartFiberMulAction hp e H hV
          exact γ • ξ
        let targetSmul : H → p ⁻¹' ({z} : Set B) → p ⁻¹' ({z} : Set B) := fun γ ξ ↦ by
          letI := universalCoverDeckFiberMulAction hp e H z
          exact γ • ξ
        -- Apply the proved conjugacy for the slice homeomorphism and invert it.
        apply s.injective
        calc
          s (s.symm (sourceSmul γ ξ)) = sourceSmul γ ξ := s.apply_symm_apply _
          _ = s (targetSmul γ (s.symm ξ)) := by
                symm
                simpa [sourceSmul, targetSmul, s] using
                  universalCoverDeck_chartFiberSliceHomeomorph_equivariant
                    hp e H hV.discreteTopology_fiber hzV T hT γ (s.symm ξ))
  -- First compare the transported chart-fiber quotient with the literal deck-action quotient, and
  -- then identify the latter with the actual fiber of the descended cover.
  exact hconj.trans (universalCoverOrbitProjection_fiberHomeomorph hp e H z)

-- The remaining topological work is to descend one chosen fundamental neighborhood of the
-- universal cover to the subgroup quotient.
/-- Helper for Theorem 3.8.10: any fundamental neighborhood for the universal cover remains a
fundamental neighborhood for the quotient covering. -/
private theorem universalCoverOrbitProjection_isFundamentalNeighborhood
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) {z : B} {V : Set B}
    (hV : IsFundamentalNeighborhood p z V) :
    IsFundamentalNeighborhood (universalCoverOrbitProjection e H) z V := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  -- Local instance justification (proof-local temporary data): the chosen fundamental
  -- neighborhood `hV` supplies the discrete fiber topology only for this local descended-chart
  -- construction.
  letI : DiscreteTopology (p ⁻¹' ({z} : Set B)) := hV.discreteTopology_fiber
  let hzV : z ∈ V := hV.mem
  let hVOpen : IsOpen V := hV.isOpen
  let hVPath : IsPathConnected V := hV.isPathConnected
  let T : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({z} : Set B)) := fundamentalNeighborhoodHomeomorph hV
  let hT : ∀ x, (T x).1.1 = p x := fundamentalNeighborhoodHomeomorph_fst hV
  have hsecond :
      ∀ (γ : H) (ξ : p ⁻¹' ({z} : Set B)) (v : V),
        (T
            ⟨(γ : FundamentalGroup B (p e)) • (T.symm (v, ξ)).1,
              universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (v, ξ))⟩).2 =
          (T
            ⟨(γ : FundamentalGroup B (p e)) • (T.symm (⟨z, hzV⟩, ξ)).1,
              universalCoverDeck_smul_mem_preimage hp e H V γ (T.symm (⟨z, hzV⟩, ξ))⟩).2 := by
    intro γ ξ v
    -- Route correction: the remaining descent step now uses a proved constancy lemma for the
    -- transported fiber coordinate, so the unresolved work is only the quotient-kernel packaging.
    exact universalCoverDeck_chart_secondCoord_eq_basepoint hp e H hzV hVPath T hT γ ξ v
  let hPre := universalCoverOrbitProjection_preimageHomeomorph hp e H hV
  let hChart := universalCoverDeck_chartQuotientHomeomorph hp e H hV
  let hProd := chart_product_quotient_homeomorph hp e H hV
  let hFiber := chartFiberQuotientHomeomorph hp e H hV
  let Hdesc :
      ((universalCoverOrbitProjection e H) ⁻¹' V) ≃ₜ
        V × ((universalCoverOrbitProjection e H) ⁻¹' ({z} : Set B)) :=
    hPre.symm.trans <|
      hChart.trans <|
        hProd.trans <|
          Homeomorph.prodCongr (Homeomorph.refl V) hFiber
  refine
    ⟨universalCoverOrbitProjection_discreteTopology_fiber hp e H z, hzV, hVOpen, hVPath,
      hVOpen.preimage (universalCoverOrbitProjection e H).continuous, Hdesc, ?_⟩
  intro x
  rcases x with ⟨q, hq⟩
  rcases Quotient.exists_rep q with ⟨y, rfl⟩
  let yV : p ⁻¹' V := ⟨y, by simpa [universalCoverOrbitProjection] using hq⟩
  let T' : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({z} : Set B)) := fundamentalNeighborhoodHomeomorph hV
  let hT' : ∀ x, (T' x).1.1 = p x := fundamentalNeighborhoodHomeomorph_fst hV
  have hPre_apply :
      hPre (Quotient.mk'' yV) =
        ⟨Quotient.mk'' y, by simpa [universalCoverOrbitProjection] using hq⟩ := by
    simpa [yV] using
      universalCoverOrbitProjection_preimageHomeomorph_apply_mk hp e H hV yV
  have hPre_symm :
      hPre.symm ⟨Quotient.mk'' y, by simpa [universalCoverOrbitProjection] using hq⟩ =
        Quotient.mk'' yV := by
    simpa [hPre_apply] using hPre.left_inv (Quotient.mk'' yV)
  have hChart_apply :
      hChart (Quotient.mk'' yV) = Quotient.mk'' (T' yV) := by
    simpa [T'] using universalCoverDeck_chartQuotientHomeomorph_apply_mk hp e H hV yV
  have hProd_apply :
      hProd (Quotient.mk'' (T' yV)) = ((T' yV).1, Quotient.mk'' (T' yV).2) := by
    simpa using chart_product_quotient_homeomorph_apply_mk hp e H hV (T' yV)
  -- Evaluate the descended chart on a representative and read off the unchanged base coordinate.
  calc
    (((Hdesc ⟨Quotient.mk'' y, by simpa [universalCoverOrbitProjection] using hq⟩).1 : V) : B) =
        (((T' yV).1 : V) : B) := by
          simp [Hdesc, hPre_symm, hChart_apply, hProd_apply]
    _ = p yV.1 := by simpa using hT' yV
    _ = universalCoverOrbitProjection e H (Quotient.mk'' y) := rfl

/-- The quotient of a universal cover by any subgroup of the deck group is again a covering space
over the same base. -/
-- Proof sketch: quotient the universal cover by the subgroup action coming from deck
-- transformations, then descend one fundamental neighborhood of the universal cover to the
-- quotient cover.
instance universalCoverOrbitProjection_isPathConnectedCoveringMap
    [hp : IsUniversalCoveringMap p] (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    IsPathConnectedCoveringMap (universalCoverOrbitProjection e H) := by
  -- Route correction: abandon the generic right-factor descent. The intended source-faithful
  -- proof is to descend a fixed fundamental neighborhood `V` for `p` directly to the quotient
  -- cover `E / H → B`, using the explicit quotient-fiber identification over `V`.
  -- Local instance justification (proof-local temporary data): the evenly-covered-neighborhood
  -- API here needs `[LocPathConnectedSpace B]`, and this proof obtains that structure from the
  -- specific universal covering map `p` only for the duration of the argument.
  letI : LocPathConnectedSpace B := baseLocPathConnectedSpace hp
  refine ⟨universalCoverOrbitProjection_surjective hp e H, ?_⟩
  intro z
  rcases hV : hp.isPathConnectedCoveringMap.2 z with
    ⟨hdisc, V, hzV, hVOpen, hVPath, hpreVOpen, T, hT⟩
  let hFundV : IsFundamentalNeighborhood p z V :=
    ⟨hdisc, hzV, hVOpen, hVPath, hpreVOpen, T, hT⟩
  -- The descended quotient chart over the same `V` witnesses a fundamental neighborhood below.
  exact IsFundamentalNeighborhood.isPathConnectedEvenlyCovered
    (universalCoverOrbitProjection_isFundamentalNeighborhood hp e H hFundV)

/-- The orbit-space map attached to an orbit-category morphism between subgroups of the deck
group of a universal cover. -/
noncomputable def universalCoverOrbitMap
    [IsUniversalCoveringMap p] (e : E)
    {H K : O(FundamentalGroup B (p e))} (α : H ⟶ K) :
    C(
      universalCoverOrbit e (H : Subgroup (FundamentalGroup B (p e))),
      universalCoverOrbit e (K : Subgroup (FundamentalGroup B (p e)))) :=
  orbitSpaceMap α

private noncomputable abbrev universalCoverOrbitObj
    [IsUniversalCoveringMap p] (e : E) (H : O(FundamentalGroup B (p e))) : Type u :=
  universalCoverOrbit e (H : Subgroup (FundamentalGroup B (p e)))

private noncomputable abbrev universalCoverOrbitPointObj
    [IsUniversalCoveringMap p] (e : E) (H : O(FundamentalGroup B (p e))) :
    universalCoverOrbitObj e H :=
  universalCoverOrbitPoint e (H : Subgroup (FundamentalGroup B (p e)))

private noncomputable abbrev universalCoverOrbitProjectionObj
    [hp : IsUniversalCoveringMap p] (e : E) (H : O(FundamentalGroup B (p e))) :
    C(universalCoverOrbitObj e H, B) :=
  universalCoverOrbitProjection e (H : Subgroup (FundamentalGroup B (p e)))

/-- The connected covering space over `B` represented by the subgroup `H` of the deck group of a
universal cover. -/
noncomputable def universalCoverOrbitCovering
    [hp : IsUniversalCoveringMap p] (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    ConnectedCoveringSpace B :=
  ⟨Over.mk (TopCat.ofHom (universalCoverOrbitProjection e H)),
    ⟨universalCoverOrbitProjection_isPathConnectedCoveringMap e H,
      show PathConnectedSpace (universalCoverOrbit e H) from inferInstance⟩⟩

private noncomputable abbrev universalCoverOrbitCoveringObj
    [hp : IsUniversalCoveringMap p] (e : E) (H : O(FundamentalGroup B (p e))) :
    ConnectedCoveringSpace B :=
  universalCoverOrbitCovering e (H : Subgroup (FundamentalGroup B (p e)))

/-- Helper for Theorem 3.8.10: the canonical coset-to-orbit map based at `e` lands in the fiber
of `E / K → B` over `p e`. -/
private theorem universalCoverOrbitPointMap_mem_fiber
    (hp : IsUniversalCoveringMap p) (e : E)
    (K : O(FundamentalGroup B (p e)))
    (q : FundamentalGroup B (p e) ⧸ K) :
    letI : IsUniversalCoveringMap p := hp
    letI := universalCoverDeckMulActionOf hp e
    universalCoverOrbitProjection e (K : Subgroup (FundamentalGroup B (p e)))
        (orbitSpacePointMap e q) = p e := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  refine Quotient.inductionOn' q ?_
  intro γ
  -- The representative `γ⁻¹ • e` stays over `p e` because deck transformations preserve `p`.
  simpa using universalCoverDeck_smul_proj e γ⁻¹ e

/-- Helper for Theorem 3.8.10: the canonical orbit-fiber point represented by a coset of
`π₁(B, p e)` over `K` in `E / K` is the orbit class of the corresponding deck translate of `e`. -/
private noncomputable def universalCoverOrbitFiberPointMap
    (hp : IsUniversalCoveringMap p) (e : E)
    (K : O(FundamentalGroup B (p e))) :
    letI : IsUniversalCoveringMap p := hp
    letI := universalCoverDeckMulActionOf hp e
    FundamentalGroup B (p e) ⧸ K →
      (universalCoverOrbitProjection e (K : Subgroup (FundamentalGroup B (p e)))) ⁻¹' {p e} :=
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  fun q ↦
    ⟨orbitSpacePointMap e q,
      universalCoverOrbitPointMap_mem_fiber hp e K q⟩

/-- Helper for Theorem 3.8.10: because the deck action of `π₁(B, p e)` on the universal cover is
free, the canonical map `G / K → E / K` determined by `e` is injective. -/
private theorem universalCoverOrbitPointMap_injective
    (hp : IsUniversalCoveringMap p) (e : E)
    (K : O(FundamentalGroup B (p e))) :
    letI : IsUniversalCoveringMap p := hp
    letI := universalCoverDeckMulActionOf hp e
    Function.Injective
      (orbitSpacePointMap e :
        FundamentalGroup B (p e) ⧸ K →
          universalCoverOrbit e (K : Subgroup (FundamentalGroup B (p e)))) := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  letI : IsCancelSMul (FundamentalGroup B (p e)) E := universalCoverDeck_isCancelSMul e
  intro q₁ q₂ hq
  rcases Quotient.exists_rep q₁ with ⟨γ₁, rfl⟩
  rcases Quotient.exists_rep q₂ with ⟨γ₂, rfl⟩
  rw [orbitSpacePointMap_apply_mk, orbitSpacePointMap_apply_mk] at hq
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hq
  rcases hq with ⟨δ, hδ⟩
  -- Equality of orbit classes lifts to equality of the corresponding deck translates of `e`.
  have hδ' : ((δ : FundamentalGroup B (p e)) • (γ₂⁻¹ • e)) = γ₁⁻¹ • e := by
    simpa using hδ
  have hδ'' : (((δ : FundamentalGroup B (p e)) * γ₂⁻¹) • e) = γ₁⁻¹ • e := by
    simpa [smul_smul, mul_assoc] using hδ'
  have hcancel : (δ : FundamentalGroup B (p e)) * γ₂⁻¹ = γ₁⁻¹ := by
    apply IsCancelSMul.right_cancel ((δ : FundamentalGroup B (p e)) * γ₂⁻¹) (γ₁⁻¹) e
    exact hδ''
  have hmem : γ₁⁻¹ * γ₂ ∈ (K : Subgroup (FundamentalGroup B (p e))) := by
    have hδeq : (δ : FundamentalGroup B (p e)) = γ₁⁻¹ * γ₂ := by
      calc
        (δ : FundamentalGroup B (p e)) = ((δ : FundamentalGroup B (p e)) * γ₂⁻¹) * γ₂ := by
          simp [mul_assoc]
        _ = γ₁⁻¹ * γ₂ := by rw [hcancel]
    simpa [hδeq] using δ.2
  exact QuotientGroup.eq.mpr hmem

/-- Helper for Theorem 3.8.10: every point of the universal-cover fiber over `p e` is obtained
from `e` by the deck action of some element of `π₁(B, p e)`. -/
private theorem universalCoverDeck_exists_smul_eq_of_mem_fiber
    (hp : IsUniversalCoveringMap p) (e : E) (x : p ⁻¹' {p e}) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    ∃ γ : FundamentalGroup B (p e), γ • e = x.1 := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI := universalCoverDeckMulActionOf hp e
  have hbot :
      ∀ y : p ⁻¹' {p e}, (FundamentalGroup.mapOfEq p y.2).range = ⊥ := by
    intro y
    exact hp.fundamentalGroup_mapOfEq_range_eq_bot y
  have hex :
      ∃! h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p), h.left.hom e = x.1 := by
    simpa using
      (IsPathConnectedCoveringMap.existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
        hp.isPathConnectedCoveringMap (p e) ⟨e, rfl⟩ x).2
        (by rw [hbot ⟨e, rfl⟩, hbot x])
  rcases hex with ⟨h, hh, _⟩
  have hIso : IsIso h := by
    refine
      (IsPathConnectedCoveringMap.coveringSpaceMorphism_isIso_iff_fundamentalGroup_range_eq
        hp.isPathConnectedCoveringMap hp.isPathConnectedCoveringMap (p e) ⟨e, rfl⟩ x h hh).2 ?_
    rw [hbot ⟨e, rfl⟩, hbot x]
  let i : CoveringSpaceAut p := asIso h
  refine ⟨coveringSpaceAutMulEquivFundamentalGroup hp e i, ?_⟩
  simpa [i, universalCoverDeck_smul_def, CategoryTheory.asIso_hom] using hh

/-- Helper for Theorem 3.8.10: the canonical coset-to-fiber map for the quotient cover `E / K`
is surjective. -/
private theorem universalCoverOrbitFiberPointMap_surjective
    (hp : IsUniversalCoveringMap p) (e : E)
    (K : O(FundamentalGroup B (p e))) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    Function.Surjective (universalCoverOrbitFiberPointMap hp e K) := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI := universalCoverDeckMulActionOf hp e
  intro y
  obtain ⟨x, hx⟩ := Quotient.exists_rep y.1
  let x₀ : p ⁻¹' {p e} := ⟨x, by
    have hx' :
        universalCoverOrbitProjectionObj e K (Quotient.mk'' x) = p e := by
      calc
        universalCoverOrbitProjectionObj e K (Quotient.mk'' x) =
            universalCoverOrbitProjectionObj e K y.1 := congrArg
              (universalCoverOrbitProjectionObj e K) hx
        _ = p e := y.2
    simpa using hx'⟩
  rcases universalCoverDeck_exists_smul_eq_of_mem_fiber hp e x₀ with ⟨γ, hγ⟩
  refine ⟨((γ⁻¹ : FundamentalGroup B (p e)) : FundamentalGroup B (p e) ⧸ K), ?_⟩
  apply Subtype.ext
  -- Route correction: write the target orbit point using a representative `γ⁻¹ K`, so the
  -- inverse in `orbitSpacePointMap` lands exactly on the chosen representative `x`.
  change
    (universalCoverOrbitFiberPointMap hp e K
      ((γ⁻¹ : FundamentalGroup B (p e)) : FundamentalGroup B (p e) ⧸ K)).1 = y.1
  calc
    (universalCoverOrbitFiberPointMap hp e K
        ((γ⁻¹ : FundamentalGroup B (p e)) : FundamentalGroup B (p e) ⧸ K)).1 =
      Quotient.mk'' (γ • e) := by
        change Quotient.mk'' (((γ⁻¹ : FundamentalGroup B (p e))⁻¹) • e) = Quotient.mk'' (γ • e)
        simp
    _ = Quotient.mk'' x := by rw [hγ]
    _ = y.1 := hx

/-- Helper for Theorem 3.8.10: the canonical coset-to-fiber map for `E / K` is bijective. -/
private theorem universalCoverOrbitFiberPointMap_bijective
    (hp : IsUniversalCoveringMap p) (e : E)
    (K : O(FundamentalGroup B (p e))) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    Function.Bijective (universalCoverOrbitFiberPointMap hp e K) := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI := universalCoverDeckMulActionOf hp e
  refine ⟨?_, universalCoverOrbitFiberPointMap_surjective hp e K⟩
  intro q₁ q₂ hq
  exact (universalCoverOrbitPointMap_injective hp e K) (congrArg Subtype.val hq)

/-- The orbit-space map induced by an orbit-category morphism commutes with the quotient covering
projections to `B`. -/
-- Proof sketch: on representatives the induced map is given by a deck transformation of the
-- universal cover, so composing with the quotient covering still agrees with the original
-- projection `p : E → B`.
private theorem universalCoverOrbitMap_comm
    (hp : IsUniversalCoveringMap p) (e : E)
    {H K : O(FundamentalGroup B (p e))} (α : H ⟶ K) :
    TopCat.ofHom (universalCoverOrbitMap e α) ≫
      TopCat.ofHom (universalCoverOrbitProjectionObj e K) =
        TopCat.ofHom (universalCoverOrbitProjectionObj e H) := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  -- Local instance justification (proof-local temporary data): need continuity for the orbit API.
  letI : ContinuousConstSMul (FundamentalGroup B (p e)) E :=
    universalCoverDeckContinuousConstSMul e
  ext q
  refine Quotient.inductionOn' q ?_
  intro x
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep
    ((orbitCategory.homEvalOne H K α :
      FundamentalGroup B (p e) ⧸ K) : FundamentalGroup B (p e) ⧸ K)
  have hα : α.toFun ((1 : FundamentalGroup B (p e)) : FundamentalGroup B (p e) ⧸ H) =
      (γ : FundamentalGroup B (p e) ⧸ K) := by
    -- Rewrite the canonical fixed coset of `α` by the chosen representative `γK`.
    simpa [orbitCategory.homEvalOne] using hγ.symm
  have hproj : p (γ⁻¹ • x) = p x := universalCoverDeck_smul_proj e γ⁻¹ x
  -- On quotient representatives the orbit-space map acts by `x ↦ γ⁻¹ • x`, and deck
  -- transformations preserve the base projection.
  change
    universalCoverOrbitProjectionObj e K
        (universalCoverOrbitMap e α (Quotient.mk'' x)) =
      universalCoverOrbitProjectionObj e H (Quotient.mk'' x)
  have horbit :
      universalCoverOrbitMap e α (Quotient.mk'' x) = Quotient.mk'' (γ⁻¹ • x) := by
    simpa [universalCoverOrbitMap] using
      orbitSpaceMap_apply_mk_of_apply_one α hα x
  rw [horbit]
  change p (γ⁻¹ • x) = p x
  exact hproj

/-- An orbit-category morphism induces a morphism between the corresponding quotient coverings
over `B`. -/
noncomputable def universalCoverOrbitCoveringHom
    [hp : IsUniversalCoveringMap p] (e : E)
    {H K : O(FundamentalGroup B (p e))} (α : H ⟶ K) :
    universalCoverOrbitCoveringObj e H ⟶ universalCoverOrbitCoveringObj e K :=
  ObjectProperty.homMk <|
    Over.homMk
      (TopCat.ofHom (universalCoverOrbitMap e α))
      (universalCoverOrbitMap_comm hp e α)

/-- Identity arrows in the orbit category induce identity morphisms of the corresponding quotient
coverings. -/
-- Proof sketch: `orbitSpaceMap (𝟙 H)` is the identity on `E / H`, so the resulting morphism in
-- the over-category is the identity morphism of the quotient covering.
private theorem universalCoverOrbitCoveringHom_id
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : O(FundamentalGroup B (p e))) :
    universalCoverOrbitCoveringHom e (𝟙 H) =
      𝟙 (universalCoverOrbitCoveringObj e H) := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  -- Local instance justification (proof-local temporary data): need continuity for the orbit API.
  letI : ContinuousConstSMul (FundamentalGroup B (p e)) E :=
    universalCoverDeckContinuousConstSMul e
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  -- The underlying orbit-space map is the identity on the quotient `E / H`.
  simpa [universalCoverOrbitMap] using
    congrArg TopCat.ofHom
      (orbitSpaceMap_id H)

/-- Composition in the orbit category matches composition of the induced quotient-covering
morphisms over `B`. -/
-- Proof sketch: this is functoriality of `orbitSpaceMap`, rewritten in the over-category using the
-- commutative-triangle identities for the quotient covering projections.
private theorem universalCoverOrbitCoveringHom_comp
    (hp : IsUniversalCoveringMap p) (e : E)
    {H K L : O(FundamentalGroup B (p e))}
    (α : H ⟶ K) (β : K ⟶ L) :
    universalCoverOrbitCoveringHom e (α ≫ β) =
      universalCoverOrbitCoveringHom e α ≫
        universalCoverOrbitCoveringHom e β := by
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  -- Local instance justification (proof-local temporary data): need continuity for the orbit API.
  letI : ContinuousConstSMul (FundamentalGroup B (p e)) E :=
    universalCoverDeckContinuousConstSMul e
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  -- Composition of quotient-covering morphisms is exactly composition of the orbit-space maps.
  simpa [universalCoverOrbitMap] using
    congrArg TopCat.ofHom
      (orbitSpaceMap_comp α β)

/-- The orbit-category functor attached to a universal cover sends `G / H` to the quotient
connected covering `E / H → B`. -/
noncomputable def universalCoverOrbitFunctor
    [hp : IsUniversalCoveringMap p] (e : E) :
    O(FundamentalGroup B (p e)) ⥤ ConnectedCoveringSpace B where
  obj H := universalCoverOrbitCoveringObj e H
  map {_ _} α := universalCoverOrbitCoveringHom e α
  map_id H := universalCoverOrbitCoveringHom_id hp e H
  map_comp α β := universalCoverOrbitCoveringHom_comp hp e α β

/-- Helper for Theorem 3.8.10: the quotient-covering functor is already faithful, because an
orbit-category map is determined by the image of the identity coset and that image is recovered by
evaluating the induced covering map at the canonical orbit point. -/
private theorem universalCoverOrbitFunctor_faithful
    (hp : IsUniversalCoveringMap p) (e : E) :
    ((universalCoverOrbitFunctor e :
        O(FundamentalGroup B (p e)) ⥤ ConnectedCoveringSpace B)).Faithful := by
  refine
    { map_injective := ?_ }
  intro H K α β hab
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  have hbase :
      (orbitCategory.homEvalOne H K α : FundamentalGroup B (p e) ⧸ K) =
        (orbitCategory.homEvalOne H K β : FundamentalGroup B (p e) ⧸ K) := by
    exact (universalCoverOrbitPointMap_injective hp e K) <| by
      have hpoint :
          TopCat.Hom.hom (universalCoverOrbitCoveringHom e α).hom.left
              (universalCoverOrbitPointObj e H) =
            TopCat.Hom.hom (universalCoverOrbitCoveringHom e β).hom.left
              (universalCoverOrbitPointObj e H) := by
        exact congrArg
          (fun f ↦ TopCat.Hom.hom f.hom.left (universalCoverOrbitPointObj e H))
          hab
      -- Evaluating at the canonical orbit point converts both covering maps into the corresponding
      -- cosets `α(1H)` and `β(1H)` inside `G / K`.
      simpa
        [universalCoverOrbitCoveringHom, universalCoverOrbitMap, universalCoverOrbitPointObj] using
        hpoint
  have hfixed :
      orbitCategory.homEvalOne H K α = orbitCategory.homEvalOne H K β := by
    exact Subtype.ext hbase
  -- Reconstruct both orbit-category morphisms from their value on the identity coset.
  calc
    α = orbitCategory.homOfFixedPoint H K (orbitCategory.homEvalOne H K α) := by
          symm
          exact orbitCategory.homOfFixedPoint_homEvalOne H K α
    _ = orbitCategory.homOfFixedPoint H K (orbitCategory.homEvalOne H K β) := by
          rw [hfixed]
    _ = β := orbitCategory.homOfFixedPoint_homEvalOne H K β

/-- The quotient map `E → E / H` is a morphism of covering spaces from the universal cover to the
quotient covering `E / H → B`. This is the canonical comparison map reused by later files. -/
noncomputable def universalCoverOrbitQuotientMapHom
    [IsUniversalCoveringMap p] (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    Over.mk (TopCat.ofHom p) ⟶
      Over.mk (TopCat.ofHom (universalCoverOrbitProjection e H)) :=
  Over.homMk
    (TopCat.ofHom ⟨Quotient.mk'', continuous_quotient_mk'⟩)
    (by
      -- The orbit projection was defined by descending `p`, so the triangle commutes on
      -- representatives.
      ext x
      rfl)

/-- Helper for Theorem 3.8.10: the point of the universal-cover fiber over `p e` represented by a
deck translate `γ • e`. -/
private noncomputable def universalCoverDeckFiberPoint
    (hp : IsUniversalCoveringMap p) (e : E)
    (γ : FundamentalGroup B (p e)) :
    p ⁻¹' ({p e} : Set B) :=
  letI : IsUniversalCoveringMap p := hp
  letI := universalCoverDeckMulActionOf hp e
  ⟨γ • e,
    universalCoverDeck_smul_mem_fiber hp e ⊤ (p e)
      ⟨γ, Set.mem_univ _⟩ ⟨e, rfl⟩⟩

/-- Helper for Theorem 3.8.10: a morphism between quotient coverings is determined by the image of
the canonical orbit point, because restriction to the fiber over `p e` is faithful and the source
fiber monodromy action is pretransitive. -/
private theorem universalCoverOrbitCoveringHom_eq_of_eq_at_orbitPoint
    (hp : IsUniversalCoveringMap p) (e : E)
    {H K : O(FundamentalGroup B (p e))}
    (F G : universalCoverOrbitCoveringObj e H ⟶ universalCoverOrbitCoveringObj e K)
    (hFG :
      TopCat.Hom.hom F.hom.left (universalCoverOrbitPointObj e H) =
        TopCat.Hom.hom G.hom.left (universalCoverOrbitPointObj e H)) :
    F = G := by
  let hpH := universalCoverOrbitProjection_isPathConnectedCoveringMap e
    (H : Subgroup (FundamentalGroup B (p e)))
  let hpK := universalCoverOrbitProjection_isPathConnectedCoveringMap e
    (K : Subgroup (FundamentalGroup B (p e)))
  let b0 : B := universalCoverOrbitProjectionObj e H (universalCoverOrbitPointObj e H)
  let x0 : (universalCoverOrbitProjectionObj e H) ⁻¹' {b0} :=
    ⟨universalCoverOrbitPointObj e H, rfl⟩
  -- Local instance justification (proof-local temporary data): fixed source quotient cover.
  letI : IsPathConnectedCoveringMap (universalCoverOrbitProjectionObj e H) := hpH
  -- Local instance justification (proof-local temporary data): fixed target quotient cover.
  letI : IsPathConnectedCoveringMap (universalCoverOrbitProjectionObj e K) := hpK
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hpH b0
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hpK b0
  apply ObjectProperty.hom_ext
  apply (IsPathConnectedCoveringMap.coveringSpaceHomToFiber_bijective b0).1
  apply MulActionHom.ext
  intro x
  have hx0 :
      (IsPathConnectedCoveringMap.coveringSpaceHomToFiber b0 F.hom) x0 =
        (IsPathConnectedCoveringMap.coveringSpaceHomToFiber b0 G.hom) x0 := by
    apply Subtype.ext
    simpa [x0, b0] using hFG
  rcases
      (MulAction.isPretransitive_iff_base x0).mp
        (IsPathConnectedCoveringMap.fiberMonodromyMulAction_isPretransitive
          (universalCoverOrbitPointObj e H)) x with
    ⟨γ, rfl⟩
  -- Compare both fiber maps after moving the chosen basepoint to the target fiber point.
  calc
    (IsPathConnectedCoveringMap.coveringSpaceHomToFiber b0 F.hom) (γ • x0) =
      γ • (IsPathConnectedCoveringMap.coveringSpaceHomToFiber b0 F.hom) x0 := by
          exact (IsPathConnectedCoveringMap.coveringSpaceHomToFiber b0 F.hom).map_smul' γ x0
    _ =
      γ • (IsPathConnectedCoveringMap.coveringSpaceHomToFiber b0 G.hom) x0 := by
          rw [hx0]
    _ =
      (IsPathConnectedCoveringMap.coveringSpaceHomToFiber b0 G.hom) (γ • x0) := by
          exact ((IsPathConnectedCoveringMap.coveringSpaceHomToFiber b0 G.hom).map_smul' γ x0).symm

/-- Helper for Theorem 3.8.10: the fiber permutation induced by a universal-cover deck
transformation commutes with ordinary monodromy on the universal-cover fiber over `p e`. -/
private theorem universalCoverDeckFiberPerm_commutes_with_monodromy
    (hp : IsUniversalCoveringMap p) (e : E)
    (δ γ : FundamentalGroup B (p e)) (x : p ⁻¹' ({p e} : Set B)) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
    IsPathConnectedCoveringMap.coveringSpaceAutFiberPerm e
        ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm δ) (γ • x) =
      γ •
        IsPathConnectedCoveringMap.coveringSpaceAutFiberPerm e
          ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm δ) x := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI : IsPathConnectedCoveringMap p := hp.isPathConnectedCoveringMap
  letI := universalCoverDeckMulActionOf hp e
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
  have hcentral :=
    IsPathConnectedCoveringMap.coveringSpaceAutFiberPerm_mem_gSetAut e
      ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm δ)
  rw [Subgroup.mem_centralizer_iff] at hcentral
  have hcomm :=
    hcentral
      ((MulAction.toPermHom (FundamentalGroup B (p e)) (p ⁻¹' ({p e} : Set B))) γ)
      ⟨γ, rfl⟩
  -- Evaluate the centralizer identity at the chosen fiber point `x`.
  have happly :=
    congrArg (fun τ : Equiv.Perm (p ⁻¹' ({p e} : Set B)) ↦ τ x) hcomm
  simpa using happly.symm

/-- Helper for Theorem 3.8.10: applying the deck transformation corresponding to `δ` to the
represented universal-cover fiber point for `β` gives the represented point for `δ * β`. -/
private theorem universalCoverDeckFiberPerm_apply_representative
    (hp : IsUniversalCoveringMap p) (e : E)
    (δ β : FundamentalGroup B (p e)) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    IsPathConnectedCoveringMap.coveringSpaceAutFiberPerm e
        ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm δ)
        (universalCoverDeckFiberPoint hp e β) =
      universalCoverDeckFiberPoint hp e (δ * β) := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI := universalCoverDeckMulActionOf hp e
  apply Subtype.ext
  -- Both sides evaluate the same composite deck transformation at the basepoint `e`.
  change
    ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm δ *
        (coveringSpaceAutMulEquivFundamentalGroup hp e).symm β) • e =
      ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm (δ * β)) • e
  simp

/- Helper for Theorem 3.8.10: transporting the categorical fiber map of a deck transformation
through `fundamentalGroupoidMapFiberEquiv` recovers the ordinary restriction of that covering
automorphism to the fiber over `p e`. -/
private abbrev universalCoverFundamentalGroupoidFiber
    (hp : IsUniversalCoveringMap p) (e : E) :=
  let q := hp.isPathConnectedCoveringMap.fundamentalGroupoidMap
  q.Fiber (FundamentalGroupoid.mk (p e))

omit [LocPathConnectedSpace E] in
private theorem universalCoverDeck_fundamentalGroupoidFiberEquiv_map
    (hp : IsUniversalCoveringMap p) (e : E) (α : CoveringSpaceAut p)
    (x : universalCoverFundamentalGroupoidFiber hp e) :
    hp.isPathConnectedCoveringMap.fundamentalGroupoidMapFiberEquiv (p e)
      (Functor.IsCovering.mapOfCoveringsToFiberFun
          (FundamentalGroupoid.mk (p e))
          (hp.isPathConnectedCoveringMap.toFundamentalGroupoidCoveringHom
            hp.isPathConnectedCoveringMap α.hom)
          x) =
      IsPathConnectedCoveringMap.coveringSpaceHomToFiberFun (p e) α.hom
        (hp.isPathConnectedCoveringMap.fundamentalGroupoidMapFiberEquiv (p e) x) := by
  -- Both constructions evaluate the same deck transformation on the underlying point of the
  -- chosen groupoid fiber.
  apply Subtype.ext
  rfl

/-- Helper for Theorem 3.8.10: the Corollary 3.7.11 equivalence chain carries the deck
transformation corresponding to `γ⁻¹` to the explicit fiber automorphism used in the basepoint
comparison. -/
private theorem universalCoverDeck_basepoint_fiberAut_eq_explicit
    (hp : IsUniversalCoveringMap p) (e : E)
    (γ : FundamentalGroup B (p e)) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    let h_regular := IsUniversalCoveringMap.isRegularCoveringMap hp e
    letI : (FundamentalGroup.map p e).range.Normal := h_regular.normal_fundamentalGroup_map_range
    letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
    let α : CoveringSpaceAut p :=
      (coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ⁻¹
    let φ : Aut_ (FundamentalGroup B (p e)) (p ⁻¹' ({p e} : Set B)) :=
      (hp.isPathConnectedCoveringMap.fiberAutMulEquivWeylGroup_fundamentalGroupRange e).symm
        ((Subgroup.weylGroupMulEquivQuotientOfNormal ((FundamentalGroup.map p e).range)).symm
          ((QuotientGroup.quotientMulEquivOfEq (hp.fundamentalGroup_map_range_eq_bot e)).symm
            (QuotientGroup.quotientBot.symm γ⁻¹)))
    (hp.isPathConnectedCoveringMap.coveringSpaceAutMulEquivFiberAut e) α = φ := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI : IsPathConnectedCoveringMap p := hp.isPathConnectedCoveringMap
  letI := universalCoverDeckMulActionOf hp e
  let h_regular := IsUniversalCoveringMap.isRegularCoveringMap hp e
  letI : (FundamentalGroup.map p e).range.Normal := h_regular.normal_fundamentalGroup_map_range
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
  let α : CoveringSpaceAut p :=
    (coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ⁻¹
  have hα : coveringSpaceAutMulEquivFundamentalGroup hp e α = γ⁻¹ := by
    -- The chosen deck transformation is defined as the inverse image of `γ⁻¹`.
    simp [α]
  let φ : Aut_ (FundamentalGroup B (p e)) (p ⁻¹' ({p e} : Set B)) :=
    (hp.isPathConnectedCoveringMap.fiberAutMulEquivWeylGroup_fundamentalGroupRange e).symm
      ((Subgroup.weylGroupMulEquivQuotientOfNormal ((FundamentalGroup.map p e).range)).symm
        ((QuotientGroup.quotientMulEquivOfEq (hp.fundamentalGroup_map_range_eq_bot e)).symm
          (QuotientGroup.quotientBot.symm γ⁻¹)))
  -- Normalize the deck automorphism and the explicit model through the quotient and Weyl-group
  -- stages of Corollary 3.7.11.
  apply
    (hp.isPathConnectedCoveringMap.fiberAutMulEquivWeylGroup_fundamentalGroupRange e).injective
  have hquot :
      IsRegularCoveringMap.coveringSpaceAutMulEquivQuotientFundamentalGroupRange
          h_regular α =
        (QuotientGroup.quotientMulEquivOfEq (hp.fundamentalGroup_map_range_eq_bot e)).symm
          (QuotientGroup.quotientBot.symm γ⁻¹) := by
    -- Extract the quotient-stage value from the universal-cover equivalence formula.
    rw [IsUniversalCoveringMap.coveringSpaceAutMulEquivFundamentalGroup_apply] at hα
    exact
      (((QuotientGroup.quotientMulEquivOfEq (hp.fundamentalGroup_map_range_eq_bot e)).trans
        QuotientGroup.quotientBot).injective hα)
  have hweyl :
      (IsPathConnectedCoveringMap.coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange e) α =
        (Subgroup.weylGroupMulEquivQuotientOfNormal ((FundamentalGroup.map p e).range)).symm
          (IsRegularCoveringMap.coveringSpaceAutMulEquivQuotientFundamentalGroupRange
            h_regular α) := by
    -- Move from the quotient description of deck automorphisms to the Weyl-group model.
    apply (Subgroup.weylGroupMulEquivQuotientOfNormal ((FundamentalGroup.map p e).range)).injective
    simpa [IsRegularCoveringMap.coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange,
      IsRegularCoveringMap.weylGroupMulEquivFundamentalGroupRangeQuotient] using
      IsRegularCoveringMap.coveringSpaceAutMulEquivQuotientFundamentalGroupRange_apply
        h_regular α
  calc
    (hp.isPathConnectedCoveringMap.fiberAutMulEquivWeylGroup_fundamentalGroupRange e)
        ((hp.isPathConnectedCoveringMap.coveringSpaceAutMulEquivFiberAut e) α) =
        (hp.isPathConnectedCoveringMap.coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange e)
          α := by
          have happly :=
            IsPathConnectedCoveringMap.coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange_apply
              e α
          exact happly.symm
    _ =
      (Subgroup.weylGroupMulEquivQuotientOfNormal ((FundamentalGroup.map p e).range)).symm
        ((QuotientGroup.quotientMulEquivOfEq (hp.fundamentalGroup_map_range_eq_bot e)).symm
          (QuotientGroup.quotientBot.symm γ⁻¹)) := by
            exact hweyl.trans (by rw [hquot])
    _ =
      (hp.isPathConnectedCoveringMap.fiberAutMulEquivWeylGroup_fundamentalGroupRange e) φ := by
          simp [φ]

/-- Helper for Theorem 3.8.10: the deck transformation corresponding to `γ⁻¹` sends the
distinguished universal-cover fiber point to the monodromy translate by `γ`. -/
private theorem quotientStabilizerEquivOfIsPretransitive_basepoint
    {G S : Type u} [Group G] [MulAction G S] [MulAction.IsPretransitive G S]
    (s : S) :
    quotientStabilizerEquivOfIsPretransitive s
        (((1 : G) : G) : G ⧸ MulAction.stabilizer G s) = s := by
  -- The identity coset acts trivially on the chosen basepoint.
  change (1 : G) • s = s
  simp

/-- Helper for Theorem 3.8.10: the chosen basepoint corresponds to the identity coset in the
quotient-stabilizer model. -/
private theorem quotientStabilizerEquivOfIsPretransitive_symm_basepoint
    {G S : Type u} [Group G] [MulAction G S] [MulAction.IsPretransitive G S]
    (s : S) :
    (quotientStabilizerEquivOfIsPretransitive s).symm s =
      (((1 : G) : G) : G ⧸ MulAction.stabilizer G s) := by
  let e : G ⧸ MulAction.stabilizer G s ≃ S := quotientStabilizerEquivOfIsPretransitive s
  -- Injectivity lets us identify the preimage of the basepoint with the identity coset.
  apply e.injective
  rw [e.apply_symm_apply, quotientStabilizerEquivOfIsPretransitive_basepoint]

/-- Helper for Theorem 3.8.10: for a quotient permutation, evaluating the inverse at the identity
coset is equivalent to checking that the forward permutation sends the translated identity coset
back to the identity. -/
private theorem quotient_gset_symm_apply_identity_iff
    {G : Type u} [Group G] (H : Subgroup G) [H.Normal]
    (σ : gSetAut G (G ⧸ H)) (g : G) :
    σ.1.symm ((((1 : G) : G) : G ⧸ H)) = g • (((1 : G) : G) : G ⧸ H) ↔
      σ.1 (g • (((1 : G) : G) : G ⧸ H)) = (((1 : G) : G) : G ⧸ H) := by
  -- Rewrite inverse evaluation into a forward evaluation at the translated identity coset.
  constructor
  · intro h
    rw [Equiv.symm_apply_eq] at h
    exact h.symm
  · intro h
    rw [Equiv.symm_apply_eq]
    exact h.symm

/-- Helper for Theorem 3.8.10: after identifying the stabilizer with `⊥`, the Weyl-group element
coming from `g⁻¹` should send the identity coset to `gG_s`. -/
private theorem weylGroup_quotientGSet_apply_identity_of_bot
    {G : Type u} [Group G] (g : G) :
    ((weylGroupMulEquivQuotientGSetAut (⊥ : Subgroup G))
        ((Subgroup.weylGroupMulEquivQuotientOfNormal (⊥ : Subgroup G)).symm
          (QuotientGroup.quotientBot.symm g⁻¹))).1
      ((((1 : G) : G) : G ⧸ (⊥ : Subgroup G))) =
        g • (((1 : G) : G) : G ⧸ (⊥ : Subgroup G)) := by
  -- In the literal `⊥` quotient model, the Weyl-group automorphism is just right translation.
  conv_lhs =>
    whnf
    whnf
    whnf
  rw [show g • (((1 : G) : G) : G ⧸ (⊥ : Subgroup G)) =
      (((g * 1 : G) : G) : G ⧸ (⊥ : Subgroup G)) by
    rfl]
  -- One more weak-head normalization exposes the quotient representative `g`.
  conv_lhs =>
    whnf
  simp
  rfl

/-- Helper for Theorem 3.8.10: after identifying the stabilizer with `⊥`, the Weyl-group element
coming from `g⁻¹` should send the identity coset to `gG_s`. -/
private theorem weylGroup_quotientAut_apply_identity_of_stabilizer_eq_bot
    {G S : Type u} [Group G] [MulAction G S] [MulAction.IsPretransitive G S]
    (s : S) (hstab : MulAction.stabilizer G s = ⊥) (g : G) :
    letI : (MulAction.stabilizer G s).Normal := hstab ▸ Subgroup.normal_bot
    ((weylGroupMulEquivQuotientAut (MulAction.stabilizer G s))
        ((Subgroup.weylGroupMulEquivQuotientOfNormal (MulAction.stabilizer G s)).symm
          ((QuotientGroup.quotientMulEquivOfEq hstab).symm
            (QuotientGroup.quotientBot.symm g⁻¹)))).hom.hom
      ((((1 : G) : G) : G ⧸ MulAction.stabilizer G s)) =
        g • (((1 : G) : G) : G ⧸ MulAction.stabilizer G s) := by
  letI : (MulAction.stabilizer G s).Normal := hstab ▸ Subgroup.normal_bot
  -- Route correction: transport to the literal `⊥` quotient model instead of eliminating the
  -- dependent normality witness directly.
  change
    ((weylGroupMulEquivQuotientGSetAut (MulAction.stabilizer G s))
        ((Subgroup.weylGroupMulEquivQuotientOfNormal (MulAction.stabilizer G s)).symm
          ((QuotientGroup.quotientMulEquivOfEq hstab).symm
            (QuotientGroup.quotientBot.symm g⁻¹)))).1
      ((((1 : G) : G) : G ⧸ MulAction.stabilizer G s)) =
        g • (((1 : G) : G) : G ⧸ MulAction.stabilizer G s)
  -- Weak-head normalization exposes the quotient representative `g` of the Weyl element.
  conv_lhs =>
    whnf
    whnf
    whnf
  rw [show g • (((1 : G) : G) : G ⧸ MulAction.stabilizer G s) =
      (((g * 1 : G) : G) : G ⧸ MulAction.stabilizer G s) by
    rfl]
  simp
  rfl

/-- Helper for Theorem 3.8.10: the deck transformation corresponding to `γ⁻¹` sends the
distinguished universal-cover fiber point to the monodromy translate by `γ`. -/
private theorem weylGroup_aut_apply_basepoint_of_stabilizer_eq_bot
    {G S : Type u} [Group G] [MulAction G S] [MulAction.IsPretransitive G S]
    (s : S) (hstab : MulAction.stabilizer G s = ⊥) (g : G) :
    letI : (MulAction.stabilizer G s).Normal := hstab ▸ Subgroup.normal_bot
    let φ : Aut_ G S :=
      weylGroup_stabilizer_mulEquiv_aut s
        ((Subgroup.weylGroupMulEquivQuotientOfNormal (MulAction.stabilizer G s)).symm
          ((QuotientGroup.quotientMulEquivOfEq hstab).symm
            (QuotientGroup.quotientBot.symm g⁻¹)))
    φ.hom.hom s = g • s := by
  letI : (MulAction.stabilizer G s).Normal := hstab ▸ Subgroup.normal_bot
  let φ : Aut_ G S :=
    weylGroup_stabilizer_mulEquiv_aut s
      ((Subgroup.weylGroupMulEquivQuotientOfNormal (MulAction.stabilizer G s)).symm
        ((QuotientGroup.quotientMulEquivOfEq hstab).symm
          (QuotientGroup.quotientBot.symm g⁻¹)))
  let e : G ⧸ MulAction.stabilizer G s ≃ S := quotientStabilizerEquivOfIsPretransitive s
  -- Route correction: isolate the remaining issue as a pure quotient-automorphism computation
  -- on the identity coset, away from the universal-cover topology.
  rw [weylGroup_stabilizer_mulEquiv_aut_apply]
  rw [quotientStabilizerAutMulEquiv_apply]
  change
    e
      (((weylGroupMulEquivQuotientAut (MulAction.stabilizer G s))
            ((Subgroup.weylGroupMulEquivQuotientOfNormal (MulAction.stabilizer G s)).symm
              ((QuotientGroup.quotientMulEquivOfEq hstab).symm
                (QuotientGroup.quotientBot.symm g⁻¹)))).hom.hom
        (e.symm s)) =
      g • s
  rw [quotientStabilizerEquivOfIsPretransitive_symm_basepoint s]
  rw [weylGroup_quotientAut_apply_identity_of_stabilizer_eq_bot s hstab g]
  -- Transport the solved quotient-side computation back to the original transitive action.
  calc
    e (g • (((1 : G) : G) : G ⧸ MulAction.stabilizer G s)) =
        g • e (((1 : G) : G) : G ⧸ MulAction.stabilizer G s) := by
          simpa [e] using
            quotientStabilizerEquivOfIsPretransitive_equivariant
              s g (((1 : G) : G) : G ⧸ MulAction.stabilizer G s)
    _ = g • s := by
          rw [quotientStabilizerEquivOfIsPretransitive_basepoint s]

/-- Helper for Theorem 3.8.10: transporting the normal-subgroup quotient representative from
`R` to `K` along equalities `K = R` and `R = ⊥` agrees with the direct quotient representative
for `K = ⊥`. -/
private theorem weyl_group_quotient_of_eq_bot_cast_eq
    {G : Type u} [Group G] (K R : Subgroup G)
    (hKR : K = R) (hR : R = ⊥) (g : G) :
    letI : K.Normal := (hKR.trans hR) ▸ Subgroup.normal_bot
    letI : R.Normal := hR ▸ Subgroup.normal_bot
    cast (by simp [hKR, hR])
      ((Subgroup.weylGroupMulEquivQuotientOfNormal R).symm
        ((QuotientGroup.quotientMulEquivOfEq hR).symm
          (QuotientGroup.quotientBot.symm g⁻¹))) =
      ((Subgroup.weylGroupMulEquivQuotientOfNormal K).symm
        ((QuotientGroup.quotientMulEquivOfEq (hKR.trans hR)).symm
          (QuotientGroup.quotientBot.symm g⁻¹))) := by
  letI : K.Normal := (hKR.trans hR) ▸ Subgroup.normal_bot
  letI : R.Normal := hR ▸ Subgroup.normal_bot
  -- Once both subgroup equalities are specialized to `rfl`, the transported quotient element is
  -- definitionally the direct quotient representative.
  cases hKR
  cases hR
  rfl

/- Helper for Theorem 3.8.10: the universal-cover fiber action has trivial stabilizer at the
distinguished basepoint. -/
omit [LocPathConnectedSpace E] in
private theorem universalCoverFiberMonodromy_stabilizer_eq_bot
    (hp : IsUniversalCoveringMap p) (e : E) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
    let x0 : p ⁻¹' ({p e} : Set B) := ⟨e, rfl⟩
    MulAction.stabilizer (FundamentalGroup B (p e)) x0 = ⊥ := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : IsPathConnectedCoveringMap p := hp.isPathConnectedCoveringMap
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
  let x0 : p ⁻¹' ({p e} : Set B) := ⟨e, rfl⟩
  -- Compare the monodromy stabilizer with the image subgroup, then use universality.
  have hstabRange :
      MulAction.stabilizer (FundamentalGroup B (p e)) x0 =
        (FundamentalGroup.map p e).range :=
    hp.isPathConnectedCoveringMap.fiberMonodromyMulAction_stabilizer_eq_fundamentalGroupRange e
  simpa [x0] using hstabRange.trans (hp.fundamentalGroup_map_range_eq_bot e)

omit [LocPathConnectedSpace E] in
/-- Helper for Theorem 3.8.10: the explicit inverse fiber-automorphism model sends the
distinguished universal-cover fiber point to the monodromy translate by `γ`. -/
private theorem universalCoverFiberAutEquiv_apply_basepoint
    (hp : IsUniversalCoveringMap p) (e : E)
    (γ : FundamentalGroup B (p e)) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
    let x0 : p ⁻¹' ({p e} : Set B) := ⟨e, rfl⟩
    let h_regular := IsUniversalCoveringMap.isRegularCoveringMap hp e
    letI : (FundamentalGroup.map p e).range.Normal := h_regular.normal_fundamentalGroup_map_range
    let φ : Aut_ (FundamentalGroup B (p e)) (p ⁻¹' ({p e} : Set B)) :=
      (hp.isPathConnectedCoveringMap.fiberAutMulEquivWeylGroup_fundamentalGroupRange e).symm
        ((Subgroup.weylGroupMulEquivQuotientOfNormal ((FundamentalGroup.map p e).range)).symm
          ((QuotientGroup.quotientMulEquivOfEq (hp.fundamentalGroup_map_range_eq_bot e)).symm
            (QuotientGroup.quotientBot.symm γ⁻¹)))
    φ.hom.hom x0 = γ • x0 := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : IsPathConnectedCoveringMap p := hp.isPathConnectedCoveringMap
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
  letI : MulAction.IsPretransitive (FundamentalGroup B (p e)) (p ⁻¹' ({p e} : Set B)) :=
    IsPathConnectedCoveringMap.fiberMonodromyMulAction_isPretransitive e
  let h_regular := IsUniversalCoveringMap.isRegularCoveringMap hp e
  letI : (FundamentalGroup.map p e).range.Normal := h_regular.normal_fundamentalGroup_map_range
  let x0 : p ⁻¹' ({p e} : Set B) := ⟨e, rfl⟩
  let φ : Aut_ (FundamentalGroup B (p e)) (p ⁻¹' ({p e} : Set B)) :=
    (hp.isPathConnectedCoveringMap.fiberAutMulEquivWeylGroup_fundamentalGroupRange e).symm
      ((Subgroup.weylGroupMulEquivQuotientOfNormal ((FundamentalGroup.map p e).range)).symm
        ((QuotientGroup.quotientMulEquivOfEq (hp.fundamentalGroup_map_range_eq_bot e)).symm
          (QuotientGroup.quotientBot.symm γ⁻¹)))
  have hstab : MulAction.stabilizer (FundamentalGroup B (p e)) x0 = ⊥ := by
    -- Universality turns the fiber stabilizer into the trivial subgroup.
    simpa [x0] using universalCoverFiberMonodromy_stabilizer_eq_bot hp e
  have hstabRange :
      MulAction.stabilizer (FundamentalGroup B (p e)) x0 = (FundamentalGroup.map p e).range := by
    -- Corollary 3.7.11 identifies the fiber stabilizer with the image subgroup.
    simpa [x0] using
      hp.isPathConnectedCoveringMap.fiberMonodromyMulAction_stabilizer_eq_fundamentalGroupRange e
  letI : (MulAction.stabilizer (FundamentalGroup B (p e)) x0).Normal := hstab ▸ Subgroup.normal_bot
  have hφ :
      φ =
        (weylGroup_stabilizer_mulEquiv_aut x0)
          ((Subgroup.weylGroupMulEquivQuotientOfNormal
              (MulAction.stabilizer (FundamentalGroup B (p e)) x0)).symm
            ((QuotientGroup.quotientMulEquivOfEq hstab).symm
              (QuotientGroup.quotientBot.symm γ⁻¹))) := by
    -- Rewrite the range-based Weyl element in the universal-cover fiber equivalence into the
    -- stabilizer-based Weyl model used by the generic basepoint computation.
    dsimp [φ, IsPathConnectedCoveringMap.fiberAutMulEquivWeylGroup_fundamentalGroupRange]
    simpa [hstab] using
      congrArg (weylGroup_stabilizer_mulEquiv_aut x0)
        (weyl_group_quotient_of_eq_bot_cast_eq
          (MulAction.stabilizer (FundamentalGroup B (p e)) x0)
          (FundamentalGroup.map p e).range
          hstabRange (hp.fundamentalGroup_map_range_eq_bot e) γ)
  change φ.hom.hom x0 = γ • x0
  rw [hφ]
  -- The remaining pointwise computation is exactly the generic stabilizer-`⊥` statement.
  exact weylGroup_aut_apply_basepoint_of_stabilizer_eq_bot x0 hstab γ

private theorem universalCoverDeck_basepoint_fiberPerm_eq_monodromy
    (hp : IsUniversalCoveringMap p) (e : E)
    (γ : FundamentalGroup B (p e)) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
    let x0 : p ⁻¹' ({p e} : Set B) := ⟨e, rfl⟩
    let α : CoveringSpaceAut p :=
      (coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ⁻¹
    IsPathConnectedCoveringMap.coveringSpaceAutFiberPerm e α x0 = γ • x0 := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI : IsPathConnectedCoveringMap p := hp.isPathConnectedCoveringMap
  letI := universalCoverDeckMulActionOf hp e
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
  let h_regular := IsUniversalCoveringMap.isRegularCoveringMap hp e
  letI : (FundamentalGroup.map p e).range.Normal := h_regular.normal_fundamentalGroup_map_range
  let x0 : p ⁻¹' ({p e} : Set B) := ⟨e, rfl⟩
  let α : CoveringSpaceAut p :=
    (coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ⁻¹
  let φ : Aut_ (FundamentalGroup B (p e)) (p ⁻¹' ({p e} : Set B)) :=
    (hp.isPathConnectedCoveringMap.fiberAutMulEquivWeylGroup_fundamentalGroupRange e).symm
      ((Subgroup.weylGroupMulEquivQuotientOfNormal ((FundamentalGroup.map p e).range)).symm
        ((QuotientGroup.quotientMulEquivOfEq (hp.fundamentalGroup_map_range_eq_bot e)).symm
          (QuotientGroup.quotientBot.symm γ⁻¹)))
  -- Route correction: compute the deck action at the basepoint through the universal-cover
  -- automorphism/fiber-action equivalence, instead of comparing lifts directly.
  have hφ :
      (IsPathConnectedCoveringMap.coveringSpaceAutMulEquivFiberAut e) α = φ := by
    -- Reuse the extracted normalization lemma so the remaining blocker is purely pointwise.
    simpa [h_regular, α, φ] using universalCoverDeck_basepoint_fiberAut_eq_explicit hp e γ
  -- Evaluate the explicit quotient/Weyl-group automorphism at the distinguished fiber point.
  have hbase : φ.hom.hom x0 = γ • x0 := by
    simpa [h_regular, x0, φ] using universalCoverFiberAutEquiv_apply_basepoint hp e γ
  -- Rewrite the deck permutation into the fiber automorphism identified above.
  change
    ((hp.isPathConnectedCoveringMap.coveringSpaceAutMulEquivFiberAut e) α).hom.hom x0 = γ • x0
  rw [hφ]
  exact hbase

/-- Helper for Theorem 3.8.10: after transporting to the ordinary fiber over `p e`, the
categorical action of `γ.toPath⁻¹` agrees with the induced map of the deck transformation
representing `γ⁻¹`. -/
private theorem universalCoverDeck_basepoint_groupoidFiber_compare
    (hp : IsUniversalCoveringMap p) (e : E)
    (γ : FundamentalGroup B (p e)) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
    let hp' := hp.isPathConnectedCoveringMap
    letI : MulAction (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e))
      (hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e))) :=
      Functor.IsCovering.fiberTranslationMulAction
        hp'.fundamentalGroupoidMap_isCovering (FundamentalGroupoid.mk (p e))
    let ξ0 : hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e)) :=
      ⟨FundamentalGroupoid.mk e, rfl⟩
    let δ : FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e) := γ.toPath
    let α : CoveringSpaceAut p :=
      (coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ⁻¹
    δ⁻¹ • ξ0 =
      Functor.IsCovering.mapOfCoveringsToFiberFun
        (FundamentalGroupoid.mk (p e))
        (hp'.toFundamentalGroupoidCoveringHom hp' α.hom)
        ξ0 := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI := universalCoverDeckMulActionOf hp e
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
  let hp' := hp.isPathConnectedCoveringMap
  letI : MulAction (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e))
      (hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e))) :=
    Functor.IsCovering.fiberTranslationMulAction
      hp'.fundamentalGroupoidMap_isCovering (FundamentalGroupoid.mk (p e))
  let x0 : p ⁻¹' ({p e} : Set B) := ⟨e, rfl⟩
  let ξ0 : hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e)) :=
    ⟨FundamentalGroupoid.mk e, rfl⟩
  let δ : FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e) := γ.toPath
  let α : CoveringSpaceAut p :=
    (coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ⁻¹
  have hsmul :
      δ⁻¹ • ξ0 =
        Functor.IsCovering.fiberTranslationMap
          hp'.fundamentalGroupoidMap_isCovering δ ξ0 := by
    -- Rewrite the categorical vertex-group action as direct fiber translation by `δ`.
    change δ⁻¹ • ξ0 =
      (Functor.IsCovering.fiberTranslationFunctor
        hp'.fundamentalGroupoidMap_isCovering).map δ ξ0
    simpa using Functor.vertexGroupAction_smul_eq_map_inv
      (Functor.IsCovering.fiberTranslationFunctor
        hp'.fundamentalGroupoidMap_isCovering)
      (FundamentalGroupoid.mk (p e)) δ⁻¹ ξ0
  have htransport :
      hp'.fundamentalGroupoidMapFiberEquiv (p e)
          (Functor.IsCovering.fiberTranslationMap
            hp'.fundamentalGroupoidMap_isCovering δ ξ0) =
        hp'.fiberTranslationMap δ x0 := by
    -- Transport the categorical fiber translation back to the ordinary fiber over `p e`.
    change hp'.fundamentalGroupoidMapFiberEquiv (p e)
        (Functor.IsCovering.fiberTranslationMap
          hp'.fundamentalGroupoidMap_isCovering γ.toPath ξ0) =
      hp'.fiberTranslationMap γ.toPath x0
    exact IsPathConnectedCoveringMap.fundamentalGroupoidMapFiberEquiv_fiberTranslation
      hp' (p e) γ ξ0
  apply (hp'.fundamentalGroupoidMapFiberEquiv (p e)).injective
  -- After transporting both sides to the ordinary fiber, Step 1 identifies the remaining point.
  calc
    hp'.fundamentalGroupoidMapFiberEquiv (p e) (δ⁻¹ • ξ0) =
        hp'.fundamentalGroupoidMapFiberEquiv (p e)
          (Functor.IsCovering.fiberTranslationMap
            hp'.fundamentalGroupoidMap_isCovering δ ξ0) := by
              exact congrArg (hp'.fundamentalGroupoidMapFiberEquiv (p e)) hsmul
    _ = hp'.fiberTranslationMap δ x0 := htransport
    _ = γ • x0 := by rfl
    _ = IsPathConnectedCoveringMap.coveringSpaceAutFiberPerm e α x0 := by
          symm
          simpa [x0, α] using universalCoverDeck_basepoint_fiberPerm_eq_monodromy hp e γ
    _ = IsPathConnectedCoveringMap.coveringSpaceHomToFiberFun (p e) α.hom x0 := by
          rfl
    _ = hp'.fundamentalGroupoidMapFiberEquiv (p e)
          (Functor.IsCovering.mapOfCoveringsToFiberFun
            (FundamentalGroupoid.mk (p e))
            (hp'.toFundamentalGroupoidCoveringHom hp' α.hom)
            ξ0) := by
          symm
          simpa [x0, α] using universalCoverDeck_fundamentalGroupoidFiberEquiv_map hp e α ξ0

/-- Helper for Theorem 3.8.10: transporting the categorical fiber action of `γ.toPath⁻¹` at the
distinguished groupoid-fiber point recovers the explicit deck-translate representative
`γ⁻¹ • e` in the ordinary fiber over `p e`. -/
private theorem universalCoverDeck_basepoint_groupoidFiber_eq
    (hp : IsUniversalCoveringMap p) (e : E)
    (γ : FundamentalGroup B (p e)) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
    γ • (⟨e, rfl⟩ : p ⁻¹' ({p e} : Set B)) =
      universalCoverDeckFiberPoint hp e γ⁻¹ := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI := universalCoverDeckMulActionOf hp e
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
  let hp' := hp.isPathConnectedCoveringMap
  letI : MulAction (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e))
      (hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e))) :=
    Functor.IsCovering.fiberTranslationMulAction
      hp'.fundamentalGroupoidMap_isCovering (FundamentalGroupoid.mk (p e))
  let x0 : p ⁻¹' ({p e} : Set B) := ⟨e, rfl⟩
  let ξ0 : hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e)) :=
    ⟨FundamentalGroupoid.mk e, rfl⟩
  let δ : FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e) := γ.toPath
  have hsmul :
      δ⁻¹ • ξ0 =
        Functor.IsCovering.fiberTranslationMap
          hp'.fundamentalGroupoidMap_isCovering δ ξ0 := by
    -- Rewrite the categorical vertex-group action as direct fiber translation along `γ.toPath`.
    change δ⁻¹ • ξ0 =
      (Functor.IsCovering.fiberTranslationFunctor
        hp'.fundamentalGroupoidMap_isCovering).map δ ξ0
    simpa using Functor.vertexGroupAction_smul_eq_map_inv
      (Functor.IsCovering.fiberTranslationFunctor
        hp'.fundamentalGroupoidMap_isCovering)
      (FundamentalGroupoid.mk (p e)) δ⁻¹ ξ0
  have htransport :
      hp'.fundamentalGroupoidMapFiberEquiv (p e)
          (Functor.IsCovering.fiberTranslationMap
            hp'.fundamentalGroupoidMap_isCovering δ ξ0) =
        hp'.fiberTranslationMap δ x0 := by
    -- Transport the categorical fiber translation back to the ordinary fiber over `p e`.
    change hp'.fundamentalGroupoidMapFiberEquiv (p e)
        (Functor.IsCovering.fiberTranslationMap
          hp'.fundamentalGroupoidMap_isCovering δ ξ0) =
      hp'.fiberTranslationMap δ x0
    exact IsPathConnectedCoveringMap.fundamentalGroupoidMapFiberEquiv_fiberTranslation
      hp' (p e) γ ξ0
  let α : CoveringSpaceAut p :=
    (coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ⁻¹
  have hdeckMap :
      hp'.fundamentalGroupoidMapFiberEquiv (p e)
          (Functor.IsCovering.mapOfCoveringsToFiberFun
            (FundamentalGroupoid.mk (p e))
            (hp'.toFundamentalGroupoidCoveringHom hp' α.hom)
            ξ0) =
        universalCoverDeckFiberPoint hp e γ⁻¹ := by
    -- Transport the induced categorical map of the chosen deck transformation back to the
    -- ordinary fiber and then evaluate it at the distinguished basepoint `e`.
    calc
      hp'.fundamentalGroupoidMapFiberEquiv (p e)
          (Functor.IsCovering.mapOfCoveringsToFiberFun
            (FundamentalGroupoid.mk (p e))
            (hp'.toFundamentalGroupoidCoveringHom hp' α.hom)
            ξ0) =
          IsPathConnectedCoveringMap.coveringSpaceHomToFiberFun
            (p e) α.hom x0 := by
              simpa [hp', x0] using
                universalCoverDeck_fundamentalGroupoidFiberEquiv_map hp e α ξ0
      _ = universalCoverDeckFiberPoint hp e γ⁻¹ := by
            apply Subtype.ext
            -- Both sides are the value of the same deck transformation at the basepoint `e`.
            change TopCat.Hom.hom α.hom.left e = γ⁻¹ • e
            rw [universalCoverDeck_smul_def e γ⁻¹ e]
            rfl
  have hdeck :
      hp'.fundamentalGroupoidMapFiberEquiv (p e) (δ⁻¹ • ξ0) =
        universalCoverDeckFiberPoint hp e γ⁻¹ := by
    have hcompare :
        δ⁻¹ • ξ0 =
          Functor.IsCovering.mapOfCoveringsToFiberFun
            (FundamentalGroupoid.mk (p e))
            (hp'.toFundamentalGroupoidCoveringHom hp' α.hom)
            ξ0 := by
      -- Compare the two categorical points by transporting them to the ordinary fiber over `p e`.
      simpa [hp', ξ0, δ, α] using universalCoverDeck_basepoint_groupoidFiber_compare hp e γ
    -- After the categorical comparison, the transported point is exactly the explicit deck
    -- representative `γ⁻¹ • e`.
    calc
      hp'.fundamentalGroupoidMapFiberEquiv (p e) (δ⁻¹ • ξ0) =
          hp'.fundamentalGroupoidMapFiberEquiv (p e)
            (Functor.IsCovering.mapOfCoveringsToFiberFun
              (FundamentalGroupoid.mk (p e))
              (hp'.toFundamentalGroupoidCoveringHom hp' α.hom)
              ξ0) := by rw [hcompare]
      _ = universalCoverDeckFiberPoint hp e γ⁻¹ := hdeckMap
  -- Route correction: compare monodromy with the explicit representative by transporting the
  -- groupoid-fiber action first, instead of unpacking the Weyl-group inverse description.
  calc
    γ • x0 = hp'.fiberTranslationMap γ.toPath x0 := by
      rfl
    _ = hp'.fundamentalGroupoidMapFiberEquiv (p e)
          (Functor.IsCovering.fiberTranslationMap
            hp'.fundamentalGroupoidMap_isCovering γ.toPath ξ0) := htransport.symm
    _ = hp'.fundamentalGroupoidMapFiberEquiv (p e) (δ⁻¹ • ξ0) := by
          exact congrArg (hp'.fundamentalGroupoidMapFiberEquiv (p e)) hsmul.symm
    _ = universalCoverDeckFiberPoint hp e γ⁻¹ := hdeck

/-- Helper for Theorem 3.8.10: monodromy at the distinguished universal-cover fiber point agrees
with the fiber permutation induced by the deck transformation corresponding to `γ⁻¹`. -/
private theorem universalCoverFiberMonodromy_basepoint_eq_deckPerm
    (hp : IsUniversalCoveringMap p) (e : E)
    (γ : FundamentalGroup B (p e)) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
    γ • (⟨e, rfl⟩ : p ⁻¹' ({p e} : Set B)) =
      IsPathConnectedCoveringMap.coveringSpaceAutFiberPerm e
        ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ⁻¹)
        (⟨e, rfl⟩ : p ⁻¹' ({p e} : Set B)) := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI := universalCoverDeckMulActionOf hp e
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
  let x0 : p ⁻¹' ({p e} : Set B) := ⟨e, rfl⟩
  have hone : universalCoverDeckFiberPoint hp e (1 : FundamentalGroup B (p e)) = x0 := by
    apply Subtype.ext
    simp [universalCoverDeckFiberPoint, x0]
  -- First identify both sides with the same represented deck translate `γ⁻¹ • e`.
  calc
    γ • x0 = universalCoverDeckFiberPoint hp e γ⁻¹ := by
      simpa [x0] using universalCoverDeck_basepoint_groupoidFiber_eq hp e γ
    _ =
      IsPathConnectedCoveringMap.coveringSpaceAutFiberPerm e
        ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ⁻¹) x0 := by
          calc
            universalCoverDeckFiberPoint hp e γ⁻¹ =
              IsPathConnectedCoveringMap.coveringSpaceAutFiberPerm e
                ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ⁻¹)
                (universalCoverDeckFiberPoint hp e 1) := by
                  symm
                  simpa using
                    universalCoverDeckFiberPerm_apply_representative hp e γ⁻¹ 1
            _ =
              IsPathConnectedCoveringMap.coveringSpaceAutFiberPerm e
                ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ⁻¹) x0 := by
                  rw [hone]

/-- Helper for Theorem 3.8.10: monodromy at the distinguished universal-cover fiber point agrees
with the inverse-representative deck-translation convention used by the orbit-space point map. -/
private theorem universalCoverFiberMonodromy_basepoint_eq_inverse_orbit_representative
    (hp : IsUniversalCoveringMap p) (e : E)
    (γ : FundamentalGroup B (p e)) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
    γ • (⟨e, rfl⟩ : p ⁻¹' ({p e} : Set B)) =
      universalCoverDeckFiberPoint hp e γ⁻¹ := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI := universalCoverDeckMulActionOf hp e
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
  let x0 : p ⁻¹' ({p e} : Set B) := ⟨e, rfl⟩
  have hone : universalCoverDeckFiberPoint hp e (1 : FundamentalGroup B (p e)) = x0 := by
    apply Subtype.ext
    simp [universalCoverDeckFiberPoint, x0]
  -- First identify monodromy at the basepoint with the corresponding deck permutation on the
  -- fiber, then evaluate that permutation on the represented identity point.
  calc
    γ • x0 =
      IsPathConnectedCoveringMap.coveringSpaceAutFiberPerm e
        ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ⁻¹) x0 := by
          simpa [x0] using universalCoverFiberMonodromy_basepoint_eq_deckPerm hp e γ
    _ = universalCoverDeckFiberPoint hp e γ⁻¹ := by
          calc
            IsPathConnectedCoveringMap.coveringSpaceAutFiberPerm e
                ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ⁻¹) x0 =
              IsPathConnectedCoveringMap.coveringSpaceAutFiberPerm e
                ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ⁻¹)
                (universalCoverDeckFiberPoint hp e 1) := by
                  rw [hone]
            _ = universalCoverDeckFiberPoint hp e (γ⁻¹ * 1) :=
                universalCoverDeckFiberPerm_apply_representative hp e γ⁻¹ 1
            _ = universalCoverDeckFiberPoint hp e γ⁻¹ := by simp

/-- Helper for Theorem 3.8.10: the represented universal-cover fiber point for the identity loop
is the distinguished basepoint of the fiber. -/
private theorem universalCoverDeckFiberPoint_one
    (hp : IsUniversalCoveringMap p) (e : E) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    universalCoverDeckFiberPoint hp e (1 : FundamentalGroup B (p e)) =
      (⟨e, rfl⟩ : p ⁻¹' ({p e} : Set B)) := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI := universalCoverDeckMulActionOf hp e
  apply Subtype.ext
  -- At the identity element, the deck action fixes the chosen basepoint.
  simp [universalCoverDeckFiberPoint]

/-- Helper for Theorem 3.8.10: monodromy on the universal-cover fiber sends the represented point
for `δ⁻¹` to the represented point for `δ⁻¹ * γ⁻¹`. -/
private theorem universalCoverFiberMonodromy_representative_mul
    (hp : IsUniversalCoveringMap p) (e : E)
    (δ γ : FundamentalGroup B (p e)) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
    γ • universalCoverDeckFiberPoint hp e δ⁻¹ =
      universalCoverDeckFiberPoint hp e (δ⁻¹ * γ⁻¹) := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI := universalCoverDeckMulActionOf hp e
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hp.isPathConnectedCoveringMap (p e)
  let x0 : p ⁻¹' ({p e} : Set B) := ⟨e, rfl⟩
  let permδ :
      Equiv.Perm (p ⁻¹' ({p e} : Set B)) :=
    IsPathConnectedCoveringMap.coveringSpaceAutFiberPerm e
      ((coveringSpaceAutMulEquivFundamentalGroup hp e).symm δ⁻¹)
  have hrep :
      permδ (universalCoverDeckFiberPoint hp e 1) =
        universalCoverDeckFiberPoint hp e δ⁻¹ := by
    simpa [permδ] using universalCoverDeckFiberPerm_apply_representative hp e δ⁻¹ 1
  -- Rewrite the represented point `δ⁻¹ • e` as a deck permutation of the basepoint, commute
  -- that permutation past monodromy, and then evaluate both representatives explicitly.
  calc
    γ • universalCoverDeckFiberPoint hp e δ⁻¹ =
        γ • permδ (universalCoverDeckFiberPoint hp e 1) := by
          rw [hrep.symm]
    _ = permδ (γ • universalCoverDeckFiberPoint hp e 1) := by
          simpa [permδ] using
            (universalCoverDeckFiberPerm_commutes_with_monodromy hp e δ⁻¹ γ
              (universalCoverDeckFiberPoint hp e 1)).symm
    _ = permδ (γ • x0) := by
          rw [universalCoverDeckFiberPoint_one hp e]
    _ = permδ (universalCoverDeckFiberPoint hp e γ⁻¹) := by
          rw [universalCoverFiberMonodromy_basepoint_eq_inverse_orbit_representative hp e γ]
    _ = universalCoverDeckFiberPoint hp e (δ⁻¹ * γ⁻¹) := by
          simpa [permδ] using universalCoverDeckFiberPerm_apply_representative hp e δ⁻¹ γ⁻¹

namespace universalCoverOrbitQuotientMapHom

/-- Helper for Theorem 3.8.10: restricting the quotient map `E → E / K` to the fiber over
`p e` sends the represented deck point for `β` to the corresponding represented orbit point. -/
private theorem coveringSpaceHomToFiberFun_apply_representative
    (hp : IsUniversalCoveringMap p) (e : E)
    (K : O(FundamentalGroup B (p e)))
    (β : FundamentalGroup B (p e)) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    IsPathConnectedCoveringMap.coveringSpaceHomToFiberFun (p e)
        (universalCoverOrbitQuotientMapHom e K)
        (universalCoverDeckFiberPoint hp e β) =
      universalCoverOrbitFiberPointMap hp e K ((β⁻¹ : FundamentalGroup B (p e)) :
        FundamentalGroup B (p e) ⧸ K) := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI := universalCoverDeckMulActionOf hp e
  -- Both sides are literally the orbit class of the represented deck translate.
  simp [IsPathConnectedCoveringMap.coveringSpaceHomToFiberFun, universalCoverOrbitFiberPointMap,
    universalCoverDeckFiberPoint, orbitSpacePointMap_apply_mk]
  rfl

end universalCoverOrbitQuotientMapHom

/-- Helper for Theorem 3.8.10: the canonical coset-to-fiber map for `E / K` intertwines the
quotient action of `π₁(B, p e)` on `π₁(B, p e) / K` with fiber monodromy on the fiber of the
quotient cover over `p e`. -/
private theorem universalCoverOrbitFiberPointMap_equivariant
    (hp : IsUniversalCoveringMap p) (e : E)
    (K : O(FundamentalGroup B (p e)))
    (γ : FundamentalGroup B (p e)) (q : FundamentalGroup B (p e) ⧸ K) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction
      (universalCoverOrbitProjection_isPathConnectedCoveringMap e
        (K : Subgroup (FundamentalGroup B (p e)))) (p e)
    universalCoverOrbitFiberPointMap hp e K (γ • q) =
      γ • universalCoverOrbitFiberPointMap hp e K q := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI : IsPathConnectedCoveringMap p := hp.isPathConnectedCoveringMap
  letI := universalCoverDeckMulActionOf hp e
  let hpK := universalCoverOrbitProjection_isPathConnectedCoveringMap e
    (K : Subgroup (FundamentalGroup B (p e)))
  -- Local instance justification (proof-local temporary data): fixed target quotient cover.
  letI : IsPathConnectedCoveringMap (universalCoverOrbitProjectionObj e K) := hpK
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hpK (p e)
  refine Quotient.inductionOn' q ?_
  intro δ
  have hcomm :=
    IsPathConnectedCoveringMap.coveringSpaceHomToFiberFun_comm (p e)
      (universalCoverOrbitQuotientMapHom e K) γ
      (universalCoverDeckFiberPoint hp e δ⁻¹)
  -- Route correction: rewrite the source monodromy term and both target fiber-map terms on the
  -- represented universal-cover points before simplifying the group expression.
  rw [universalCoverFiberMonodromy_representative_mul hp e δ γ] at hcomm
  rw [universalCoverOrbitQuotientMapHom.coveringSpaceHomToFiberFun_apply_representative
        hp e K (δ⁻¹ * γ⁻¹),
      universalCoverOrbitQuotientMapHom.coveringSpaceHomToFiberFun_apply_representative
        hp e K δ⁻¹] at hcomm
  simpa [mul_assoc] using hcomm

/-- Helper for Theorem 3.8.10: an equivariant bijection from `π₁(B, p e) / K` to the quotient
fiber preserves the stabilizer of every point. -/
private theorem universalCoverOrbitFiberPointMap_stabilizer_eq
    (hp : IsUniversalCoveringMap p) (e : E)
    (K : O(FundamentalGroup B (p e)))
    (q : FundamentalGroup B (p e) ⧸ K) :
    letI : IsUniversalCoveringMap p := hp
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulActionOf hp e
    letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction
      (universalCoverOrbitProjection_isPathConnectedCoveringMap e
        (K : Subgroup (FundamentalGroup B (p e)))) (p e)
    MulAction.stabilizer (FundamentalGroup B (p e))
        (universalCoverOrbitFiberPointMap hp e K q) =
      MulAction.stabilizer (FundamentalGroup B (p e)) q := by
  letI : IsUniversalCoveringMap p := hp
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  letI := universalCoverDeckMulActionOf hp e
  let hpK := universalCoverOrbitProjection_isPathConnectedCoveringMap e
    (K : Subgroup (FundamentalGroup B (p e)))
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hpK (p e)
  have hbij := universalCoverOrbitFiberPointMap_bijective hp e K
  ext γ
  constructor
  · intro hγ
    change γ • q = q
    apply hbij.1
    calc
      universalCoverOrbitFiberPointMap hp e K (γ • q) =
          γ • universalCoverOrbitFiberPointMap hp e K q :=
            universalCoverOrbitFiberPointMap_equivariant hp e K γ q
      _ = universalCoverOrbitFiberPointMap hp e K q := hγ
  · intro hγ
    change γ • universalCoverOrbitFiberPointMap hp e K q =
        universalCoverOrbitFiberPointMap hp e K q
    rw [← universalCoverOrbitFiberPointMap_equivariant hp e K γ q, hγ]

/-- The quotient cover `E / H → B` realizes the subgroup `H` at the canonical orbit point of `e`.
This is the subgroup computation reused by Lemma 3.8.11. -/
theorem universalCoverOrbitProjection_range_eq_subgroup
    [hp : IsUniversalCoveringMap p] (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    (FundamentalGroup.mapOfEq
      (universalCoverOrbitProjection e H)
      (universalCoverOrbitProjection_point e H)).range = H := by
  let K : O(FundamentalGroup B (p e)) := ⟨H⟩
  let hpH := universalCoverOrbitProjection_isPathConnectedCoveringMap e H
  -- Local instance justification (proof-local temporary data): fix the quotient-cover monodromy
  -- action at the chosen basepoint `p e` for the stabilizer computation below.
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hpH (p e)
  let q0 : FundamentalGroup B (p e) ⧸ K := (1 : FundamentalGroup B (p e))
  let y0 : (universalCoverOrbitProjection e H) ⁻¹' ({p e} : Set B) :=
    ⟨universalCoverOrbitPoint e H, universalCoverOrbitProjection_point e H⟩
  have hy0 :
      universalCoverOrbitFiberPointMap hp e K q0 = y0 := by
    -- The identity coset maps to the canonical orbit point of `e`.
    apply Subtype.ext
    simp [universalCoverOrbitFiberPointMap, universalCoverOrbitPoint, q0, y0]
    rfl
  have hmap_eq :
      FundamentalGroup.map (universalCoverOrbitProjection e H) (universalCoverOrbitPoint e H) =
        FundamentalGroup.mapOfEq
          (universalCoverOrbitProjection e H)
          (universalCoverOrbitProjection_point e H) := by
    -- The chosen orbit point already lies over `p e`, so the two basepoint conventions coincide.
    ext γ
    refine Quotient.inductionOn γ ?_
    intro r
    simpa using
      (FundamentalGroup.mapOfEq_apply
        (universalCoverOrbitProjection e H)
        (universalCoverOrbitProjection_point e H)
        r).symm
  -- Compare the target stabilizer first with the image subgroup, then with the identity coset.
  rw [← hmap_eq]
  calc
    (FundamentalGroup.map
      (universalCoverOrbitProjection e H)
      (universalCoverOrbitPoint e H)).range =
        MulAction.stabilizer (FundamentalGroup B (p e)) y0 := by
          simpa [y0] using
            (hpH.fiberMonodromyMulAction_stabilizer_eq_fundamentalGroupRange
              (universalCoverOrbitPoint e H)).symm
    _ = MulAction.stabilizer (FundamentalGroup B (p e))
          (universalCoverOrbitFiberPointMap hp e K q0) := by
            rw [hy0]
    _ = MulAction.stabilizer (FundamentalGroup B (p e)) q0 := by
          simpa [q0, K] using universalCoverOrbitFiberPointMap_stabilizer_eq hp e K q0
    _ = H := by
          change
            MulAction.stabilizer (FundamentalGroup B (p e))
              (((1 : FundamentalGroup B (p e)) : FundamentalGroup B (p e) ⧸ H)) = H
          exact MulAction.stabilizer_quotient H

/-- Helper for Theorem 3.8.10: every morphism between quotient coverings comes from a unique
orbit-category morphism. -/
private theorem universalCoverOrbitFunctor_full
    (hp : IsUniversalCoveringMap p) (e : E) :
    ((universalCoverOrbitFunctor e :
        O(FundamentalGroup B (p e)) ⥤ ConnectedCoveringSpace B)).Full := by
  refine
    { map_surjective := ?_ }
  intro H K F
  -- Local instance justification (proof-local temporary data): fixed universal covering `hp`.
  letI : IsUniversalCoveringMap p := hp
  -- Local instance justification (proof-local temporary data): use the monodromy API.
  letI : PathConnectedSpace E := inferInstance
  -- Local instance justification (proof-local temporary data): fixed deck action at `e`.
  letI := universalCoverDeckMulActionOf hp e
  -- Local instance justification (proof-local temporary data): need continuity for the orbit API.
  letI : ContinuousConstSMul (FundamentalGroup B (p e)) E :=
    universalCoverDeckContinuousConstSMul e
  let hpH := universalCoverOrbitProjection_isPathConnectedCoveringMap e
    (H : Subgroup (FundamentalGroup B (p e)))
  let hpK := universalCoverOrbitProjection_isPathConnectedCoveringMap e
    (K : Subgroup (FundamentalGroup B (p e)))
  -- Local instance justification (proof-local temporary data): fixed source quotient cover.
  letI : IsPathConnectedCoveringMap (universalCoverOrbitProjectionObj e H) := hpH
  -- Local instance justification (proof-local temporary data): fixed target quotient cover.
  letI : IsPathConnectedCoveringMap (universalCoverOrbitProjectionObj e K) := hpK
  -- Local instance justification (proof-local temporary data): source monodromy at `p e`.
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hpH (p e)
  -- Local instance justification (proof-local temporary data): target monodromy at `p e`.
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hpK (p e)
  let x0 : (universalCoverOrbitProjectionObj e H) ⁻¹' ({p e} : Set B) :=
    ⟨universalCoverOrbitPointObj e H, rfl⟩
  have hy_mem :
      universalCoverOrbitProjectionObj e K
          (TopCat.Hom.hom F.hom.left (universalCoverOrbitPointObj e H)) = p e := by
    -- Evaluating the commutative triangle at the canonical orbit point keeps the same basepoint.
    have hcomm := congrArg
      (fun f : TopCat.of (universalCoverOrbitObj e H) ⟶ TopCat.of B ↦
        f.hom (universalCoverOrbitPointObj e H))
      (Over.w F.hom)
    simpa [ContinuousMap.comp_apply] using hcomm
  let y : (universalCoverOrbitProjectionObj e K) ⁻¹' ({p e} : Set B) :=
    ⟨TopCat.Hom.hom F.hom.left (universalCoverOrbitPointObj e H), hy_mem⟩
  obtain ⟨q, hq⟩ := (universalCoverOrbitFiberPointMap_bijective hp e K).2 y
  have hx0_fixed :
      ∀ h : H, ((h : FundamentalGroup B (p e)) • x0) = x0 := by
    intro h
    -- The canonical orbit point corresponds to the identity coset, whose stabilizer is exactly `H`.
    have hh_mem :
        (h : FundamentalGroup B (p e)) ∈
          MulAction.stabilizer (FundamentalGroup B (p e))
            (universalCoverOrbitFiberPointMap hp e H
              ((1 : FundamentalGroup B (p e)) : FundamentalGroup B (p e) ⧸ H)) := by
      rw [universalCoverOrbitFiberPointMap_stabilizer_eq hp e H
        ((1 : FundamentalGroup B (p e)) : FundamentalGroup B (p e) ⧸ H)]
      change
        (h : FundamentalGroup B (p e)) ∈
          MulAction.stabilizer (FundamentalGroup B (p e))
            ((1 : FundamentalGroup B (p e)) : FundamentalGroup B (p e) ⧸ H)
      rw [MulAction.stabilizer_quotient]
      exact h.2
    rw [MulAction.mem_stabilizer_iff] at hh_mem
    simpa [x0, universalCoverOrbitFiberPointMap, universalCoverOrbitPoint] using hh_mem
  have hy_fixed :
      ∀ h : H, ((h : FundamentalGroup B (p e)) • y) = y := by
    intro h
    -- The induced fiber map of `F` is equivariant, so it preserves the fixed image of the source.
    calc
      (h : FundamentalGroup B (p e)) • y =
          (IsPathConnectedCoveringMap.coveringSpaceHomToFiber (p e) F.hom)
            ((h : FundamentalGroup B (p e)) • x0) := by
            symm
            exact
              (IsPathConnectedCoveringMap.coveringSpaceHomToFiber (p e) F.hom).map_smul'
                (h : FundamentalGroup B (p e)) x0
      _ = (IsPathConnectedCoveringMap.coveringSpaceHomToFiber (p e) F.hom) x0 := by
            rw [hx0_fixed h]
      _ = y := by
            rfl
  have hq_fixed :
      q ∈ MulAction.fixedPoints (H : Subgroup (FundamentalGroup B (p e)))
        (FundamentalGroup B (p e) ⧸ K) := by
    rw [MulAction.mem_fixedPoints]
    intro h
    -- Injectivity of the coset-to-fiber map turns fixedness of `y` into fixedness of `q`.
    apply (universalCoverOrbitFiberPointMap_bijective hp e K).1
    calc
      universalCoverOrbitFiberPointMap hp e K ((h : FundamentalGroup B (p e)) • q) =
          (h : FundamentalGroup B (p e)) • universalCoverOrbitFiberPointMap hp e K q := by
            exact universalCoverOrbitFiberPointMap_equivariant hp e K h q
      _ = (h : FundamentalGroup B (p e)) • y := by rw [hq]
      _ = y := hy_fixed h
      _ = universalCoverOrbitFiberPointMap hp e K q := hq.symm
  let α : H ⟶ K := orbitCategory.homOfFixedPoint H K ⟨q, hq_fixed⟩
  refine ⟨α, ?_⟩
  apply universalCoverOrbitCoveringHom_eq_of_eq_at_orbitPoint hp e
  -- The covering induced by the fixed coset `q` agrees with `F` at the canonical orbit point.
  have hpoint_eval :
      TopCat.Hom.hom (universalCoverOrbitCoveringHom e α).hom.left
          (universalCoverOrbitPointObj e H) =
        (universalCoverOrbitFiberPointMap hp e K q).1 := by
    -- Evaluating the orbit-category map at the identity coset recovers the chosen fixed coset `q`.
    calc
      TopCat.Hom.hom (universalCoverOrbitCoveringHom e α).hom.left
          (universalCoverOrbitPointObj e H) =
        orbitSpacePointMap e
          (orbitCategory.homEvalOne H K α) := by
            simpa [universalCoverOrbitCoveringHom, universalCoverOrbitMap,
              universalCoverOrbitPointObj] using
              (orbitSpaceMap_apply_mk α e)
      _ = orbitSpacePointMap e q := by
            rw [show ((orbitCategory.homEvalOne H K α :
            MulAction.fixedPoints (H : Subgroup (FundamentalGroup B (p e)))
                  (FundamentalGroup B (p e) ⧸ K)) :
                  FundamentalGroup B (p e) ⧸ K) = q by
              unfold α
              exact congrArg Subtype.val
                (orbitCategory.homEvalOne_homOfFixedPoint H K ⟨q, hq_fixed⟩)
              ]
      _ = (universalCoverOrbitFiberPointMap hp e K q).1 := rfl
  have hpoint_target :
      (universalCoverOrbitFiberPointMap hp e K q).1 =
        TopCat.Hom.hom F.hom.left (universalCoverOrbitPointObj e H) := by
    -- The chosen coset `q` was defined from the fiber image of the canonical orbit point.
    simpa [y] using congrArg Subtype.val hq
  simpa [universalCoverOrbitFunctor] using hpoint_eval.trans hpoint_target

/-- Helper for Theorem 3.8.10: every connected covering over `B` is isomorphic to the quotient of
the chosen universal cover by the subgroup carried by a fiber point over `p e`. -/
private theorem universalCoverOrbitFunctor_essSurj
    (hp : IsUniversalCoveringMap p) (e : E) :
    ((universalCoverOrbitFunctor e :
        O(FundamentalGroup B (p e)) ⥤ ConnectedCoveringSpace B)).EssSurj := by
  -- Local instance justification (proof-local temporary data): the covering-space and
  -- fundamental-group machinery below needs `[LocPathConnectedSpace B]`, and this proof derives
  -- that ambient structure from the chosen universal covering map `p` without changing the
  -- theorem interface.
  letI : LocPathConnectedSpace B := baseLocPathConnectedSpace hp
  refine { mem_essImage := ?_ }
  intro X
  let pXHom := X.obj.hom
  let pX : C(X.obj.left, B) := pXHom.hom
  have hpX : IsPathConnectedCoveringMap pX := by
    simpa [pX] using ConnectedCoveringSpace.isPathConnectedCoveringMap X
  letI : PathConnectedSpace X.obj.left := ConnectedCoveringSpace.pathConnectedSpace X
  obtain ⟨x₀, hx₀⟩ := hpX.1 (p e)
  let x₀' : pX ⁻¹' ({p e} : Set B) := ⟨x₀, hx₀⟩
  let K : O(FundamentalGroup B (p e)) := ⟨(FundamentalGroup.mapOfEq pX x₀'.2).range⟩
  let y₀ : (universalCoverOrbitProjectionObj e K) ⁻¹' ({p e} : Set B) :=
    ⟨universalCoverOrbitPointObj e K, rfl⟩
  have hsub :
      (FundamentalGroup.mapOfEq
        (universalCoverOrbitProjectionObj e K)
        (show universalCoverOrbitProjectionObj e K (universalCoverOrbitPointObj e K) = p e from
          by
            simp [universalCoverOrbitProjectionObj, universalCoverOrbitPointObj])).range ≤
        (FundamentalGroup.mapOfEq pX x₀'.2).range := by
    -- The chosen subgroup is exactly the target image subgroup at `x₀`.
    simpa [K] using
      (universalCoverOrbitProjection_range_eq_subgroup e
        (K : Subgroup (FundamentalGroup B (p e)))).le
  obtain ⟨h, hh, _⟩ :=
    (IsPathConnectedCoveringMap.existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
      hpX (p e) y₀ x₀').2 hsub
  letI : LocPathConnectedSpace X.obj.left :=
    IsPathConnectedCoveringMap.locPathConnectedSpace_totalSpace
      hpX
  have hIso : IsIso h := by
    refine
      (IsPathConnectedCoveringMap.coveringSpaceMorphism_isIso_iff_fundamentalGroup_range_eq
        (universalCoverOrbitProjection_isPathConnectedCoveringMap e
          (K : Subgroup (FundamentalGroup B (p e))))
        hpX
        (p e) y₀ x₀' h hh).2 ?_
    -- Route correction: after installing local path connectedness on the target total space,
    -- the standard subgroup-equality criterion from Theorem 3.7.6 applies unchanged.
    calc
      (FundamentalGroup.mapOfEq
        (universalCoverOrbitProjectionObj e K)
        (show universalCoverOrbitProjectionObj e K (universalCoverOrbitPointObj e K) = p e from
          by
            simp [universalCoverOrbitProjectionObj, universalCoverOrbitPointObj])).range =
        K := by
            exact universalCoverOrbitProjection_range_eq_subgroup e
              (K : Subgroup (FundamentalGroup B (p e)))
      _ = (FundamentalGroup.mapOfEq pX x₀'.2).range := rfl
  refine ⟨K, ⟨?_⟩⟩
  -- Package the point-preserving covering isomorphism into the full subcategory of connected
  -- coverings over `B`.
  exact ObjectProperty.isoMk _ <| by
    exact @asIso _ _ _ _ h hIso

/-- Theorem 3.8.10: for a universal covering `p : E → B` with chosen point `e : E`, the functor
`E(-) : O(π₁(B, p e)) ⥤` connected covering spaces over `B`, sending `G / H` to the quotient
covering `E / H → B`, is an equivalence of categories. In particular, every subgroup
`H ≤ π₁(B, p e)` is realized by a quotient of the universal cover. -/
-- Proof sketch: identify deck transformations of the universal cover with `π₁(B, p e)` via
-- Corollary 3.7.11, use Lemma 3.8.8 to descend equivariant maps of the universal cover to maps of
-- quotient coverings, and apply Theorem 3.7.6 to identify morphisms and isomorphisms of
-- coverings with subgroup inclusions and equalities.
instance universalCoverOrbitFunctor_isEquivalence
    [hp : IsUniversalCoveringMap p] (e : E) :
    Functor.IsEquivalence
      (universalCoverOrbitFunctor e : O(FundamentalGroup B (p e)) ⥤ ConnectedCoveringSpace B) := by
  let F : O(FundamentalGroup B (p e)) ⥤ ConnectedCoveringSpace B := universalCoverOrbitFunctor e
  let _ : F.Faithful :=
    universalCoverOrbitFunctor_faithful hp e
  let _ : F.Full :=
    universalCoverOrbitFunctor_full hp e
  let _ : F.EssSurj :=
    universalCoverOrbitFunctor_essSurj hp e
  -- The quotient-covering functor is faithful, full, and essentially surjective.
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

end IsUniversalCoveringMap
