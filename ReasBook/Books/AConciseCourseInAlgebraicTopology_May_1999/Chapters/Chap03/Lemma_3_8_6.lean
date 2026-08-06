import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_8_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_8_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_2_3
import Mathlib.Topology.Subpath

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Path.Homotopic.Quotient
open TopologicalSpace
open TopologicalSpace.OpenNhdsOf
open scoped FundamentalGroup unitInterval UniversalCover

variable {B : Type u} [TopologicalSpace B]

section

variable [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]

/- The ambient endpoint projection used throughout the covering-space argument. -/
/-- Helper for Lemma 3.8.6: the endpoint projection on the path-class model is continuous for the
generated topology. -/
private theorem universal_cover_candidate_projection_continuous
    (b : B) :
    Continuous (fun q : universalCoverCandidate b ↦ q.1) := by
  let hBasis := universalCoverCandidateBasicSets_isTopologicalBasis b
  rw [continuous_def]
  intro N hN
  rw [hBasis.isOpen_iff]
  intro r hr
  let Nnhd : TopologicalSpace.OpenNhdsOf r.1 := ⟨⟨N, hN⟩, hr⟩
  rcases exists_suitable_universal_cover_neighborhood_subset r.1 Nnhd with
    ⟨U, hUN, hU⟩
  refine ⟨U[r], ?_, ?_, ?_⟩
  · -- Suitable basic sheets are among the generating basis elements.
    exact ⟨r, U, hU, rfl⟩
  · -- The center point lies in its own sheet via the constant path.
    exact universalCoverCandidateBasicSet_self_mem r U
  · -- Every point of the chosen sheet projects into the ambient neighborhood `N`.
    intro s hs
    exact hUN (universalCoverCandidateBasicSet_endpoint_mem r U hs)

/-- Helper for Lemma 3.8.6: the universal-cover candidate carries its canonical endpoint
projection to the base. -/
private def universal_cover_candidate_projectionMap
    (b : B) :
    C(universalCoverCandidate b, B) :=
  ⟨fun q ↦ q.1, universal_cover_candidate_projection_continuous b⟩

/-- Helper for Lemma 3.8.6: every endpoint of the path-class model lies in the path component of
the chosen basepoint. -/
private theorem universal_cover_candidate_endpoint_mem_pathComponent
    (b : B) (q : universalCoverCandidate b) :
    q.1 ∈ pathComponent b := by
  cases q with
  | mk x γ =>
      obtain ⟨f, rfl⟩ := mk_surjective γ
      -- A representing path from `b` to `x` witnesses membership in the path component.
      exact mem_pathComponent_iff.mpr ⟨f⟩

/-- Helper for Lemma 3.8.6: the endpoint projection lands exactly on the path component of the
chosen basepoint. -/
private theorem universal_cover_candidate_projection_range_eq_pathComponent
    (b : B) :
    Set.range (universal_cover_candidate_projectionMap b) = pathComponent b := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    -- Any path class from `b` ends inside the path component of `b`.
    exact universal_cover_candidate_endpoint_mem_pathComponent b q
  · intro hx
    rcases mem_pathComponent_iff.mp hx with ⟨f⟩
    -- A path from `b` to `x` represents a point of the total space projecting to `x`.
    exact ⟨⟨x, mk f⟩, rfl⟩

/-- Helper for Lemma 3.8.6: suitable basic sheets are open in the generated topology. -/
private theorem universal_cover_candidate_basic_set_isOpen
    {b : B} (q : universalCoverCandidate b)
    (U : TopologicalSpace.OpenNhdsOf q.1) (hU : U.IsSuitableForUniversalCover) :
    IsOpen (U[q]) := by
  -- The topology on the path-class model was generated from these sheets.
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨q, U, hU, rfl⟩

/-- Helper for Lemma 3.8.6: if two suitable sheets over the same neighborhood meet, then their
centers agree. -/
private theorem universal_cover_candidate_basic_sheet_eq_of_inter
    {b : B} {q₁ q₂ : universalCoverCandidate b}
    (U : TopologicalSpace.OpenNhdsOf q₁.1) (hU : U.IsSuitableForUniversalCover)
    (hq₂ : q₂.1 = q₁.1)
    {r : universalCoverCandidate b}
    (hr₁ : r ∈ U[q₁]) (hr₂ : r ∈ universalCoverCandidateBasicSet q₂ (hq₂ ▸ U)) :
    q₁ = q₂ := by
  cases q₁ with
  | mk x γ₁ =>
      cases q₂ with
      | mk x' γ₂ =>
          dsimp at hq₂
          subst hq₂
          dsimp at hr₁ hr₂ ⊢
          rcases hr₁ with ⟨y₁, c₁, rfl⟩
          rcases hr₂ with ⟨y₂, c₂, hEq⟩
          have hy : y₁ = y₂ := by
            -- The common point forces the two endpoint witnesses in `U` to match.
            apply Subtype.ext
            exact congrArg Sigma.fst hEq
          subst hy
          have hpaths :
              γ₁.trans ((mk c₁).map U.subtypeVal) =
                γ₂.trans ((mk c₂).map U.subtypeVal) := by
            -- Equal sigma points identify the concatenated endpoint-fixed classes.
            exact eq_of_heq ((Sigma.mk.inj_iff).mp hEq).2
          have hright_same :
              γ₂.trans ((mk c₁).map U.subtypeVal) =
                γ₂.trans ((mk c₂).map U.subtypeVal) := by
            -- Trivial monodromy in `U` lets us replace one endpoint path by the other.
            have hsigma :
                (⟨y₁.1, γ₂.trans ((mk c₁).map U.subtypeVal)⟩ :
                  universalCoverCandidate b) =
                ⟨y₁.1, γ₂.trans ((mk c₂).map U.subtypeVal)⟩ :=
              universalCoverCandidate_pathClass_eq_of_paths
                ⟨x', γ₂⟩ U hU.2 y₁ c₁ c₂
            exact eq_of_heq ((Sigma.mk.inj_iff).mp hsigma).2
          let α : Path.Homotopic.Quotient x' y₁.1 := ((mk c₁).map U.subtypeVal)
          have hcommon : γ₁.trans α = γ₂.trans α := by
            -- Rewrite both sides with the same suffix path class.
            simpa [α] using hpaths.trans hright_same.symm
          have hγ : γ₁ = γ₂ := by
            -- Cancel the common suffix by composing with its inverse.
            calc
              γ₁ = (γ₁.trans α).trans α.symm := by
                rw [trans_assoc, trans_symm, trans_refl]
              _ = (γ₂.trans α).trans α.symm := by rw [hcommon]
              _ = γ₂ := by
                rw [trans_assoc, trans_symm, trans_refl]
          simp [hγ]

/-- Helper for Lemma 3.8.6: a fiber point over `x` has underlying endpoint `x`. -/
private theorem universal_cover_candidate_fiber_point_eq
    {b x : B} (q : universal_cover_candidate_projectionMap b ⁻¹' ({x} : Set B)) :
    q.1.1 = x := by
  have hmem :
      universal_cover_candidate_projectionMap b q.1 ∈ ({x} : Set B) :=
    q.2
  have hmem' : q.1.1 ∈ ({x} : Set B) := by
    simpa [universal_cover_candidate_projectionMap] using hmem
  exact Set.mem_singleton_iff.mp hmem'

/-- Helper for Lemma 3.8.6: in a fixed fiber, a suitable centered sheet cuts out a singleton. -/
private theorem universal_cover_candidate_fiber_singleton_eq_sheet_inter
    {b x : B} (q : universalCoverCandidate b)
    (U : TopologicalSpace.OpenNhdsOf q.1) (hU : U.IsSuitableForUniversalCover) (hq : q.1 = x) :
    { y : universal_cover_candidate_projectionMap b ⁻¹' ({x} : Set B) |
        y.1 ∈ U[q] } =
      {⟨q, by simp [universal_cover_candidate_projectionMap, hq]⟩} := by
  ext y
  constructor
  · intro hy
    have hy' : y.1.1 = q.1 := by
      calc
        y.1.1 = x := universal_cover_candidate_fiber_point_eq y
        _ = q.1 := hq.symm
    have hyself :
        y.1 ∈ (hy' ▸ U)[y.1] := by
      -- Every point belongs to the sheet centered at itself.
      exact universalCoverCandidateBasicSet_self_mem y.1 (hy' ▸ U)
    have hqy : q = y.1 := by
      -- Two sheets meeting in one fiber point must have the same center.
      exact
        universal_cover_candidate_basic_sheet_eq_of_inter U hU hy' hy hyself
    exact Set.mem_singleton_iff.mpr (Subtype.ext hqy.symm)
  · rintro rfl
    -- The center belongs to its own sheet via the constant path.
    exact universalCoverCandidateBasicSet_self_mem q U

/-- Helper for Lemma 3.8.6: transporting suitability data along an endpoint equality preserves the
same suitable neighborhood. -/
private theorem isSuitableForUniversalCover_ndrec
    {x y : B} (h : x = y) (U : TopologicalSpace.OpenNhdsOf y)
    (hU : U.IsSuitableForUniversalCover) :
    (Eq.ndrec U h.symm).IsSuitableForUniversalCover := by
  -- Suitability depends only on the identified open neighborhood.
  subst h
  simpa using hU

/-- Helper for Lemma 3.8.6: successive neighborhood transports compose as expected. -/
private theorem openNhdsOf_ndrec_trans
    {x y z : B} (hxy : y = x) (hxz : x = z) (U : TopologicalSpace.OpenNhdsOf z) :
    Eq.ndrec (Eq.ndrec U hxz.symm) hxy.symm = Eq.ndrec U (hxy.trans hxz).symm := by
  -- After identifying all endpoints, both transports are definitionally the same.
  subst hxy
  subst hxz
  rfl

/-- Helper for Lemma 3.8.6: the centered sheet at a fiber point is the suitable sheet obtained by
transporting the neighborhood to that center. -/
private def universal_cover_candidate_center_sheet
    {b x : B} (q : universal_cover_candidate_projectionMap b ⁻¹' ({x} : Set B))
    (U : TopologicalSpace.OpenNhdsOf x) :
    Set (universalCoverCandidate b) :=
  (Eq.ndrec U (universal_cover_candidate_fiber_point_eq q).symm)[q.1]

/-- Helper for Lemma 3.8.6: every point over a suitable neighborhood belongs to one centered
sheet. -/
private theorem universal_cover_candidate_center_sheet_cover
    {b x : B} (U : TopologicalSpace.OpenNhdsOf x) (hU : U.IsSuitableForUniversalCover)
    {r : universalCoverCandidate b} (hr : r.1 ∈ (U : Set B)) :
    ∃ q : universal_cover_candidate_projectionMap b ⁻¹' ({x} : Set B),
      r ∈ universal_cover_candidate_center_sheet q U := by
  let i : C(U, B) := U.subtypeVal
  let xU : U := ⟨x, U.mem⟩
  let rU : U := ⟨r.1, hr⟩
  let c : Path xU rU := (hU.1.joinedIn x U.mem r.1 hr).joined_subtype.somePath
  let q : universalCoverCandidate b :=
    ⟨x, r.2.trans (((mk c).map i).symm)⟩
  let qf : universal_cover_candidate_projectionMap b ⁻¹' ({x} : Set B) :=
    ⟨q, by simp [universal_cover_candidate_projectionMap, q]⟩
  refine ⟨qf, ?_⟩
  have hrSheet : r ∈ U[q] := by
    refine ⟨⟨r.1, hr⟩, c, ?_⟩
    apply Sigma.ext
    · rfl
    · -- Appending the short path in `U` recovers the original class of `r`.
      dsimp [q]
      rw [trans_assoc, symm_trans, trans_refl]
  simpa [universal_cover_candidate_center_sheet, qf, q] using hrSheet

/-- Helper for Lemma 3.8.6: on a centered sheet, the endpoint projection is injective. -/
private theorem universal_cover_candidate_center_sheet_injOn
    {b x : B} (U : TopologicalSpace.OpenNhdsOf x) (hU : U.IsSuitableForUniversalCover)
    (q : universal_cover_candidate_projectionMap b ⁻¹' ({x} : Set B)) :
    (universal_cover_candidate_center_sheet q U).InjOn
      (universal_cover_candidate_projectionMap b) := by
  have hq : q.1.1 = x := universal_cover_candidate_fiber_point_eq q
  have hUq : (Eq.ndrec U hq.symm).IsSuitableForUniversalCover := by
    -- Reindex the same suitable neighborhood at the actual sheet center.
    exact isSuitableForUniversalCover_ndrec hq U hU
  intro r₁ hr₁ r₂ hr₂ hp
  have hr₁' : r₁ ∈ (Eq.ndrec U hq.symm)[q.1] := by
    simpa [universal_cover_candidate_center_sheet] using hr₁
  have hr₂' : r₂ ∈ (Eq.ndrec U hq.symm)[q.1] := by
    simpa [universal_cover_candidate_center_sheet] using hr₂
  rcases hr₁' with ⟨y₁, c₁, rfl⟩
  rcases hr₂' with ⟨y₂, c₂, rfl⟩
  dsimp [universal_cover_candidate_projectionMap] at hp
  have hy : y₁ = y₂ := Subtype.ext hp
  subst hy
  -- Over a suitable neighborhood, equal endpoints determine equal path classes in one sheet.
  exact universalCoverCandidate_pathClass_eq_of_paths
    q.1 (Eq.ndrec U hq.symm) hUq.2 y₁ c₁ c₂

/-- Helper for Lemma 3.8.6: every centered sheet is open. -/
private theorem universal_cover_candidate_center_sheet_isOpen
    {b x : B} (U : TopologicalSpace.OpenNhdsOf x) (hU : U.IsSuitableForUniversalCover)
    (q : universal_cover_candidate_projectionMap b ⁻¹' ({x} : Set B)) :
    IsOpen (universal_cover_candidate_center_sheet q U) := by
  have hq : q.1.1 = x := universal_cover_candidate_fiber_point_eq q
  let Uq : TopologicalSpace.OpenNhdsOf q.1.1 := Eq.ndrec U hq.symm
  have hUq : Uq.IsSuitableForUniversalCover := by
    -- Suitability survives the endpoint transport to the chosen sheet center.
    exact isSuitableForUniversalCover_ndrec hq U hU
  simpa [universal_cover_candidate_center_sheet, Uq] using
    universal_cover_candidate_basic_set_isOpen q.1 Uq hUq

/-- Helper for Lemma 3.8.6: a centered sheet projects surjectively onto its indexing suitable
neighborhood. -/
private theorem universal_cover_candidate_center_sheet_surjOn
    {b x : B} (U : TopologicalSpace.OpenNhdsOf x) (hU : U.IsSuitableForUniversalCover)
    (q : universal_cover_candidate_projectionMap b ⁻¹' ({x} : Set B)) :
    (universal_cover_candidate_center_sheet q U).SurjOn
      (universal_cover_candidate_projectionMap b) (U : Set B) := by
  rcases q with ⟨q, hqmem⟩
  have hq : q.1 = x := by
    -- Unpack the fiber condition to identify the sheet center with the neighborhood basepoint.
    simpa [universal_cover_candidate_projectionMap] using hqmem
  subst hq
  simpa [universal_cover_candidate_center_sheet, universal_cover_candidate_projectionMap] using
    universalCoverCandidateBasicSet_endpoint_surjOn q U hU

/-- Helper for Lemma 3.8.6: centered sheets over one suitable neighborhood are pairwise
disjoint. -/
private theorem universal_cover_candidate_center_sheets_pairwise_disjoint
    {b x : B} (U : TopologicalSpace.OpenNhdsOf x) (hU : U.IsSuitableForUniversalCover) :
    Pairwise
      (fun q₁ q₂ : universal_cover_candidate_projectionMap b ⁻¹' ({x} : Set B) ↦
        Disjoint (universal_cover_candidate_center_sheet q₁ U)
          (universal_cover_candidate_center_sheet q₂ U)) := by
  intro q₁ q₂ hne
  refine Set.disjoint_left.2 ?_
  intro r hr₁ hr₂
  have hq₁ : q₁.1.1 = x := universal_cover_candidate_fiber_point_eq q₁
  have hq₂ : q₂.1.1 = x := universal_cover_candidate_fiber_point_eq q₂
  have hU₁ : (Eq.ndrec U hq₁.symm).IsSuitableForUniversalCover := by
    -- Reindex the chosen suitable neighborhood at the first sheet center.
    exact isSuitableForUniversalCover_ndrec hq₁ U hU
  have hr₁' : r ∈ (Eq.ndrec U hq₁.symm)[q₁.1] := by
    simpa [universal_cover_candidate_center_sheet] using hr₁
  have hr₂' : r ∈ (Eq.ndrec U hq₂.symm)[q₂.1] := by
    simpa [universal_cover_candidate_center_sheet] using hr₂
  have hendpoint : q₂.1.1 = q₁.1.1 := hq₂.trans hq₁.symm
  have htransport :
      hendpoint ▸ (Eq.ndrec U hq₁.symm) = Eq.ndrec U hq₂.symm := by
    -- Both transports move the same original neighborhood to the second center.
    simpa [hendpoint] using
      (openNhdsOf_ndrec_trans hendpoint hq₁ U)
  have hr₂'' : r ∈ (hendpoint ▸ (Eq.ndrec U hq₁.symm))[q₂.1] := by
    -- Rewrite the second-sheet membership so both sheets use the same base neighborhood.
    simpa [htransport] using hr₂'
  have hsame :
      q₁.1 = q₂.1 := by
    -- Any point in the intersection forces the two sheet centers to coincide.
    exact
      universal_cover_candidate_basic_sheet_eq_of_inter
        (Eq.ndrec U hq₁.symm) hU₁ hendpoint hr₁' hr₂''
  exact hne (Subtype.ext hsame)

/-- Helper for Lemma 3.8.6: every fiber of the endpoint projection is discrete. -/
private theorem universal_cover_candidate_fiber_discrete
    {b x : B} :
    DiscreteTopology (universal_cover_candidate_projectionMap b ⁻¹' ({x} : Set B)) := by
  rcases exists_suitable_universal_cover_neighborhood x with ⟨U, hU⟩
  refine discreteTopology_iff_isOpen_singleton.mpr ?_
  intro q
  have hq : q.1.1 = x := universal_cover_candidate_fiber_point_eq q
  let Uq : TopologicalSpace.OpenNhdsOf q.1.1 := Eq.ndrec U hq.symm
  have hUq : Uq.IsSuitableForUniversalCover := by
    -- Reuse the same suitable neighborhood after identifying the fiber point with `x`.
    exact isSuitableForUniversalCover_ndrec hq U hU
  have hopen_center :
      IsOpen (universal_cover_candidate_center_sheet q U) := by
    simpa [universal_cover_candidate_center_sheet, Uq] using
      universal_cover_candidate_basic_set_isOpen q.1 Uq hUq
  have hopen_trace :
      IsOpen {y : universal_cover_candidate_projectionMap b ⁻¹' ({x} : Set B) |
        y.1 ∈ universal_cover_candidate_center_sheet q U} := by
    -- The fiber trace of an open centered sheet is open by continuity of the subtype inclusion.
    simpa [Set.preimage] using
      hopen_center.preimage
        (continuous_subtype_val :
          Continuous fun y :
            universal_cover_candidate_projectionMap b ⁻¹' ({x} : Set B) ↦ y.1)
  have hsingleton :
      {y : universal_cover_candidate_projectionMap b ⁻¹' ({x} : Set B) |
          y.1 ∈ universal_cover_candidate_center_sheet q U} = {q} := by
    simpa [universal_cover_candidate_center_sheet, Uq] using
      (universal_cover_candidate_fiber_singleton_eq_sheet_inter q.1 Uq hUq hq)
  simpa [hsingleton] using hopen_trace

/-- Helper for Lemma 3.8.6: the ambient endpoint projection is a covering map onto its path
component image. -/
private theorem universal_cover_candidate_projection_isCoveringMap
    (b : B) :
    IsCoveringMap (universal_cover_candidate_projectionMap b) := by
  let p : C(universalCoverCandidate b, B) := universal_cover_candidate_projectionMap b
  have hRange :
      Set.range p = pathComponent b :=
    universal_cover_candidate_projection_range_eq_pathComponent b
  have hopenMap : IsOpenMap p := by
    simpa [p, universal_cover_candidate_projectionMap] using
      universalCoverCandidate_endpoint_isOpenMap (B := B) b
  -- Route correction: the map need not be surjective onto all of `B`, so we build a covering map
  -- by trivializing it on the path-component image and using the open complement elsewhere.
  classical
  let F : B → Type u := fun x ↦ ↥(p ⁻¹' ({x} : Set B))
  let topF : ∀ x, TopologicalSpace (F x) := fun x => by
    dsimp [F]
    infer_instance
  let discF : ∀ x, DiscreteTopology (F x) := fun x => by
    dsimp [F]
    simpa [p] using
      (universal_cover_candidate_fiber_discrete (b := b) (x := x))
  refine @IsCoveringMap.mk' _ _ _ _ p F topF discF ?_ ?_
  · intro x hx
    let Nnhd : TopologicalSpace.OpenNhdsOf x := by
      refine ⟨⟨pathComponent b, IsOpen.pathComponent b⟩, ?_⟩
      simpa [hRange] using hx
    let U : TopologicalSpace.OpenNhdsOf x :=
      Classical.choose (exists_suitable_universal_cover_neighborhood_subset x Nnhd)
    have hUall :
        (∀ ⦃y : B⦄, y ∈ U → y ∈ Nnhd) ∧ U.IsSuitableForUniversalCover :=
      Classical.choose_spec (exists_suitable_universal_cover_neighborhood_subset x Nnhd)
    have hUN : ∀ ⦃y : B⦄, y ∈ U → y ∈ Nnhd := hUall.1
    have hU : U.IsSuitableForUniversalCover := hUall.2
    have hcenter_cover :
        ∀ {r : universalCoverCandidate b}, r.1 ∈ (U : Set B) →
          ∃ q : p ⁻¹' ({x} : Set B), r ∈ universal_cover_candidate_center_sheet q U := by
      intro r hr
      simpa [p] using
        universal_cover_candidate_center_sheet_cover (b := b) (x := x) U hU hr
    have hcenter_disjoint :
        Pairwise (fun q₁ q₂ : p ⁻¹' ({x} : Set B) ↦
          Disjoint (universal_cover_candidate_center_sheet q₁ U)
            (universal_cover_candidate_center_sheet q₂ U)) := by
      simpa [p] using
        universal_cover_candidate_center_sheets_pairwise_disjoint (b := b) (x := x) U hU
    have hsheet_inj :
        ∀ q : p ⁻¹' ({x} : Set B),
          (universal_cover_candidate_center_sheet q U).InjOn p := by
      intro q
      simpa [p] using
        universal_cover_candidate_center_sheet_injOn (b := b) (x := x) U hU q
    have hopen_iff :
        ∀ q : p ⁻¹' ({x} : Set B), ∀ {W : Set B}, W ⊆ (U : Set B) →
          (IsOpen W ↔ IsOpen (p ⁻¹' W ∩ universal_cover_candidate_center_sheet q U)) := by
      intro q W hWU
      constructor
      · intro hW
        -- Open subsets downstairs pull back to open traces on each centered sheet.
        exact (hW.preimage p.continuous).inter
          (universal_cover_candidate_center_sheet_isOpen (b := b) (x := x) U hU q)
      · intro hPre
        have himage :
            p '' (p ⁻¹' W ∩ universal_cover_candidate_center_sheet q U) = W := by
          ext y
          constructor
          · rintro ⟨r, hr, rfl⟩
            exact hr.1
          · intro hy
            have hyU : y ∈ (U : Set B) := hWU hy
            have hsurjOn :=
              universal_cover_candidate_center_sheet_surjOn (b := b) (x := x) U hU q
            rcases hsurjOn hyU with ⟨r, hrSheet, hpr⟩
            have hrW : r ∈ p ⁻¹' W := by
              change p r ∈ W
              exact hpr ▸ hy
            exact ⟨r, ⟨hrW, hrSheet⟩, hpr⟩
        -- Global openness of `p` converts the local image equality into the reverse implication.
        simpa [himage] using hopenMap _ hPre
    let _ : Nonempty (B → universalCoverCandidate b) := ⟨fun _ ↦ ⟨b, refl b⟩⟩
    let _ : Nonempty (p ⁻¹' ({x} : Set B)) := by
      rcases hx with ⟨e, rfl⟩
      exact ⟨⟨e, rfl⟩⟩
    let t : Bundle.Trivialization (p ⁻¹' ({x} : Set B)) p :=
      U.isOpen.trivializationDiscrete
        (fun q ↦ universal_cover_candidate_center_sheet q U) (U : Set B) hopen_iff
        hsheet_inj
        (fun q ↦ universal_cover_candidate_center_sheet_surjOn (b := b) (x := x) U hU q)
        hcenter_disjoint
        (by
          intro r hr
          rcases hcenter_cover hr with ⟨q, hq⟩
          exact Set.mem_iUnion.mpr ⟨q, hq⟩)
    exact ⟨t, by simpa [t] using U.mem⟩
  · simpa [hRange] using (IsClopen.pathComponent b).isClosed

/-- Helper for Lemma 3.8.6: the initial segment `γ|[0,t]`, recast so its source is the fixed
basepoint. -/
private abbrev universal_cover_candidate_initial_subpath
    {b x : B} (γ : Path b x) (t : I) : Path b (γ t) :=
  (γ.subpath 0 t).cast γ.source.symm rfl

/-- Helper for Lemma 3.8.6: if a short suffix of `γ` stays in `U`, then the canonical point at
time `t` lies in the basic sheet centered at time `s`. -/
private theorem universal_cover_candidate_subpath_mem_basic_set_of_segment_subset
    {b x : B} (γ : Path b x) (s t : I) (U : TopologicalSpace.OpenNhdsOf (γ s))
    (hseg : ∀ u : I, γ.subpath s t u ∈ (U : Set B)) :
    (⟨γ t, mk
        (universal_cover_candidate_initial_subpath γ t)⟩ :
      universalCoverCandidate b) ∈
        U[(⟨γ s, mk
            (universal_cover_candidate_initial_subpath γ s)⟩ :
          universalCoverCandidate b)] := by
  let y : U := ⟨γ t, by simpa using hseg 1⟩
  have hc_cont : Continuous fun u : I ↦ (⟨γ.subpath s t u, hseg u⟩ : U) := by
    fun_prop
  have hc_source :
      (⟨γ.subpath s t 0, hseg 0⟩ : U) = ⟨γ s, U.mem⟩ := by
    apply Subtype.ext
    simp
  have hc_target :
      (⟨γ.subpath s t 1, hseg 1⟩ : U) = y := by
    apply Subtype.ext
    simp [y]
  let cMap : C(I, U) := ⟨fun u ↦ ⟨γ.subpath s t u, hseg u⟩, hc_cont⟩
  let c : Path ⟨γ s, U.mem⟩ y := ⟨cMap, hc_source, hc_target⟩
  have hc_map :
      c.map continuous_subtype_val = γ.subpath s t := by
    ext u
    rfl
  have hc_quot :
      ((mk c).map U.subtypeVal) = mk (γ.subpath s t) := by
    simpa using congrArg mk hc_map
  have hquot :
      (mk (universal_cover_candidate_initial_subpath γ s)).trans
          ((mk c).map U.subtypeVal) =
        mk (universal_cover_candidate_initial_subpath γ t) := by
    -- Concatenating the initial segment with the short suffix is homotopic to the direct subpath.
    calc
      (mk (universal_cover_candidate_initial_subpath γ s)).trans
          ((mk c).map U.subtypeVal) =
          (mk (universal_cover_candidate_initial_subpath γ s)).trans
            (mk (γ.subpath s t)) := by rw [hc_quot]
      _ = mk
            (((γ.subpath 0 s).trans (γ.subpath s t)).cast γ.source.symm rfl) := by
          rw [← mk_trans]
          simp [universal_cover_candidate_initial_subpath, Path.cast_trans]
      _ = mk (universal_cover_candidate_initial_subpath γ t) := by
          exact eq.mpr
            ⟨(Path.Homotopy.subpathTransSubpath γ 0 s t).pathCast γ.source.symm rfl⟩
  refine ⟨y, c, ?_⟩
  apply Sigma.ext
  · simp [y]
  · simpa [c] using hquot.symm

/-- Helper for Lemma 3.8.6: near any time `t₀`, one can choose a small interval on which all
short suffixes of `γ` stay inside the chosen neighborhood of `γ t₀`. -/
private theorem universal_cover_candidate_subpath_local_sheet_control
    {b x : B} (γ : Path b x) (t₀ : I) (U : TopologicalSpace.OpenNhdsOf (γ t₀)) :
    ∃ W : Set I, IsOpen W ∧ t₀ ∈ W ∧
      ∀ ⦃t : I⦄, t ∈ W → ∀ u : I, γ.subpath t₀ t u ∈ (U : Set B) := by
  let F : I × I → B := fun z ↦ γ.subpath t₀ z.1 z.2
  have hF_cont : Continuous F := by
    have hcoord : Continuous fun z : I × I ↦ (t₀, z.1, z.2) := by
      fun_prop
    simpa [F] using γ.subpath_continuous_family.comp hcoord
  let N : Set (I × I) := F ⁻¹' (U : Set B)
  have hN_open : IsOpen N := U.isOpen.preimage hF_cont
  have hbase : ({t₀} : Set I) ×ˢ (Set.univ : Set I) ⊆ N := by
    intro z hz
    rcases z with ⟨t, u⟩
    rcases hz with ⟨ht, _⟩
    rcases ht with rfl
    change F (t, u) ∈ (U : Set B)
    simpa [F, Path.subpath_self] using U.mem
  rcases generalized_tube_lemma isCompact_singleton isCompact_univ hN_open hbase with
    ⟨W, V, hW_open, _hV_open, hW_mem, hV_mem, hWV⟩
  refine ⟨W, hW_open, hW_mem (by simp), ?_⟩
  intro t ht u
  have hu : u ∈ V := hV_mem (by simp)
  have hzu : (t, u) ∈ W ×ˢ V := ⟨ht, hu⟩
  change F (t, u) ∈ (U : Set B)
  exact hWV hzu

/-- Helper for Lemma 3.8.6: the canonical family `t ↦ [γ|[0,t]]` is continuous. -/
private theorem universal_cover_candidate_subpath_family_continuous
    {b x : B} (γ : Path b x) :
    Continuous fun t ↦
      (⟨γ t, mk
          (universal_cover_candidate_initial_subpath γ t)⟩ :
        universalCoverCandidate b) := by
  let hBasis := universalCoverCandidateBasicSets_isTopologicalBasis b
  rw [continuous_def]
  intro N hN
  rw [isOpen_iff_mem_nhds]
  intro t₀ ht₀
  let r₀ : universalCoverCandidate b :=
    ⟨γ t₀, mk
      (universal_cover_candidate_initial_subpath γ t₀)⟩
  rcases (hBasis.isOpen_iff.mp hN) r₀ ht₀ with
    ⟨s, hs, hr₀s, hsN⟩
  rcases hs with ⟨q, U, hU, rfl⟩
  let U₀ : TopologicalSpace.OpenNhdsOf (γ t₀) :=
    ⟨U.1, universalCoverCandidateBasicSet_endpoint_mem q U hr₀s⟩
  rcases exists_suitable_universal_cover_neighborhood_subset (γ t₀) U₀ with
    ⟨V, hVU, hV⟩
  have hsubset : V[r₀] ⊆ U[q] := by
    -- Shrinking inside `U` keeps the recentered basic sheet inside the original one.
    exact universal_cover_candidate_basic_set_subset_of_mem U hr₀s hVU
  rcases universal_cover_candidate_subpath_local_sheet_control γ t₀ V with
    ⟨W, hW_open, ht₀W, hWmem⟩
  refine mem_nhds_iff.mpr ⟨W, ?_, hW_open, ht₀W⟩
  intro t ht
  have hBasic :
      (⟨γ t, mk
          (universal_cover_candidate_initial_subpath γ t)⟩ :
        universalCoverCandidate b) ∈ V[r₀] := by
    -- Local sheet control converts geometric containment in `V` into basis membership upstairs.
    exact
      universal_cover_candidate_subpath_mem_basic_set_of_segment_subset γ t₀ t V
        (hWmem ht)
  exact hsN (hsubset hBasic)

/-- Helper for Lemma 3.8.6: the explicit subpath family gives a path from the distinguished point
to the class of any represented path. -/
private theorem universal_cover_candidate_joined_from_base
    (b : B) (q : universalCoverCandidate b) :
    Joined (⟨b, refl b⟩ : universalCoverCandidate b) q := by
  rcases q with ⟨x, γq⟩
  obtain ⟨γ, rfl⟩ := mk_surjective γq
  let Γ : C(I, universalCoverCandidate b) :=
    ⟨fun t ↦ ⟨γ t, mk
      (universal_cover_candidate_initial_subpath γ t)⟩,
      universal_cover_candidate_subpath_family_continuous γ⟩
  have hΓ_zero :
      Γ 0 = (⟨b, refl b⟩ : universalCoverCandidate b) := by
    apply Sigma.ext
    · change γ 0 = b
      exact γ.source
    · have hzero : HEq ((Γ 0).snd) (Path.Homotopic.Quotient.refl b) := by
        have hpointwise :
            ∀ t, ((Path.refl (γ 0)).cast γ.source.symm rfl) t = (Path.refl b) t := fun t ↦ by
              simp [Path.cast, γ.source]
        simpa [Γ, universal_cover_candidate_initial_subpath, Path.subpath_self, Path.cast,
          γ.source] using
          (Path.Homotopic.hpath_hext hpointwise)
      exact hzero
  have hΓ_one :
      Γ 1 = (⟨x, mk γ⟩ : universalCoverCandidate b) := by
    apply Sigma.ext
    · change γ 1 = x
      exact γ.target
    · have hone : HEq ((Γ 1).snd) (mk γ) := by
        have hpointwise : ∀ t, (γ.cast rfl γ.target) t = γ t := fun t ↦ by
          rfl
        simpa [Γ, universal_cover_candidate_initial_subpath, Path.subpath_zero_one, Path.cast,
          γ.target] using
          (Path.Homotopic.hpath_hext hpointwise)
      exact hone
  refine ⟨Path.mk Γ hΓ_zero hΓ_one⟩

/-- Helper for Lemma 3.8.6: the path-class model is path connected. -/
private theorem universal_cover_candidate_pathConnectedSpace
    (b : B) :
    PathConnectedSpace (universalCoverCandidate b) := by
  let e₀ : universalCoverCandidate b := ⟨b, refl b⟩
  refine ⟨⟨e₀⟩, ?_⟩
  intro x y
  -- Join both points to the distinguished class of the constant path.
  exact (universal_cover_candidate_joined_from_base b x).symm.trans
    (universal_cover_candidate_joined_from_base b y)

/-- Helper for Lemma 3.8.6: the covering lift of a path from the distinguished basepoint ends at
the corresponding endpoint-fixed homotopy class. -/
private theorem universal_cover_candidate_liftPath_endpoint_eq_pathClass
    (b : B)
    (hp : IsCoveringMap (universal_cover_candidate_projectionMap b))
    {x : B} (γ : Path b x) :
    hp.liftPath γ
        (⟨b, refl b⟩ :
          universalCoverCandidate b)
        γ.source 1 =
      ⟨x, mk γ⟩ := by
  let e₀ : universalCoverCandidate b := ⟨b, refl b⟩
  let Γ : C(I, universalCoverCandidate b) :=
    ⟨fun t ↦ ⟨γ t, mk
        (universal_cover_candidate_initial_subpath γ t)⟩,
      universal_cover_candidate_subpath_family_continuous γ⟩
  have hγ₀ : γ 0 = (universal_cover_candidate_projectionMap b) e₀ := by
    change γ 0 = b
    exact γ.source
  have hΓ :
      Γ = hp.liftPath γ e₀ hγ₀ := by
    -- The explicit subpath family is a lift of `γ`, so uniqueness identifies it with the
    -- abstract covering lift.
    refine (hp.eq_liftPath_iff' hγ₀).2 ?_
    constructor
    · ext t
      rfl
    · apply Sigma.ext
      · change γ 0 = b
        exact γ.source
      · have hzero : HEq ((Γ 0).snd) e₀.snd := by
          have hpointwise :
              ∀ t, ((Path.refl (γ 0)).cast γ.source.symm rfl) t = (Path.refl b) t := fun t ↦ by
                simp [Path.cast, γ.source]
          simpa [Γ, e₀, universal_cover_candidate_initial_subpath, Path.subpath_self, Path.cast,
            γ.source] using
            (Path.Homotopic.hpath_hext hpointwise)
        exact hzero
  have hΓ_one :
      Γ 1 = (⟨x, mk γ⟩ :
        universalCoverCandidate b) := by
    apply Sigma.ext
    · change γ 1 = x
      exact γ.target
    · have hone : HEq ((Γ 1).snd) (⟨x, mk γ⟩ :
          universalCoverCandidate b).snd := by
          have hpointwise : ∀ t, (γ.cast rfl γ.target) t = γ t := fun t ↦ by
            rfl
          simpa [Γ, universal_cover_candidate_initial_subpath, Path.subpath_zero_one, Path.cast,
            γ.target] using
            (Path.Homotopic.hpath_hext hpointwise)
      exact hone
  calc
    hp.liftPath γ e₀ hγ₀ 1 = Γ 1 := by
      simpa using congrArg (fun f : C(I, universalCoverCandidate b) ↦ f 1) hΓ.symm
    _ = ⟨x, mk γ⟩ := hΓ_one

/-- Helper for Lemma 3.8.6: the distinguished point in the path-class model has trivial image in
the base fundamental group. -/
private theorem universal_cover_candidate_fundamentalGroup_range_eq_bot
    (b : B)
    (hp : IsCoveringMap (universal_cover_candidate_projectionMap b)) :
    (FundamentalGroup.map (universal_cover_candidate_projectionMap b)
      (⟨b, refl b⟩ :
        universalCoverCandidate b)).range = ⊥ := by
  let E : Type u := universalCoverCandidate b
  let p : C(E, B) := universal_cover_candidate_projectionMap b
  let e₀ : E := ⟨b, refl b⟩
  rw [FundamentalGroup.map_eq_mapOfEq_rfl e₀]
  rw [MonoidHom.range_eq_bot_iff]
  ext γ
  refine Quotient.inductionOn γ ?_
  intro δ
  change FundamentalGroup.mapOfEq p rfl
      (FundamentalGroup.fromPath (mk δ)) = 1
  rw [FundamentalGroup.mapOfEq_apply]
  change FundamentalGroup.fromPath
      (mk ((δ.map p.continuous).cast rfl rfl)) = 1
  have hLift :
      δ.toContinuousMap =
        hp.liftPath (δ.map p.continuous) e₀ (δ.map p.continuous).source := by
    -- A loop upstairs is already the unique lift of its projection from `e₀`.
    refine (hp.eq_liftPath_iff' (δ.map p.continuous).source).2 ?_
    constructor
    · rfl
    · exact δ.source
  have hend :
      (⟨b, mk (δ.map p.continuous)⟩ : E) = e₀ := by
    -- Evaluating the lift endpoint formula at `1` forces the projected class to be trivial.
    calc
      (⟨b, mk (δ.map p.continuous)⟩ : E) =
          hp.liftPath (δ.map p.continuous) e₀
            (δ.map p.continuous).source 1 := by
              symm
              simpa [p, e₀] using
                universal_cover_candidate_liftPath_endpoint_eq_pathClass b
                  hp (δ.map p.continuous)
      _ = δ 1 := by
            simpa using congrArg (fun f : C(I, E) ↦ f 1) hLift.symm
      _ = e₀ := δ.target
  have hclass :
      mk ((δ.map p.continuous).cast rfl rfl) =
        refl b := by
    -- Equality of sigma points identifies the projected loop with the constant loop class.
    exact eq_of_heq ((Sigma.mk.inj_iff).mp hend).2
  simpa [hclass]

/-- Helper for Lemma 3.8.6: injectivity of `p_*` together with trivial image forces the total
space to be simply connected. -/
private theorem simplyConnectedSpace_of_fundamentalGroupRangeEqBot
    {E : Type u} [TopologicalSpace E] [PathConnectedSpace E]
    {p : C(E, B)} (hp : IsCoveringMap p) (e : E)
    (hbot : (FundamentalGroup.map p e).range = ⊥) :
    SimplyConnectedSpace E := by
  have hsub_e : Subsingleton (FundamentalGroup E e) := by
    let f : FundamentalGroup E e →* FundamentalGroup B (p e) := FundamentalGroup.map p e
    have hf : Function.Injective f := by
      simpa using hp.fundamentalGroup_map_injective e
    -- Injectivity plus trivial image collapses the based loop group at `e`.
    rw [MonoidHom.range_eq_bot_iff] at hbot
    refine ⟨fun γ δ ↦ hf ?_⟩
    simpa using
      (congrArg (fun g : FundamentalGroup E e →* FundamentalGroup B (p e) ↦ g γ) hbot).trans
        (congrArg (fun g : FundamentalGroup E e →* FundamentalGroup B (p e) ↦ g δ) hbot).symm
  have hsub : ∀ x : E, Subsingleton (FundamentalGroup E x) := fun x ↦ by
    let ex : FundamentalGroup E e ≃* FundamentalGroup E x :=
      FundamentalGroup.fundamentalGroupMulEquivOfPathConnected e x
    -- Path connectedness transports triviality of the loop group from `e` to every basepoint.
    letI := hsub_e
    refine ⟨fun γ δ ↦ ?_⟩
    have hpre : ex.symm γ = ex.symm δ := Subsingleton.elim _ _
    simpa using congrArg ex hpre
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, ?_⟩
  intro x γ
  letI := hsub x
  have h :
      (FundamentalGroup.fromPath (mk γ) :
        FundamentalGroup E x) = 1 :=
    Subsingleton.elim _ _
  -- Convert triviality in the based loop group back to path homotopy to the constant loop.
  rw [show (1 : FundamentalGroup E x) =
      FundamentalGroup.fromPath (mk (Path.refl x)) by rfl] at h
  exact eq.mp h

/- The owner fact behind Lemma 3.8.6 (2): the path-class space is locally path connected. -/
-- Proof sketch: the standard basic neighborhoods from Construction 3.8.3 are indexed by suitable
-- open neighborhoods in `B`. By Lemma 3.8.5, each such basic neighborhood is identified with its
-- indexing neighborhood, which is path connected by definition, so these basic sets form a
-- path-connected neighborhood basis on the total space.
instance instLocPathConnectedSpace_universalCoverCandidate (b : B) :
    LocPathConnectedSpace (universalCoverCandidate b) := by
  -- Use the generated basis of suitable basic sheets, each of which is open and path connected.
  let hBasis := universalCoverCandidateBasicSets_isTopologicalBasis b
  have hBasis' :
      IsTopologicalBasis
        {s : Set (universalCoverCandidate b) | IsOpen s ∧ IsPathConnected s} := by
    refine IsTopologicalBasis.of_isOpen_of_subset ?_ hBasis ?_
    · intro s hs
      exact hs.1
    · intro s hs
      rcases hs with ⟨q, U, hU, rfl⟩
      constructor
      · exact universal_cover_candidate_basic_set_isOpen q U hU
      · exact universalCoverCandidateBasicSet_isPathConnected q U hU
  exact
    (locPathConnectedSpace_iff_isTopologicalBasis_isOpen_isPathConnected).2 hBasis'

/- The owner fact behind Lemma 3.8.6 (3): the path-class space is simply connected. -/
-- Proof sketch: a loop in the total space based at the class of the constant path projects to a
-- loop in `B`. The endpoint-fixed path-class construction identifies the endpoint of the lifted
-- loop with the resulting path class in `B`, so a loop can close only when that class is trivial.
-- This makes every based loop null-homotopic, hence the total space is simply connected.
instance instSimplyConnectedSpace_universalCoverCandidate (b : B) :
    SimplyConnectedSpace (universalCoverCandidate b) := by
  let p : C(universalCoverCandidate b, B) := universal_cover_candidate_projectionMap b
  let e₀ : universalCoverCandidate b := ⟨b, refl b⟩
  have hp : IsCoveringMap p := universal_cover_candidate_projection_isCoveringMap b
  have hpath : PathConnectedSpace (universalCoverCandidate b) :=
    universal_cover_candidate_pathConnectedSpace b
  let _ : PathConnectedSpace (universalCoverCandidate b) := hpath
  have hbot : (FundamentalGroup.map p e₀).range = ⊥ :=
    universal_cover_candidate_fundamentalGroup_range_eq_bot b hp
  -- Apply the generic closing lemma once the endpoint map is known to be a covering map.
  exact simplyConnectedSpace_of_fundamentalGroupRangeEqBot hp e₀ hbot

end

/-- Lemma 3.8.6 (1): the path-class space constructed over the basepoint `b` is connected. -/
theorem universalCoverCandidate_connectedSpace
    (b : B) [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] :
    ConnectedSpace (universalCoverCandidate b) :=
  inferInstance

/-- Lemma 3.8.6 (2): the path-class space constructed over the basepoint `b` is locally path
connected. -/
theorem universalCoverCandidate_locPathConnectedSpace
    (b : B) [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] :
    LocPathConnectedSpace (universalCoverCandidate b) :=
  inferInstance

/-- Lemma 3.8.6 (3): the path-class space constructed over the basepoint `b` is simply connected.
-/
theorem universalCoverCandidate_simplyConnectedSpace
    (b : B) [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] :
    SimplyConnectedSpace (universalCoverCandidate b) :=
  inferInstance
