import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Construction_3_8_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_2_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_8_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_2_3
import Mathlib.Topology.Subpath

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open Path.Homotopic.Quotient
open TopologicalSpace.OpenNhdsOf
open scoped FundamentalGroup unitInterval UniversalCover

variable {B : Type u} [TopologicalSpace B]

/-- Helper for Theorem 3.8.2: a path-connected covering with trivial induced subgroup at one
basepoint is already universal. -/
private theorem isUniversalCoveringMap_of_fundamentalGroup_range_eq_bot
    {E : Type u} [TopologicalSpace E] [PathConnectedSpace E] {p : C(E, B)}
    (hp : IsPathConnectedCoveringMap p) (e : E)
    (hbot : (FundamentalGroup.map p e).range = ⊥) :
    IsUniversalCoveringMap p := by
  have hsub_e : Subsingleton (FundamentalGroup E e) := by
    let f : FundamentalGroup E e →* FundamentalGroup B (p e) := FundamentalGroup.map p e
    have hf : Function.Injective f := by
      simpa using hp.isCoveringMap.fundamentalGroup_map_injective e
    -- Injectivity plus trivial image makes the based fundamental group at `e` trivial.
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
  have hsimply : SimplyConnectedSpace E := by
    rw [simply_connected_iff_loops_nullhomotopic]
    refine ⟨inferInstance, ?_⟩
    intro x γ
    letI := hsub x
    have h :
        (FundamentalGroup.fromPath (mk γ) :
          FundamentalGroup E x) = 1 :=
      Subsingleton.elim _ _
    -- Converting the trivial loop-group element back to a path class shows `γ` is
    -- null-homotopic.
    rw [show (1 : FundamentalGroup E x) =
        FundamentalGroup.fromPath (mk (Path.refl x)) by rfl] at h
    exact eq.mp h
  exact
    { left := hp.1
      right := hp.2
      toSimplyConnectedSpace := hsimply }

/-- Helper for Theorem 3.8.2: if two basic sheets over the same suitable neighborhood meet, then
their indexing path classes coincide. -/
private theorem universal_cover_candidate_basic_sheet_eq_of_inter
    {b0 : B} {q₁ q₂ : universalCoverCandidate b0}
    (U : TopologicalSpace.OpenNhdsOf q₁.1) (hU : U.IsSuitableForUniversalCover)
    (hq₂ : q₂.1 = q₁.1)
    {r : universalCoverCandidate b0}
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
            -- The first coordinates of the common point force the two endpoints in `U` to agree.
            apply Subtype.ext
            exact congrArg Sigma.fst hEq
          subst hy
          have hpaths :
              (γ₁.trans ((mk c₁).map U.subtypeVal)) =
                (γ₂.trans ((mk c₂).map U.subtypeVal)) := by
            -- Once the endpoints match, the common point identifies the two concatenated classes.
            exact eq_of_heq ((Sigma.mk.inj_iff).mp hEq).2
          have hright_same :
              (γ₂.trans ((mk c₁).map U.subtypeVal)) =
                (γ₂.trans ((mk c₂).map U.subtypeVal)) := by
            -- Trivial monodromy in `U` lets us replace the chosen path to the common endpoint.
            have hsigma :
                (⟨y₁.1, γ₂.trans ((mk c₁).map U.subtypeVal)⟩ :
                  universalCoverCandidate b0) =
                ⟨y₁.1, γ₂.trans ((mk c₂).map U.subtypeVal)⟩ :=
              universalCoverCandidate_pathClass_eq_of_paths
                ⟨x', γ₂⟩ U hU.2 y₁ c₁ c₂
            exact eq_of_heq ((Sigma.mk.inj_iff).mp hsigma).2
          let α : Path.Homotopic.Quotient x' y₁.1 :=
            ((mk c₁).map U.subtypeVal)
          have hcommon : γ₁.trans α = γ₂.trans α := by
            -- Replace the right-hand extension by the same endpoint path class on both sides.
            simpa [α] using hpaths.trans hright_same.symm
          have hγ : γ₁ = γ₂ := by
            -- Cancel the common suffix by composing with its inverse.
            calc
              γ₁ = (γ₁.trans α).trans α.symm := by
                rw [trans_assoc, trans_symm,
                  trans_refl]
              _ = (γ₂.trans α).trans α.symm := by rw [hcommon]
              _ = γ₂ := by
                rw [trans_assoc, trans_symm,
                  trans_refl]
          simp [hγ]

/-- Helper for Theorem 3.8.2: the endpoint projection on the path-class space is continuous for
the topology generated by the standard basic sets. -/
private theorem universal_cover_candidate_projection_continuous
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] (b0 : B) :
    Continuous (fun q : universalCoverCandidate b0 ↦ q.1) := by
  let hBasis := universalCoverCandidateBasicSets_isTopologicalBasis b0
  rw [continuous_def]
  intro N hN
  rw [hBasis.isOpen_iff]
  intro r hr
  let Nnhd : TopologicalSpace.OpenNhdsOf r.1 := ⟨⟨N, hN⟩, hr⟩
  rcases exists_suitable_universal_cover_neighborhood_subset r.1 Nnhd with
    ⟨U, hUN, hU⟩
  refine ⟨U[r], ?_, ?_, ?_⟩
  · -- Suitable basic sheets are among the chosen basis elements by construction.
    exact ⟨r, U, hU, rfl⟩
  · -- The point `r` lies in its own `U`-sheet by the constant-path witness.
    exact universalCoverCandidateBasicSet_self_mem r U
  · -- Every point of the `U`-sheet projects into `U ⊆ N`.
    intro s hs
    exact hUN (universalCoverCandidateBasicSet_endpoint_mem r U hs)

/-- Helper for Theorem 3.8.2: the path-class model carries the canonical endpoint projection to
the base space. -/
private def universal_cover_candidate_projectionMap
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] (b0 : B) :
    C(universalCoverCandidate b0, B) :=
  ⟨fun q ↦ q.1, universal_cover_candidate_projection_continuous b0⟩

/-- Helper for Theorem 3.8.2: each suitable basic sheet is open in the generated topology on the
path-class total space. -/
private theorem universal_cover_candidate_basic_set_isOpen
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 : B} (q : universalCoverCandidate b0)
    (U : TopologicalSpace.OpenNhdsOf q.1) (hU : U.IsSuitableForUniversalCover) :
    IsOpen (U[q]) := by
  -- The path-class topology was generated from these suitable basic sheets.
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨q, U, hU, rfl⟩

/-- Helper for Theorem 3.8.2: inside the fiber over `b`, a suitable sheet centered at `q` meets
that fiber only at the point `q`. -/
private theorem universal_cover_candidate_fiber_point_eq
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B}
    (q : universal_cover_candidate_projectionMap b0 ⁻¹' ({b} : Set B)) :
    q.1.1 = b := by
  have hmem :
      universal_cover_candidate_projectionMap b0 q.1 ∈ ({b} : Set B) :=
    q.2
  have hmem' : q.1.1 ∈ ({b} : Set B) := by
    simpa [universal_cover_candidate_projectionMap] using hmem
  exact Set.mem_singleton_iff.mp hmem'

/-- Helper for Theorem 3.8.2: inside the fiber over `b`, a suitable sheet centered at `q` meets
that fiber only at the point `q`. -/
private theorem universal_cover_candidate_fiber_singleton_eq_sheet_inter
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} (q : universalCoverCandidate b0)
    (U : TopologicalSpace.OpenNhdsOf q.1) (hU : U.IsSuitableForUniversalCover) (hq : q.1 = b) :
    { x : universal_cover_candidate_projectionMap b0 ⁻¹' ({b} : Set B) |
        x.1 ∈ U[q] } =
      {⟨q, by simp [universal_cover_candidate_projectionMap, hq]⟩} := by
  ext x
  constructor
  · intro hx
    have hx' : x.1.1 = q.1 := by
      calc
        x.1.1 = b := universal_cover_candidate_fiber_point_eq x
        _ = q.1 := hq.symm
    have hxself :
        x.1 ∈ (hx' ▸ U)[x.1] := by
      -- Every point lies in the basic sheet indexed by itself.
      exact universalCoverCandidateBasicSet_self_mem x.1 (hx' ▸ U)
    have hqx : q = x.1 := by
      -- If two sheets over the same suitable neighborhood meet in a fiber point, they agree.
      exact universal_cover_candidate_basic_sheet_eq_of_inter
        U hU hx' hx hxself
    exact Set.mem_singleton_iff.mpr (Subtype.ext hqx.symm)
  · rintro rfl
    -- The center point belongs to its own sheet via the constant path.
    exact universalCoverCandidateBasicSet_self_mem q U

/-- Helper for Theorem 3.8.2: the endpoint projection from the path-class model is surjective,
since any basepoint can be reached by a path from the chosen origin `b0`. -/
private theorem universal_cover_candidate_projectionMap_surjective
    [ConnectedSpace B] [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] (b0 : B) :
    Function.Surjective (universal_cover_candidate_projectionMap b0) := by
  let _ : PathConnectedSpace B := PathConnectedSpace.of_locPathConnectedSpace
  intro x
  -- Represent `x` by the class of any path from `b0` to `x`.
  refine ⟨⟨x, mk (PathConnectedSpace.somePath b0 x)⟩, rfl⟩

/-- Helper for Theorem 3.8.2: the sheet centered at a fiber point is obtained by transporting the
chosen suitable neighborhood along the endpoint equality of that fiber point. -/
private def universal_cover_candidate_center_sheet
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} (q : universal_cover_candidate_projectionMap b0 ⁻¹' ({b} : Set B))
    (U : TopologicalSpace.OpenNhdsOf b) :
    Set (universalCoverCandidate b0) :=
  (Eq.ndrec U (universal_cover_candidate_fiber_point_eq q).symm)[q.1]

/-- Helper for Theorem 3.8.2: transporting a suitable neighborhood along an endpoint equality does
not change the suitability data. -/
private theorem isSuitableForUniversalCover_ndrec
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {x y : B} (h : x = y) (U : TopologicalSpace.OpenNhdsOf y)
    (hU : U.IsSuitableForUniversalCover) :
    (Eq.ndrec U h.symm).IsSuitableForUniversalCover := by
  -- Suitability depends only on the underlying open neighborhood and the identified basepoint.
  subst h
  simpa using hU

/-- Helper for Theorem 3.8.2: successive transports of an open neighborhood along endpoint
equalities compose in the expected way. -/
private theorem openNhdsOf_ndrec_trans
    {x y z : B} (hxy : y = x) (hxz : x = z) (U : TopologicalSpace.OpenNhdsOf z) :
    Eq.ndrec (Eq.ndrec U hxz.symm) hxy.symm = Eq.ndrec U (hxy.trans hxz).symm := by
  -- Collapse the two transports after identifying all three endpoints.
  subst hxy
  subst hxz
  rfl

/-- Helper for Theorem 3.8.2: every point over a suitable neighborhood belongs to one of the
centered sheets indexed by the fiber over the neighborhood basepoint. -/
private theorem universal_cover_candidate_center_sheet_cover
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} (U : TopologicalSpace.OpenNhdsOf b) (hU : U.IsSuitableForUniversalCover)
    {r : universalCoverCandidate b0} (hr : r.1 ∈ (U : Set B)) :
    ∃ q : universal_cover_candidate_projectionMap b0 ⁻¹' ({b} : Set B),
      r ∈ universal_cover_candidate_center_sheet q U := by
  let i : C(U, B) := U.subtypeVal
  let bU : U := ⟨b, U.mem⟩
  let rU : U := ⟨r.1, hr⟩
  let c : Path bU rU := (hU.1.joinedIn b U.mem r.1 hr).joined_subtype.somePath
  let q : universalCoverCandidate b0 :=
    ⟨b, r.2.trans (((mk c).map i).symm)⟩
  let qf : universal_cover_candidate_projectionMap b0 ⁻¹' ({b} : Set B) :=
    ⟨q, by simp [universal_cover_candidate_projectionMap, q]⟩
  refine ⟨qf, ?_⟩
  have hrSheet : r ∈ U[q] := by
    refine ⟨⟨r.1, hr⟩, c, ?_⟩
    apply Sigma.ext
    · rfl
    · -- Cancelling the path inside `U` returns the original path class at `r`.
      dsimp [q]
      rw [trans_assoc, symm_trans, trans_refl]
  simpa [universal_cover_candidate_center_sheet, qf, q] using hrSheet

/-- Helper for Theorem 3.8.2: on a fixed suitable neighborhood, two points in the same centered
sheet are equal as soon as they have the same projection to the base. -/
private theorem universal_cover_candidate_center_sheet_injOn
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} (U : TopologicalSpace.OpenNhdsOf b) (hU : U.IsSuitableForUniversalCover)
    (q : universal_cover_candidate_projectionMap b0 ⁻¹' ({b} : Set B)) :
    (universal_cover_candidate_center_sheet q U).InjOn
      (universal_cover_candidate_projectionMap b0) := by
  have hq : q.1.1 = b := universal_cover_candidate_fiber_point_eq q
  have hUq : (Eq.ndrec U hq.symm).IsSuitableForUniversalCover := by
    -- Reindex the same suitable neighborhood so it is based at the endpoint of `q`.
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
  -- Over a suitable neighborhood, equal endpoints force equal path classes in one sheet.
  exact universalCoverCandidate_pathClass_eq_of_paths
    q.1 (Eq.ndrec U hq.symm) hUq.2 y₁ c₁ c₂

/-- Helper for Theorem 3.8.2: a centered sheet is open, since after transporting the indexing
neighborhood to the fiber point it is just an ordinary suitable basic sheet. -/
private theorem universal_cover_candidate_center_sheet_isOpen
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} (U : TopologicalSpace.OpenNhdsOf b) (hU : U.IsSuitableForUniversalCover)
    (q : universal_cover_candidate_projectionMap b0 ⁻¹' ({b} : Set B)) :
    IsOpen (universal_cover_candidate_center_sheet q U) := by
  have hq : q.1.1 = b := universal_cover_candidate_fiber_point_eq q
  let Uq : TopologicalSpace.OpenNhdsOf q.1.1 := Eq.ndrec U hq.symm
  have hUq : Uq.IsSuitableForUniversalCover := by
    -- Suitability is unchanged by transporting the same open neighborhood to the sheet center.
    exact isSuitableForUniversalCover_ndrec hq U hU
  -- After rewriting the transported neighborhood, the centered sheet is a basic open set.
  simpa [universal_cover_candidate_center_sheet, Uq] using
    universal_cover_candidate_basic_set_isOpen q.1 Uq hUq

/-- Helper for Theorem 3.8.2: the endpoint projection is surjective on each centered sheet over a
suitable neighborhood. -/
private theorem universal_cover_candidate_center_sheet_surjOn
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} (U : TopologicalSpace.OpenNhdsOf b) (hU : U.IsSuitableForUniversalCover)
    (q : universal_cover_candidate_projectionMap b0 ⁻¹' ({b} : Set B)) :
    (universal_cover_candidate_center_sheet q U).SurjOn
      (universal_cover_candidate_projectionMap b0) (U : Set B) := by
  rcases q with ⟨q, hqmem⟩
  have hq : q.1 = b := by
    -- Unpack the fiber condition to identify the center point with the neighborhood basepoint.
    simpa [universal_cover_candidate_projectionMap] using hqmem
  subst hq
  -- After the endpoint rewrite, the centered sheet is the ordinary suitable basic sheet.
  simpa [universal_cover_candidate_center_sheet, universal_cover_candidate_projectionMap] using
    universalCoverCandidateBasicSet_endpoint_surjOn q U hU

/-- Helper for Theorem 3.8.2: centered sheets over one suitable neighborhood are pairwise
disjoint. -/
private theorem universal_cover_candidate_center_sheets_pairwise_disjoint
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} (U : TopologicalSpace.OpenNhdsOf b) (hU : U.IsSuitableForUniversalCover) :
    Pairwise
      (fun q₁ q₂ : universal_cover_candidate_projectionMap b0 ⁻¹' ({b} : Set B) ↦
        Disjoint (universal_cover_candidate_center_sheet q₁ U)
          (universal_cover_candidate_center_sheet q₂ U)) := by
  intro q₁ q₂ hne
  refine Set.disjoint_left.2 ?_
  intro r hr₁ hr₂
  have hq₁ : q₁.1.1 = b := universal_cover_candidate_fiber_point_eq q₁
  have hq₂ : q₂.1.1 = b := universal_cover_candidate_fiber_point_eq q₂
  have hU₁ : (Eq.ndrec U hq₁.symm).IsSuitableForUniversalCover := by
    -- Reindex the fixed suitable neighborhood at the first sheet center.
    exact isSuitableForUniversalCover_ndrec hq₁ U hU
  have hr₁' : r ∈ (Eq.ndrec U hq₁.symm)[q₁.1] := by
    simpa [universal_cover_candidate_center_sheet] using hr₁
  have hr₂' : r ∈ (Eq.ndrec U hq₂.symm)[q₂.1] := by
    simpa [universal_cover_candidate_center_sheet] using hr₂
  have hendpoint : q₂.1.1 = q₁.1.1 := hq₂.trans hq₁.symm
  have htransport :
      hendpoint ▸ (Eq.ndrec U hq₁.symm) = Eq.ndrec U hq₂.symm := by
    -- Both ways of transporting the original neighborhood to the second endpoint agree.
    simpa [hendpoint] using
      (openNhdsOf_ndrec_trans hendpoint hq₁ U)
  have hr₂'' : r ∈ (hendpoint ▸ (Eq.ndrec U hq₁.symm))[q₂.1] := by
    -- Rewrite the second centered-sheet membership to the common neighborhood based at `q₁`.
    simpa [htransport] using hr₂'
  have hsame :
      q₁.1 = q₂.1 := by
    -- A point lying in both centered sheets forces the two indexing path classes to coincide.
    exact
      universal_cover_candidate_basic_sheet_eq_of_inter
        (Eq.ndrec U hq₁.symm) hU₁ hendpoint hr₁' hr₂''
  exact hne (Subtype.ext hsame)

/-- Helper for Theorem 3.8.2: each fiber of the path-class projection is discrete, because a
suitable sheet cuts out a singleton around each fiber point. -/
private theorem universal_cover_candidate_fiber_discrete
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 b : B} :
    DiscreteTopology (universal_cover_candidate_projectionMap b0 ⁻¹' ({b} : Set B)) := by
  rcases exists_suitable_universal_cover_neighborhood b with ⟨U, hU⟩
  refine discreteTopology_iff_isOpen_singleton.mpr ?_
  intro q
  have hq : q.1.1 = b := universal_cover_candidate_fiber_point_eq q
  let Uq : TopologicalSpace.OpenNhdsOf q.1.1 := Eq.ndrec U hq.symm
  have hUq : Uq.IsSuitableForUniversalCover := by
    -- Reuse the same suitable neighborhood at the endpoint of the chosen fiber point.
    exact isSuitableForUniversalCover_ndrec hq U hU
  have hopen_center :
      IsOpen (universal_cover_candidate_center_sheet q U) := by
    -- After one explicit transport, the centered sheet is an ordinary suitable basic set.
    simpa [universal_cover_candidate_center_sheet, Uq] using
      universal_cover_candidate_basic_set_isOpen q.1 Uq hUq
  have hopen_trace :
      IsOpen {x : universal_cover_candidate_projectionMap b0 ⁻¹' ({b} : Set B) |
        x.1 ∈ universal_cover_candidate_center_sheet q U} := by
    -- The fiber trace of an open centered sheet is open by continuity of the subtype inclusion.
    simpa [Set.preimage] using
      hopen_center.preimage
        (continuous_subtype_val :
          Continuous fun x :
            universal_cover_candidate_projectionMap b0 ⁻¹' ({b} : Set B) ↦ x.1)
  have hsingleton :
      {x : universal_cover_candidate_projectionMap b0 ⁻¹' ({b} : Set B) |
          x.1 ∈ universal_cover_candidate_center_sheet q U} = {q} := by
    -- In the fiber, the centered sheet meets the fiber only at its center.
    simpa [universal_cover_candidate_center_sheet, Uq] using
      (universal_cover_candidate_fiber_singleton_eq_sheet_inter q.1 Uq hUq hq)
  simpa [hsingleton] using hopen_trace

/-- Helper for Theorem 3.8.2: the initial segment `γ|[0,t]`, recast so that its source is the
distinguished basepoint `b0`. -/
private abbrev universal_cover_candidate_initial_subpath
    {b0 x : B} (γ : Path b0 x) (t : I) : Path b0 (γ t) :=
  (γ.subpath 0 t).cast γ.source.symm rfl

/-- Helper for Theorem 3.8.2: if the short suffix of `γ` from `s` to `t` stays in `U`, then the
canonical endpoint-fixed class at time `t` lies in the basic sheet centered at time `s`. -/
private theorem universal_cover_candidate_subpath_mem_basic_set_of_segment_subset
    {b0 x : B} (γ : Path b0 x) (s t : I) (U : TopologicalSpace.OpenNhdsOf (γ s))
    (hseg : ∀ u : I, γ.subpath s t u ∈ (U : Set B)) :
    (⟨γ t, mk
        (universal_cover_candidate_initial_subpath γ t)⟩ :
      universalCoverCandidate b0) ∈
        U[(⟨γ s, mk
            (universal_cover_candidate_initial_subpath γ s)⟩ :
          universalCoverCandidate b0)] := by
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
      ((mk c).map
        U.subtypeVal) =
        mk (γ.subpath s t) := by
    simpa using congrArg mk hc_map
  have hquot :
      (mk (universal_cover_candidate_initial_subpath γ s)).trans
          ((mk c).map
            U.subtypeVal) =
        mk (universal_cover_candidate_initial_subpath γ t) := by
    -- Concatenating the initial segment with the short suffix is homotopic to the direct subpath.
    calc
      (mk (universal_cover_candidate_initial_subpath γ s)).trans
          ((mk c).map
            U.subtypeVal) =
        (mk (universal_cover_candidate_initial_subpath γ s)).trans
          (mk (γ.subpath s t)) := by
            rw [hc_quot]
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

/-- Helper for Theorem 3.8.2: near any time `t₀`, one can choose an open interval in the unit
interval on which every short suffix of `γ` remains inside the chosen neighborhood of `γ t₀`. -/
private theorem universal_cover_candidate_subpath_local_sheet_control
    {b0 x : B} (γ : Path b0 x) (t₀ : I) (U : TopologicalSpace.OpenNhdsOf (γ t₀)) :
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

/-- Helper for Theorem 3.8.2: the canonical family `t ↦ [γ|[0,t]]` is continuous for the
generated path-class topology. -/
private theorem universal_cover_candidate_subpath_family_continuous
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 x : B} (γ : Path b0 x) :
    Continuous fun t ↦
      (⟨γ t, mk
          (universal_cover_candidate_initial_subpath γ t)⟩ :
        universalCoverCandidate b0) := by
  let hBasis := universalCoverCandidateBasicSets_isTopologicalBasis b0
  rw [continuous_def]
  intro N hN
  rw [isOpen_iff_mem_nhds]
  intro t₀ ht₀
  let r₀ : universalCoverCandidate b0 :=
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
    -- Recenter the basic sheet at the actual value of the canonical family.
    exact
      universal_cover_candidate_basic_set_subset_of_mem U hr₀s hVU
  rcases universal_cover_candidate_subpath_local_sheet_control γ t₀ V with
    ⟨W, hW_open, ht₀W, hWmem⟩
  refine mem_nhds_iff.mpr ⟨W, ?_, hW_open, ht₀W⟩
  intro t ht
  have hBasic :
      (⟨γ t, mk
          (universal_cover_candidate_initial_subpath γ t)⟩ :
        universalCoverCandidate b0) ∈ V[r₀] := by
    -- Local sheet control converts geometric containment in `V` into basis membership upstairs.
    exact
      universal_cover_candidate_subpath_mem_basic_set_of_segment_subset γ t₀ t V
        (hWmem ht)
  exact hsN (hsubset hBasic)

/-- Helper for Theorem 3.8.2: the covering lift of a path from the distinguished basepoint ends
at the corresponding endpoint-fixed homotopy class. -/
private theorem universal_cover_candidate_liftPath_endpoint_eq_pathClass
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 x : B}
    (hp : IsPathConnectedCoveringMap
      (universal_cover_candidate_projectionMap b0))
    (γ : Path b0 x) :
    hp.isCoveringMap.liftPath γ
        (⟨b0, refl b0⟩ :
          universalCoverCandidate b0)
        γ.source 1 =
      ⟨x, mk γ⟩ := by
  let e₀ : universalCoverCandidate b0 :=
    ⟨b0, refl b0⟩
  let Γ : C(I, universalCoverCandidate b0) :=
    ⟨fun t ↦ ⟨γ t, mk
        (universal_cover_candidate_initial_subpath γ t)⟩,
      universal_cover_candidate_subpath_family_continuous γ⟩
  have hγ₀ : γ 0 = (universal_cover_candidate_projectionMap b0) e₀ := by
    change γ 0 = b0
    exact γ.source
  have hΓ :
      Γ = hp.isCoveringMap.liftPath γ e₀ hγ₀ := by
    -- The explicit subpath family is a lift of `γ` from `e₀`, so uniqueness identifies it with
    -- the abstract covering lift.
    refine (hp.isCoveringMap.eq_liftPath_iff' hγ₀).2 ?_
    constructor
    · ext t
      rfl
    · apply Sigma.ext
      · change γ 0 = b0
        exact γ.source
      · have hzero : HEq ((Γ 0).snd) e₀.snd := by
          have hpointwise :
              ∀ t, ((Path.refl (γ 0)).cast γ.source.symm rfl) t = (Path.refl b0) t := fun t ↦ by
                simp [Path.cast, γ.source]
          simpa [Γ, e₀, universal_cover_candidate_initial_subpath, Path.subpath_self, Path.cast,
            γ.source] using
            (Path.Homotopic.hpath_hext hpointwise)
        exact hzero
  have hΓ_one :
      Γ 1 = (⟨x, mk γ⟩ :
        universalCoverCandidate b0) := by
    -- Evaluating the explicit family at `1` recovers the full path class.
    apply Sigma.ext
    · change γ 1 = x
      exact γ.target
    · have hone : HEq ((Γ 1).snd) (⟨x, mk γ⟩ :
          universalCoverCandidate b0).snd := by
          have hpointwise : ∀ t, (γ.cast rfl γ.target) t = γ t := fun t ↦ by
            rfl
          simpa [Γ, universal_cover_candidate_initial_subpath, Path.subpath_zero_one, Path.cast,
            γ.target] using
            (Path.Homotopic.hpath_hext hpointwise)
      exact hone
  calc
    hp.isCoveringMap.liftPath γ e₀ hγ₀ 1 = Γ 1 := by
      simpa using congrArg (fun f : C(I, universalCoverCandidate b0) ↦ f 1) hΓ.symm
    _ = ⟨x, mk γ⟩ := hΓ_one

/-- Helper for Theorem 3.8.2: the distinguished point in the path-class model has trivial induced
subgroup in the base fundamental group. -/
private theorem universal_cover_candidate_fundamentalGroup_range_eq_bot
    [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B]
    {b0 : B}
    (hp : IsPathConnectedCoveringMap
      (universal_cover_candidate_projectionMap b0)) :
    (FundamentalGroup.map (universal_cover_candidate_projectionMap b0)
      (⟨b0, refl b0⟩ :
        universalCoverCandidate b0)).range = ⊥ := by
  let E : Type u := universalCoverCandidate b0
  let p : C(E, B) := universal_cover_candidate_projectionMap b0
  let e₀ : E := ⟨b0, refl b0⟩
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
        hp.isCoveringMap.liftPath (δ.map p.continuous) e₀ (δ.map p.continuous).source := by
    -- A loop in the total space is already the unique lift of its projection starting at `e₀`.
    refine (hp.isCoveringMap.eq_liftPath_iff' (δ.map p.continuous).source).2 ?_
    constructor
    · rfl
    · exact δ.source
  have hend :
      (⟨b0, mk (δ.map p.continuous)⟩ : E) = e₀ := by
    -- Closing up the lifted loop forces the projected path class to be the endpoint formula.
    calc
      (⟨b0, mk (δ.map p.continuous)⟩ : E) =
          hp.isCoveringMap.liftPath (δ.map p.continuous) e₀
            (δ.map p.continuous).source 1 := by
              symm
              simpa [p, e₀] using
                universal_cover_candidate_liftPath_endpoint_eq_pathClass
                  hp (δ.map p.continuous)
      _ = δ 1 := by
            simpa using congrArg (fun f : C(I, E) ↦ f 1) hLift.symm
      _ = e₀ := δ.target
  have hclass :
      mk ((δ.map p.continuous).cast rfl rfl) =
        refl b0 := by
    -- Equality of the sigma points identifies the projected loop with the constant loop class.
    exact eq_of_heq ((Sigma.mk.inj_iff).mp hend).2
  simpa [hclass]

/-- Helper for Theorem 3.8.2: the source-faithful path-class construction should produce a
path-connected covering with trivial image subgroup at a chosen point. -/
private theorem exists_pathConnectedCovering_with_trivial_fundamentalGroup_range
    [ConnectedSpace B] [LocPathConnectedSpace B] [SemilocallySimplyConnectedSpace B] :
    ∃ (E : Type u) (_ : TopologicalSpace E) (_ : PathConnectedSpace E) (p : C(E, B)),
      IsPathConnectedCoveringMap p ∧ ∃ e : E, (FundamentalGroup.map p e).range = ⊥ := by
  -- Route correction: the remaining work is the covering assembly for the path-class space, not a
  -- fresh simply-connectedness development.
  classical
  let b0 : B := Classical.choice inferInstance
  let E : Type u := universalCoverCandidate b0
  let p : C(E, B) := universal_cover_candidate_projectionMap b0
  have hsurj : Function.Surjective p := universal_cover_candidate_projectionMap_surjective b0
  have hfiber_discrete :
      ∀ b : B, DiscreteTopology (p ⁻¹' ({b} : Set B)) := fun b ↦
        by
          simpa [p, E] using
            (universal_cover_candidate_fiber_discrete :
              DiscreteTopology (universal_cover_candidate_projectionMap b0 ⁻¹' ({b} : Set B)))
  have hcenter_cover :
      ∀ b : B, ∀ U : TopologicalSpace.OpenNhdsOf b, U.IsSuitableForUniversalCover →
        ∀ {r : E}, r.1 ∈ (U : Set B) →
          ∃ q : p ⁻¹' ({b} : Set B), r ∈ universal_cover_candidate_center_sheet q U := by
    intro b U hU r hr
    simpa [p, E] using universal_cover_candidate_center_sheet_cover
      U hU hr
  have hcenter_disjoint :
      ∀ b : B, ∀ U : TopologicalSpace.OpenNhdsOf b, U.IsSuitableForUniversalCover →
        Pairwise (fun q₁ q₂ : p ⁻¹' ({b} : Set B) ↦
          Disjoint (universal_cover_candidate_center_sheet q₁ U)
            (universal_cover_candidate_center_sheet q₂ U)) := by
    intro b U hU
    simpa [p, E] using universal_cover_candidate_center_sheets_pairwise_disjoint
      U hU
  have hsheet_inj :
      ∀ b : B, ∀ U : TopologicalSpace.OpenNhdsOf b, U.IsSuitableForUniversalCover →
        ∀ q : p ⁻¹' ({b} : Set B),
          (universal_cover_candidate_center_sheet q U).InjOn p := by
    intro b U hU q
    simpa [p, E] using universal_cover_candidate_center_sheet_injOn
      U hU q
  have hopenMap : IsOpenMap p := by
    simpa [p, E, universal_cover_candidate_projectionMap] using
      universalCoverCandidate_endpoint_isOpenMap (B := B) b0
  let _ : Nonempty (B → E) := ⟨fun x ↦ Classical.choose (hsurj x)⟩
  have hp : IsPathConnectedCoveringMap p := by
    refine ⟨hsurj, fun b ↦ ?_⟩
    rcases exists_suitable_universal_cover_neighborhood b with ⟨U, hU⟩
    let _ : Nonempty (p ⁻¹' ({b} : Set B)) := by
      rcases hsurj b with ⟨e, he⟩
      exact ⟨⟨e, by simpa using he⟩⟩
    have hopen_iff :
        ∀ q : p ⁻¹' ({b} : Set B), ∀ {W : Set B}, W ⊆ (U : Set B) →
          (IsOpen W ↔ IsOpen (p ⁻¹' W ∩ universal_cover_candidate_center_sheet q U)) := by
      intro q W hWU
      constructor
      · intro hW
        -- Open subsets downstairs pull back to open traces on each centered sheet.
        exact (hW.preimage p.continuous).inter
          (universal_cover_candidate_center_sheet_isOpen U hU q)
      · intro hPre
        have himage :
            p '' (p ⁻¹' W ∩ universal_cover_candidate_center_sheet q U) = W := by
          ext y
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact hx.1
          · intro hy
            have hyU : y ∈ (U : Set B) := hWU hy
            have hsurjOn := universal_cover_candidate_center_sheet_surjOn U hU q
            rcases hsurjOn hyU with
              ⟨x, hxSheet, hpx⟩
            have hxW : x ∈ p ⁻¹' W := by
              change p x ∈ W
              exact hpx ▸ hy
            exact ⟨x, ⟨hxW, hxSheet⟩, hpx⟩
        -- Route correction: global openness of `p` converts the local image equality into the
        -- reverse `open_iff` direction needed for the sheet trivialization.
        simpa [himage] using hopenMap _ hPre
    let t : Bundle.Trivialization (p ⁻¹' ({b} : Set B)) p :=
      U.isOpen.trivializationDiscrete
        (fun q ↦ universal_cover_candidate_center_sheet q U) (U : Set B) hopen_iff
        (hsheet_inj b U hU)
        (fun q ↦ universal_cover_candidate_center_sheet_surjOn U hU q)
        (hcenter_disjoint b U hU)
        (by
          intro r hr
          rcases hcenter_cover b U hU hr with ⟨q, hq⟩
          exact Set.mem_iUnion.mpr ⟨q, hq⟩)
    refine ⟨hfiber_discrete b, (U : Set B), U.mem, U.isOpen, hU.1, ?_, ?_, ?_⟩
    · -- The preimage of the suitable neighborhood is open by continuity of the endpoint map.
      simpa using U.isOpen.preimage p.continuous
    · -- The centered sheets package into the required product chart via `trivializationDiscrete`.
      exact t.preimageHomeomorph (by simp [t])
    · intro e
      -- The product chart records the basepoint coordinate as the projection of `e`.
      have hApply := t.preimageHomeomorph_apply (by simp [t]) e
      exact congrArg (fun z ↦ z.1.1) hApply
  let e₀ : E := ⟨b0, refl b0⟩
  let _ : PathConnectedSpace B := PathConnectedSpace.of_locPathConnectedSpace
  have hjoined_from_base : ∀ e : E, Joined e₀ e := by
    intro e
    rcases e with ⟨x, q⟩
    obtain ⟨γ, rfl⟩ := mk_surjective q
    let Γ : Path e₀ (⟨x, mk γ⟩ : E) :=
      Path.mk (hp.isCoveringMap.liftPath γ e₀ γ.source)
        (hp.isCoveringMap.liftPath_zero γ e₀ γ.source)
        (universal_cover_candidate_liftPath_endpoint_eq_pathClass hp γ)
    -- The explicit lifted path joins the distinguished basepoint to the chosen endpoint class.
    exact ⟨Γ⟩
  have hEpath : PathConnectedSpace E := by
    refine ⟨⟨e₀⟩, ?_⟩
    intro x y
    -- Join any two points by returning to `e₀` and then following the canonical lift outward.
    exact (hjoined_from_base x).symm.trans (hjoined_from_base y)
  have hbot :
      (FundamentalGroup.map p e₀).range = ⊥ := by
    -- A loop at `e₀` projects to the trivial class because its covering lift closes up at `e₀`.
    simpa [p, e₀] using
      universal_cover_candidate_fundamentalGroup_range_eq_bot hp
  exact ⟨E, inferInstance, hEpath, p, hp, e₀, hbot⟩

/-- Companion to Theorem 3.8.2: the universal-cover existence statement can be realized by a
continuous map whose total space carries the required topology. -/
theorem exists_universalCoveringContinuousMap [ConnectedSpace B] [LocPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] :
    ∃ (E : Type u) (_ : TopologicalSpace E) (p : C(E, B)), IsUniversalCoveringMap p := by
  classical
  have hexists :
      ∃ (E : Type u) (_ : TopologicalSpace E) (_ : PathConnectedSpace E) (p : C(E, B)),
        IsPathConnectedCoveringMap p ∧ ∃ e : E, (FundamentalGroup.map p e).range = ⊥ :=
    exists_pathConnectedCovering_with_trivial_fundamentalGroup_range
  obtain ⟨E, hE, hEpath, p, hp, e, hbot⟩ := hexists
  let _ : TopologicalSpace E := hE
  let _ : PathConnectedSpace E := hEpath
  exact ⟨E, hE, p, isUniversalCoveringMap_of_fundamentalGroup_range_eq_bot hp e hbot⟩

/-- Theorem 3.8.2: a connected, locally path connected, semilocally simply connected space admits
a universal covering map. -/
-- Proof sketch: fix a basepoint of `B` using connectedness. Construct a covering object
-- `X : Over (TopCat.of B)` from endpoint-fixed homotopy classes of paths starting at that
-- basepoint, topologized by the standard basic neighborhoods coming from semilocally simply
-- connected open sets. The projection `X.hom` is then a path-connected covering map, and the
-- path-class model makes the total space `X.left` simply connected, hence `X.hom` is universal.
theorem exists_universalCoveringMap [ConnectedSpace B] [LocPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] :
    ∃ X : Over (TopCat.of B), IsUniversalCoveringMap X.hom := by
  classical
  have hexists :
      ∃ (E : Type u) (_ : TopologicalSpace E) (p : C(E, B)), IsUniversalCoveringMap p :=
    exists_universalCoveringContinuousMap
  obtain ⟨E, hE, p, hp⟩ := hexists
  let _ : TopologicalSpace E := hE
  let X : Over (TopCat.of B) := Over.mk (TopCat.ofHom p)
  refine ⟨X, ?_⟩
  simpa [X] using hp
