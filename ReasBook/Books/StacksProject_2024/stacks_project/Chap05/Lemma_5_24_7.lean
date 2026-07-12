import Mathlib
import StacksProject_2024.Chap05.Lemma_5_24_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits
open TopologicalSpace.Opens

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

/-- In a spectral space, a subset is closed in the constructible topology exactly when it admits
the source-style presentation as an intersection of constructible subsets. -/
theorem isClosed_constructibleTopology_iff_eq_sInter_constructible (W : Set X) :
    IsClosed[constructibleTopology X] W ↔
      ∃ S : Set (Set X), (∀ Z ∈ S, IsConstructible Z) ∧ W = ⋂₀ S := sorry

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
  sorry

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
    ∃ V : CompactOpens X, V ∈ S ∧ (V : Set X) ⊆ U := sorry

end
