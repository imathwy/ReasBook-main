import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.Spectral.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_23_1 (from Chap05) -/
/- Domain-style sampling for spectral topological spaces:
- owner declarations: `SpectralSpace`, `PrespectralSpace`, `QuasiSeparatedSpace`, `IsSpectralMap`
- canonical owner abstraction: `SpectralSpace`
- supporting owner fields: `T0Space`, `CompactSpace`, `QuasiSober`, `QuasiSeparatedSpace`,
  `PrespectralSpace`

Layer triage:
- `source-facing`: Definition 5.23.1 recalls the textbook notion of a spectral space
- `core/canonical`: `SpectralSpace`
- `bridge/view`: direct reuse of the inherited canonical field-level API from `SpectralSpace`

Primitive data belongs to the canonical owner class `SpectralSpace`; the inherited field-level
typeclass API is already available directly, so this item should remain a pure canonical recall.
-/

/- Definition 5.23.1: the Stacks notion of a spectral topological space is the canonical
mathlib typeclass `SpectralSpace`. -/
recall SpectralSpace

/- Companion recall: spectral maps are already owned by the canonical predicate `IsSpectralMap`,
so this item reuses that owner directly rather than introducing a local wrapper. -/
recall IsSpectralMap

/-! ### Lemma_5_23_2 (from Chap05) -/
open Set TopologicalSpace Topology

universe u

/- Domain-style sampling for the constructible topology of spectral spaces:
- owner declarations in mathlib: `constructibleTopology`, `WithConstructibleTopology`,
  `compactSpace_withConstructibleTopology`
- spectral compact-open basis owner: `PrespectralSpace.isTopologicalBasis`
- separation owner API: `TotallySeparatedSpace`, together with the derived instances
  `TotallySeparatedSpace.t2Space` and `TotallySeparatedSpace.totallyDisconnectedSpace`

Layer triage:
- `source-facing`: Lemma 5.23.2 states that the constructible topology on a spectral space is
  compact Hausdorff and totally disconnected
- `core/canonical`: the owner object is `WithConstructibleTopology X`
- `bridge/view`: the explicit `@T2Space X (constructibleTopology X)`,
  `@TotallyDisconnectedSpace X (constructibleTopology X)`, and
  `@CompactSpace X (constructibleTopology X)` statements are the source-facing view of those owner
  instances

Primitive data is just the spectral-space compact-open basis plus mathlib's constructible-topology
owner. Compactness is already owned upstream by mathlib, so this file only adds the missing
clopen/separation layer and then exposes the Stacks-style conjunction as derived API.
-/

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

/-- In a spectral space, every constructible subset is clopen for the constructible topology. -/
theorem isClopen_constructibleTopology_of_isConstructible {s : Set X} (hs : IsConstructible s) :
    @IsClopen X (constructibleTopology X) s := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUretro =>
    refine ⟨?_, hUretro.isCompact.isOpen_constructibleTopology_of_isOpen hUopen⟩
    let s : Set X := Uᶜ
    have hsClosed : IsClosed s := by
      simpa [s] using hUopen.isClosed_compl
    have hsCompact : IsCompact sᶜ := by
      simpa [s] using hUretro.isCompact
    have hUcompl_open : IsOpen[constructibleTopology X] Uᶜ := by
      simpa [s] using hsCompact.isOpen_constructibleTopology_of_isClosed hsClosed
    simpa using @IsOpen.isClosed_compl X (constructibleTopology X) Uᶜ hUcompl_open
  | union s _ t _ hs ht =>
    exact @IsClopen.union X (constructibleTopology X) s t hs ht
  | compl s _ hs =>
    exact @IsClopen.compl X (constructibleTopology X) s hs

/-- If `X` is spectral, then the constructible topology on `X` is totally separated. -/
instance :
    TotallySeparatedSpace (WithConstructibleTopology X) := by
  classical
  have hBasis : IsTopologicalBasis { U : Set X | IsOpen U ∧ IsCompact U } :=
    PrespectralSpace.isTopologicalBasis
  refine totallySeparatedSpace_iff_exists_isClopen.2 ?_
  intro x y hxy
  have hxyBasis : ∃ V, V ∈ { U : Set X | IsOpen U ∧ IsCompact U } ∧ ¬ (x ∈ V ↔ y ∈ V) := by
    by_contra hxyBasis
    apply hxy
    apply (TopologicalSpace.IsTopologicalBasis.eq_iff hBasis).2
    intro s hs
    by_contra hxys
    exact hxyBasis ⟨s, hs, hxys⟩
  obtain ⟨V, hV, hxyV⟩ := hxyBasis
  have hVclopen : @IsClopen X (constructibleTopology X) V :=
    isClopen_constructibleTopology_of_isConstructible (hV.2.isConstructible hV.1)
  by_cases hxV : x ∈ V
  · have hyV : y ∉ V := by
      intro hyV
      exact hxyV (by simp [hxV, hyV])
    exact ⟨V, hVclopen, hxV, hyV⟩
  · have hyV : y ∈ V := by
      by_contra hyV
      exact hxyV (by simp [hxV, hyV])
    have hVcompl : @IsClopen X (constructibleTopology X) Vᶜ :=
      @IsClopen.compl X (constructibleTopology X) V hVclopen
    exact ⟨Vᶜ, hVcompl, by simpa using hxV, by simpa using hyV⟩

/-- Lemma 5.23.2 (1): if `X` is spectral, then the constructible topology on `X` is Hausdorff. -/
-- Proof sketch: derive `T2Space` from the already available totally separated instance on
-- `WithConstructibleTopology X`.
theorem constructibleTopology_t2Space_of_spectralSpace :
    @T2Space X (constructibleTopology X) := by
  -- The clopen-separation argument above already gives total separation on the owner type.
  have hT2 : T2Space (WithConstructibleTopology X) := inferInstance
  -- Transport the owner instance back to the explicit constructible topology on `X`.
  simpa [WithConstructibleTopology] using hT2

/-- Lemma 5.23.2 (2): if `X` is spectral, then the constructible topology on `X` is totally
disconnected. -/
-- Proof sketch: use the derived `TotallyDisconnectedSpace` instance coming from the totally
-- separated constructible topology.
theorem constructibleTopology_totallyDisconnectedSpace_of_spectralSpace :
    @TotallyDisconnectedSpace X (constructibleTopology X) := by
  -- Total separation of the owner type immediately yields total disconnectedness.
  have hTotDisc : TotallyDisconnectedSpace (WithConstructibleTopology X) := inferInstance
  -- Rewrite the owner type back to the explicit constructible topology on `X`.
  simpa [WithConstructibleTopology] using hTotDisc

/-- Lemma 5.23.2 (3): if `X` is spectral, then the constructible topology on `X` is
quasi-compact. -/
-- Proof sketch: transport the upstream compactness instance for `WithConstructibleTopology X`
-- back to the constructible topology on `X`.
theorem constructibleTopology_compactSpace_of_spectralSpace :
    @CompactSpace X (constructibleTopology X) := by
  -- Mathlib already owns compactness for the constructible-topology wrapper.
  have hCompact : CompactSpace (WithConstructibleTopology X) := inferInstance
  -- Transport that compactness instance to the explicit constructible topology.
  simpa [WithConstructibleTopology] using hCompact

end

/-! ### Lemma_5_23_3 (from Chap05) -/
universe u v

open Set TopologicalSpace Topology

/- Domain-style sampling for spectral maps and constructible topologies:
- primary domain: spectral maps of spectral spaces, viewed through constructible subsets and the
  constructible topology;
- sampled canonical declarations:
  `IsSpectralMap`,
  `Topology.IsConstructible.preimage`,
  `constructibleTopology`,
  `constructibleTopology_t2_totallyDisconnected_and_compact_of_spectralSpace`;
- best owner abstractions: `IsSpectralMap` for the map data and
  `Topology.IsConstructible.preimage` for the pullback-stability statement; compactness and
  Hausdorffness of the constructible topology are derived from the owner `WithConstructibleTopology`
  package already established in `Lemma_5_23_2`.

Layer triage:
- `source-facing`: Lemma 5.23.3, giving the constructible-topology continuity, quasi-compact
  fibers, and constructible-closed image of a spectral map;
- `core/canonical`: `IsSpectralMap`, `Topology.IsConstructible.preimage`, and
  `WithConstructibleTopology`;
- `bridge/view`: the constructible-preimage specialization and the continuity statement for
  `constructibleTopology`.

Primitive data is only the spectral-map owner together with the earlier compact Hausdorff package
for the constructible topology on a spectral space. Constructible preimages, compact fibers, and
constructible-closed range are derived API and should be obtained from those owners rather than by
parallel local wrappers.
-/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

-- Proof sketch: a spectral map pulls back each subbasic open of the constructible topology to a
-- subbasic open of the constructible topology. For compact opens this is the defining spectral-map
-- compactness condition, and for closed compact-complement subsets it follows by taking
-- complements.
/-- Lemma 5.23.3 (1): a spectral map of spectral spaces is continuous for the constructible
topologies. -/
theorem IsSpectralMap.continuous_constructibleTopology (hf : IsSpectralMap f) :
    Continuous[constructibleTopology X, constructibleTopology Y] f := by
  rw [constructibleTopology, continuous_generateFrom_iff]
  intro s hs
  rcases hs with (⟨hsOpen, hsCompact⟩ | ⟨hsClosed, hsCompactCompl⟩)
  · exact (hf.isCompact_preimage_of_isOpen hsOpen hsCompact).isOpen_constructibleTopology_of_isOpen
      (hsOpen.preimage hf.continuous)
  · exact
      (show IsCompact ((f ⁻¹' s)ᶜ) from by
        simpa [Set.preimage_compl] using
          hf.isCompact_preimage_of_isOpen hsClosed.isOpen_compl hsCompactCompl).isOpen_constructibleTopology_of_isClosed
        (hsClosed.preimage hf.continuous)

end

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [SpectralSpace X] [SpectralSpace Y] {f : X → Y}

-- Proof sketch: the general owner theorem
-- `Topology.IsConstructible.preimage` therefore gives constructible preimages, which are open in
-- the constructible topology by Lemma 5.23.2.
/-- Companion bridge for Lemma 5.23.3 (1): equivalently, a spectral map pulls back constructible
subsets to constructible subsets. -/
theorem IsSpectralMap.isConstructible_preimage (hf : IsSpectralMap f) {s : Set Y}
    (hs : IsConstructible s) : IsConstructible (f ⁻¹' s) :=
  hs.preimage hf.continuous fun _ hUopen hUretro ↦
    (hf.isCompact_preimage_of_isOpen hUopen hUretro.isCompact).isRetrocompact
      (hUopen.preimage hf.continuous)

-- Proof sketch: in the constructible topology on `Y`, the singleton `{y}` is closed because that
-- topology is Hausdorff by Lemma 5.23.2. Its preimage is then closed in the compact
-- constructible topology on `X`, hence compact there, and the identity map from the constructible
-- topology to the original topology is continuous.
/-- Lemma 5.23.3 (2): every fiber of a spectral map of spectral spaces is quasi-compact. -/
theorem IsSpectralMap.isCompact_fiber (hf : IsSpectralMap f) (y : Y) :
    IsCompact (f ⁻¹' ({y} : Set Y)) := by
  -- Pass from the original topology to the constructible one by expanding opens along the
  -- compact-open basis of the spectral topology.
  have hOriginalOpen : ∀ ⦃U : Set X⦄, IsOpen U → IsOpen[constructibleTopology X] U := by
    intro U hU
    refine PrespectralSpace.isTopologicalBasis.isOpen_induction ?_ ?_ hU
    · intro V hV
      exact hV.2.isOpen_constructibleTopology_of_isOpen hV.1
    · intro S hS
      let _ : TopologicalSpace X := constructibleTopology X
      exact isOpen_sUnion fun V hV ↦ hS V hV
  -- This is the textbook map `X' → X`, used to transport compactness of the patch fiber back to
  -- the original topology.
  have hContToOriginal : @Continuous X X (constructibleTopology X) ‹TopologicalSpace X› id :=
    continuous_id_of_le hOriginalOpen
  have hPatchContinuous : Continuous[constructibleTopology X, constructibleTopology Y] f :=
    hf.continuous_constructibleTopology
  have hPatchT2Y : @T2Space Y (constructibleTopology Y) :=
    constructibleTopology_t2Space_of_spectralSpace
  have hPatchCompactX : @CompactSpace X (constructibleTopology X) :=
    constructibleTopology_compactSpace_of_spectralSpace
  -- In the constructible topology on `Y`, singleton fibers are closed because the patch topology
  -- is Hausdorff, so their preimages in the compact patch space `X'` are compact.
  have hFiberCompactPatch : @IsCompact X (constructibleTopology X) (f ⁻¹' ({y} : Set Y)) := by
    letI : TopologicalSpace X := constructibleTopology X
    letI : TopologicalSpace Y := constructibleTopology Y
    letI : T2Space Y := hPatchT2Y
    letI : CompactSpace X := hPatchCompactX
    have hFiberClosedPatch : IsClosed (f ⁻¹' ({y} : Set Y)) := by
      exact isClosed_singleton.preimage hPatchContinuous
    exact hFiberClosedPatch.isCompact
  -- The identity map on the underlying set sends the compact patch fiber onto the original fiber.
  simpa using
    @IsCompact.image X X (constructibleTopology X) ‹TopologicalSpace X›
      (f ⁻¹' ({y} : Set Y)) id hFiberCompactPatch hContToOriginal

-- Proof sketch: by part `(1)`, the map is continuous for the constructible topologies. Since a
-- spectral space is compact in the constructible topology and that topology on `Y` is Hausdorff by
-- Lemma 5.23.2, the image is compact and therefore closed.
/-- Lemma 5.23.3 (3): the image of a spectral map of spectral spaces is closed for the
constructible topology. -/
theorem IsSpectralMap.isClosed_range_constructibleTopology (hf : IsSpectralMap f) :
    IsClosed[constructibleTopology Y] (range f) := by
  have hPatchContinuous : Continuous[constructibleTopology X, constructibleTopology Y] f :=
    hf.continuous_constructibleTopology
  have hPatchCompactX : @CompactSpace X (constructibleTopology X) :=
    constructibleTopology_compactSpace_of_spectralSpace
  have hPatchT2Y : @T2Space Y (constructibleTopology Y) :=
    constructibleTopology_t2Space_of_spectralSpace
  -- The constructible topology makes the source compact, so the constructible-topology image is
  -- compact by continuity from part `(1)`.
  have hRangeCompact : @IsCompact Y (constructibleTopology Y) (range f) := by
    letI : TopologicalSpace X := constructibleTopology X
    letI : TopologicalSpace Y := constructibleTopology Y
    letI : CompactSpace X := hPatchCompactX
    simpa using isCompact_range hPatchContinuous
  -- The constructible topology on a spectral space is Hausdorff, so compact subsets are closed.
  letI : TopologicalSpace Y := constructibleTopology Y
  letI : T2Space Y := hPatchT2Y
  exact hRangeCompact.isClosed

end

/-! ### Lemma_5_23_4 (from Chap05) -/
universe u v

open TopologicalSpace Topology

/- Domain-style sampling for spectral maps and constructible topologies:
- primary domain: spectral maps between spectral spaces, compared with continuity for the
  constructible topologies;
- sampled owner declarations:
  `IsSpectralMap`,
  `IsSpectralMap.continuous_constructibleTopology`,
  `WithConstructibleTopology`,
  `compactSpace_withConstructibleTopology`,
  `PrespectralSpace.isTopologicalBasis`;
- best owner abstraction: `IsSpectralMap` is the core owner for the map property, while
  constructible-topology continuity is derived bridge API from that owner.

Layer triage:
- `source-facing`: this lemma is the textbook equivalence between spectrality of a continuous map
  and continuity for the constructible topologies;
- `core/canonical`: `IsSpectralMap` and the constructible-topology owner `WithConstructibleTopology`;
- `bridge/view`: `IsSpectralMap.continuous_constructibleTopology` gives the forward direction, and
  compactness of `WithConstructibleTopology` on a spectral space recovers the compact-open
  preimage condition for the converse.

Primitive data is only the owner predicate `IsSpectralMap f` together with the ambient spectral
space structures. Constructible continuity, clopen patch subsets, and compactness transport back to
the original topology are derived API and should not be duplicated by a parallel local owner.
-/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [SpectralSpace X] [SpectralSpace Y] {f : X → Y}

-- Proof sketch: for a spectral map, quasi-compact opens pull back to quasi-compact opens, hence
-- constructible subsets pull back to constructible subsets and `f` is continuous for the generated
-- constructible topologies. Conversely, if `f` is constructibly continuous, then the preimage of a
-- quasi-compact open is clopen in the constructible topology on `X`, hence compact there; the
-- identity map to the original topology is continuous and surjective, so that preimage is compact
-- in the original topology, giving `IsSpectralMap f`.
/-- Lemma 5.23.4: for spectral spaces, a continuous map is spectral if and only if it is
continuous for the constructible topologies on source and target. -/
theorem isSpectralMap_iff_continuous_constructibleTopology (hfcont : Continuous f) :
    IsSpectralMap f ↔
      Continuous[constructibleTopology X, constructibleTopology Y] f := by
  constructor
  · exact IsSpectralMap.continuous_constructibleTopology
  · intro hpatch
    refine ⟨hfcont, fun s hsOpen hsCompact ↦ ?_⟩
    have hPatchCompact : CompactSpace (WithConstructibleTopology X) := inferInstance
    have hsClosedPatch : IsClosed[constructibleTopology Y] s :=
      (isClopen_constructibleTopology_of_isConstructible (hsCompact.isConstructible hsOpen)).1
    have hpreClosed := by
      letI : TopologicalSpace X := constructibleTopology X
      letI : TopologicalSpace Y := constructibleTopology Y
      exact hsClosedPatch.preimage hpatch
    have hpreCompactPatch := by
      letI : TopologicalSpace X := constructibleTopology X
      letI : CompactSpace X := by
        simpa [WithConstructibleTopology] using hPatchCompact
      exact hpreClosed.isCompact
    have hOriginalOpen : ∀ ⦃U : Set X⦄, IsOpen U → IsOpen[constructibleTopology X] U := by
      intro U hU
      refine PrespectralSpace.isTopologicalBasis.isOpen_induction ?_ ?_ hU
      · intro V hV
        exact hV.2.isOpen_constructibleTopology_of_isOpen hV.1
      · intro S hS
        let _ : TopologicalSpace X := constructibleTopology X
        exact isOpen_sUnion fun V hV ↦ hS V hV
    have hContToOriginal := continuous_id_of_le hOriginalOpen
    simpa using
      @IsCompact.image X X (constructibleTopology X) ‹TopologicalSpace X› (f ⁻¹' s) id
        hpreCompactPatch hContToOriginal

end

/-! ### Lemma_5_23_5 (from Chap05) -/
universe u

open Set TopologicalSpace Topology
open scoped Set.Notation

/- Domain-style sampling for patch-closed subspaces of spectral spaces:
- primary domain: spectral spaces, constructible topology, and spectral subspaces;
- sampled owner declarations:
  `SpectralSpace`,
  `PrespectralSpace.of_isTopologicalBasis'`,
  `isOpen_constructibleTopology_of_isConstructible`,
  `IsGenericPoint.dense_preimage_iff_mem_of_isFiniteUnionOfLocallyClosed`;
- best owner abstractions:
  `SpectralSpace` for the ambient/subspace notion,
  `constructibleTopology` for patch-closedness,
  and the generic-point owner `IsGenericPoint` for the irreducible-closure contradiction.

Layer triage:
- `source-facing`: Lemma 5.23.5, asserting that a constructible-topology-closed subspace of a
  spectral space is spectral in the induced topology;
- `core/canonical`: `SpectralSpace`, `constructibleTopology`, and the compact-open basis owner
  `PrespectralSpace.isTopologicalBasis`;
- `bridge/view`: the closed-subspace spectral helper and the constructible-topology continuity of
  subtype maps.

Primitive data is only the ambient spectral-space structure and the patch-closed subset. The
compact-open basis, quasi-separatedness, and the needed generic-point contradiction are derived
from the existing owners and should not be repackaged locally.
-/

noncomputable section

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X] {E : Set X}

private theorem isTopologicalBasis_subtype_compactOpens (S : Set X) :
    IsTopologicalBasis
      (Set.range fun U : CompactOpens X ↦ (Subtype.val : S → X) ⁻¹' (U : Set X)) := by
  convert
    (PrespectralSpace.isTopologicalBasis.isInducing IsEmbedding.subtypeVal.isInducing :
      IsTopologicalBasis
        (((Subtype.val : S → X) ⁻¹' ·) '' { U : Set X | IsOpen U ∧ IsCompact U }))
  ext V
  constructor
  · rintro ⟨U, rfl⟩
    exact ⟨(U : Set X), ⟨U.isOpen, U.isCompact⟩, rfl⟩
  · rintro ⟨U, hU, rfl⟩
    exact ⟨⟨⟨U, hU.2⟩, hU.1⟩, rfl⟩

private theorem spectralSpace_subtype_of_isClosed {S : Set X} (hS : IsClosed S) :
    SpectralSpace S := by
  let b : CompactOpens X → Set S := fun U ↦ (Subtype.val : S → X) ⁻¹' (U : Set X)
  have hBasis : IsTopologicalBasis (Set.range b) :=
    isTopologicalBasis_subtype_compactOpens S
  have hCompactBasis : ∀ U : CompactOpens X, IsCompact (b U) := by
    intro U
    rw [Subtype.isCompact_iff]
    simpa [b, Set.image_preimage_eq_inter_range, Set.inter_comm] using U.isCompact.inter_right hS
  have hCompactInter :
      ∀ U V : CompactOpens X, IsCompact (b U ∩ b V) := by
    intro U V
    have hUV_compact :
        IsCompact ((U : Set X) ∩ (V : Set X)) :=
      QuasiSeparatedSpace.inter_isCompact (U : Set X) (V : Set X) U.isOpen U.isCompact V.isOpen
        V.isCompact
    rw [Subtype.isCompact_iff]
    simpa [b, Set.image_inter, Set.image_preimage_eq_inter_range, Set.inter_assoc,
      Set.inter_left_comm, Set.inter_comm] using
      ((hUV_compact.inter_right hS).inter_right hS :
        IsCompact ((((U : Set X) ∩ (V : Set X)) ∩ S) ∩ S))
  have hCompactSubspace : IsCompact S := hS.isCompact
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hCompactSubspace
  refine
    { toT0Space := IsEmbedding.subtypeVal.t0Space
      toCompactSpace := inferInstance
      toQuasiSober := hS.isClosedEmbedding_subtypeVal.quasiSober
      toQuasiSeparatedSpace := QuasiSeparatedSpace.of_isTopologicalBasis hBasis hCompactInter
      toPrespectralSpace := PrespectralSpace.of_isTopologicalBasis' hBasis hCompactBasis }

/-- Helper for Lemma 5.23.5: a subset closed in the constructible topology contains a
specialization point over each point in its ordinary closure. -/
private theorem exists_specializingPoint_of_mem_closure_patch_closed
    {E : Set X} (hE : IsClosed[constructibleTopology X] E) {x : X} (hx : x ∈ closure E) :
    ∃ y ∈ E, y ⤳ x := by
  let 𝒰 : Type u := { U : CompactOpens X // x ∈ (U : Set X) }
  let F : 𝒰 → Set X := fun U ↦ E ∩ (U.1 : Set X)
  have hPatchCompact : CompactSpace (WithConstructibleTopology X) := inferInstance
  have hF_closed_patch : ∀ U : 𝒰, IsClosed[constructibleTopology X] (F U) := by
    intro U
    have hU_constructible : IsConstructible (U.1 : Set X) :=
      U.1.isCompact.isConstructible U.1.isOpen
    have hU_closed_patch : IsClosed[constructibleTopology X] (U.1 : Set X) :=
      (isClopen_constructibleTopology_of_isConstructible hU_constructible).1
    letI : TopologicalSpace X := constructibleTopology X
    exact hE.inter hU_closed_patch
  have hF_nonempty : ∀ U : 𝒰, (F U).Nonempty := by
    intro U
    rcases mem_closure_iff.1 hx (U.1 : Set X) U.1.isOpen U.2 with ⟨z, hzU, hzE⟩
    exact ⟨z, hzE, hzU⟩
  have hF_directed : Directed (· ⊇ ·) F := by
    intro U V
    refine ⟨⟨U.1 ⊓ V.1, by simpa [CompactOpens.coe_inf] using ⟨U.2, V.2⟩⟩, ?_, ?_⟩
    · intro y hy
      exact ⟨hy.1, hy.2.1⟩
    · intro y hy
      exact ⟨hy.1, hy.2.2⟩
  haveI : Nonempty 𝒰 := ⟨⟨⊤, by simp⟩⟩
  have hF_compact_patch : ∀ U : 𝒰, @IsCompact X (constructibleTopology X) (F U) := by
    intro U
    letI : TopologicalSpace X := constructibleTopology X
    letI : CompactSpace X := by
      simpa [WithConstructibleTopology] using hPatchCompact
    exact (hF_closed_patch U).isCompact
  obtain ⟨y, hy⟩ :=
    Set.nonempty_iInter.mp <|
      @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        X (constructibleTopology X) 𝒰 inferInstance F hF_directed hF_nonempty
        hF_compact_patch hF_closed_patch
  have hyx : y ⤳ x := by
    rw [specializes_iff_mem_closure]
    refine mem_closure_iff.2 fun U hU hxU ↦ ?_
    obtain ⟨V, ⟨hV_open, hV_compact⟩, hxV, hVU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxU hU
    let W : 𝒰 := ⟨⟨⟨V, hV_compact⟩, hV_open⟩, hxV⟩
    exact ⟨y, hVU (hy W).2, by simp⟩
  let Utop : 𝒰 := ⟨⊤, by simp⟩
  exact ⟨y, (hy Utop).1, hyx⟩

-- Proof sketch: argue as in Stacks Project, Tag 0902. Quasi-compactness comes from patch
-- compactness, sobriety from the generic point of the closure of a closed irreducible subset,
-- and the quasi-compact open basis is given by intersections `E ∩ U` with `U` quasi-compact open
-- in `X`.
/-- Lemma 5.23.5: if `X` is spectral and `E ⊆ X` is closed in the constructible topology, then
`E` with the induced topology is a spectral space. In particular this applies when `E` is
constructible or closed in `X`. -/
theorem spectralSpace_subtype_of_isClosed_constructibleTopology
    (hE : IsClosed[constructibleTopology X] E) : SpectralSpace E := by
  let b : CompactOpens X → Set E := fun U ↦ (Subtype.val : E → X) ⁻¹' (U : Set X)
  have hBasis : IsTopologicalBasis (Set.range b) :=
    isTopologicalBasis_subtype_compactOpens E
  have hOriginalOpen :
      ∀ ⦃s : Set X⦄, IsOpen s → IsOpen[constructibleTopology X] s := by
    intro s hs
    obtain ⟨S, hSB, rfl⟩ := PrespectralSpace.isTopologicalBasis.open_eq_sUnion hs
    exact @isOpen_sUnion X (constructibleTopology X) S fun t ht ↦
      (hSB ht).2.isOpen_constructibleTopology_of_isOpen (hSB ht).1
  have hContToOriginal : @Continuous X X (constructibleTopology X) ‹TopologicalSpace X› id := by
    rw [continuous_def]
    intro s hs
    exact hOriginalOpen hs
  have hPatchCompact : @CompactSpace X (constructibleTopology X) :=
    constructibleTopology_compactSpace_of_spectralSpace
  have hCompact_of_patch_closed {s : Set X} (hs : IsClosed[constructibleTopology X] s) :
      IsCompact s := by
    have hs_compact : @IsCompact X (constructibleTopology X) s := by
      letI : TopologicalSpace X := constructibleTopology X
      letI : CompactSpace X := hPatchCompact
      change IsCompact s
      exact IsClosed.isCompact hs
    simpa using
      @IsCompact.image X X (constructibleTopology X) ‹TopologicalSpace X› s id hs_compact
        hContToOriginal
  have hCompactSubspace : IsCompact E := by
    exact hCompact_of_patch_closed hE
  have hCompactBasis : ∀ U : CompactOpens X, IsCompact (b U) := by
    intro U
    have hU_closed_constructible : IsClosed[constructibleTopology X] (U : Set X) :=
      (isClopen_constructibleTopology_of_isConstructible
        (U.isCompact.isConstructible U.isOpen)).1
    have hEU_closed_constructible : IsClosed[constructibleTopology X] (E ∩ (U : Set X)) := by
      letI : TopologicalSpace X := constructibleTopology X
      exact hE.inter hU_closed_constructible
    rw [Subtype.isCompact_iff]
    simpa [b, Set.image_preimage_eq_inter_range, Set.inter_comm] using
      hCompact_of_patch_closed hEU_closed_constructible
  have hCompactInter :
      ∀ U V : CompactOpens X, IsCompact (b U ∩ b V) := by
    intro U V
    have hU_closed_constructible : IsClosed[constructibleTopology X] (U : Set X) :=
      (isClopen_constructibleTopology_of_isConstructible
        (U.isCompact.isConstructible U.isOpen)).1
    have hV_closed_constructible : IsClosed[constructibleTopology X] (V : Set X) :=
      (isClopen_constructibleTopology_of_isConstructible
        (V.isCompact.isConstructible V.isOpen)).1
    have hTarget_closed :
        IsClosed[constructibleTopology X] (E ∩ (E ∩ ((U : Set X) ∩ (V : Set X)))) := by
      letI : TopologicalSpace X := constructibleTopology X
      exact hE.inter <| hE.inter <| hU_closed_constructible.inter hV_closed_constructible
    rw [Subtype.isCompact_iff]
    convert
      (hCompact_of_patch_closed hTarget_closed :
        IsCompact (E ∩ (E ∩ ((U : Set X) ∩ (V : Set X))))) using 1
    ext x
    simp [b, Set.image_inter, Set.image_preimage_eq_inter_range, Set.inter_assoc,
      Set.inter_left_comm, Set.inter_comm]
  letI : CompactSpace E := isCompact_iff_compactSpace.mp hCompactSubspace
  have hQuasiSober : QuasiSober E := by
    rw [quasiSober_iff]
    intro S hS_irred hS_closed
    let T : Set X := (Subtype.val : E → X) '' S
    let C : Set X := closure T
    have hT_subset : T ⊆ E := by
      rintro _ ⟨y, hyS, rfl⟩
      exact y.2
    have hT_irred : IsIrreducible T := hS_irred.image Subtype.val continuous_subtype_val.continuousOn
    have hC_irred : IsIrreducible C := hT_irred.closure
    have hC_spectral : SpectralSpace C :=
      spectralSpace_subtype_of_isClosed isClosed_closure
    letI : SpectralSpace C := hC_spectral
    have hSC_eq :
        S = (Subtype.val : E → X) ⁻¹' C := by
      calc
        S = closure S := hS_closed.closure_eq.symm
        _ = (Subtype.val : E → X) ⁻¹' closure T := by
          simpa [T] using IsEmbedding.subtypeVal.closure_eq_preimage_closure_image S
        _ = (Subtype.val : E → X) ⁻¹' C := rfl
    let T' : Set C := (Subtype.val : C → X) ⁻¹' E
    have hT'_closed :
        IsClosed[constructibleTopology C] T' := by
      have hClosureProper : IsProperMap (Subtype.val : C → X) :=
        isClosed_closure.isClosedEmbedding_subtypeVal.isProperMap
      have hClosureSpectralMap : IsSpectralMap (Subtype.val : C → X) :=
        hClosureProper.isSpectralMap
      have hSubtypePatchCont :
          Continuous[constructibleTopology C, constructibleTopology X] (Subtype.val : C → X) :=
        hClosureSpectralMap.continuous_constructibleTopology
      letI : TopologicalSpace C := constructibleTopology C
      letI : TopologicalSpace X := constructibleTopology X
      exact (show IsClosed E from hE).preimage
        (show Continuous (Subtype.val : C → X) from hSubtypePatchCont)
    let S' : Set C := (Subtype.val : C → X) ⁻¹' T
    have hS'_subset : S' ⊆ T' := by
      intro z hz
      exact hT_subset hz
    have hImageS' : (Subtype.val : C → X) '' S' = T := by
      rw [Set.image_preimage_eq_of_subset]
      simpa [C] using (subset_closure : T ⊆ closure T)
    have hClosureS' : closure S' = univ := by
      calc
        closure S' = (Subtype.val : C → X) ⁻¹' closure ((Subtype.val : C → X) '' S') := by
          simpa using IsEmbedding.subtypeVal.closure_eq_preimage_closure_image S'
        _ = (Subtype.val : C → X) ⁻¹' closure T := by simp [hImageS']
        _ = univ := by ext z; simp
    have hClosureT' : closure T' = univ := by
      apply eq_univ_iff_forall.2
      intro z
      have hz : z ∈ closure S' := by simp [hClosureS']
      exact closure_mono hS'_subset hz
    letI : IrreducibleSpace C := Subtype.irreducibleSpace hC_irred
    let x : C := genericPoint C
    have hx_mem_closure : x ∈ closure T' := by
      simp [hClosureT']
    obtain ⟨y, hyT', hyx⟩ :=
      exists_specializingPoint_of_mem_closure_patch_closed hT'_closed hx_mem_closure
    have hy_generic_C : IsGenericPoint y (univ : Set C) := by
      rw [isGenericPoint_iff_specializes]
      intro z
      constructor
      · intro hyz
        simp
      · intro hz
        exact hyx.trans (genericPoint_specializes z)
    have hy_closure : closure ({y.1} : Set X) = C := by
      have hPreimageClosure :
          (Subtype.val : C → X) ⁻¹' closure ({y.1} : Set X) = univ := by
        calc
          (Subtype.val : C → X) ⁻¹' closure ({y.1} : Set X)
              = closure ({y} : Set C) := by
                symm
                simpa using
                  IsEmbedding.subtypeVal.closure_eq_preimage_closure_image ({y} : Set C)
          _ = univ := hy_generic_C.def
      have hC_subset : C ⊆ closure ({y.1} : Set X) := by
        intro z hz
        have : (⟨z, hz⟩ : C) ∈ (Subtype.val : C → X) ⁻¹' closure ({y.1} : Set X) := by
          simp [hPreimageClosure]
        exact this
      have hclosure_subset : closure ({y.1} : Set X) ⊆ C :=
        isClosed_closure.closure_subset_iff.2 (by simp)
      exact subset_antisymm hclosure_subset hC_subset
    refine ⟨⟨y.1, hyT'⟩, ?_⟩
    calc
      closure ({⟨y.1, hyT'⟩} : Set E)
          = (Subtype.val : E → X) ⁻¹' closure ({y.1} : Set X) := by
            simpa using
              IsEmbedding.subtypeVal.closure_eq_preimage_closure_image ({⟨y.1, hyT'⟩} : Set E)
      _ = (Subtype.val : E → X) ⁻¹' C := by rw [hy_closure]
      _ = S := hSC_eq.symm
  refine
    { toT0Space := IsEmbedding.subtypeVal.t0Space
      toCompactSpace := inferInstance
      toQuasiSober := hQuasiSober
      toQuasiSeparatedSpace := QuasiSeparatedSpace.of_isTopologicalBasis hBasis hCompactInter
      toPrespectralSpace := PrespectralSpace.of_isTopologicalBasis' hBasis hCompactBasis }

end

/-! ### Lemma_5_23_6 (from Chap05) -/
universe u

open Set TopologicalSpace Topology

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

/- Domain-style sampling for Lemma 5.23.6:
- primary domain: spectral spaces, constructible topology, and specialization/generalization
  stability of subsets
- inspected owner declarations:
  `constructibleTopology`,
  `constructibleTopology_t2_totallyDisconnected_and_compact_of_spectralSpace`,
  `isClopen_constructibleTopology_of_isConstructible`,
  `stableUnderGeneralization_compl_iff`
- best owner abstraction: the compact Hausdorff owner `WithConstructibleTopology X` attached to a
  spectral space, together with a subset `E ⊆ X` closed in that constructible topology
- primitive data: the constructible-topology-closed subset `E`; specialization/generalization
  stability is derived extra structure used only for clauses `(2)` and `(3)`
- derived API: clause `(1)` extracts a specializing point from compactness in the constructible
  topology, while clauses `(2)` and `(3)` are closure/open consequences derived from clause `(1)`
  and the canonical complement bridge between specialization and generalization stability

Layer triage:
- `source-facing`: the three Stacks clauses relating constructible-topology closed/open subsets to
  specialization/generalization behavior in a spectral space
- `core/canonical`: the owner abstraction is `WithConstructibleTopology X`
- `bridge/view`: `stableUnderGeneralization_compl_iff`

No upstream theorem in mathlib or earlier Chapter 5 files was found with the exact source-facing
interface of clause `(1)`. The canonical reuse point is therefore the constructible-topology owner
of the ambient spectral space, not a parallel local wrapper around constructible closed data.
-/

-- Proof sketch: intersect `E` with the quasi-compact open neighbourhoods of `x`; in the compact
-- Hausdorff constructible topology these traces are closed, hence compact, and finite
-- intersections stay nonempty because `x` lies in the ordinary closure of `E`.
/-- Lemma 5.23.6 (1): if `E ⊆ X` is closed in the constructible topology of a spectral space and
`x` lies in the ordinary closure of `E`, then `x` is the specialization of some point of `E`.
This matches the Stacks Project statement for subsets closed in the constructible topology, for
example constructible subsets. -/
theorem exists_specializingPoint_of_mem_closure_of_isClosed_constructibleTopology
    {E : Set X} (hE : IsClosed[constructibleTopology X] E) {x : X} (hx : x ∈ closure E) :
    ∃ y ∈ E, y ⤳ x := by
  let 𝒰 : Type u := { U : CompactOpens X // x ∈ (U : Set X) }
  let F : 𝒰 → Set X := fun U ↦ E ∩ (U.1 : Set X)
  have hPatchCompact : CompactSpace (WithConstructibleTopology X) := inferInstance
  have hF_closed_patch : ∀ U : 𝒰, IsClosed[constructibleTopology X] (F U) := by
    intro U
    have hU_constructible : IsConstructible (U.1 : Set X) :=
      U.1.isCompact.isConstructible U.1.isOpen
    have hU_closed_patch : IsClosed[constructibleTopology X] (U.1 : Set X) :=
      (isClopen_constructibleTopology_of_isConstructible hU_constructible).1
    letI : TopologicalSpace X := constructibleTopology X
    exact hE.inter hU_closed_patch
  have hF_nonempty : ∀ U : 𝒰, (F U).Nonempty := by
    intro U
    rcases mem_closure_iff.1 hx (U.1 : Set X) U.1.isOpen U.2 with ⟨z, hzU, hzE⟩
    exact ⟨z, hzE, hzU⟩
  have hF_directed : Directed (· ⊇ ·) F := by
    intro U V
    refine ⟨⟨U.1 ⊓ V.1, by simpa [CompactOpens.coe_inf] using ⟨U.2, V.2⟩⟩, ?_, ?_⟩
    · intro y hy
      exact ⟨hy.1, hy.2.1⟩
    · intro y hy
      exact ⟨hy.1, hy.2.2⟩
  haveI : Nonempty 𝒰 := ⟨⟨⊤, by simp⟩⟩
  have hF_compact_patch : ∀ U : 𝒰, @IsCompact X (constructibleTopology X) (F U) := by
    intro U
    letI : TopologicalSpace X := constructibleTopology X
    letI : CompactSpace X := by
      simpa [WithConstructibleTopology] using hPatchCompact
    exact (hF_closed_patch U).isCompact
  obtain ⟨y, hy⟩ :=
    Set.nonempty_iInter.mp <|
      @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        X (constructibleTopology X) 𝒰 inferInstance F hF_directed hF_nonempty
        hF_compact_patch hF_closed_patch
  have hyx : y ⤳ x := by
    rw [specializes_iff_mem_closure]
    refine mem_closure_iff.2 fun U hU hxU ↦ ?_
    obtain ⟨V, ⟨hV_open, hV_compact⟩, hxV, hVU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxU hU
    let W : 𝒰 := ⟨⟨⟨V, hV_compact⟩, hV_open⟩, hxV⟩
    exact ⟨y, hVU (hy W).2, by simp⟩
  let Utop : 𝒰 := ⟨⊤, by simp⟩
  exact ⟨y, (hy Utop).1, hyx⟩

-- Proof sketch: apply part (1) to a point `x ∈ closure E`; the resulting point of `E`
-- specializing to `x` forces `x ∈ E` by specialization stability, so `closure E ⊆ E`.
/-- Lemma 5.23.6 (2): a constructible-topology-closed subset of a spectral space that is stable
under specialization is closed in the original topology. -/
theorem isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization
    {E : Set X} (hE : IsClosed[constructibleTopology X] E)
    (hE_spec : StableUnderSpecialization E) : IsClosed E := by
  exact isClosed_of_closure_subset fun x hx ↦ by
    rcases exists_specializingPoint_of_mem_closure_of_isClosed_constructibleTopology hE hx with
      ⟨y, hyE, hyx⟩
    exact hE_spec hyx hyE

-- Proof sketch: apply part (2) to the complement of `E`; patch-openness gives patch-closedness of
-- the complement, and generalization stability of `E` becomes specialization stability of `Eᶜ`.
/-- Lemma 5.23.6 (3): a subset of a spectral space that is open in the constructible topology and
stable under generalization is open in the original topology. This matches the Stacks Project
statement for subsets open in the constructible topology, for example constructible subsets. -/
theorem isOpen_of_isOpen_constructibleTopology_of_stableUnderGeneralization
    {E : Set X} (hE : IsOpen[constructibleTopology X] E)
    (hE_gen : StableUnderGeneralization E) : IsOpen E := by
  rw [← isClosed_compl_iff]
  have hE_closed : IsClosed[constructibleTopology X] Eᶜ := by
    letI : TopologicalSpace X := constructibleTopology X
    exact hE.isClosed_compl
  exact
    isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization hE_closed hE_gen.compl

end

/-! ### Lemma_5_23_7 (from Chap05) -/
universe u

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

variable [SpectralSpace X]

/- Domain-style sampling for spectral separation via specializations:
- owner declarations inspected: `SpectralSpace`, `PrespectralSpace.isTopologicalBasis`,
  `compactSpace_withConstructibleTopology`, `specializes_iff_forall_open`, `SeparatedNhds`
- best owner abstraction: the compact-open basis owner `PrespectralSpace.isTopologicalBasis`,
  together with compactness of `constructibleTopology X`
- primitive data: compact open neighborhoods in a spectral space, and separation by neighborhoods
  via `SeparatedNhds`
- derived API: specialization is recovered from membership in every open neighborhood via
  `specializes_iff_forall_open`

Layer triage:
- `source-facing`: the Stacks dichotomy between a common generalization and separated
  neighborhoods
- `core/canonical`: compact-open basis plus constructible-topology compactness
- `bridge/view`: the source conclusion is expressed through `SeparatedNhds` and `z ⤳ x`, `z ⤳ y`

The public theorem is genuinely source-facing, so it should stay a theorem rather than collapse to
an owner recall. The proof should nevertheless reuse the canonical owner data instead of rebuilding
local wrapper notions of quasi-compact neighborhoods or constructible compactness.
-/

-- Proof sketch: if `x` and `y` do not admit disjoint open neighbourhoods, then every pair of
-- quasi-compact open neighbourhoods of `x` and `y` has nonempty intersection. In the compact
-- constructible topology, finite-intersection compactness gives a point lying in every compact
-- open neighbourhood of both points, hence specializing to both `x` and `y`.
/-- Lemma 5.23.7: in a spectral space, either there exists a third point specializing to both
`x` and `y`, or the singleton subsets `{x}` and `{y}` are separated by neighborhoods, i.e. there
exist disjoint open neighbourhoods containing `x` and `y`. -/
theorem exists_point_specializing_to_both_or_disjoint_open_neighborhoods (x y : X) :
    (∃ z : X, z ⤳ x ∧ z ⤳ y) ∨ SeparatedNhds ({x} : Set X) ({y} : Set X) := by
  by_cases hsep : SeparatedNhds ({x} : Set X) ({y} : Set X)
  · exact Or.inr hsep
  · let 𝒦 : Set (Set X) := {U : Set X | IsOpen U ∧ IsCompact U ∧ (x ∈ U ∨ y ∈ U)}
    have hInter :
        ∀ {U V : Set X}, IsOpen U → IsCompact U → x ∈ U →
          IsOpen V → IsCompact V → y ∈ V → (U ∩ V).Nonempty := by
      intro U V hUopen hUcompact hxU hVopen hVcompact hyV
      by_contra hUV
      apply hsep
      refine ⟨U, V, hUopen, hVopen, ?_, ?_, ?_⟩
      · simpa using singleton_subset_iff.mpr hxU
      · simpa using singleton_subset_iff.mpr hyV
      · exact disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hUV)
    have h𝒦_closed : ∀ U ∈ 𝒦, @IsClosed X (constructibleTopology X) U := by
      intro U hU
      have hUcompact : IsCompact (Uᶜᶜ) := by
        simpa using hU.2.1
      have hUcompl_open : @IsOpen X (constructibleTopology X) Uᶜ := by
        simpa using hUcompact.isOpen_constructibleTopology_of_isClosed hU.1.isClosed_compl
      simpa using @IsOpen.isClosed_compl X (constructibleTopology X) Uᶜ hUcompl_open
    have h𝒦_fip : ∀ t ⊆ 𝒦, t.Finite → (⋂₀ t).Nonempty := by
      intro t ht htfin
      let tx : Set (Set X) := {U : Set X | U ∈ t ∧ x ∈ U}
      let ty : Set (Set X) := {U : Set X | U ∈ t ∧ y ∈ U}
      have htxfin : tx.Finite := htfin.subset fun U hU ↦ hU.1
      have htyfin : ty.Finite := htfin.subset fun U hU ↦ hU.1
      have htx_open : ∀ U ∈ tx, IsOpen U := by
        intro U hU
        exact (ht hU.1).1
      have hty_open : ∀ U ∈ ty, IsOpen U := by
        intro U hU
        exact (ht hU.1).1
      have htx_compact : ∀ U ∈ tx, IsCompact U := by
        intro U hU
        exact (ht hU.1).2.1
      have hty_compact : ∀ U ∈ ty, IsCompact U := by
        intro U hU
        exact (ht hU.1).2.1
      have hx_mem : x ∈ ⋂₀ tx := by
        rw [Set.mem_sInter]
        intro U hU
        exact hU.2
      have hy_mem : y ∈ ⋂₀ ty := by
        rw [Set.mem_sInter]
        intro U hU
        exact hU.2
      have htx_isCompact : IsCompact (⋂₀ tx) :=
        QuasiSeparatedSpace.isCompact_sInter htxfin (fun U hU ↦ Or.inl (htx_open U hU))
          htx_compact
      have hty_isCompact : IsCompact (⋂₀ ty) :=
        QuasiSeparatedSpace.isCompact_sInter htyfin (fun U hU ↦ Or.inl (hty_open U hU))
          hty_compact
      have htx_isOpen : IsOpen (⋂₀ tx) := htxfin.isOpen_sInter htx_open
      have hty_isOpen : IsOpen (⋂₀ ty) := htyfin.isOpen_sInter hty_open
      obtain ⟨z, hztx, hzty⟩ :=
        hInter htx_isOpen htx_isCompact hx_mem hty_isOpen hty_isCompact hy_mem
      refine ⟨z, ?_⟩
      rw [Set.mem_sInter]
      intro U hU
      have hUxy : x ∈ U ∨ y ∈ U := (ht hU).2.2
      cases hUxy with
      | inl hxU =>
          exact Set.mem_sInter.1 hztx U ⟨hU, hxU⟩
      | inr hyU =>
          exact Set.mem_sInter.1 hzty U ⟨hU, hyU⟩
    obtain ⟨z, hz𝒦⟩ :
        (⋂₀ 𝒦).Nonempty := by
      exact
        @CompactSpace.nonempty_sInter X (constructibleTopology X)
          compactSpace_withConstructibleTopology 𝒦 h𝒦_closed h𝒦_fip
    refine Or.inl ⟨z, ?_, ?_⟩
    · rw [specializes_iff_forall_open]
      intro U hU hxU
      obtain ⟨V, ⟨hVopen, hVcompact⟩, hxV, hVU⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxU hU
      have hV𝒦 : V ∈ 𝒦 := ⟨hVopen, hVcompact, Or.inl hxV⟩
      exact hVU (Set.mem_sInter.1 hz𝒦 V hV𝒦)
    · rw [specializes_iff_forall_open]
      intro U hU hyU
      obtain ⟨V, ⟨hVopen, hVcompact⟩, hyV, hVU⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hyU hU
      have hV𝒦 : V ∈ 𝒦 := ⟨hVopen, hVcompact, Or.inr hyV⟩
      exact hVU (Set.mem_sInter.1 hz𝒦 V hV𝒦)

/-! ### Lemma_5_23_8 (from Chap05) -/
universe u

open Set TopologicalSpace Topology

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

/- Domain-style sampling for Lemma 5.23.8:
- primary domain: spectral spaces, constructible topology, specialization order, and irreducible
  components
- owner declarations inspected:
  `TotallyDisconnectedSpace`,
  `totallyDisconnectedSpace_iff_connectedComponent_subsingleton`,
  `irreducibleComponent`,
  `PrespectralSpace.isTopologicalBasis`
- best owner abstraction: the ambient spectral-space/topological-space owners together with the
  canonical owner set `irreducibleComponent x`
- primitive data: the ambient topological owner instances and the canonical irreducible component
  through a point
- derived API: singleton/closedness consequences, trivial-specialization criteria, and the
  constructible-topology comparison

Layer triage:
- `source-facing`: the Stacks TFAE statement for spectral spaces
- `core/canonical`: mathlib’s owners `TotallyDisconnectedSpace`, `irreducibleComponent`,
  `constructibleTopology`, and `PrespectralSpace.isTopologicalBasis`
- `bridge/view`: the TFAE implications relating those owner-level notions

The theorem is source-facing, so it remains a theorem. The refinement target is therefore its
proof surface: reuse owner-level declarations directly, delete local proof noise, and avoid
parallel wrappers or redundant argument plumbing.
-/

-- Proof sketch: combine the earlier spectral-space criteria. Lemma `5.22.2` gives the profinite
-- versus compact Hausdorff totally disconnected comparison; spectral spaces are sober, so
-- triviality of specializations is equivalent to every point being closed and to every point being
-- the generic point of its irreducible component; Lemma `5.23.6` identifies constructible subsets
-- with clopen subsets under trivial specialization, and the definition of `constructibleTopology`
-- turns closedness of quasi-compact opens into equality with the original topology.
/-- Lemma 5.23.8: for a spectral space, the eight explicit visible conditions in the Stacks
statement are equivalent: profiniteness, Hausdorffness, total disconnectedness, closedness of
quasi-compact opens, triviality of specializations, closedness of all points, each point being the
generic point of an irreducible component, and equality of the constructible and given topologies.
-/
theorem spectralSpace_profinite_criteria
    (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    List.TFAE
      [ ∃ P : Profinite.{u}, Nonempty (X ≃ₜ P),
        T2Space X,
        TotallyDisconnectedSpace X,
        ∀ U : Set X, IsOpen U → IsCompact U → IsClosed U,
        ∀ ⦃x y : X⦄, x ⤳ y → x = y,
        ∀ x : X, IsClosed ({x} : Set X),
        ∀ x : X, IsGenericPoint x (irreducibleComponent x),
        constructibleTopology X = ‹TopologicalSpace X› ] := by
  tfae_have 1 → 3 := by
    rintro ⟨P, ⟨e⟩⟩
    exact e.symm.totallyDisconnectedSpace
  tfae_have 2 → 4 := by
    intro hT2 U hU hUcompact
    letI : T2Space X := hT2
    exact hUcompact.isClosed
  tfae_have 3 → 7 := by
    intro hTot x
    letI : TotallyDisconnectedSpace X := hTot
    -- A totally disconnected irreducible component is a singleton, so its generic point is the
    -- unique point it contains.
    have hpre : IsPreconnected (irreducibleComponent x) :=
      isIrreducible_irreducibleComponent.2.isPreconnected
    have hsub :
        (irreducibleComponent x).Subsingleton :=
      hpre.subsingleton
    have hEq : irreducibleComponent x = ({x} : Set X) := by
      ext y
      constructor
      · intro hy
        exact hsub hy mem_irreducibleComponent
      · rintro rfl
        exact mem_irreducibleComponent
    have hxClosed : IsClosed ({x} : Set X) := by
      exact hEq ▸ (isClosed_irreducibleComponent : IsClosed (irreducibleComponent x))
    exact hxClosed.closure_eq.trans hEq.symm
  tfae_have 4 → 8 := by
    intro hCompactOpenClosed
    apply le_antisymm
    · intro s hs
      obtain ⟨S, hSB, rfl⟩ := PrespectralSpace.isTopologicalBasis.open_eq_sUnion hs
      exact @isOpen_sUnion X (constructibleTopology X) S fun t ht ↦
        (hSB ht).2.isOpen_constructibleTopology_of_isOpen (hSB ht).1
    · rw [constructibleTopology]
      exact le_generateFrom fun s hs ↦ by
        rcases hs with hs | hs
        · exact hs.1
        · simpa using (hCompactOpenClosed sᶜ hs.1.isOpen_compl hs.2).isOpen_compl
  tfae_have 5 → 6 := by
    intro hSpecializesEq x
    letI : T1Space X := t1Space_iff_specializes_imp_eq.mpr fun _ _ h ↦ hSpecializesEq h
    exact isClosed_singleton
  tfae_have 5 → 8 := by
    intro hSpecializesEq
    apply le_antisymm
    · intro s hs
      obtain ⟨S, hSB, rfl⟩ := PrespectralSpace.isTopologicalBasis.open_eq_sUnion hs
      exact @isOpen_sUnion X (constructibleTopology X) S fun t ht ↦
        (hSB ht).2.isOpen_constructibleTopology_of_isOpen (hSB ht).1
    · rw [constructibleTopology]
      exact le_generateFrom fun s hs ↦ by
        rcases hs with hs | hs
        · exact hs.1
        · exact
            isOpen_of_isOpen_constructibleTopology_of_stableUnderGeneralization
              (hs.2.isOpen_constructibleTopology_of_isClosed hs.1)
              (fun _ _ hxy hx ↦ by simpa [hSpecializesEq hxy] using hx)
  tfae_have 6 → 5 := by
    intro hClosed _ _ hxy
    letI : T1Space X := ⟨hClosed⟩
    exact hxy.eq
  tfae_have 7 → 5 := by
    intro hGeneric x y hxy
    have hy_mem : y ∈ irreducibleComponent x := by
      rw [← (hGeneric x).def]
      exact hxy.mem_closure
    have hComponentSubset : irreducibleComponent y ⊆ irreducibleComponent x := by
      rw [← (hGeneric y).def]
      exact closure_minimal (singleton_subset_iff.mpr hy_mem) isClosed_irreducibleComponent
    have hComponentSubset' : irreducibleComponent x ⊆ irreducibleComponent y :=
      (irreducibleComponent_mem_irreducibleComponents y).2
        isIrreducible_irreducibleComponent hComponentSubset
    have hEq :
        irreducibleComponent x = irreducibleComponent y :=
      subset_antisymm hComponentSubset' hComponentSubset
    have hyGeneric : IsGenericPoint y (irreducibleComponent x) := by
      simpa [hEq] using hGeneric y
    exact (hGeneric x).eq hyGeneric
  tfae_have 8 → 1 := by
    intro hEq
    letI : T2Space X := hEq ▸ constructibleTopology_t2Space_of_spectralSpace
    letI : TotallyDisconnectedSpace X := hEq ▸
      constructibleTopology_totallyDisconnectedSpace_of_spectralSpace
    letI : CompactSpace X := hEq ▸ constructibleTopology_compactSpace_of_spectralSpace
    exact t2Space_compactSpace_totallyDisconnectedSpace_implies_exists_profinite X
  tfae_have 8 → 2 := by
    intro hEq
    exact hEq ▸ constructibleTopology_t2Space_of_spectralSpace
  tfae_finish

end

/-! ### Lemma_5_23_9 (from Chap05) -/
universe u

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

/- Domain-style sampling for connected components of spectral spaces:
- primary domain: connected-component quotients and profinite topology
- inspected owner declarations:
  `PrespectralSpace.connectedComponent_eq_iInter_isClopen`,
  `ConnectedComponents.t2_of_connectedComponent_eq_iInter_isClopen`,
  `connectedComponents_exists_profinite`,
  `Profinite.of`
- best owner abstraction: the quotient owner `ConnectedComponents X`, with profiniteness expressed
  through the canonical bundled owner `Profinite`

Layer triage:
- `source-facing`: Lemma 5.23.9, asserting that the connected-components quotient of a spectral
  space is profinite
- `core/canonical`: `ConnectedComponents X` and the owner theorem
  `connectedComponents_exists_profinite`
- `bridge/view`: the spectral-space specialization obtained from
  `PrespectralSpace.connectedComponent_eq_iInter_isClopen`

Primitive data is only the ambient spectral-space structure. The clopen-neighborhood description of
connected components is derived from the canonical owner theorem in
`PrespectralSpace.connectedComponent_eq_iInter_isClopen`, and the bundled profinite space is then
the canonical `Profinite.of (ConnectedComponents X)`. A local alias for that bundled object would
therefore duplicate existing owner API rather than add source mathematics.
-/

-- Proof sketch: in a spectral space, connected components are intersections of the clopen
-- neighborhoods of their points by Lemma 5.12.10. Lemma 5.22.5 is then the exact owner theorem
-- turning that description into a profinite realization of `ConnectedComponents X`.
/-- Lemma 5.23.9: if `X` is a spectral space, then `π₀(X)` is profinite. The canonical Lean model
of `π₀(X)` is `ConnectedComponents X`; its bundled profinite realization is the owner object
`Profinite.of (ConnectedComponents X)`, so no separate local alias is needed here. -/
theorem connectedComponents_exists_profinite_of_spectralSpace :
    ∃ P : Profinite.{u}, Nonempty (ConnectedComponents X ≃ₜ P) := by
  -- Specialize Lemma 5.12.10 to identify each connected component with the intersection of the
  -- clopen neighborhoods of its point.
  -- Feed that structural description into Lemma 5.22.5, which is exactly the profinite existence
  -- criterion for connected components.
  exact
    connectedComponents_exists_profinite
      PrespectralSpace.connectedComponent_eq_iInter_isClopen

end

/-! ### Lemma_5_23_10 (from Chap05) -/
universe u v

open Set TopologicalSpace Topology

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-
Domain-style sampling for products of spectral spaces:
- primary domain: spectral spaces and their owner ingredients `PrespectralSpace`,
  `QuasiSeparatedSpace`, and `QuasiSober`
- owner declarations inspected:
  `SpectralSpace`,
  `PrespectralSpace.isTopologicalBasis`,
  `PrespectralSpace.of_isTopologicalBasis'`,
  `QuasiSeparatedSpace.of_isTopologicalBasis`,
  `IsTopologicalBasis.prod`
- best owner abstraction: the public owner remains `SpectralSpace`, while the product proof is
  assembled from the canonical owner ingredients already built into its structure
- primitive data: compact-open rectangles in the product and the generic-point behavior of
  irreducible closed subsets under the two projections
- derived API: the product `SpectralSpace` instance itself

Layer triage:
- `source-facing`: Lemma 5.23.10, asserting that products of spectral spaces are spectral
- `core/canonical`: `SpectralSpace` together with its ingredient classes
  `PrespectralSpace`, `QuasiSeparatedSpace`, and `QuasiSober`
- `bridge/view`: the rectangle-basis and projection-to-generic-point constructions used to build
  the owner instance
-/

/-- Identify compact-open rectangles with the product basis indexed by compact opens in each
factor. -/
private theorem compactOpenRect_image2_eq :
    Set.image2 (· ×ˢ ·) { U : Set X | IsOpen U ∧ IsCompact U }
        { V : Set Y | IsOpen V ∧ IsCompact V } =
      Set.range
        (fun p : CompactOpens X × CompactOpens Y ↦
          ((p.1 ×ˢ p.2 : CompactOpens (X × Y)) : Set (X × Y))) := by
  have hX :
      (Set.range fun U : CompactOpens X ↦ (U : Set X)) =
        { U : Set X | IsOpen U ∧ IsCompact U } := by
    ext U
    constructor
    · rintro ⟨V, rfl⟩
      exact ⟨V.isOpen, V.isCompact⟩
    · intro hU
      exact ⟨⟨⟨U, hU.2⟩, hU.1⟩, rfl⟩
  have hY :
      (Set.range fun V : CompactOpens Y ↦ (V : Set Y)) =
        { V : Set Y | IsOpen V ∧ IsCompact V } := by
    ext V
    constructor
    · rintro ⟨W, rfl⟩
      exact ⟨W.isOpen, W.isCompact⟩
    · intro hV
      exact ⟨⟨⟨V, hV.2⟩, hV.1⟩, rfl⟩
  simpa [hX, hY] using
    (Set.image2_range
      (fun U V ↦ U ×ˢ V)
      (fun U : CompactOpens X ↦ (U : Set X))
      (fun V : CompactOpens Y ↦ (V : Set Y)))

section Prespectral

variable [PrespectralSpace X] [PrespectralSpace Y]

/-- Compact-open rectangles form a topological basis on the product of prespectral spaces. -/
private theorem compactOpenRect_isTopologicalBasis :
    IsTopologicalBasis
      (Set.range
        (fun p : CompactOpens X × CompactOpens Y ↦
          ((p.1 ×ˢ p.2 : CompactOpens (X × Y)) : Set (X × Y)))) := by
  simpa [compactOpenRect_image2_eq] using
    (show IsTopologicalBasis { U : Set X | IsOpen U ∧ IsCompact U } from
      PrespectralSpace.isTopologicalBasis).prod
      (show IsTopologicalBasis { V : Set Y | IsOpen V ∧ IsCompact V } from
        PrespectralSpace.isTopologicalBasis)

/-- The product of prespectral spaces is prespectral. -/
private instance prespectralSpaceProd : PrespectralSpace (X × Y) :=
  PrespectralSpace.of_isTopologicalBasis'
    compactOpenRect_isTopologicalBasis
    fun p ↦ p.1.isCompact.prod p.2.isCompact

/-- The product of quasi-separated prespectral spaces is quasi-separated. -/
private instance quasiSeparatedSpaceProd [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y] :
    QuasiSeparatedSpace (X × Y) :=
  QuasiSeparatedSpace.of_isTopologicalBasis compactOpenRect_isTopologicalBasis fun p q ↦ by
    simpa [Set.prod_inter_prod, Set.inter_comm] using
      (p.1.isCompact.inter_of_isOpen q.1.isCompact p.1.isOpen q.1.isOpen).prod
        (p.2.isCompact.inter_of_isOpen q.2.isCompact p.2.isOpen q.2.isOpen)

end Prespectral

section QuasiSober

variable [QuasiSober X] [QuasiSober Y]

/-- The product of quasi-sober spaces is quasi-sober. -/
private instance quasiSoberProd : QuasiSober (X × Y) where
  sober {S} hS hSclosed := by
    have hSx : IsIrreducible (Prod.fst '' S) := hS.image Prod.fst continuous_fst.continuousOn
    have hSy : IsIrreducible (Prod.snd '' S) := hS.image Prod.snd continuous_snd.continuousOn
    let hx : X := hSx.genericPoint
    let hy : Y := hSy.genericPoint
    have hfst : IsGenericPoint hx (closure (Prod.fst '' S)) :=
      by simpa [hx] using hSx.isGenericPoint_genericPoint_closure
    have hsnd : IsGenericPoint hy (closure (Prod.snd '' S)) :=
      by simpa [hy] using hSy.isGenericPoint_genericPoint_closure
    have hxy_mem : (hx, hy) ∈ S := by
      have hxy_closure : (hx, hy) ∈ closure S := by
        rw [mem_closure_iff]
        intro U hU hxyU
        rcases isOpen_prod_iff.mp hU hx hy hxyU with ⟨U₁, U₂, hU₁, hU₂, hxU₁, hyU₂, hsub⟩
        have hSU₁ : (S ∩ (U₁ ×ˢ (Set.univ : Set Y))).Nonempty := by
          rcases mem_closure_iff.1 hfst.mem U₁ hU₁ hxU₁ with ⟨x, hxU₁, hxS⟩
          rcases hxS with ⟨p, hpS, rfl⟩
          exact ⟨p, ⟨hpS, ⟨hxU₁, Set.mem_univ _⟩⟩⟩
        have hSU₂ : (S ∩ ((Set.univ : Set X) ×ˢ U₂)).Nonempty := by
          rcases mem_closure_iff.1 hsnd.mem U₂ hU₂ hyU₂ with ⟨y, hyU₂, hyS⟩
          rcases hyS with ⟨p, hpS, rfl⟩
          exact ⟨p, ⟨hpS, ⟨Set.mem_univ _, hyU₂⟩⟩⟩
        have hSrect : (S ∩ (U₁ ×ˢ U₂)).Nonempty := by
          convert hS.isPreirreducible (U₁ ×ˢ (Set.univ : Set Y))
            ((Set.univ : Set X) ×ˢ U₂)
            (hU₁.prod isOpen_univ) (isOpen_univ.prod hU₂) hSU₁ hSU₂ using 1
          ext p
          simp [Set.prod_inter_prod, Set.inter_comm]
        rcases hSrect with ⟨p, hpS, hpRect⟩
        exact ⟨p, ⟨hsub hpRect, hpS⟩⟩
      simpa [hSclosed.closure_eq] using hxy_closure
    refine ⟨(hx, hy), ?_⟩
    rw [isGenericPoint_iff_specializes]
    intro p
    constructor
    · intro hp
      have hclosure : closure ({(hx, hy)} : Set (X × Y)) ⊆ S :=
        hSclosed.closure_subset_iff.mpr (by simp [hxy_mem])
      exact hclosure hp.mem_closure
    · intro hp
      exact (hfst.specializes <| subset_closure ⟨p, hp, rfl⟩).prod
        (hsnd.specializes <| subset_closure ⟨p, hp, rfl⟩)

end QuasiSober

section Spectral

variable [SpectralSpace X] [SpectralSpace Y]

-- Proof sketch: the product inherits `T₀` and quasi-compactness from the factors. For
-- quasi-sobriety, an irreducible closed subset of `X × Y` has generic point given by the generic
-- points of the closures of its projections. For the compact-open basis, use rectangles `U × V`
-- with `U` and `V` quasi-compact open in the factors.
/-- Lemma 5.23.10 (Stacks tag `0907`): the product of two spectral spaces is spectral. -/
instance spectralSpace_prod : SpectralSpace (X × Y) where
  toT0Space := inferInstance
  toCompactSpace := inferInstance
  toQuasiSober := inferInstance
  toQuasiSeparatedSpace := inferInstance
  toPrespectralSpace := inferInstance

attribute [stacks 0907] spectralSpace_prod

end Spectral

end

/-! ### Lemma_5_23_11 (from Chap05) -/
universe u v

open Set TopologicalSpace Topology

/- Domain-style sampling for bijective spectral maps of spectral spaces:
- primary domain: spectral spaces, constructible topology, and specialization/generalization
  lifting along spectral maps
- sampled owner declarations:
  `IsSpectralMap.continuous_constructibleTopology`,
  `constructibleTopology_t2Space_of_spectralSpace`,
  `constructibleTopology_compactSpace_of_spectralSpace`,
  `SpecializingMap.stableUnderSpecialization_image`,
  `GeneralizingMap.stableUnderGeneralization_image`
- best owner abstraction: `IsSpectralMap` is the primitive map owner, while the canonical bridge
  to homeomorphisms runs through the constructible topologies, where spectral spaces become compact
  Hausdorff and a bijective spectral map becomes a homeomorphism

Layer triage:
- `source-facing`: Lemma 5.23.11, giving a homeomorphism criterion for a bijective spectral map
  under a lifting hypothesis
- `core/canonical`: `IsSpectralMap`, `SpecializingMap`, `GeneralizingMap`, and `IsHomeomorph`
- `bridge/view`: the constructible-topology homeomorphism and the patch-open/patch-closed
  criteria from Lemma `5.23.6`

Primitive data is only the spectral-map owner, bijectivity, and one lifting predicate. The
constructible-topology homeomorphism, image stability of specialization/generalization-stable
subsets, and the resulting open-map argument are all derived API and should not be repackaged as a
parallel public wrapper.
-/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [SpectralSpace X] [SpectralSpace Y] {f : X → Y}

/-- Helper for Lemma 5.23.11: a bijective spectral map is a homeomorphism for the
constructible topologies on spectral spaces. -/
private theorem isHomeomorph_constructibleTopology (hf : IsSpectralMap f)
    (hf_bijective : Function.Bijective f) :
    @IsHomeomorph X Y (constructibleTopology X) (constructibleTopology Y) f := by
  -- In the constructible topology, spectral spaces are compact and Hausdorff.
  let hXCompact : @CompactSpace X (constructibleTopology X) :=
    constructibleTopology_compactSpace_of_spectralSpace
  let hYT2 : @T2Space Y (constructibleTopology Y) :=
    constructibleTopology_t2Space_of_spectralSpace
  -- A continuous bijection from compact to Hausdorff is a homeomorphism.
  exact
    (@isHomeomorph_iff_continuous_bijective X Y (constructibleTopology X) (constructibleTopology Y)
      f hXCompact hYT2).2 ⟨hf.continuous_constructibleTopology, hf_bijective⟩

/-- Helper for Lemma 5.23.11: lifted generalizations make a bijective spectral map open. -/
private theorem isOpenMap_of_isSpectralMap_bijective_of_generalizingMap
    (hf : IsSpectralMap f) (hf_bijective : Function.Bijective f) (hgen : GeneralizingMap f) :
    IsOpenMap f := by
  let hpatch := isHomeomorph_constructibleTopology hf hf_bijective
  -- It suffices to check openness on the quasi-compact open basis of a spectral space.
  refine (PrespectralSpace.isTopologicalBasis.isOpenMap_iff).2 ?_
  intro U hU
  -- A basis open is patch-open, and its image is patch-open under the constructible homeomorphism.
  have hU_patch_open : IsOpen[constructibleTopology X] U :=
    hU.2.isOpen_constructibleTopology_of_isOpen hU.1
  have hpatch_openMap : @IsOpenMap X Y (constructibleTopology X) (constructibleTopology Y) f :=
    @IsHomeomorph.isOpenMap X Y (constructibleTopology X) (constructibleTopology Y) f hpatch
  have hImage_patch_open : IsOpen[constructibleTopology Y] (f '' U) :=
    hpatch_openMap _ hU_patch_open
  -- Generalization stability upgrades a patch-open subset of a spectral space to an open subset.
  have hImage_gen : StableUnderGeneralization (f '' U) :=
    hgen.stableUnderGeneralization_image hU.1.stableUnderGeneralization
  exact isOpen_of_isOpen_constructibleTopology_of_stableUnderGeneralization
    hImage_patch_open hImage_gen

/-- Helper for Lemma 5.23.11: lifted specializations make a bijective spectral map open. -/
private theorem isOpenMap_of_isSpectralMap_bijective_of_specializingMap
    (hf : IsSpectralMap f) (hf_bijective : Function.Bijective f) (hspec : SpecializingMap f) :
    IsOpenMap f := by
  let hpatch := isHomeomorph_constructibleTopology hf hf_bijective
  -- Again, it is enough to test openness on the quasi-compact open basis.
  refine (PrespectralSpace.isTopologicalBasis.isOpenMap_iff).2 ?_
  intro U hU
  -- Pass to complements so that the patch homeomorphism gives a closed image.
  have hU_patch_open : IsOpen[constructibleTopology X] U :=
    hU.2.isOpen_constructibleTopology_of_isOpen hU.1
  have hUcompl_patch_closed : @IsClosed X (constructibleTopology X) Uᶜ :=
    @IsOpen.isClosed_compl X (constructibleTopology X) U hU_patch_open
  have hpatch_closedMap : @IsClosedMap X Y (constructibleTopology X) (constructibleTopology Y) f :=
    @IsHomeomorph.isClosedMap X Y (constructibleTopology X) (constructibleTopology Y) f hpatch
  have hCompl_patch_closed : IsClosed[constructibleTopology Y] (f '' Uᶜ) :=
    hpatch_closedMap _ hUcompl_patch_closed
  -- Specialization stability upgrades a patch-closed subset of a spectral space to a closed subset.
  have hCompl_spec : StableUnderSpecialization (f '' Uᶜ) :=
    hspec.stableUnderSpecialization_image hU.1.isClosed_compl.stableUnderSpecialization
  have hCompl_closed : IsClosed (f '' Uᶜ) :=
    isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization
      hCompl_patch_closed hCompl_spec
  -- Bijectivity identifies the complement of the image with the image of the complement.
  rw [← isClosed_compl_iff, ← Set.image_compl_eq hf_bijective]
  exact hCompl_closed

-- Proof sketch: pass to the constructible topologies, where a spectral space is compact Hausdorff;
-- then a bijective spectral map is a homeomorphism there. For lifted generalizations, the image of
-- each quasi-compact open basis element is patch-open and stable under generalization, hence open
-- in the original topology by Lemma `5.23.6`. For lifted specializations, apply the same argument
-- to the complement of a quasi-compact open basis element to show its image complement is closed,
-- so the basis image itself is open. Thus `f` is an open bijection, hence a homeomorphism.
/-- Lemma 5.23.11: a bijective spectral map between spectral spaces is a homeomorphism if either
specializations or generalizations lift along the map. -/
theorem isHomeomorph_of_isSpectralMap_bijective_of_lift_specializations_or_generalizations
    (hf : IsSpectralMap f) (hf_bijective : Function.Bijective f)
    (hLift : SpecializingMap f ∨ GeneralizingMap f) : IsHomeomorph f := by
  -- Once the map is known to be open in the original topology, continuity and bijectivity finish.
  refine ⟨hf.continuous, ?_, hf_bijective⟩
  rcases hLift with hspec | hgen
  · exact isOpenMap_of_isSpectralMap_bijective_of_specializingMap hf hf_bijective hspec
  · exact isOpenMap_of_isSpectralMap_bijective_of_generalizingMap hf hf_bijective hgen

end
