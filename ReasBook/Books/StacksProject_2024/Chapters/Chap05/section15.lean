import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Constructible

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_15_1 (from Chap05) -/
universe u

open Topology

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for constructible and locally constructible subsets:
- inspected canonical declarations: `Topology.IsConstructible`, `Topology.IsLocallyConstructible`,
  `Topology.IsConstructible.isLocallyConstructible`, and
  `Topology.IsLocallyConstructible.iff_of_isOpenCover`.
- best owner abstractions: `Topology.IsConstructible` for constructible subsets and
  `Topology.IsLocallyConstructible` for their local form.
- primitive-vs-derived split:
  primitive data: membership in the canonical constructible-subset predicate, and membership in the
    canonical locally constructible predicate.
  derived API: the implication from constructible to locally constructible, and the source-style
    open-cover reformulation of local constructibility.

Layer triage:
- `source-facing`: Definition 5.15.1 introduces constructible and locally constructible subsets.
- `core/canonical`: the mathlib owner predicates `Topology.IsConstructible` and
  `Topology.IsLocallyConstructible`.
- `bridge/view`: `Topology.IsLocallyConstructible.iff_of_isOpenCover`, which recovers the source
  open-cover phrasing without introducing a parallel local definition.

This file should therefore stay at the direct canonical recall layer, with only a thin companion
bridge for the source open-cover formulation of local constructibility.
-/

/- Definition 5.15.1 (1) is recalled canonically by `Topology.IsConstructible`: in mathlib this is
the Boolean-subalgebra-generated notion equivalent to the Stacks source formulation by finite
unions of subsets `U ∩ Vᶜ` with `U` and `V` open and retrocompact. -/
recall IsConstructible

/- Definition 5.15.1 (2) is recalled canonically by `Topology.IsLocallyConstructible`: this is
the standard local formulation equivalent to the Stacks source open-cover condition that each
trace `E ∩ Vᵢ` be constructible in the subspace `Vᵢ`. -/
recall IsLocallyConstructible

/- Companion recall: the source open-cover formulation of local constructibility is the canonical
equivalence `Topology.IsLocallyConstructible.iff_of_isOpenCover`. -/
recall IsLocallyConstructible.iff_of_isOpenCover

/-! ### Lemma_5_15_2 (from Chap05) -/
universe u

open Topology

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for constructible-set closure operations:
- primary domain: constructible subsets in a topological space, organized around the owner
  predicate `Topology.IsConstructible`;
- sampled canonical declarations:
  `Topology.IsConstructible`,
  `Topology.IsConstructible.compl`,
  `Topology.IsConstructible.union`,
  `Topology.IsConstructible.inter`;
- best owner abstraction: `Topology.IsConstructible`;
- primitive-vs-derived split:
  primitive data: membership in the canonical Boolean-subalgebra predicate `IsConstructible`;
  derived API: closure under complement, binary union, and binary intersection.

Layer triage:
- `source-facing`: Lemma 5.15.2 records that constructible subsets are closed under complements,
  unions, and intersections;
- `core/canonical`: the existing owner predicate `Topology.IsConstructible`;
- `bridge/view`: the closure-operation lemmas `isConstructible_compl`, `IsConstructible.union`, and
  `IsConstructible.inter`.

This file should therefore stay recall-only and use the source-faithful binary closure lemmas,
without upgrading the main entries to the stronger finite-family theorems `sUnion` and `sInter`. -/

/- Lemma 5.15.2 (complements): closure of constructible subsets under complements is exactly the
canonical directional theorem `Topology.IsConstructible.compl`. -/
recall IsConstructible.compl

/- Lemma 5.15.2 (unions): closure of constructible subsets under binary unions is exactly the
canonical theorem `Topology.IsConstructible.union`. -/
recall IsConstructible.union

/- Lemma 5.15.2 (intersections): closure of constructible subsets under binary intersections is
exactly the canonical theorem `Topology.IsConstructible.inter`. -/
recall IsConstructible.inter

/-! ### Lemma_5_15_3 (from Chap05) -/
universe u v

open Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Domain-style sampling for constructible preimages in topological spaces:
- primary domain: constructible subsets, retrocompact opens, and pullback stability in topology;
- sampled canonical declarations:
  `IsConstructible.preimage`,
  `IsConstructible.preimage_of_isOpenEmbedding`,
  `IsConstructible.preimage_of_isClosedEmbedding`,
  `IsSpectralMap.isConstructible_preimage`;
- best owner abstraction: the owner of the general pullback-stability statement is the mathlib
  theorem `IsConstructible.preimage`; the open-embedding, closed-embedding, and spectral-map forms
  are derived specializations;
- primitive-vs-derived split: the primitive data are continuity of `f` together with the
  retrocompact-open preimage hypothesis. The constructible-preimage conclusion and its stronger
  special cases are derived API from that owner theorem.

Layer triage:
- `source-facing`: the Stacks lemma on pullbacks of constructible subsets under maps preserving
  retrocompact opens;
- `core/canonical`: `IsConstructible.preimage`;
- `bridge/view`: the open-embedding, closed-embedding, and spectral-map specializations.
-/

/- Lemma 5.15.3: if `f : X → Y` is continuous and inverse images of retrocompact open subsets are
retrocompact, then inverse images of constructible subsets are constructible. This is exactly the
canonical theorem `Topology.IsConstructible.preimage`. -/
recall IsConstructible.preimage

/-! ### Lemma_5_15_4 (from Chap05) -/
namespace Topology

/- Domain-style sampling for constructible pullbacks along subspace inclusions:
- owner declaration: `Topology.IsConstructible.preimage_of_isOpenEmbedding`
- same-domain project declarations: `Topology.IsConstructible.preimage`,
  `Topology.IsConstructible.preimage_of_isClosedEmbedding`, and
  `Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact`
- `source-facing`: the trace of a constructible subset on an open subspace
- `core/canonical`: `Topology.IsConstructible.preimage_of_isOpenEmbedding`
- `bridge/view`: the subtype inclusion `Subtype.val : U → X` supplies the owner input from
  `IsOpen U`
- target layer here: direct recall/use of the canonical owner theorem, since the source item adds
  no extra mathematics beyond that open-subspace specialization

Primitive data belongs to the owner theorem: an open embedding and a constructible subset. For the
subtype inclusion of an open subset, the open embedding is derived canonically from `IsOpen U`, so
this file should recall the owner rather than keep a parallel wrapper theorem.
-/

/- Lemma 5.15.4: if `U ⊆ X` is open and `E ⊆ X` is constructible, then `E ∩ U` is constructible
in the open subspace `U`. This is the open-subspace specialization of the canonical theorem
`Topology.IsConstructible.preimage_of_isOpenEmbedding`. -/
recall IsConstructible.preimage_of_isOpenEmbedding

end Topology

/-! ### Lemma_5_15_5 (from Chap05) -/
namespace Topology

/- Domain-style sampling for constructible images along subspace inclusions:
- owner declaration: `Topology.IsConstructible.image_of_isOpenEmbedding`
- same-domain chapter bridges:
  `Topology.IsConstructible.preimage_subtypeVal_of_isOpen`,
  `Topology.IsConstructible.image_subtypeVal_of_isClosed_of_isRetrocompact_compl`
- target layer here: `bridge/view`, specializing the owner theorem to the open-subspace map
  `Subtype.val : U → X`

Primitive data belongs to the owner theorem: an open embedding together with retrocompact range.
For the subtype inclusion of an open subset, both facts are derived canonically from `IsOpen U`
and `IsRetrocompact U`, so this file should recall the owner rather than keep a parallel wrapper
theorem.
-/

/- Lemma 5.15.5: if `U ⊆ X` is a retrocompact open and `E ⊆ U` is constructible in the open
subspace `U`, then `E` is constructible in `X`. This is the open-subspace specialization of the
canonical theorem `Topology.IsConstructible.image_of_isOpenEmbedding`. -/
recall IsConstructible.image_of_isOpenEmbedding

end Topology

/-! ### Lemma_5_15_6 (from Chap05) -/
universe u v

open Set TopologicalSpace Topology
open scoped Set.Notation

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for constructibility on finite retrocompact open covers:
- primary domain: constructible subsets and their locality on open covers;
- sampled canonical declarations:
  `Topology.IsConstructible.preimage_of_isOpenEmbedding`,
  `Topology.IsConstructible.image_of_isOpenEmbedding`,
  `Topology.IsLocallyConstructible.iff_of_isOpenCover`,
  `TopologicalSpace.IsOpenCover.iUnion_inter`.
- best owner abstraction: `Topology.IsConstructible` is the owner predicate; the finite-cover
  reconstruction and the subtype image/preimage identification are derived API.
- primitive-vs-derived split:
  primitive data: the indexed open cover, retrocompactness of each cover member, and the
    constructible traces on those members;
  derived API: the ambient constructible pieces
    `Subtype.val '' ((V i : Set X) ↓∩ E) = (V i : Set X) ∩ E`
    and the cover identity `⋃ i, ((V i : Set X) ∩ E) = E`.

Layer triage:
- `source-facing`: Lemma 5.15.6 itself, asserting locality of constructibility on a finite
  retrocompact open cover;
- `core/canonical`: `Topology.IsConstructible`;
- `bridge/view`: the subtype inclusions `Subtype.val : V i → X` together with
  `IsOpenCover.iUnion_inter`.
-/

-- Proof sketch: use the canonical constructible-set API for open embeddings. For the forward
-- implication, pull back along each `Subtype.val : V i → X`. For the reverse implication, push
-- each constructible trace forward along the same open embedding, then reconstruct `E` as the
-- finite union of these traces over the cover.
/-- Lemma 5.15.6: a subset `E ⊆ X` is constructible if and only if its trace on each member of a
finite retrocompact open cover is constructible in that open subspace. -/
theorem isConstructible_iff_forall_preimage_subtypeVal_of_finite_retrocompact_openCover
    {ι : Type v} [Finite ι] (V : ι → Opens X) (hV : IsOpenCover V)
    (hretro : ∀ i, IsRetrocompact (V i : Set X)) {E : Set X} :
    IsConstructible E ↔ ∀ i, IsConstructible ((V i : Set X) ↓∩ E) := by
  constructor
  · intro hE i
    -- Pull back the ambient constructible set along the open-subspace inclusion.
    simpa using hE.preimage_of_isOpenEmbedding (V i).2.isOpenEmbedding_subtypeVal
  · intro hE
    -- Reassemble `E` from its traces on the cover and prove each trace constructible in `X`.
    rw [← hV.iUnion_inter E]
    exact IsConstructible.iUnion fun i ↦ by
      -- Push the constructible trace forward along the retrocompact open embedding.
      simpa [image_preimage_eq_range_inter, inter_comm] using
        (hE i).image_of_isOpenEmbedding (V i).2.isOpenEmbedding_subtypeVal
        (by simpa using hretro i)

/-! ### Lemma_5_15_7 (from Chap05) -/
universe u

open Set

namespace Topology

/- Domain-style sampling for constructible pullbacks along subspace inclusions:
- owner declaration: `Topology.IsConstructible.preimage_of_isClosedEmbedding`
- same-domain declarations inspected: `Topology.IsConstructible.preimage`,
  `Topology.IsConstructible.preimage_of_isClosedEmbedding`,
  `Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact`
- `source-facing`: the closed-subspace pullback statement for a constructible subset
- `core/canonical`: `Topology.IsConstructible.preimage_of_isClosedEmbedding`
- `bridge/view`: the subtype inclusion `Subtype.val : Z → X` supplies the owner inputs from
  `IsClosed Z` and `IsCompact Zᶜ`
- target layer here: direct recall/use of the canonical owner theorem, since the source item adds
  no extra mathematics beyond that closed-subspace specialization

Primitive data belongs to the owner theorem: a closed embedding together with compact complement of
its range. For the subtype inclusion of a closed subset, both facts are derived canonically from
`IsClosed Z` and `IsCompact Zᶜ`, so this file should recall the owner rather than keep a parallel
local wheel.
-/

/- Lemma 5.15.7: if `Z ⊆ X` is closed and `Zᶜ` is quasi-compact, then the trace of a constructible
subset `E ⊆ X` on the closed subspace `Z` is constructible in `Z`. This is the closed-subspace
specialization of the canonical theorem `Topology.IsConstructible.preimage_of_isClosedEmbedding`. -/
recall IsConstructible.preimage_of_isClosedEmbedding

end Topology

/-! ### Lemma_5_15_8 (from Chap05) -/
open Set TopologicalSpace Topology
open scoped Set.Notation

universe u

namespace Topology

section

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X] {T : Set X}

/-
Domain-style sampling for constructible pullbacks along retrocompact subspace inclusions:
- primary domain: constructible subsets, retrocompact opens, and spectral maps into a prespectral
  space
- sampled canonical declarations:
  `Topology.IsConstructible.preimage`,
  `IsRetrocompact_iff_isSpectralMap_subtypeVal`,
  `TopologicalSpace.IsTopologicalBasis.isInducing`,
  `eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open`
- best owner abstraction: `Topology.IsConstructible.preimage` is the main owner for constructible
  pullbacks, and the supporting retrocompact-preimage bridge belongs at the
  `IsInducing`/`IsSpectralMap` layer rather than as a subtype-specific helper

Layer triage:
- `source-facing`: the trace of a constructible subset on a retrocompact subspace
- `core/canonical`: `Topology.IsConstructible.preimage`
- `bridge/view`: `Subtype.val : T → X`, viewed canonically through
  `IsRetrocompact_iff_isSpectralMap_subtypeVal`

Primitive data for the public statement are the constructible subset `E`, the retrocompact subset
`T`, and the ambient prespectral structure on `X`. The compact-open basis induced on the source of
an inducing spectral map is derived API and should be exposed once at that owner level rather than
packaged as a subtype-only local lemma.
-/

private theorem isRetrocompact_preimage_of_isSpectralMap
    {Y : Type*} [TopologicalSpace Y] {f : Y → X} (hf_ind : IsInducing f) (hf_spec : IsSpectralMap f)
    {U : Set X} (hU_open : IsOpen U) (hU_retro : IsRetrocompact U) :
    IsRetrocompact (f ⁻¹' U) := by
  let basisY : Set (Set Y) := Set.preimage f '' {V : Set X | IsOpen V ∧ IsCompact V}
  have hBasisY : IsTopologicalBasis basisY :=
    PrespectralSpace.isTopologicalBasis.isInducing hf_ind
  intro V hV_comp hV_open
  obtain ⟨s, hsV⟩ :=
    eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open basisY hBasisY V hV_comp hV_open
  rw [hsV, Set.sUnion_image]
  have hEq :
      (f ⁻¹' U ∩ ⋃ W ∈ (↑s : Set basisY), ((W : basisY) : Set Y)) =
        ⋃ W ∈ (↑s : Set basisY), (f ⁻¹' U ∩ ((W : basisY) : Set Y)) := by
    ext y
    simp
  rw [hEq]
  refine s.isCompact_biUnion fun W _ ↦ ?_
  rcases W.2 with ⟨W', hW', hW_eq⟩
  rw [← hW_eq]
  rw [show f ⁻¹' U ∩ f ⁻¹' W' = f ⁻¹' (U ∩ W') by ext y; rfl]
  exact hf_spec.isCompact_preimage_of_isOpen (hU_open.inter hW'.1) (hU_retro hW'.2 hW'.1)

-- Proof sketch: apply `Topology.IsConstructible.preimage` to the subtype map `Subtype.val : T → X`.
-- For a compact open `U ⊆ X`, use the compact-open basis hypothesis on the subspace `T` to show
-- that `(Subtype.val) ⁻¹' U = U ∩ T` is retrocompact in `T`; then pull back the constructible set
-- `E` along the subtype inclusion.
/-- Lemma 5.15.8: if `T ⊆ X` is retrocompact and compact open subsets form a topological basis of
`X`, then the trace of a constructible subset `E ⊆ X` on the subspace `T` is constructible in
`T`. The ambient compact-open-basis hypothesis is expressed canonically as `[PrespectralSpace X]`.
-/
theorem IsConstructible.preimage_subtypeVal_of_isRetrocompact
    {E : Set X} (hE : IsConstructible E) (hT : IsRetrocompact T) :
    IsConstructible (T ↓∩ E) :=
  let hSubtype : IsSpectralMap (Subtype.val : T → X) :=
    IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hT
  hE.preimage continuous_subtype_val
    (fun _ hs_open hs_retro ↦
      isRetrocompact_preimage_of_isSpectralMap IsInducing.subtypeVal hSubtype hs_open hs_retro)

end

end Topology

/-! ### Lemma_5_15_9 (from Chap05) -/
namespace Topology

/- Domain-style sampling for constructible images along closed-subspace inclusions:
- primary domain: constructible subsets and their stability under maps preserving the
  retrocompact-open generators used by `Topology.IsConstructible`;
- sampled canonical declarations:
  `Topology.IsConstructible.preimage`,
  `Topology.IsConstructible.preimage_of_isClosedEmbedding`,
  `Topology.IsConstructible.image_of_isOpenEmbedding`,
  `Topology.IsConstructible.image_of_isClosedEmbedding`;
- best owner abstraction: `Topology.IsConstructible.image_of_isClosedEmbedding`.

Primitive-vs-derived split:
- primitive data: a closed embedding together with retrocompact complement of its range;
- derived API: the closed-subspace specialization obtained from `Subtype.val : Z → X`.

Layer triage:
- `source-facing`: a constructible subset of a closed subspace has constructible image in the
  ambient space under the Stacks closed-subspace hypotheses;
- `core/canonical`: `Topology.IsConstructible.image_of_isClosedEmbedding`;
- `bridge/view`: the subtype inclusion `Subtype.val : Z → X`, whose owner hypotheses are supplied
  canonically by `IsClosed Z` and `IsRetrocompact Zᶜ`.

This file should therefore recall the owner theorem rather than keep a parallel local wrapper.
-/

/- Lemma 5.15.9: if `Z ⊆ X` is closed and `Zᶜ` is retrocompact open in `X`, then a constructible
subset of the closed subspace `Z` has constructible image in `X`. This is the closed-subspace
specialization of the canonical theorem
`Topology.IsConstructible.image_of_isClosedEmbedding`. -/
recall IsConstructible.image_of_isClosedEmbedding

end Topology

/-! ### Lemma_5_15_10 (from Chap05) -/
universe u

open Set TopologicalSpace Topology

namespace Topology

variable {X : Type u} [TopologicalSpace X] {E : Set X}

/-
Domain-style sampling for constructible subsets and retrocompactness:
- primary domain: constructible subsets of topological spaces, viewed through the Boolean
  subalgebra generated by open retrocompact subsets;
- sampled canonical declarations:
  `Topology.IsConstructible`,
  `BooleanSubalgebra.closure_sdiff_sup_induction`,
  `IsRetrocompact.union`,
  `IsRetrocompact.inter_isOpen`;
- best owner abstraction: `Topology.IsConstructible` is the source-facing owner notion, and its
  generator-style proofs should be organized through
  `BooleanSubalgebra.closure_sdiff_sup_induction` on the family of open retrocompact subsets;
- primitive-vs-derived split: the primitive data is only membership in that Boolean closure.
  Retrocompactness of an arbitrary constructible subset is derived API, so this file should expose
  the theorem directly and keep any lattice witness local to the proof.

Layer triage:
- `source-facing`: Lemma 5.15.10 itself, asserting that constructible subsets are retrocompact;
- `core/canonical`: the Boolean-subalgebra closure induction principle;
- `bridge/view`: none.
-/

-- Proof sketch: `IsConstructible E` means membership in the Boolean subalgebra generated by the
-- open retrocompact subsets. The generator family is a sublattice, and the difference of two
-- open retrocompact subsets is retrocompact. So
-- `BooleanSubalgebra.closure_sdiff_sup_induction` upgrades retrocompactness from the generators to
-- every constructible set.
/-- Lemma 5.15.10: every constructible subset of a topological space is retrocompact. -/
theorem IsConstructible.isRetrocompact (hE : IsConstructible E) : IsRetrocompact E := by
  -- Rewrite constructibility into membership in the Boolean closure generated by open
  -- retrocompact subsets so the source proof becomes a closure induction.
  change E ∈ BooleanSubalgebra.closure {U : Set X | IsOpen U ∧ IsRetrocompact U} at hE
  refine BooleanSubalgebra.closure_sdiff_sup_induction
    (⟨
      fun U hU V hV ↦ ⟨hU.1.union hV.1, hU.2.union hV.2⟩,
      fun U hU V hV ↦ ⟨hU.1.inter hV.1, hU.2.inter_isOpen hV.2 hV.1⟩
    ⟩ : IsSublattice {U : Set X | IsOpen U ∧ IsRetrocompact U})
    (by simp) (by simp) ?_ ?_ E hE
  · intro U hU V hV W hW_comp hW_open
    -- Intersect the locally closed piece `U \ V` with an arbitrary compact open `W`,
    -- then use compactness of `(U ∩ W) \ V` and rewrite back to the desired trace.
    simpa [sdiff_eq, inter_assoc, inter_left_comm, inter_comm] using
      (hU.2 hW_comp hW_open).diff hV.1
  · intro U _ V _ hU hV
    -- The union branch is exactly stability of retrocompactness under finite unions.
    exact hU.union hV

end Topology

/-! ### Lemma_5_15_11 (from Chap05) -/
universe u

open Set TopologicalSpace Topology
open scoped Set.Notation

namespace Topology

section

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X] {T E : Set X}

/- Domain-style sampling for constructible pullbacks along subtype inclusions in prespectral spaces:
- primary domain: constructible subsets and their restriction to constructible subspaces;
- sampled declarations:
  `Topology.IsConstructible.preimage`,
  `Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact`,
  `Topology.IsConstructible.isRetrocompact`,
  `PrespectralSpace.isTopologicalBasis`;
- best owner abstraction: the chapter owner for subtype pullback is
  `Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact`; the ambient prespectral
  structure and the retrocompactness of the subspace are supporting data for that owner;
- primitive-vs-derived split: the primitive data are the ambient constructible subset being
  pulled back and the retrocompact subspace. `PrespectralSpace X` is canonical ambient structure,
  and `Topology.IsConstructible.isRetrocompact` derives the owner input from the source-facing
  constructibility hypothesis on the subspace.

Layer triage:
- `source-facing`: Lemma 5.15.11, the constructible-subspace specialization of the trace theorem;
- `core/canonical`: `Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact`;
- `bridge/view`: this file's derivation of the owner input from
  `Topology.IsConstructible.isRetrocompact`.
-/

-- Proof sketch: derive that the constructible subspace `T` is retrocompact by
-- `Topology.IsConstructible.isRetrocompact`, then feed that derived input into the canonical
-- subtype-pullback owner `Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact`.
/-- Lemma 5.15.11: if compact open subsets form a topological basis of `X` and `T, E ⊆ X` are
constructible, then the intersection `T ∩ E`, viewed as a subset of the subspace `T`, is
constructible in `T`. The ambient basis hypothesis is expressed canonically as
`[PrespectralSpace X]`. -/
theorem IsConstructible.preimage_subtypeVal_of_isConstructible
    (hE : IsConstructible E) (hT : IsConstructible T) :
    IsConstructible (T ↓∩ E) :=
  hE.preimage_subtypeVal_of_isRetrocompact hT.isRetrocompact

end

end Topology

/-! ### Lemma_5_15_12 (from Chap05) -/
universe u

open Set TopologicalSpace Topology
open scoped Set.Notation

namespace Topology

section

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X] {E : Set X} {F : Set E}

/- Domain-style sampling for constructible subsets inside constructible subspaces:
- primary domain: constructible subsets, subtype inclusions, and the owner `Topology.IsConstructible`
  API for passing between a subspace and the ambient space;
- sampled canonical declarations:
  `Topology.IsConstructible.image_of_isOpenEmbedding`,
  `Topology.IsConstructible.image_of_isClosedEmbedding`,
  `Topology.IsConstructible.preimage_subtypeVal_of_isConstructible`,
  `Topology.IsConstructible.isRetrocompact`;
- best owner abstraction: the public statement should be the constructible image of the canonical
  map `Subtype.val : E → X`, not a separate global coercion wrapper;
- primitive-vs-derived split: the primitive data are the constructible ambient subspace `E` and
  the constructible subset `F ⊆ E`. The ambient subset `(F : Set X)` is derived from the owner
  map as `Subtype.val '' F`.

Layer triage:
- `source-facing`: Lemma 5.15.12, asserting that a constructible subset of a constructible
  subspace is constructible in the ambient space;
- `core/canonical`: `Topology.IsConstructible` together with image theorems for maps such as
  `Subtype.val`;
- `bridge/view`: the coercion `Set E → Set X`, which should be secondary to the image statement.
-/

/-- Helper for Lemma 5.15.12: a constructible subspace of a prespectral space is again
prespectral. -/
private theorem prespectralSpace_subtype_of_isConstructible {S : Set X}
    (hS : IsConstructible S) : PrespectralSpace S := by
  -- The subtype map of a retrocompact subset is spectral, so the compact-open basis descends.
  let hSpec : IsSpectralMap (Subtype.val : S → X) :=
    IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hS.isRetrocompact
  exact PrespectralSpace.of_isInducing (Subtype.val : S → X) IsInducing.subtypeVal hSpec

/-- Helper for Lemma 5.15.12: a constructible subset is a finite union of locally closed pieces
`U \ V` with `U` and `V` open retrocompact. -/
private theorem exists_finite_iUnion_eq_retrocompact_open_sdiff {S : Set X}
    (hS : IsConstructible S) :
    ∃ ι : Type u, ∃ _ : Finite ι, ∃ Z : ι → Set X,
      (∀ i, ∃ U V : Set X,
        IsOpen U ∧ IsRetrocompact U ∧ IsOpen V ∧ IsRetrocompact V ∧ Z i = U \ V) ∧
      S = ⋃ i, Z i := by
  -- Work directly with the Boolean-closure definition so the generators stay retrocompact.
  change S ∈ BooleanSubalgebra.closure {U : Set X | IsOpen U ∧ IsRetrocompact U} at hS
  refine BooleanSubalgebra.closure_sdiff_sup_induction
    (⟨
      fun U hU V hV ↦ ⟨hU.1.union hV.1, hU.2.union hV.2⟩,
      fun U hU V hV ↦ ⟨hU.1.inter hV.1, hU.2.inter_isOpen hV.2 hV.1⟩
    ⟩ : IsSublattice {U : Set X | IsOpen U ∧ IsRetrocompact U})
    (by simp) (by simp) ?_ ?_ S hS
  · intro U hU V hV
    -- A single generator difference already has the required form.
    refine ⟨PUnit, inferInstance, fun _ ↦ U \ V, ?_, ?_⟩
    · intro _
      exact ⟨U, V, hU.1, hU.2, hV.1, hV.2, rfl⟩
    · ext x
      simp
  · intro s hs t ht hs_ind ht_ind
    -- Finite unions are handled by concatenating the finite index sets.
    rcases hs_ind with ⟨ιs, hιs, Zs, hZs, rfl⟩
    rcases ht_ind with ⟨ιt, hιt, Zt, hZt, rfl⟩
    letI := hιs
    letI := hιt
    refine ⟨ιs ⊕ ιt, inferInstance, Sum.elim Zs Zt, ?_, ?_⟩
    · intro i
      cases i with
      | inl i => simpa using hZs i
      | inr i => simpa using hZt i
    · simp [iUnion_sum]

/-- Helper for Lemma 5.15.12: a constructible subset of a locally closed piece `U \ V` with `U`
and `V` open retrocompact has constructible image in the ambient space. -/
private theorem image_subtypeVal_of_retrocompact_open_sdiff {U V : Set X}
    (hU_open : IsOpen U) (hU_retro : IsRetrocompact U)
    (hV_open : IsOpen V) (hV_retro : IsRetrocompact V)
    {S : Set ↥(U \ V)} (hS : IsConstructible S) :
    IsConstructible (Subtype.val '' S) := by
  let i : ↥(U \ V) → U := Set.inclusion (show U \ V ⊆ U by intro x hx; exact hx.1)
  have hi_closed : IsClosedEmbedding i := by
    -- Inside `U`, the piece `U \ V` is closed because its complement is the open trace of `V`.
    refine Topology.IsClosedEmbedding.inclusion (show U \ V ⊆ U by intro x hx; exact hx.1) ?_
    have hOpen : IsOpen ((U : Set X) ↓∩ V) := by
      simpa [Subtype.preimage_coe_inter_self] using hV_open.preimage continuous_subtype_val
    simpa [Subtype.preimage_coe_inter_self, sdiff_eq, inter_assoc, inter_left_comm, inter_comm] using
      hOpen.isClosed_compl
  have hi_compl : IsRetrocompact (range i)ᶜ := by
    -- The complement of that closed embedding is the trace of the retrocompact open `V` on `U`.
    have : IsRetrocompact ((U : Set X) ↓∩ V) := by
      simpa [Subtype.preimage_coe_inter_self] using
        hV_retro.preimage_of_isOpenEmbedding hU_open.isOpenEmbedding_subtypeVal
    have hRangeCompl : (range i)ᶜ = ((U : Set X) ↓∩ V) := by
      ext x
      simp [i]
    rw [hRangeCompl]
    exact this
  have hSU : IsConstructible (i '' S) := hS.image_of_isClosedEmbedding hi_closed hi_compl
  have hOpenEmbedding : IsOpenEmbedding (Subtype.val : U → X) := hU_open.isOpenEmbedding_subtypeVal
  have hImageInX : IsConstructible ((Subtype.val : U → X) '' (i '' S)) :=
    hSU.image_of_isOpenEmbedding hOpenEmbedding (by simpa using hU_retro)
  -- Compose the closed-subspace and open-subspace images to recover the ambient image in `X`.
  simpa [i, Set.image_image] using hImageInX

/-- Lemma 5.15.12: in a topological space whose quasi-compact opens form a basis, equivalently
`[PrespectralSpace X]`, the image in `X` of a constructible subset of a constructible subspace `E`
is constructible. The canonical public surface uses the subtype inclusion `Subtype.val : E → X`
rather than a separate coercion wrapper. -/
theorem IsConstructible.image_subtypeVal_of_isConstructible
    (hF : IsConstructible F) (hE : IsConstructible E) :
    IsConstructible (Subtype.val '' F) := by
  -- Decompose the ambient constructible set `E` into finitely many locally closed pieces `U \ V`.
  obtain ⟨ι, hι, Z, hZ, hcover⟩ := exists_finite_iUnion_eq_retrocompact_open_sdiff hE
  letI := hι
  letI : PrespectralSpace E := prespectralSpace_subtype_of_isConstructible hE
  have hPiece :
      ∀ i, IsConstructible ((fun y : E ↓∩ Z i ↦ (y : X)) ''
        ((((E ↓∩ Z i) ↓∩ F) : Set (E ↓∩ Z i)))) := by
    intro i
    obtain ⟨U, V, hU_open, hU_retro, hV_open, hV_retro, hZi_eq⟩ := hZ i
    have hZi_constructible : IsConstructible (Z i) := by
      -- Each cover piece is constructible because it is a difference of open retrocompact sets.
      simpa [hZi_eq] using
        (hU_retro.isConstructible hU_open).sdiff (hV_retro.isConstructible hV_open)
    have hEi : IsConstructible (E ↓∩ Z i) :=
      hZi_constructible.preimage_subtypeVal_of_isConstructible hE
    have hFi : IsConstructible ((E ↓∩ Z i) ↓∩ F) :=
      -- Restrict `F` from `E` to the constructible piece `E ∩ Z i`.
      hF.preimage_subtypeVal_of_isConstructible hEi
    have hZi_subset : Z i ⊆ E := by
      intro x hx
      rw [hcover]
      exact mem_iUnion_of_mem i hx
    let e : (E ↓∩ Z i) ≃ₜ Z i :=
      { toEquiv :=
          { toFun := fun x ↦ ⟨x.1.1, x.2⟩
            invFun := fun z ↦ ⟨⟨z.1, hZi_subset z.2⟩, z.2⟩
            left_inv := by
              intro x
              cases x with
              | mk x hx =>
                  cases x with
                  | mk x hxE => rfl
            right_inv := by
              intro z
              cases z with
              | mk z hz => rfl }
        continuous_toFun := by
          -- Both directions only forget or restore redundant subtype data.
          fun_prop
        continuous_invFun := by
          fun_prop }
    let e' : (E ↓∩ Z i) ≃ₜ ↥(U \ V) := e.trans (Homeomorph.ofEqSubtypes hZi_eq)
    have hFi' : IsConstructible (e' '' (((E ↓∩ Z i) ↓∩ F) : Set (E ↓∩ Z i))) :=
      -- Transport the trace of `F` across the canonical identification with the ambient piece.
      hFi.image_of_isOpenEmbedding e'.isOpenEmbedding
        (by simpa using (IsRetrocompact.univ : IsRetrocompact (range e')))
    -- The reduced `U \ V` case now places this transported trace back inside `X`.
    simpa [e', e, Set.image_image] using
      image_subtypeVal_of_retrocompact_open_sdiff hU_open hU_retro hV_open hV_retro hFi'
  have hUnion :
      IsConstructible (⋃ i, ((fun y : E ↓∩ Z i ↦ (y : X)) ''
        ((((E ↓∩ Z i) ↓∩ F) : Set (E ↓∩ Z i))))) :=
    IsConstructible.iUnion hPiece
  have hEq :
      (Subtype.val '' F) = ⋃ i, ((fun y : E ↓∩ Z i ↦ (y : X)) ''
        ((((E ↓∩ Z i) ↓∩ F) : Set (E ↓∩ Z i)))) := by
    -- Reassemble the ambient image of `F` from the images of its traces on the finite cover.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyCover : y.1 ∈ ⋃ i, Z i := by
        simpa [hcover] using y.2
      rcases mem_iUnion.1 hyCover with ⟨i, hi⟩
      refine mem_iUnion.2 ⟨i, ?_⟩
      exact ⟨⟨y, hi⟩, hy, rfl⟩
    · intro hx
      rcases mem_iUnion.1 hx with ⟨i, hx⟩
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y.1, hy, rfl⟩
  rw [hEq]
  exact hUnion

end

end Topology

/-! ### Lemma_5_15_13 (from Chap05) -/
universe u

open Set TopologicalSpace Topology

namespace Topology

section

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] {T : Set X}

/- Domain-style sampling for compact locally closed subsets with retrocompact complement:
- core/canonical owner declarations inspected:
  `Topology.IsConstructible`,
  `PrespectralSpace.exists_isCompact_and_isOpen_between`,
  `IsCompact.isConstructible`,
  `IsConstructible.sdiff`
- target layer here: `source-facing`. This item adds the extra source content that a compact
  locally closed subset with retrocompact complement is constructible, so it should stay as a
  theorem rather than collapse to a recall.

Best owner abstraction: `Topology.IsConstructible` is the canonical owner predicate, and the
source-facing theorem is most naturally attached to the primitive hypothesis `IsLocallyClosed T`
rather than kept as a standalone wrapper theorem.

Primitive data for the statement are exactly the locally closed subset `T`, its compactness, and
the retrocompactness of `Tᶜ`. The compact open neighborhood `U` and the auxiliary open
compact subset `V` are derived proof data from the prespectral owner API and should remain
internal.
-/

-- Proof sketch: choose a compact open `U` with `T ⊆ U ⊆ coborder T`, so `T = U ∩ closure T`.
-- Then `V = U ∩ Tᶜ` is a compact open subset of `X`, and inside `U` one has
-- `V = U ∩ (closure T)ᶜ`. Hence `T = U \ V`, a difference of constructible sets.
/-- Lemma 5.15.13: let `X` be a quasi-compact topological space having a basis consisting of
quasi-compact opens such that the intersection of any two quasi-compact opens is quasi-compact.
Let `T ⊆ X` be a locally closed subset such that `T` is quasi-compact and `Tᶜ` is retrocompact in
`X`. Then `T` is constructible in `X`.

The ambient quasi-compactness hypothesis from the source is redundant for this conclusion, so the
Lean statement keeps only the hypotheses actually used by the proof. -/
theorem IsLocallyClosed.isConstructible_of_isCompact_of_retrocompact_compl
    (hT_loc : IsLocallyClosed T) (hT_compact : IsCompact T) (hTc_retro : IsRetrocompact Tᶜ) :
    IsConstructible T := by
  obtain ⟨U, hU_compact, hU_open, hTU, hUcob⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hT_compact hT_loc.isOpen_coborder
      subset_coborder
  let V : Set X := U ∩ Tᶜ
  have hV_eq : V = U ∩ (closure T)ᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      have hxCob : x ∈ T ∪ (closure T)ᶜ := by
        simpa [coborder_eq_union_closure_compl] using hUcob hx.1
      rcases hxCob with hxT | hxclosure
      · exact (hx.2 hxT).elim
      · exact hxclosure
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hxT
      exact hx.2 (subset_closure hxT)
  have hV_open : IsOpen V := by
    rw [hV_eq]
    exact hU_open.inter isClosed_closure.isOpen_compl
  have hV_compact : IsCompact V := by
    simpa [V, inter_left_comm, inter_comm, inter_assoc] using hTc_retro hU_compact hU_open
  have hU_constructible : IsConstructible U := hU_compact.isConstructible hU_open
  have hV_constructible : IsConstructible V := hV_compact.isConstructible hV_open
  have hT_eq : T = U \ V := by
    ext x
    constructor
    · intro hx
      refine ⟨hTU hx, ?_⟩
      simp [V, hx]
    · intro hx
      by_contra hxT
      exact hx.2 (by simpa [V, hxT] using hx.1)
  simpa [hT_eq] using hU_constructible.sdiff hV_constructible

end

end Topology

/-! ### Lemma_5_15_14 (from Chap05) -/
universe u v

open Set TopologicalSpace Topology
open scoped Set.Notation

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X]

/- Domain-style sampling for constructibility on finite constructible covers:
- primary domain: constructible subsets of prespectral spaces and their behavior under subtype
  restriction and re-embedding;
- sampled declarations:
  `Topology.IsConstructible.iUnion`,
  `Topology.IsConstructible.preimage_subtypeVal_of_isConstructible`,
  `Topology.IsConstructible.image_subtypeVal_of_isConstructible`,
  `Subtype.image_preimage_val`;
- best owner abstraction: `Topology.IsConstructible` is the owner predicate; the finite-cover
  reconstruction is derived API built from the subtype pullback/image lemmas and finite union;
- primitive-vs-derived split:
  primitive data: the finite constructible family `Z`, the covering inclusion of `E`, and the
    constructible traces `Z i ↓∩ E`;
  derived API: the ambient pieces `Subtype.val '' (Z i ↓∩ E) = Z i ∩ E` and the reconstruction
    `⋃ i, Z i ∩ E = E`.

Layer triage:
- `source-facing`: Lemma 5.15.14, the finite constructible-cover locality statement;
- `core/canonical`: `Topology.IsConstructible`;
- `bridge/view`: the subtype inclusion `Subtype.val : Z i → X` together with
  `Subtype.image_preimage_val`.
-/

-- Proof sketch: apply Lemma `5.15.11` to restrict a constructible subset of `X` to each
-- constructible covering piece. Conversely, use Lemma `5.15.12` to view each constructible trace
-- as a constructible subset of `X`, then recover `E` as the finite union of those pieces over a
-- finite constructible cover of `E`.
/-- Lemma 5.15.14: in a space whose quasi-compact opens form a basis, equivalently
`[PrespectralSpace X]`, a subset `E ⊆ X` is
constructible iff its trace on each member of a finite constructible cover of `E` is constructible
in that member. -/
theorem isConstructible_iff_forall_preimage_subtypeVal_of_finite_constructible_cover
    {ι : Type v} [Finite ι] (Z : ι → Set X) (hZ : ∀ i, IsConstructible (Z i)) {E : Set X}
    (hcover : E ⊆ ⋃ i, Z i) :
    IsConstructible E ↔ ∀ i, IsConstructible (Z i ↓∩ E) := by
  constructor
  · intro hE i
    exact hE.preimage_subtypeVal_of_isConstructible (hZ i)
  · intro hE
    have hUnion : IsConstructible (⋃ i, Z i ∩ E) :=
      IsConstructible.iUnion fun i ↦ by
        simpa [Subtype.image_preimage_val] using
          (hE i).image_subtypeVal_of_isConstructible (hZ i)
    have hcover' : (⋃ i, Z i) ∩ E = E := by
      ext x
      constructor
      · intro hx
        exact hx.2
      · intro hx
        exact ⟨hcover hx, hx⟩
    simpa [← iUnion_inter, hcover'] using hUnion

/-- Textbook cover-of-`X` corollary of Lemma 5.15.14. -/
theorem isConstructible_iff_forall_preimage_subtypeVal_of_finite_constructible_cover_of_iUnion_eq_univ
    {ι : Type v} [Finite ι] (Z : ι → Set X) (hZ : ∀ i, IsConstructible (Z i))
    (hcover : (⋃ i, Z i) = (univ : Set X)) {E : Set X} :
    IsConstructible E ↔ ∀ i, IsConstructible (Z i ↓∩ E) := by
  refine isConstructible_iff_forall_preimage_subtypeVal_of_finite_constructible_cover Z hZ ?_
  intro x hx
  simp [hcover]

/-! ### Lemma_5_15_15 (from Chap05) -/
universe u

open Set Topology TopologicalSpace
open scoped Set.Notation

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for dense traces on irreducible subspaces:
- primary domain: irreducible subsets, generic points, dense traces, and finite unions of locally
  closed subsets;
- sampled canonical declarations:
  `IsGenericPoint.mem_open_set_iff`,
  `IsGenericPoint.mem_closed_set_iff`,
  `IsFiniteUnionOfLocallyClosed.exists_eq_iUnion`,
  `Set.preimage_val_eq_univ_of_subset`,
  `IsLocallyClosed.isOpen_preimage_val_closure`;
- best owner abstractions: `IsGenericPoint` owns the pointwise generic-point criterion, while
  `IsIrreducible` is the natural owner for the irreducible-subspace dense/open-dense dichotomy;
- primitive-vs-derived split: the primitive inputs are the irreducible set or generic point,
  together with the finite locally closed decomposition of `E`; the open dense trace is derived
  data and should be exposed via `Opens Z`, with the trace written through the canonical subtype
  notation `Z ↓∩ E` rather than raw subtype preimages.

Layer triage:
- `source-facing`: the irreducible-subspace dense/open-dense criterion;
- `core/canonical`: `IsIrreducible`, `IsGenericPoint`, and `Opens`;
- `bridge/view`: the canonical subtype trace `Z ↓∩ E` together with the finite locally closed
  decomposition supplied by `IsFiniteUnionOfLocallyClosed.exists_eq_iUnion`.
-/

-- Proof sketch: write `E ∩ Z` as a finite union of locally closed subsets of the irreducible
-- subspace `Z`; one dense locally closed piece is then open in its closure, hence yields an open
-- dense subset of `Z`.
/-- Helper for Lemma 5.15.15: a locally closed subset stays locally closed after restricting to a
subspace. -/
lemma trace_piece_isLocallyClosed {Z A : Set X} (hA : IsLocallyClosed A) :
    IsLocallyClosed (Z ↓∩ A) := by
  -- Pull the locally closed subset back along the subtype map `Z → X`.
  simpa using hA.preimage continuous_subtype_val

/-- Helper for Lemma 5.15.15: in an irreducible space, a dense finite union has a dense member. -/
lemma exists_dense_piece_of_dense_iUnion {Y : Type u} [TopologicalSpace Y] [IrreducibleSpace Y]
    {n : ℕ} {T : Fin n → Set Y} (hT_dense : Dense (⋃ i, T i)) :
    ∃ i, Dense (T i) := by
  classical
  let s : Finset (Set Y) := Finset.univ.image fun i ↦ closure (T i)
  have hs_cover : (univ : Set Y) ⊆ ⋃₀ (s : Set (Set Y)) := by
    -- Rewrite density of the union as a finite closed cover of the whole space by the closures.
    rw [← hT_dense.closure_eq, closure_iUnion_of_finite]
    simp [s]
  obtain ⟨W, hW_mem, hW_cover⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp (IrreducibleSpace.isIrreducible_univ Y) s
      (fun W hW ↦ by
        rcases Finset.mem_image.mp hW with ⟨i, -, rfl⟩
        exact isClosed_closure)
      hs_cover
  rcases Finset.mem_image.mp hW_mem with ⟨i, -, rfl⟩
  -- The chosen closure contains `univ`, so that piece is dense.
  have hTi_closure : closure (T i) = (univ : Set Y) :=
    Set.Subset.antisymm (subset_univ _) hW_cover
  have hTi_dense : Dense (T i) := dense_iff_closure_eq.2 hTi_closure
  exact ⟨i, hTi_dense⟩

/-- Helper for Lemma 5.15.15: a dense locally closed subset is already an open dense subset. -/
lemma exists_open_dense_subset_of_dense_isLocallyClosed {Y : Type u} [TopologicalSpace Y]
    {s : Set Y} (hs_dense : Dense s) (hs_lc : IsLocallyClosed s) :
    ∃ U : Opens Y, Dense (U : Set Y) ∧ (U : Set Y) ⊆ s := by
  have hs_open : IsOpen s := by
    -- A locally closed set is open in its closure, and density identifies that closure with `univ`.
    simpa [hs_dense.closure_eq] using hs_lc.isOpen_preimage_val_closure
  let U : Opens Y := ⟨s, hs_open⟩
  -- Package the set itself as the required open dense subset.
  exact ⟨U, by simpa [U] using hs_dense, subset_rfl⟩

/-- Lemma 5.15.15: if `Z` is irreducible and `E` is a finite union of locally closed subsets of
`X`, then `E ∩ Z` contains an open dense subset of `Z` if and only if `E ∩ Z` is dense in `Z`. -/
theorem IsIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed
    {Z E : Set X} (hZ : IsIrreducible Z) (hE : IsFiniteUnionOfLocallyClosed E) :
    (∃ U : Opens Z, Dense (U : Set Z) ∧ (U : Set Z) ⊆ Z ↓∩ E) ↔ Dense (Z ↓∩ E) := by
  constructor
  · rintro ⟨U, hU_dense, hU_subset⟩
    -- An open dense subtrace is in particular a dense subset of the whole trace.
    exact Dense.mono hU_subset hU_dense
  · intro hZE_dense
    classical
    letI : IrreducibleSpace Z := Subtype.irreducibleSpace hZ
    obtain ⟨n, S, hS_lc, hE_eq⟩ := hE.exists_eq_iUnion
    let T : Fin n → Set Z := fun i ↦ Z ↓∩ S i
    have hT_lc : ∀ i, IsLocallyClosed (T i) := by
      intro i
      -- Restrict each ambient locally closed piece to the irreducible subtype `Z`.
      exact trace_piece_isLocallyClosed (hS_lc i)
    have hT_dense : Dense (⋃ i, T i) := by
      -- Normalize the trace of the finite union into the union of the trace pieces.
      simpa [T, hE_eq] using hZE_dense
    obtain ⟨i, hTi_dense⟩ := exists_dense_piece_of_dense_iUnion hT_dense
    obtain ⟨U, hU_dense, hU_subset⟩ :=
      exists_open_dense_subset_of_dense_isLocallyClosed hTi_dense (hT_lc i)
    refine ⟨U, hU_dense, ?_⟩
    -- The dense open piece sits inside one trace component, hence inside the full trace.
    exact hU_subset.trans <| by
      simpa [T, hE_eq] using (Set.subset_iUnion T i)

-- Proof sketch: if `ξ` is a generic point of `Z`, then membership `ξ ∈ E` is equivalent to the
-- trace `E ∩ Z` being dense in `Z`; combine the generic-point characterization of dense subsets of
-- an irreducible space with the locally closed decomposition of `E`.
/-- For a generic point `ξ` of `Z`, a finite union of locally closed subsets has dense trace on
`Z` exactly when `ξ` belongs to it. -/
theorem IsGenericPoint.dense_preimage_iff_mem_of_isFiniteUnionOfLocallyClosed
    {Z E : Set X} {ξ : X} (hξ : IsGenericPoint ξ Z) (hE : IsFiniteUnionOfLocallyClosed E) :
    Dense (Z ↓∩ E) ↔ ξ ∈ E := by
  let ξZ : Z := ⟨ξ, hξ.mem⟩
  have hξZ : IsGenericPoint ξZ (Set.univ : Set Z) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simpa [subtype_specializes_iff] using
      (hξ.specializes_iff_mem : ξ ⤳ (y : X) ↔ (y : X) ∈ Z)
  constructor
  · intro hDense
    obtain ⟨U, hU_dense, hU_subset⟩ :=
      (hξ.isIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed hE).2
        hDense
    haveI : Nonempty Z := ⟨ξZ⟩
    have hU_nonempty : (U : Set Z).Nonempty := hU_dense.nonempty
    have hξU : ξZ ∈ U := by
      exact (hξZ.mem_open_set_iff U.2).2 (by simpa using hU_nonempty)
    exact hU_subset hξU
  · intro hξE
    rw [Subtype.dense_iff]
    have hξ_closure : ξ ∈ closure (Z ∩ E) := subset_closure ⟨hξ.mem, hξE⟩
    simpa [Subtype.image_preimage_val] using
      (hξ.mem_closed_set_iff isClosed_closure).1 hξ_closure
