import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Constructible
import Mathlib.Topology.JacobsonSpace

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_12_1 (from Chap05) -/
universe u v

open Set

/- Domain-style sampling for quasi-compactness in topological spaces:
- primary domain: compactness/spectrality for spaces, maps, and subsets
- same-domain declarations inspected:
  `CompactSpace`,
  `isCompact_iff_finite_subcover`,
  `IsSpectralMap`,
  `IsRetrocompact_iff_isSpectralMap_subtypeVal`
- best owner abstractions: `CompactSpace`, `IsSpectralMap`, `IsRetrocompact`

Layer triage:
- `source-facing`: the whole-space finite-subcover characterization
- `core/canonical`: `CompactSpace`, `IsSpectralMap`, `IsRetrocompact`
- `bridge/view`: the whole-space specialization of `isCompact_iff_finite_subcover`

Primitive data belongs to the owner abstractions above. This file should not keep parallel local
wrappers when the source item is only recalling those canonical notions.
-/

section

variable {X : Type u} [TopologicalSpace X]

/- Definition 5.12.1 (space): the Stacks notion of a quasi-compact topological space is the
canonical typeclass `CompactSpace`. -/
recall CompactSpace

/-- Definition 5.12.1 (space): a topological space is quasi-compact if and only if every open cover
admits a finite subcover. -/
theorem quasiCompactSpace_iff_finite_subcover :
    CompactSpace X ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → univ ⊆ ⋃ i, U i → ∃ s : Finset ι, univ ⊆ ⋃ i ∈ s, U i := by
  rw [← isCompact_univ_iff, isCompact_iff_finite_subcover]

end

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Definition 5.12.1 (map): the Stacks notion of a quasi-compact map is the canonical predicate
`IsSpectralMap`. -/
recall IsSpectralMap

/- Source-facing unpacking: `IsSpectralMap f` is by definition the conjunction of continuity of
`f` and compactness of preimages of compact open subsets. No parallel wrapper theorem is needed,
since this item is only recalling the canonical owner predicate. -/

end

section

variable {X : Type u} [TopologicalSpace X]

/- Definition 5.12.1 (subset): the Stacks notion of a retrocompact subset is the canonical
predicate `IsRetrocompact`. -/
recall IsRetrocompact

/- Companion recall: retrocompactness of a subset is equivalent to the subtype inclusion being a
spectral map. -/
recall IsRetrocompact_iff_isSpectralMap_subtypeVal

end

/-! ### Lemma_5_12_2 (from Chap05) -/
/- Domain-style sampling for quasi-compact maps in topological spaces:
- owner declarations: `IsSpectralMap`, `IsSpectralMap.comp`, `IsRetrocompact`
- chapter owner recall: `Definition_5_12_1` identifies the Stacks quasi-compact-map notion with
  `IsSpectralMap`

Layer triage:
- `source-facing`: quasi-compact maps are stable under composition
- `core/canonical`: `IsSpectralMap`
- `bridge/view`: none needed here, since mathlib already provides the exact composed-map theorem

Primitive data is only the owner predicate `IsSpectralMap`; closure under composition is derived
API from the canonical theorem `IsSpectralMap.comp`, so this file should not introduce a parallel
local wrapper.
-/

/- Lemma 5.12.2: a composition of quasi-compact maps is quasi-compact. Via
Definition 5.12.1, the Stacks quasi-compact-map notion is the canonical mathlib predicate
`IsSpectralMap`, and this is exactly `IsSpectralMap.comp`. -/
recall IsSpectralMap.comp

/-! ### Lemma_5_12_3 (from Chap05) -/
/- Domain-style sampling for quasi-compactness of closed subsets:
- whole-space owner: `CompactSpace`
- subset-level canonical predicate: `IsCompact`
- canonical theorem for the present lemma: `IsClosed.isCompact`
- companion reverse direction in the Hausdorff case: `IsCompact.isClosed`

Layer triage:
- `source-facing`: a closed subset of a quasi-compact space is quasi-compact
- `core/canonical`: whole-space quasi-compactness as `CompactSpace`
- `bridge/view`: subset quasi-compactness as `IsCompact`, derived from the owner theorem

Primitive data here are only the ambient `CompactSpace X` instance and the hypothesis
`IsClosed E`; the subset compactness conclusion is derived API, so this file should remain a
direct recall of `IsClosed.isCompact` rather than introducing any parallel local wrapper.
-/

section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/- Lemma 5.12.3: via Definition 5.12.1, quasi-compactness of spaces is the canonical owner
`CompactSpace`, and the closed-subset consequence is exactly the canonical theorem
`IsClosed.isCompact`. -/
recall IsClosed.isCompact

end

/-! ### Lemma_5_12_4 (from Chap05) -/
universe u

/-
Domain-style sampling for quasi-compact subsets in Hausdorff spaces:
- whole-space owner: `CompactSpace`
- subset-level canonical predicate: `IsCompact`
- canonical closedness theorem: `IsCompact.isClosed`
- canonical separation theorem: `SeparatedNhds.of_isCompact_isCompact`

Layer triage:
- `source-facing`: a quasi-compact subset of a Hausdorff space is closed, and disjoint
  quasi-compact subsets admit disjoint open neighborhoods
- `core/canonical`: `IsCompact` in a `T2Space`
- `bridge/view`: `SeparatedNhds` as the owner-style formulation of disjoint open neighborhoods

Primitive data here are only the ambient topology and Hausdorff structure. The closedness and
separation conclusions are derived API from the canonical compactness owner, so this file should
stay a direct recall of the upstream theorems rather than reintroducing local wrapper lemmas.
-/
section

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/- Lemma 5.12.4: in a Hausdorff space, every quasi-compact subset is closed. In mathlib the
Stacks quasi-compactness condition for subsets is the canonical predicate `IsCompact`, and the
statement is exactly the canonical theorem `IsCompact.isClosed`. -/
recall IsCompact.isClosed

/- Companion recall: in a Hausdorff space, disjoint quasi-compact subsets admit disjoint open
neighborhoods. In mathlib this is the canonical separation statement
`SeparatedNhds.of_isCompact_isCompact`; by definition, `SeparatedNhds E F` is exactly the
existence of disjoint open neighborhoods of `E` and `F`. -/
recall SeparatedNhds.of_isCompact_isCompact

end

/-! ### Lemma_5_12_5 (from Chap05) -/
universe u

/- Domain-style sampling for quasi-compact subsets in compact Hausdorff spaces:
- same-domain declarations inspected: `CompactSpace`, `IsClosed.isCompact`, `IsCompact.isClosed`
- chapter context checked: `Lemma_5_12_3` and `Lemma_5_12_4` are `recall`-only, so they do not
  supply a reusable project-level `↔` declaration
- best owner abstractions: whole-space `CompactSpace`, subset predicates `IsClosed`, `IsCompact`

Layer triage:
- `source-facing`: the Stacks equivalence between closedness and quasi-compactness for subsets of a
  quasi-compact Hausdorff space
- `core/canonical`: `CompactSpace X` for the ambient space and `IsCompact` for subset
  quasi-compactness
- `bridge/view`: the equivalence obtained by pairing the two canonical implications above

Primitive data here are only the ambient `CompactSpace X` and `T2Space X` structures. The two
directions are already canonical theorems, so this file should keep only the source-facing bridge
statement rather than introducing any parallel wrapper owner.
-/

section

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Lemma 5.12.5: for a subset `E` of a quasi-compact Hausdorff space `X`, the conditions (a) `E`
is closed in `X` and (b) `E` is quasi-compact are equivalent. Via Definition 5.12.1, subset
quasi-compactness is the canonical predicate `IsCompact`, and this lemma is the source-facing
bridge obtained by combining `IsClosed.isCompact` and `IsCompact.isClosed`. -/
theorem isClosed_iff_isCompact (E : Set X) : IsClosed E ↔ IsCompact E :=
  ⟨IsClosed.isCompact, IsCompact.isClosed⟩

end

/-! ### Lemma_5_12_6 (from Chap05) -/
/- Domain-style sampling for finite-intersection compactness in topological spaces:
- primary domain: compactness of spaces and closed-set families
- same-domain declarations inspected:
  `CompactSpace`,
  `isCompact_univ`,
  `IsCompact.inter_iInter_nonempty`,
  `CompactSpace.iInter_nonempty`
- best owner abstraction: `CompactSpace`

Layer triage:
- `source-facing`: a family of closed subsets with the finite intersection property
- `core/canonical`: compactness of the ambient space
- `bridge/view`: the specialization from `isCompact_univ` to the whole-space theorem

Primitive data here is only the closed family together with its finite-intersection nonemptiness.
No local wrapper or parallel theorem should be kept, because the owner theorem already has the
exact source-facing interface.
-/

/- Lemma 5.12.6: in a quasi-compact topological space, a family of closed subsets with the finite
intersection property has nonempty total intersection. Via Definition 5.12.1, quasi-compact spaces
are `CompactSpace`, and this is exactly the canonical theorem `CompactSpace.iInter_nonempty`. -/
recall CompactSpace.iInter_nonempty

/-! ### Lemma_5_12_7 (from Chap05) -/
open Set Topology TopologicalSpace

universe u v

/- Domain-style sampling for quasi-compact images in topological spaces:
- owner declarations: `CompactSpace`, `IsSpectralMap`, `IsRetrocompact`
- canonical range compactness: `isCompact_range`
- canonical subset bridge: `IsRetrocompact_iff_isSpectralMap_subtypeVal`

Layer triage:
- `source-facing`: Lemma 5.12.7 identifies compactness and retrocompactness consequences for the
  image of a quasi-compact map
- `core/canonical`: `CompactSpace`, `IsSpectralMap`, `IsRetrocompact`
- `bridge/view`: the range inclusion `Set.range f → Y`

Primitive data is the owner predicate `IsSpectralMap f`; retrocompactness of `range f` is derived
through the canonical subtype-inclusion bridge.
-/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Canonical recall: if `X` is quasi-compact, then the image `f(X)` is quasi-compact. This is
exactly the canonical theorem `isCompact_range`. -/
recall isCompact_range

-- Proof sketch: apply `IsRetrocompact_iff_isSpectralMap_subtypeVal` to the subtype inclusion of
-- `range f` and use `hf` to show compactness of preimages of compact open subsets.
/-- Lemma 5.12.7: if `f` is quasi-compact, then the image `f(X)` is retrocompact. -/
theorem IsSpectralMap.isRetrocompact_range (hf : IsSpectralMap f) :
    IsRetrocompact (range f) := by
  -- Rewrite retrocompactness of the image as spectrality of its subtype inclusion.
  rw [IsRetrocompact_iff_isSpectralMap_subtypeVal]
  refine ⟨continuous_subtype_val, ?_⟩
  intro t htOpen htCompact
  -- Move compactness on the subtype back to `Y`, where the source identity is visible.
  rw [IsEmbedding.subtypeVal.isCompact_iff, Set.image_preimage_eq_inter_range,
    Subtype.range_coe_subtype, Set.setOf_mem_eq, Set.inter_comm]
  -- The source proof now applies verbatim: compactness of `f ⁻¹' t` maps to compactness of
  -- `f '' (f ⁻¹' t) = t ∩ range f`.
  have hImage : IsCompact (f '' (f ⁻¹' t)) :=
    (hf.isCompact_preimage_of_isOpen htOpen htCompact).image hf.continuous
  simpa [Set.image_preimage_eq_inter_range, Set.inter_comm] using hImage

end

/-! ### Lemma_5_12_8 (from Chap05) -/
universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T0Space X]

/-
Domain-style sampling for closed points in compact `T0` spaces:
- owner declaration: `closedPoints`
- canonical membership API: `mem_closedPoints_iff`
- canonical existence theorem on compact `T0` spaces: `IsClosed.exists_closed_singleton`

Layer triage:
- `source-facing`: existence of a closed point in a nonempty quasi-compact Kolmogorov space
- `core/canonical`: the owner set `closedPoints X`
- `bridge/view`: specialize `IsClosed.exists_closed_singleton` to `univ`

Primitive data is the owner `closedPoints X`; the existence statement is derived by the canonical
compact-`T0` singleton theorem rather than by a parallel local construction.
-/

-- Proof sketch: specialize `IsClosed.exists_closed_singleton` to the closed subset `univ` and
-- rewrite the resulting closed-singleton witness as membership in `closedPoints X`.
/-- Lemma 5.12.8: a nonempty quasi-compact Kolmogorov space has a closed point. -/
theorem exists_closed_point [Nonempty X] : (closedPoints X).Nonempty := by
  simpa [Set.nonempty_def, mem_closedPoints_iff] using
    isClosed_univ.exists_closed_singleton
      (Set.univ_nonempty : Set.Nonempty (Set.univ : Set X))

/-! ### Lemma_5_12_9 (from Chap05) -/
universe u

open Set

section

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T0Space X]

/-
Domain-style sampling for closed points in compact `T0` spaces:
- owner set: `closedPoints X`
- canonical membership API: `mem_closedPoints_iff`
- subset compactness owner: `isCompact_of_finite_subcover`
- closed-point existence in nonempty closed sets: `IsClosed.exists_closed_singleton`

Layer triage:
- `source-facing`: compactness of the closed-point subset in a quasi-compact Kolmogorov space
- `core/canonical`: the owner set `closedPoints X` together with the subset compactness predicate
  `IsCompact`
- `bridge/view`: an open cover of `closedPoints X` covers all of `X`, because any nonempty closed
  complement would contain a closed point

Primitive data is only the owner set `closedPoints X`; compactness is derived through the canonical
finite-subcover interface, so this file should not introduce any parallel wrapper around closed
points or compactness.
-/

-- Proof sketch: if an open cover of `closedPoints X` failed to cover `X`, its closed complement
-- `Z` would be nonempty. Applying `IsClosed.exists_closed_singleton` to `Z` produces a closed
-- point of `X` lying in `Z`, contradicting the cover hypothesis. Thus the same opens cover all of
-- `X`, and compactness of `X` yields a finite subcover.
/-- Lemma 5.12.9: in a quasi-compact Kolmogorov space, the subset `closedPoints X` of closed
points is compact. -/
theorem isCompact_closedPoints : IsCompact (closedPoints X) := by
  refine isCompact_of_finite_subcover fun U hU hcover ↦ ?_
  -- First extend an open cover of `closedPoints X` to an open cover of all of `X`.
  have hXcover : (univ : Set X) ⊆ ⋃ i, U i := by
    by_contra hXcover
    rw [not_subset] at hXcover
    obtain ⟨x, -, hx⟩ := hXcover
    -- A point outside the union lies in the closed complement, which contains a closed point.
    obtain ⟨y, hy, hyclosed⟩ :=
      (isOpen_iUnion hU).isClosed_compl.exists_closed_singleton ⟨x, hx⟩
    -- That closed point belongs to `closedPoints X`, so the cover hypothesis forces it back
    -- into the union, contradicting membership in the complement.
    exact hy (hcover <| mem_closedPoints_iff.2 hyclosed)
  -- Compactness of `X` now gives a finite subcover, and restricting it preserves coverage of
  -- `closedPoints X`.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hXcover
  exact ⟨t, (subset_univ _).trans ht⟩

end

/-! ### Lemma_5_12_10 (from Chap05) -/
universe u

open Set

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [PrespectralSpace X]
  [QuasiSeparatedSpace X]

namespace PrespectralSpace

/- Domain-style sampling:
- primary domain: connected components and clopen separation in compact prespectral
  quasi-separated spaces;
- same-domain owner declarations inspected:
  `PrespectralSpace.isTopologicalBasis`,
  `QuasiSeparatedSpace.inter_isCompact`,
  `connectedComponent_subset_iInter_isClopen`,
  `connectedComponent_eq_iInter_isClopen`;
- best owner abstraction: `connectedComponent x`, with the compact-open hypotheses carried by the
  canonical ambient owners `PrespectralSpace` and `QuasiSeparatedSpace`, not by a parallel
  basis-data wrapper.

Layer triage:
- `source-facing`: the Stacks lemma identifying `connectedComponent x` with the intersection of
  the clopen neighborhoods of `x` under the weaker prespectral/quasi-separated hypotheses.
- `core/canonical`: `connectedComponent`, `IsClopen`, `PrespectralSpace`, `QuasiSeparatedSpace`.
- `bridge/view`: the clopen-superset reformulation is derivable from the source-facing theorem and
  `connectedComponent_subset_iInter_isClopen`, so it is not kept as separate public API here.

Primitive data is only the point `x` together with the ambient owner instances
`[CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]`. The basis and compact-intersection
machinery is derived from those owners, so it should not remain encoded in the public theorem
name.
-/

-- Proof sketch: the inclusion from the connected component into every clopen neighbourhood is
-- canonical. For the reverse inclusion, let `S` be the intersection of all clopen neighbourhoods
-- of `x`; using compactness of closed subsets, the basis of compact opens, and compactness of
-- intersections of compact opens, show that any clopen decomposition of `S` yields a clopen
-- neighbourhood of `x` cutting off one side, so `S` is connected and hence equals
-- `connectedComponent x`.
/-
This is source-facing rather than a recall: mathlib's global theorem
`connectedComponent_eq_iInter_isClopen` assumes `[T2Space X]`, while the Stacks lemma keeps the
weaker `[PrespectralSpace X] [QuasiSeparatedSpace X]` hypotheses. The canonical forward inclusion is
still reused directly from mathlib; only the reverse inclusion is specific to this source item.
-/
/-- Lemma 5.12.10: in a quasi-compact topological space with a basis of quasi-compact opens whose
pairwise intersections are quasi-compact, the connected component containing `x` is the
intersection of all open and closed subsets containing `x`.

This is stated using the canonical typeclass interface
`[PrespectralSpace X] [QuasiSeparatedSpace X]` for the basis and intersection hypotheses.
The point-based clopen-neighborhood surface is the canonical owner-facing interface; equivalent
reformulations indexed by clopen supersets of `connectedComponent x` are derived views and should
be downstream bridges, not parallel owners. -/
theorem connectedComponent_eq_iInter_isClopen
    (x : X) :
    connectedComponent x = ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, Z := by
  classical
  apply Subset.antisymm connectedComponent_subset_iInter_isClopen
  set S : Set X := ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, Z with hS
  have hxS : x ∈ S := by
    rw [hS]
    exact mem_iInter.2 fun Z ↦ Z.2.2
  refine IsPreconnected.subset_connectedComponent ?_ hxS
  have hS_closed : IsClosed S := by
    rw [hS]
    exact isClosed_iInter fun Z ↦ Z.2.1.isClosed
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hS_closed]
  intro a b ha hb hSab hab
  have hSa_compact : IsCompact (S ∩ a) := (hS_closed.inter ha).isCompact
  have hSb_compact : IsCompact (S ∩ b) := (hS_closed.inter hb).isCompact
  have hSa_subset_bcompl : S ∩ a ⊆ bᶜ := by
    intro y hy hyb
    exact hab.le_bot ⟨hy.2, hyb⟩
  have hSb_subset_acompl : S ∩ b ⊆ aᶜ := by
    intro y hy hya
    exact hab.symm.le_bot ⟨hy.2, hya⟩
  obtain ⟨U, hU_compact, hU_open, hSaU, hUb⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hSa_compact hb.isOpen_compl hSa_subset_bcompl
  obtain ⟨V, hV_compact, hV_open, hSbV, hVa⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hSb_compact ha.isOpen_compl hSb_subset_acompl
  have hS_subset_UV : S ⊆ U ∪ V := by
    intro y hyS
    rcases hSab hyS with hya | hyb
    · exact Or.inl (hSaU ⟨hyS, hya⟩)
    · exact Or.inr (hSbV ⟨hyS, hyb⟩)
  have hSUV_empty : S ∩ (U ∩ V) = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro y hy
    rcases hSab hy.1 with hya | hyb
    · exact hVa hy.2.2 hya
    · exact hUb hy.2.1 hyb
  let K : Set X := (U ∩ V) ∪ (U ∪ V)ᶜ
  have hK_compact : IsCompact K := by
    refine (QuasiSeparatedSpace.inter_isCompact U V hU_open hU_compact hV_open hV_compact).union ?_
    exact (hU_open.union hV_open).isClosed_compl.isCompact
  have hKS_empty : K ∩ S = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro y hy
    rcases hy.1 with hyUV | hyUV
    · have : y ∉ S ∩ (U ∩ V) := by simp [hSUV_empty]
      exact this ⟨hy.2, hyUV⟩
    · exact hyUV (hS_subset_UV hy.2)
  obtain ⟨u, hu⟩ :=
    hK_compact.elim_finite_subfamily_closed
      (fun Z : { Z : Set X // IsClopen Z ∧ x ∈ Z } ↦ (Z : Set X))
      (fun Z ↦ Z.2.1.isClosed) hKS_empty
  let C : Set X := ⋂ Z ∈ u, (Z : Set X)
  have hC_clopen : IsClopen C := isClopen_biInter_finset fun Z _ ↦ Z.2.1
  have hxC : x ∈ C := by
    exact mem_iInter₂.2 fun Z hZ ↦ Z.2.2
  have hKC_empty : K ∩ C = ∅ := by
    simpa [C] using hu
  have hC_subset_UV : C ⊆ U ∪ V := by
    intro y hyC
    by_contra hyUV
    have hyK : y ∈ K := Or.inr <| by simpa using hyUV
    have : y ∈ K ∩ C := ⟨hyK, hyC⟩
    simp [hKC_empty] at this
  have hCUV_empty : C ∩ U ∩ V = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro y hy
    have hyK : y ∈ K := Or.inl ⟨hy.1.2, hy.2⟩
    have : y ∈ K ∩ C := ⟨hyK, hy.1.1⟩
    simp [hKC_empty] at this
  rcases hSab hxS with hxa | hxb
  · have hxU : x ∈ U := hSaU ⟨hxS, hxa⟩
    have hCU_clopen : IsClopen (C ∩ U) :=
      isClopen_inter_of_disjoint_cover_clopen' hC_clopen hC_subset_UV hU_open hV_open hCUV_empty
    have hS_subset_CU : S ⊆ C ∩ U := by
      rw [hS]
      exact iInter_subset (fun Z : { Z : Set X // IsClopen Z ∧ x ∈ Z } ↦ (Z : Set X))
        ⟨C ∩ U, hCU_clopen, ⟨hxC, hxU⟩⟩
    left
    intro y hyS
    have hyCU : y ∈ C ∩ U := hS_subset_CU hyS
    rcases hSab hyS with hya | hyb
    · exact hya
    · exact (hUb hyCU.2 hyb).elim
  · have hxV : x ∈ V := hSbV ⟨hxS, hxb⟩
    have hCVU_empty : C ∩ V ∩ U = ∅ := by
      simpa [inter_assoc, inter_left_comm, inter_comm] using hCUV_empty
    have hCV_clopen : IsClopen (C ∩ V) :=
      isClopen_inter_of_disjoint_cover_clopen' hC_clopen (by simpa [union_comm] using hC_subset_UV)
        hV_open hU_open hCVU_empty
    have hS_subset_CV : S ⊆ C ∩ V := by
      rw [hS]
      exact iInter_subset (fun Z : { Z : Set X // IsClopen Z ∧ x ∈ Z } ↦ (Z : Set X))
        ⟨C ∩ V, hCV_clopen, ⟨hxC, hxV⟩⟩
    right
    intro y hyS
    have hyCV : y ∈ C ∩ V := hS_subset_CV hyS
    rcases hSab hyS with hya | hyb
    · exact (hVa hyCV.2 hya).elim
    · exact hyb

end PrespectralSpace

/-! ### Lemma_5_12_11 (from Chap05) -/
universe u

/-
Domain-style sampling for connected components in compact Hausdorff spaces:
- owner abstraction: `connectedComponent x`
- same-domain declarations inspected:
  `connectedComponent_subset_iInter_isClopen`,
  `connectedComponent_eq_iInter_isClopen`,
  `isTopologicalBasis_isClopen`

Layer triage:
- `source-facing`: the connected component of a point is the intersection of all open-and-closed
  subsets containing that point
- `core/canonical`: mathlib's owner theorem `connectedComponent_eq_iInter_isClopen`
- `bridge/view`: none needed here, since the source statement already matches the canonical owner
  theorem exactly

Primitive data is only the ambient compact Hausdorff space and the point `x`; there is no extra
source-defined wrapper or auxiliary construction. The refined file should therefore remain a direct
recall of the canonical theorem, not a parallel local alias or `_iff` reformulation.
-/

section

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]

/- Lemma 5.12.11: in a quasi-compact Hausdorff space, the connected component of a point is the
intersection of all open and closed subsets containing that point. This is exactly the canonical
mathlib theorem `connectedComponent_eq_iInter_isClopen`. -/
recall connectedComponent_eq_iInter_isClopen (x : X) :
    connectedComponent x = ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, s

end

/-! ### Lemma_5_12_12 (from Chap05) -/
universe u

open Set

section

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [PrespectralSpace X]
  [QuasiSeparatedSpace X] {T : Set X}

/- Domain-style sampling for intersections of clopen supersets and connected-component saturation:
- primary domain: connected components and clopen separation in compact prespectral
  quasi-separated spaces
- same-domain owner declarations inspected:
  `PrespectralSpace.connectedComponent_eq_iInter_isClopen`,
  `IsClopen.connectedComponent_subset`,
  `connectedComponent_subset_iInter_isClopen`,
  `IsClopen.biUnion_connectedComponent_eq`
- best owner abstraction: `connectedComponent x`, with the ambient hypotheses carried by
  `PrespectralSpace` and `QuasiSeparatedSpace`

Layer triage:
- `source-facing`: the subset-level criterion that a set is an intersection of clopen subsets
  exactly when it is closed and a union of connected components
- `core/canonical`: the pointwise owner `connectedComponent x` together with clopen neighborhood
  API
- `bridge/view`: the subset-level `sInter` proof step for the family of all clopen supersets of
  `T`, derived from the pointwise owner

Primitive data are the subset `T`, its closedness, and the component-saturation property
`∀ x ∈ T, connectedComponent x ⊆ T`. The clopen-superset intersection is derived from those data,
so the file should remain a bridge theorem over the connected-component owner rather than
introducing a parallel wrapper notion.
-/

-- Proof sketch: write `T` as an `sInter` of clopen subsets, and use that arbitrary intersections
-- of closed sets are closed.
/-- Lemma 5.12.12 (1): if a subset of a quasi-compact space with a basis of quasi-compact opens
and quasi-compact intersections is an intersection of open and closed subsets, then it is closed.
-/
theorem isClosed_of_isIntersectionOfClopens
    (hT : ∃ S : Set (Set X), (∀ Z ∈ S, IsClopen Z) ∧ T = ⋂₀ S) :
    IsClosed T := by
  rcases hT with ⟨S, hS_clopen, rfl⟩
  -- An intersection of clopen subsets is an intersection of closed subsets.
  exact isClosed_sInter fun Z hZ ↦ (hS_clopen Z hZ).isClosed

-- Proof sketch: every clopen set containing `x` contains the full connected component of `x`; an
-- intersection of such clopen sets is therefore saturated under connected components.
/-- Lemma 5.12.12 (2): if a subset of a quasi-compact space with a basis of quasi-compact opens
and quasi-compact intersections is an intersection of open and closed subsets, then it is a union
of connected components of `X`. -/
theorem connectedComponent_subset_of_isIntersectionOfClopens
    (hT : ∃ S : Set (Set X), (∀ Z ∈ S, IsClopen Z) ∧ T = ⋂₀ S)
    (x : X) (hx : x ∈ T) :
    connectedComponent x ⊆ T := by
  rcases hT with ⟨S, hS_clopen, rfl⟩
  rw [mem_sInter] at hx
  intro y hy
  rw [mem_sInter]
  intro Z hZ
  -- Each clopen factor containing `x` contains the whole connected component of `x`.
  exact (hS_clopen Z hZ).connectedComponent_subset (hx Z hZ) hy

/-- Helper for Lemma 5.12.12: a component-saturated subset is disjoint from the connected
component of any point outside it. -/
lemma disjoint_connectedComponent_of_not_mem
    (hT_components : ∀ y ∈ T, connectedComponent y ⊆ T) {x : X} (hx : x ∉ T) :
    T ∩ connectedComponent x = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro y hy
  -- A point of `T ∩ connectedComponent x` forces `x` back into `T` by component saturation.
  have hxy : connectedComponent y = connectedComponent x := (connectedComponent_eq hy.2).symm
  have hx_component : x ∈ connectedComponent y := by
    rw [hxy]
    exact mem_connectedComponent
  exact hx (hT_components y hy.1 hx_component)

/-- Helper for Lemma 5.12.12: a closed component-saturated subset can be separated from any
outside point by a clopen superset. -/
lemma exists_isClopen_superset_not_mem_of_isClosed_of_component_saturated
    (hT_closed : IsClosed T) (hT_components : ∀ y ∈ T, connectedComponent y ⊆ T)
    {x : X} (hx : x ∉ T) :
    ∃ U : Set X, IsClopen U ∧ T ⊆ U ∧ x ∉ U := by
  classical
  have h_disjoint : T ∩ connectedComponent x = ∅ :=
    disjoint_connectedComponent_of_not_mem hT_components hx
  have h_inter :
      T ∩ ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, (Z : Set X) = ∅ := by
    -- Rewrite the connected component as the intersection of its clopen neighbourhoods.
    simpa [PrespectralSpace.connectedComponent_eq_iInter_isClopen x] using h_disjoint
  obtain ⟨u, hu⟩ :=
    hT_closed.isCompact.elim_finite_subfamily_closed
      (fun Z : { Z : Set X // IsClopen Z ∧ x ∈ Z } ↦ (Z : Set X))
      (fun Z ↦ Z.2.1.isClosed) h_inter
  let V : Set X := ⋂ Z ∈ u, (Z : Set X)
  have hV_clopen : IsClopen V := by
    -- A finite intersection of the chosen clopen neighbourhoods is still clopen.
    exact isClopen_biInter_finset fun Z _ ↦ Z.2.1
  have hxV : x ∈ V := by
    -- Every chosen neighbourhood contains `x`, so their finite intersection does too.
    exact mem_iInter₂.2 fun Z hZ ↦ Z.2.2
  have hTV_empty : T ∩ V = ∅ := by
    simpa [V] using hu
  refine ⟨Vᶜ, hV_clopen.compl, ?_, ?_⟩
  · -- Disjointness of `T` and `V` means `T` lands in the complement of `V`.
    intro y hyT
    simp only [mem_compl_iff]
    intro hyV
    have hyTV : y ∈ T ∩ V := ⟨hyT, hyV⟩
    simp [hTV_empty] at hyTV
  · -- Since `x ∈ V`, the separating clopen superset `Vᶜ` omits `x`.
    intro hxVcompl
    exact hxVcompl hxV

-- Proof sketch: intersect all clopen supersets of `T`; closedness gives compactness of `T`, and
-- component saturation lets one separate any point outside `T` from `T` by a clopen superset.
/-- Lemma 5.12.12 (3): if a subset of a quasi-compact space with a basis of quasi-compact opens
and quasi-compact intersections is closed and is a union of connected components of `X`, then it
is an intersection of open and closed subsets. -/
theorem isIntersectionOfClopens_of_isClosed_of_union_connectedComponents
    (hT_closed : IsClosed T) (hT_components : ∀ x ∈ T, connectedComponent x ⊆ T) :
    ∃ S : Set (Set X), (∀ Z ∈ S, IsClopen Z) ∧ T = ⋂₀ S := by
  classical
  refine ⟨{ U : Set X | IsClopen U ∧ T ⊆ U }, ?_, ?_⟩
  · intro U hU
    exact hU.1
  · apply Subset.antisymm
    · intro y hyT
      rw [mem_sInter]
      intro U hU
      exact hU.2 hyT
    · intro y hy_inter
      by_contra hyT
      obtain ⟨U, hU_clopen, hTU, hyU⟩ :=
        exists_isClopen_superset_not_mem_of_isClosed_of_component_saturated
          hT_closed hT_components hyT
      -- The separating clopen superset belongs to the defining family of the intersection.
      have hy_mem : y ∈ U := by
        rw [mem_sInter] at hy_inter
        exact hy_inter U ⟨hU_clopen, hTU⟩
      exact hyU hy_mem

end

/-! ### Lemma_5_12_13 (from Chap05) -/
universe u

open TopologicalSpace

section

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X]

/- Domain-style sampling for Noetherian spaces and retrocompact subsets:
- owner abstractions: `NoetherianSpace`, `CompactSpace`, `IsRetrocompact`
- same-domain declarations inspected:
  `NoetherianSpace.compactSpace`,
  `NoetherianSpace.isCompact`,
  `NoetherianSpace.to_quasiSeparatedSpace`,
  `IsCompact.isRetrocompact`

Layer triage:
- `source-facing`: Stacks Lemma 5.12.13, asserting quasi-compactness of the whole space and
  retrocompactness of every subset in a Noetherian space
- `core/canonical`: `NoetherianSpace`, `CompactSpace`, `IsRetrocompact`
- `bridge/view`: part (2) below is the source-facing specialization of `IsRetrocompact` obtained
  directly from the owner theorem `NoetherianSpace.isCompact`; there is no upstream theorem with
  the exact same interface, so the source-facing bridge is kept rather than replaced by a shell

Primitive data is only the `NoetherianSpace` hypothesis. Whole-space compactness and the
compactness of `s ∩ U` for compact open `U` are both derived from
`TopologicalSpace.NoetherianSpace.isCompact`, so no parallel wrapper API is needed here.
-/

/- Canonical recall: a Noetherian topological space carries the compact-space instance
`TopologicalSpace.NoetherianSpace.compactSpace`. -/
recall NoetherianSpace.compactSpace

/-- Lemma 5.12.13: every subset of a Noetherian topological space is retrocompact. -/
theorem isRetrocompact_of_noetherianSpace (s : Set X) : IsRetrocompact s :=
  fun _ _ _ ↦ NoetherianSpace.isCompact _

end

/-! ### Lemma_5_12_14 (from Chap05) -/
universe u

open Topology

namespace TopologicalSpace

section

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [LocallyNoetherianSpace X]

/-
Domain-style sampling for Lemma 5.12.14:
- primary domain: Noetherianity of quasi-compact locally Noetherian spaces
- sampled owner declarations:
  `TopologicalSpace.LocallyNoetherianSpace.exists_open`,
  `TopologicalSpace.NoetherianSpace.iUnion`,
  `TopologicalSpace.NoetherianSpace.compactSpace`,
  `AlgebraicGeometry.IsNoetherian.noetherianSpace`
- best owner abstraction: the ambient owners are the typeclasses
  `TopologicalSpace.LocallyNoetherianSpace` and `TopologicalSpace.NoetherianSpace`
- primitive data: an open Noetherian neighborhood around each point, supplied by
  `LocallyNoetherianSpace.exists_open`
- derived API: the finite-subcover step `CompactSpace.elim_nhds_subcover` and the finite-union
  theorem `NoetherianSpace.iUnion`

Layer triage:
- `source-facing`: Lemma 5.12.14, asserting that a quasi-compact locally Noetherian space is
  Noetherian
- `core/canonical`: `TopologicalSpace.NoetherianSpace`
- `bridge/view`: the finite-cover argument upgrading local Noetherian neighborhoods to a global
  `NoetherianSpace` instance

There is no upstream theorem in the chapter or in mathlib with this exact
`CompactSpace X` + `LocallyNoetherianSpace X` interface, so this file keeps the source-facing
bridge theorem and rewrites it to the canonical owner API instead of introducing a parallel local
wrapper.
-/

-- Proof sketch: use local Noetherianity to cover `X` by Noetherian neighbourhoods, extract a
-- finite subcover from quasi-compactness, and then apply the canonical finite-union theorem
-- `TopologicalSpace.NoetherianSpace.iUnion`.
/-- Lemma 5.12.14: a quasi-compact locally Noetherian topological space is Noetherian. -/
theorem LocallyNoetherianSpace.noetherianSpace :
    NoetherianSpace X := by
  classical
  -- Choose a Noetherian neighbourhood around each point from local Noetherianity.
  choose U hU_nhds hU_noeth using fun x : X ↦ LocallyNoetherianSpace.exists_mem_nhds x
  -- Quasi-compactness turns the neighbourhood cover into a finite subcover.
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U hU_nhds
  -- Rewrite the subcover statement into an equality with `univ`.
  have hcover : (⋃ x : t, (U x : Set X)) = Set.univ := by
    simpa [Set.iUnion_subtype] using ht
  -- Reduce global Noetherianity to the finite union of the chosen Noetherian pieces.
  rw [← noetherian_univ_iff, ← hcover]
  letI : ∀ x : t, NoetherianSpace (U x) := fun x ↦ hU_noeth x
  exact NoetherianSpace.iUnion fun x : t ↦ U x

attribute [instance 100] LocallyNoetherianSpace.noetherianSpace

end

end TopologicalSpace

/-! ### Lemma_5_12_15_Alexander_subbase_theorem (from Chap05) -/
universe u

open Set TopologicalSpace

/- Domain-style sampling for Alexander's subbasis theorem:
- owner abstractions: `TopologicalSpace.generateFrom`, `CompactSpace`
- same-domain declarations inspected:
  `TopologicalSpace.generateFrom`,
  `TopologicalSpace.eq_generateFrom_iff_isTopologicalBasis_finiteInterClosure`,
  `compactSpace_generateFrom`,
  `compactSpace_generateFrom'`

Layer triage:
- `source-facing`: a subbasis cover hypothesis stated as a finite-refinement condition
- `core/canonical`: `generateFrom` for the topology and `CompactSpace` for quasi-compactness
- `bridge/view`: the finite-refinement hypothesis is converted to the finite-subcover hypothesis of
  `compactSpace_generateFrom`

Primitive data is only the family `ℬ : Set (Set X)` together with the finite-refinement cover
hypothesis. The finite subcover conclusion is derived API, so this file should stay a small bridge
to `compactSpace_generateFrom` rather than introducing a parallel subbasis owner.
-/

/-- A finite cover refining a cover by `P` yields a finite subcover by members of `P`. -/
theorem exists_finite_subcover_of_refining_cover {X : Type u} {P Q : Set (Set X)}
    (hQfinite : Q.Finite) (hQcover : ⋃₀ Q = (univ : Set X))
    (hQrefines : ∀ V ∈ Q, ∃ U ∈ P, V ⊆ U) :
    ∃ R ⊆ P, R.Finite ∧ ⋃₀ R = (univ : Set X) := by
  classical
  have hQrefines' : ∀ V : Q, ∃ U ∈ P, V.1 ⊆ U := fun V ↦ hQrefines V.1 V.2
  choose r hrP hrsub using hQrefines'
  letI : Fintype Q := hQfinite.fintype
  refine ⟨Set.range r, ?_, Set.toFinite _, ?_⟩
  · rintro U ⟨V, rfl⟩
    exact hrP V
  · apply subset_antisymm (sUnion_subset fun _ _ ↦ subset_univ _)
    rw [← hQcover]
    intro x hx
    rcases mem_sUnion.mp hx with ⟨V, hVQ, hxV⟩
    refine mem_sUnion.mpr ⟨r ⟨V, hVQ⟩, ?_, ?_⟩
    · exact ⟨⟨V, hVQ⟩, rfl⟩
    · exact hrsub ⟨V, hVQ⟩ hxV

section

variable {X : Type u} [t : TopologicalSpace X]

/- Companion recall: `compactSpace_generateFrom` is mathlib's canonical finite-subcover form of
Alexander's subbasis theorem for a topology generated by a subbasis. -/
recall compactSpace_generateFrom

-- Proof sketch: starting from a cover `P ⊆ ℬ`, use the assumed finite refinement `Q`. For
-- each `V ∈ Q`, choose some `U ∈ P` with `V ⊆ U`; the chosen finitely many members of `P` still
-- cover `X`. This upgrades the finite-refinement hypothesis to the finite-subcover hypothesis of
-- `compactSpace_generateFrom`.
/-- Lemma 5.12.15 (Alexander subbase theorem): if `ℬ` is a subbasis for the topology on `X` and
every cover of `X` by elements of `ℬ` admits a finite refining cover, then `X` is
quasi-compact. Here a refining cover is a finite family `Q` covering `X` such that each
`V ∈ Q` is contained in some member of the original cover. -/
theorem compactSpace_of_subbasis_finite_refinement {ℬ : Set (Set X)}
    (hℬ : t = generateFrom ℬ)
    (hfinite :
      ∀ P ⊆ ℬ, ⋃₀ P = (univ : Set X) →
        ∃ Q : Finset (Set X), ⋃₀ (↑Q : Set (Set X)) = (univ : Set X) ∧
          ∀ V ∈ Q, ∃ U ∈ P, V ⊆ U) :
    CompactSpace X := by
  refine compactSpace_generateFrom hℬ fun P hP hcover ↦ ?_
  obtain ⟨Q, hQcover, hQrefines⟩ := hfinite P hP hcover
  exact exists_finite_subcover_of_refining_cover Q.finite_toSet hQcover fun V hV ↦
    hQrefines V (Finset.mem_coe.mp hV)

end
