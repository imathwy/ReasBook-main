import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Constructible
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.Spectral.Prespectral

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_18_1 (from Chap05) -/
universe u

variable {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace

/- The textbook notation for the closed-point locus is `X₀`. Lean parses bare `X₀` as a single
identifier, so the reusable owner-level term notation is parenthesized: `(X)₀`. In a local
context with a fixed ambient space variable `X`, one can then add `local notation "X₀" => (X)₀`
to recover the usual surface form. -/
scoped macro:max X:term noWs "₀" : term => `(closedPoints $X)

end TopologicalSpace

/-
Domain-style sampling for Jacobson spaces:
- primitive owner for closed points: `closedPoints X`, with source-facing notation `(X)₀`
- core canonical owner: `JacobsonSpace X`
- derived textbook specification: `jacobsonSpace_iff`

Layer triage:
- `source-facing`: the definition of a Jacobson space via density of closed points in closed subsets
- `core/canonical`: the mathlib class `JacobsonSpace X`
- `bridge/view`: the closure characterization `jacobsonSpace_iff`

Primitive data is the owner class `JacobsonSpace X`; the closure statement is its canonical
specification theorem, not separate structure data.
-/

/- Companion recall: the closed-point locus of `X` is the canonical set `closedPoints X`. -/
recall closedPoints

/-
Definition 5.18.1 is recalled canonically by `JacobsonSpace X`: this is the mathlib class whose
field states that every closed subset is the closure of its closed points.
-/
recall JacobsonSpace

/- Companion recall: the textbook closure characterization of Jacobson spaces is the canonical
equivalence `jacobsonSpace_iff`. -/
recall jacobsonSpace_iff

/-! ### Lemma_5_18_2 (from Chap05) -/
universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Jacobson spaces:
- source-facing hypothesis: closed points are dense in each singleton closure
- core/canonical owner: `JacobsonSpace X`
- primitive owner field: `closure_inter_closedPoints`
- bridge/view: this theorem maps the singleton-closure density hypothesis to the owner
  `JacobsonSpace X`

Primitive data belongs to the owner `JacobsonSpace X`. This lemma should therefore conclude the
owner by supplying the primitive field `closure_inter_closedPoints` directly, rather than by
rebuilding a parallel wrapper API or routing through the locally closed companion criterion.
-/

-- Proof sketch: supply the owner field `closure_inter_closedPoints`. For a closed subset `Z` and
-- `x ∈ Z`, the closure of `{x}` stays inside `Z`; the density hypothesis on `closure {x}` then
-- puts `x` in the closure of `Z ∩ closedPoints X`. This yields
-- `closure (Z ∩ closedPoints X) = Z`.
/-- Lemma 5.18.2: if for every point `x`, the closed points of `X` are dense in `closure {x}`,
then `X` is a Jacobson space. -/
theorem jacobsonSpace_of_dense_closedPoints_in_singleton_closure
    (hDense : ∀ x : X, closure (closure ({x} : Set X) ∩ closedPoints X) = closure ({x} : Set X)) :
    JacobsonSpace X := by
  refine ⟨?_⟩
  intro Z hZ
  refine subset_antisymm ?_ ?_
  · exact hZ.closure_subset_iff.mpr inter_subset_left
  · intro x hxZ
    have hclosure : closure ({x} : Set X) ⊆ Z :=
      hZ.closure_subset_iff.mpr (singleton_subset_iff.2 hxZ)
    have hx : x ∈ closure (closure ({x} : Set X) ∩ closedPoints X) := by
      simpa [hDense x] using (subset_closure (by simp : x ∈ ({x} : Set X)))
    exact (closure_mono <| inter_subset_inter hclosure subset_rfl) hx

/-! ### Lemma_5_18_3 (from Chap05) -/
universe u

open Set TopologicalSpace Topology

/-
Domain-style sampling for Jacobson behavior of prespectral `T₀` spaces:
- inspected owner declarations already upstream: `JacobsonSpace X`, `closedPoints X`,
  `jacobsonSpace_iff_locallyClosed`
- inspected ambient support API in the spectral/compact domain:
  `PrespectralSpace.isTopologicalBasis`, `IsClosed.exists_closed_singleton`

Layer triage:
- `source-facing`: a non-Jacobson prespectral `T₀` space has a non-closed point with locally
  closed singleton
- `core/canonical`: `JacobsonSpace X` and the owner set `closedPoints X`
- `bridge/view`: `IsLocallyClosed.exists_mem_isLocallyClosed_singleton` extracts a locally closed
  singleton from a nonempty locally closed subset by shrinking to a compact open neighborhood and
  applying the closed-point existence theorem in that compact subspace

Primitive data in the public theorem are only the ambient space assumptions and the negated owner
property `¬ JacobsonSpace X`. The compact-open neighborhood and compact-subspace closed point are
derived internally, so this file should not introduce any parallel public wrapper around Jacobson
spaces or closed points.
-/

variable {X : Type u} [TopologicalSpace X] [T0Space X] [PrespectralSpace X]

/-- A nonempty locally closed subset of a prespectral `T₀` space contains a point whose singleton
is locally closed. -/
theorem IsLocallyClosed.exists_mem_isLocallyClosed_singleton
    {Z : Set X} (hZ' : IsLocallyClosed Z) (hZ : Z.Nonempty) :
    ∃ x, x ∈ Z ∧ IsLocallyClosed ({x} : Set X) := by
  obtain ⟨U, C, hU, hC, rfl⟩ := hZ'
  obtain ⟨x, hx⟩ := hZ
  obtain ⟨V, hV, hxV, hVU⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hx.1 hU
  have hVC_nonempty : ((Subtype.val : V → X) ⁻¹' C).Nonempty := ⟨⟨x, hxV⟩, hx.2⟩
  haveI : CompactSpace V := isCompact_iff_compactSpace.mp hV.2
  obtain ⟨y, hyC, hyclosed⟩ :=
    (hC.preimage continuous_subtype_val).exists_closed_singleton hVC_nonempty
  refine ⟨y, ⟨hVU y.2, hyC⟩, ?_⟩
  simpa using
    hyclosed.isLocallyClosed.image IsEmbedding.subtypeVal.isInducing
      hV.1.isOpenEmbedding_subtypeVal.isOpen_range.isLocallyClosed

-- Proof sketch: contrapose `jacobsonSpace_iff_locallyClosed` to get a nonempty locally closed
-- subset `Z` containing no closed point of `X`. Choose `x ∈ Z`, shrink to a compact open
-- neighborhood inside `Z` using the compact-open basis, and apply the closed-point existence
-- theorem for nonempty compact `T₀` spaces to that compact subspace. The resulting point has
-- locally closed singleton in `X`, and it is not in `closedPoints X` because `Z` contains no
-- closed point of `X`.
/-- Lemma 5.18.3: if a Kolmogorov space with a basis of quasi-compact opens is not Jacobson, then
there exists a non-closed point whose singleton is locally closed. -/
theorem exists_nonclosed_point_with_locallyClosed_singleton_of_not_jacobsonSpace
    (hX : ¬ JacobsonSpace X) :
    ∃ x, x ∉ closedPoints X ∧ IsLocallyClosed ({x} : Set X) := by
  rw [jacobsonSpace_iff_locallyClosed] at hX
  push Not at hX
  obtain ⟨Z, hZ, hZ', hZ₀⟩ := hX
  obtain ⟨x, hxZ, hxloc⟩ :=
    hZ'.exists_mem_isLocallyClosed_singleton hZ
  refine ⟨x, fun hxclosed ↦ ?_, hxloc⟩
  have hx : x ∈ Z ∩ closedPoints X := ⟨hxZ, hxclosed⟩
  rw [hZ₀] at hx
  exact hx

/-! ### Lemma_5_18_4 (from Chap05) -/
universe u

open Set TopologicalSpace
open scoped TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

local macro "X₀" : term => `(closedPoints X)

/- 
Domain-style sampling for Jacobson locality on open covers:
- chapter owner recall already established in `Definition_5_18_1`: `closedPoints X`,
  `JacobsonSpace X`
- same-domain mathlib owner companions: `jacobsonSpace_iff_locallyClosed`,
  `TopologicalSpace.IsOpenEmbedding.preimage_closedPoints`,
  `TopologicalSpace.IsOpenCover.jacobsonSpace_iff`

Layer triage:
- `source-facing`: Lemma 5.18.4, consisting of the open-cover Jacobson criterion together with the
  closed-point union conclusion `X₀ = ⋃ i, ((↑) : U i → X) '' closedPoints (U i)`
- `core/canonical`: the owner `JacobsonSpace X`
- `bridge/view`: the image of `closedPoints (U i)` in `X` along the open-subspace inclusion

Primitive data remains the owner `JacobsonSpace X`; the open-cover criterion is exact derived API.
The extra closed-point equality is source-facing companion data, so the file should recall the
owner theorem directly and add only the atomic bridge theorem needed for the “moreover” clause.
-/

/- Lemma 5.18.4 is the canonical owner-level locality theorem for Jacobson spaces on open covers. -/
recall IsOpenCover.jacobsonSpace_iff {ι : Type*} {U : ι → Opens X} (hU : IsOpenCover U) :
  JacobsonSpace X ↔ ∀ i, JacobsonSpace (U i)

namespace TopologicalSpace.IsOpenCover

/-- Lemma 5.18.4 (moreover): in a Jacobson space, the closed points are exactly the union of the
closed points of any open cover members, viewed in `X` via the subtype inclusions. -/
theorem closedPoints_eq_iUnion_image {ι : Type*} {U : ι → Opens X} [JacobsonSpace X]
    (hU : IsOpenCover U) :
    X₀ = ⋃ i, ((↑) : U i → X) '' closedPoints (U i) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hix⟩ := hU.exists_mem x
    refine mem_iUnion.2 ⟨i, ⟨⟨x, hix⟩, ?_, rfl⟩⟩
    have hpre : ((↑) : U i → X) ⁻¹' X₀ = closedPoints (U i) :=
      (U i).2.isOpenEmbedding_subtypeVal.preimage_closedPoints
    have hx' : (⟨x, hix⟩ : U i) ∈ ((↑) : U i → X) ⁻¹' X₀ := by
      simpa using hx
    simpa [hpre] using hx'
  · intro hx
    rcases mem_iUnion.1 hx with ⟨i, hx⟩
    rcases hx with ⟨y, hy, rfl⟩
    have hpre : ((↑) : U i → X) ⁻¹' X₀ = closedPoints (U i) :=
      (U i).2.isOpenEmbedding_subtypeVal.preimage_closedPoints
    have hy' : y ∈ ((↑) : U i → X) ⁻¹' X₀ := by
      simpa [hpre] using hy
    simpa using hy'

/-- Source-style corollary of Lemma 5.18.4 (moreover): if the cover members are Jacobson, then the
same closed-point union formula holds. -/
theorem closedPoints_eq_iUnion_image_of_forall_jacobson {ι : Type*} {U : ι → Opens X}
    (hU : IsOpenCover U) (hJacobson : ∀ i, JacobsonSpace (U i)) :
    X₀ = ⋃ i, ((↑) : U i → X) '' closedPoints (U i) := by
  let _ : JacobsonSpace X := hU.jacobsonSpace_iff.2 hJacobson
  simpa using hU.closedPoints_eq_iUnion_image

end TopologicalSpace.IsOpenCover

/-! ### Lemma_5_18_5 (from Chap05) -/
universe u

open Set TopologicalSpace Topology
open scoped Set.Notation

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for Jacobson subspaces defined by local constructibility:
- primary domain: locally constructible subsets and Jacobson spaces
- inspected owner-level declarations:
  `Topology.IsLocallyConstructible`,
  `Topology.IsEmbedding.isLocallyClosed_iff`,
  `Topology.IsConstructible.isFiniteUnionOfLocallyClosed`,
  `JacobsonSpace.of_isOpenEmbedding`
- best owner abstraction: `Topology.IsLocallyConstructible`

Layer triage:
- `source-facing`: Lemma 5.18.5, asserting that a subspace locally given by unions of locally
  closed subsets is Jacobson and that its closed points are already closed in the ambient space
- `core/canonical`: `Topology.IsLocallyConstructible`, `Topology.IsConstructible`, and
  `JacobsonSpace`
- `bridge/view`: the finite-union-of-locally-closed decomposition of constructible neighborhoods
  together with the canonical subtype traces `U ↓∩ T`

Primitive data belongs to the owner predicate `IsLocallyConstructible`; the source phrase “locally
a union of locally closed subsets” is derived API recovered from
`IsConstructible.isFiniteUnionOfLocallyClosed` on each neighborhood. The constructible case is an
internal bridge: it should feed the local theorem, not survive as a parallel public owner.
-/

/-- Helper for Lemma 5.18.5: a constructible subspace of a Jacobson space is Jacobson. -/
private theorem jacobsonSpace_subtype_of_isConstructible_aux [JacobsonSpace X] {T : Set X}
    (hT : IsConstructible T) :
    JacobsonSpace T := by
  -- Reduce Jacobsonness to the closed-point criterion on nonempty locally closed subsets.
  rw [jacobsonSpace_iff_locallyClosed]
  intro Z hZ hZ'
  obtain ⟨W, hW, hWZ⟩ :=
    IsEmbedding.subtypeVal.isLocallyClosed_iff.1 hZ'
  obtain ⟨n, S, hS, hT_eq⟩ := hT.isFiniteUnionOfLocallyClosed.exists_eq_iUnion
  -- Identify the image of `Z` in `X` with the ambient trace `W ∩ T`.
  have himage_eq : ((↑) : T → X) '' Z = W ∩ T := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzW : (z : X) ∈ W := by
        have : (z : X) ∈ W ∩ Set.range ((↑) : T → X) := by
          rw [hWZ]
          exact ⟨z, hz, rfl⟩
        exact this.1
      exact ⟨hzW, z.2⟩
    · rintro ⟨hxW, hxT⟩
      rw [← hWZ]
      exact ⟨hxW, ⟨⟨x, hxT⟩, rfl⟩⟩
  have himage_iUnion : ((↑) : T → X) '' Z = ⋃ i, W ∩ S i := by
    calc
      ((↑) : T → X) '' Z = W ∩ T := himage_eq
      _ = W ∩ ⋃ i, S i := by rw [hT_eq]
      _ = ⋃ i, W ∩ S i := by rw [inter_iUnion]
  -- A nonempty image meets one locally closed constructible piece, where Jacobsonness of `X`
  -- supplies a point closed in `X`.
  have himage_nonempty : (((↑) : T → X) '' Z).Nonempty := by
    rcases hZ with ⟨z, hz⟩
    exact ⟨(z : X), ⟨z, hz, rfl⟩⟩
  rw [himage_iUnion, Set.nonempty_iUnion] at himage_nonempty
  obtain ⟨i, hi⟩ := himage_nonempty
  obtain ⟨x, hx, hxclosed⟩ :=
    nonempty_inter_closedPoints hi (hW.inter (hS i))
  have hximage : x ∈ ((↑) : T → X) '' Z := by
    rw [himage_iUnion]
    exact Set.mem_iUnion.2 ⟨i, hx⟩
  rcases hximage with ⟨z, hz, rfl⟩
  refine ⟨z, hz, ?_⟩
  rw [mem_closedPoints_iff]
  convert (mem_closedPoints_iff.1 hxclosed).preimage continuous_subtype_val using 1
  ext w
  simp [Subtype.ext_iff]

/-- Helper for Lemma 5.18.5: in the constructible case, closed points of the subspace are already
closed in the ambient space. -/
private theorem closedPoints_subset_preimage_closedPoints_of_isConstructible_aux [JacobsonSpace X]
    {T : Set X} (hT : IsConstructible T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := by
  intro x hx
  -- Turn the singleton `{x}` in the subspace into an ambient locally closed singleton.
  have hx' : IsLocallyClosed ({x} : Set T) := by
    refine ⟨univ, {x}, isOpen_univ, ?_, by ext y; simp⟩
    exact mem_closedPoints_iff.1 hx
  obtain ⟨W, hW, hWsingleton⟩ :=
    IsEmbedding.subtypeVal.isLocallyClosed_iff.1 hx'
  obtain ⟨n, S, hS, hT_eq⟩ := hT.isFiniteUnionOfLocallyClosed.exists_eq_iUnion
  have hxT : (x : X) ∈ T := x.2
  have hxUnion : (x : X) ∈ ⋃ i, S i := by simpa [hT_eq] using hxT
  rw [Set.mem_iUnion] at hxUnion
  obtain ⟨i, hxi⟩ := hxUnion
  -- On the constructible piece containing `x`, the ambient trace collapses to the singleton.
  have hWT : W ∩ T = ({(x : X)} : Set X) := by
    ext y
    constructor
    · intro hy
      have hyImage : y ∈ ((↑) : T → X) '' ({x} : Set T) := by
        rw [← hWsingleton]
        exact ⟨hy.1, ⟨⟨y, hy.2⟩, rfl⟩⟩
      rcases hyImage with ⟨z, hz, rfl⟩
      simpa using congrArg Subtype.val hz
    · intro hy
      subst hy
      have hxImage : (x : X) ∈ ((↑) : T → X) '' ({x} : Set T) := ⟨x, by simp, rfl⟩
      have hxWT' : (x : X) ∈ W ∩ Set.range ((↑) : T → X) := by
        rw [hWsingleton]
        exact hxImage
      exact ⟨hxWT'.1, x.2⟩
  have hpiece_eq : W ∩ S i = ({(x : X)} : Set X) := by
    apply Set.Subset.antisymm
    · intro y hy
      have hyWT : y ∈ W ∩ T := by
        refine ⟨hy.1, ?_⟩
        rw [hT_eq]
        exact Set.mem_iUnion.2 ⟨i, hy.2⟩
      simpa [hWT] using hyWT
    · intro y hy
      have hyx : y = x := by simpa using hy
      subst hyx
      have hxWT : (x : X) ∈ W ∩ T := by
        rw [hWT]
        simp
      exact ⟨hxWT.1, hxi⟩
  have hxLoc : IsLocallyClosed ({(x : X)} : Set X) := by
    rw [← hpiece_eq]
    exact hW.inter (hS i)
  show x.1 ∈ closedPoints X
  simpa [mem_closedPoints_iff] using
    (isClosed_singleton_of_isLocallyClosed_singleton hxLoc : IsClosed ({(x : X)} : Set X))

/-- Lemma 5.18.5: if `X` is Jacobson and `T ⊆ X` is locally constructible on `X` (equivalently,
locally on `X` a union of locally closed subsets), then the subspace `T` is Jacobson. -/
theorem jacobsonSpace_subtype_of_isLocallyConstructible
    [JacobsonSpace X] {T : Set X} (hT : IsLocallyConstructible T) :
    JacobsonSpace T := by
  -- Follow the source proof via property (*): every nonempty locally closed subset of `T`
  -- contains a point closed in the ambient space `X`.
  rw [jacobsonSpace_iff_locallyClosed]
  intro Z hZ hZ'
  obtain ⟨x, hx⟩ := hZ
  obtain ⟨U, hxU, hU, hUT⟩ := hT x
  have hxUmem : (x : X) ∈ U := mem_of_mem_nhds hxU
  -- Compare the open neighborhood of `x` inside `T` with the ambient trace `U ↓∩ T`.
  let V : Opens T := ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val⟩
  let eV : V ≃ₜ (U ∩ T : Set X) :=
    (Homeomorph.setCongr (by ext y; simp [V])).trans
      (IsEmbedding.subtypeVal.homeomorphOfSubsetRange fun y hy ↦ ⟨⟨y, hy.2⟩, rfl⟩)
  let eU : (U ↓∩ T) ≃ₜ (U ∩ T : Set X) :=
    (Homeomorph.setCongr (by ext y; simp)).trans
      (IsEmbedding.subtypeVal.homeomorphOfSubsetRange fun y hy ↦ ⟨⟨y, hy.1⟩, rfl⟩)
  let e : V ≃ₜ U ↓∩ T := eV.trans eU.symm
  haveI : JacobsonSpace U := JacobsonSpace.of_isOpenEmbedding hU.isOpenEmbedding_subtypeVal
  haveI : JacobsonSpace (U ↓∩ T) := jacobsonSpace_subtype_of_isConstructible_aux hUT
  have hVJacobson : JacobsonSpace V := JacobsonSpace.of_isOpenEmbedding e.isOpenEmbedding
  -- Restrict `Z` to this neighborhood, obtain a closed point there, then transport it back to `T`
  -- and finally to `X`.
  have hZV_nonempty : ((V : Set T) ↓∩ Z).Nonempty := ⟨⟨x, hxUmem⟩, hx⟩
  have hZV' : IsLocallyClosed ((V : Set T) ↓∩ Z) := hZ'.preimage continuous_subtype_val
  obtain ⟨y, hyZ, hyclosed⟩ :=
    (jacobsonSpace_iff_locallyClosed.mp hVJacobson) ((V : Set T) ↓∩ Z) hZV_nonempty hZV'
  refine ⟨y, hyZ, ?_⟩
  have hyC : e y ∈ closedPoints (U ↓∩ T) := by
    exact (preimage_closedPoints_subset e.symm.injective e.symm.continuous) <| by
      simpa using hyclosed
  have hyUclosed : e y ∈ (U ↓∩ T) ↓∩ closedPoints U :=
    (closedPoints_subset_preimage_closedPoints_of_isConstructible_aux hUT) hyC
  have hpreU : ((↑) : U → X) ⁻¹' closedPoints X = closedPoints U :=
    hU.isOpenEmbedding_subtypeVal.preimage_closedPoints
  have hyX' : ((e y : U) : X) ∈ closedPoints X := by
    have : (e y : U) ∈ ((↑) : U → X) ⁻¹' closedPoints X := by
      simpa [hpreU] using hyUclosed
    simpa using this
  have hyeq : ((e y : U) : X) = y := by
    have hEq : eU (e y) = eV y := by
      simp [e]
    have hEq' := congrArg (fun z : (U ∩ T : Set X) ↦ (z : X)) hEq
    simpa [eV, eU, V] using hEq'
  rw [mem_closedPoints_iff]
  convert (mem_closedPoints_iff.1 hyX').preimage continuous_subtype_val using 1
  ext w
  simp [Subtype.ext_iff, hyeq]

/-- If `X` is Jacobson and `T ⊆ X` is locally constructible on `X`, then every closed point of the
subspace `T` is a closed point of `X`. -/
theorem closedPoints_subset_preimage_closedPoints_of_isLocallyConstructible
    [JacobsonSpace X] {T : Set X} (hT : IsLocallyConstructible T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := by
  intro x hx
  obtain ⟨U, hxU, hU, hUT⟩ := hT x
  have hxUmem : (x : X) ∈ U := mem_of_mem_nhds hxU
  haveI : JacobsonSpace U := JacobsonSpace.of_isOpenEmbedding hU.isOpenEmbedding_subtypeVal
  haveI : JacobsonSpace (U ↓∩ T) := jacobsonSpace_subtype_of_isConstructible_aux hUT
  -- Reuse the same local chart as above and push the closed-point statement through it.
  let V : Opens T := ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val⟩
  let eV : V ≃ₜ (U ∩ T : Set X) :=
    (Homeomorph.setCongr (by ext y; simp [V])).trans
      (IsEmbedding.subtypeVal.homeomorphOfSubsetRange fun y hy ↦ ⟨⟨y, hy.2⟩, rfl⟩)
  let eU : (U ↓∩ T) ≃ₜ (U ∩ T : Set X) :=
    (Homeomorph.setCongr (by ext y; simp)).trans
      (IsEmbedding.subtypeVal.homeomorphOfSubsetRange fun y hy ↦ ⟨⟨y, hy.1⟩, rfl⟩)
  let e : V ≃ₜ U ↓∩ T := eV.trans eU.symm
  have hxV : (⟨x, hxUmem⟩ : V) ∈ closedPoints V := by
    rw [mem_closedPoints_iff]
    convert (mem_closedPoints_iff.1 hx).preimage continuous_subtype_val using 1
    ext w
    simp [Subtype.ext_iff]
  have hxC : e ⟨x, hxUmem⟩ ∈ closedPoints (U ↓∩ T) := by
    exact (preimage_closedPoints_subset e.symm.injective e.symm.continuous) <| by
      simpa using hxV
  have hxUclosed : e ⟨x, hxUmem⟩ ∈ (U ↓∩ T) ↓∩ closedPoints U :=
    (closedPoints_subset_preimage_closedPoints_of_isConstructible_aux hUT) hxC
  have hpreU : ((↑) : U → X) ⁻¹' closedPoints X = closedPoints U :=
    hU.isOpenEmbedding_subtypeVal.preimage_closedPoints
  have hxX' : ((e ⟨x, hxUmem⟩ : U) : X) ∈ closedPoints X := by
    have : (e ⟨x, hxUmem⟩ : U) ∈ ((↑) : U → X) ⁻¹' closedPoints X := by
      simpa [hpreU] using hxUclosed
    simpa using this
  have hxeq : ((e ⟨x, hxUmem⟩ : U) : X) = x := by
    have hEq : eU (e ⟨x, hxUmem⟩) = eV ⟨x, hxUmem⟩ := by
      simp [e]
    have hEq' := congrArg (fun z : (U ∩ T : Set X) ↦ (z : X)) hEq
    simpa [eV, eU, V] using hEq'
  show x.1 ∈ closedPoints X
  simpa [hxeq] using hxX'

/-! ### Lemma_5_18_6 (from Chap05) -/
universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Lemma 5.18.6:
- primitive owner data in this domain: `closedPoints X`
- core canonical owner: `JacobsonSpace X`
- exact canonical bridge theorem: `JacobsonSpace.discreteTopology`
- finite-space corollary already supplied by the instance
  `[Finite X] [JacobsonSpace X] : DiscreteTopology X`

Layer triage:
- `source-facing`: finitely many closed points in a Jacobson space force discreteness
- `core/canonical`: `JacobsonSpace X`
- `bridge/view`: the exact existing theorem `JacobsonSpace.discreteTopology`

Primitive data is the finiteness of `closedPoints X`; discreteness is derived canonical structure,
so this file should recall the owner theorem directly rather than introduce a parallel local lemma.
-/
/-
Lemma 5.18.6: a Jacobson space with finitely many closed points has discrete topology; in
particular, every finite Jacobson space is discrete.
-/
recall JacobsonSpace.discreteTopology [JacobsonSpace X] (h : (closedPoints X).Finite) :
  DiscreteTopology X

-- Proof sketch: use the existing instance
-- `[Finite X] [JacobsonSpace X] : DiscreteTopology X`, which is obtained in mathlib from
-- `JacobsonSpace.discreteTopology` by observing that `closedPoints X` is finite when `X` is finite.
/-- A finite Jacobson space has discrete topology. -/
theorem discreteTopology_of_finite_jacobsonSpace [Finite X] [JacobsonSpace X] :
    DiscreteTopology X := by
  -- The finite-space corollary is already registered as a typeclass instance in mathlib.
  infer_instance

/-! ### Lemma_5_18_7 (from Chap05) -/
universe u

open Set TopologicalSpace Topology
open scoped Set.Notation
open scoped TopologicalSpace

section

variable {X : Type u} [TopologicalSpace X]

local macro "X₀" : term => `(closedPoints X)

section

variable [JacobsonSpace X]

/-
Domain-style sampling for closed-point traces of finite unions of locally closed subsets:
- primary domain: Jacobson spaces, closed points, and locally closed subset traces along subtype
  inclusions
- inspected owner-level declarations:
  `closedPoints`,
  `JacobsonSpace`,
  `jacobsonSpace_iff_locallyClosed`,
  `IsLocallyClosed.preimage`
- best owner abstraction: the ambient owner `JacobsonSpace X` together with the canonical closed
  point set `X₀`; the actual trace operation is the derived bridge/view
  `X₀ ↓∩ E`

Layer triage:
- `source-facing`: the finite-union closed-point trace correspondence in Lemma 5.18.7
- `core/canonical`: `JacobsonSpace X` and `X₀`
- `bridge/view`: the canonical subtype trace `X₀ ↓∩ E`

Primitive data is the ambient Jacobson owner and the chapter bridge predicate
`IsFiniteUnionOfLocallyClosed`. The trace map itself is derived API and should therefore use the
canonical subtype-trace surface directly, rather than a second local wrapper definition.
-/

-- Proof sketch: traces to the closed-point subtype preserve locally closed
-- subsets and finite unions; surjectivity follows by lifting finite unions of locally closed
-- subsets of `X₀` piecewise from open and closed subsets of `X₀`, while injectivity is the Stacks
-- argument using that every nonempty finite union of locally closed subsets of a Jacobson space
-- meets `X₀`.
/-- Helper for Lemma 5.18.7: the empty set is a finite union of locally closed subsets. -/
private lemma isFiniteUnionOfLocallyClosed_empty {Y : Type*} [TopologicalSpace Y] :
    IsFiniteUnionOfLocallyClosed (∅ : Set Y) := by
  -- Use the empty family of locally closed pieces.
  refine ⟨∅, Set.finite_empty, ?_, ?_⟩
  · intro Z hZ
    exact False.elim (Set.notMem_empty Z hZ)
  · simp

/-- Helper for Lemma 5.18.7: finite unions of locally closed subsets are stable under binary
union. -/
private lemma isFiniteUnionOfLocallyClosed_union {Y : Type*} [TopologicalSpace Y] {E F : Set Y}
    (hE : IsFiniteUnionOfLocallyClosed E) (hF : IsFiniteUnionOfLocallyClosed F) :
    IsFiniteUnionOfLocallyClosed (E ∪ F) := by
  rcases hE with ⟨S, hSfin, hSlc, hEeq⟩
  rcases hF with ⟨T, hTfin, hTlc, hFeq⟩
  -- Combine the two finite decompositions into a single finite family.
  refine ⟨S ∪ T, hSfin.union hTfin, ?_, ?_⟩
  · intro Z hZ
    rcases hZ with hZ | hZ
    · exact hSlc Z hZ
    · exact hTlc Z hZ
  · rw [hEeq, hFeq]
    ext x
    constructor
    · rintro (hx | hx)
      · rcases hx with ⟨t, ht, hx⟩
        exact ⟨t, Or.inl ht, hx⟩
      · rcases hx with ⟨t, ht, hx⟩
        exact ⟨t, Or.inr ht, hx⟩
    · rintro ⟨t, ht, hx⟩
      rcases ht with ht | ht
      · exact Or.inl ⟨t, ht, hx⟩
      · exact Or.inr ⟨t, ht, hx⟩

/-- Helper for Lemma 5.18.7: a finite indexed union of finite unions of locally closed subsets is
again a finite union of locally closed subsets. -/
private lemma isFiniteUnionOfLocallyClosed_iUnion {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    {S : Fin n → Set Y}
    (hS : ∀ i, IsFiniteUnionOfLocallyClosed (S i)) :
    IsFiniteUnionOfLocallyClosed (⋃ i, S i) := by
  induction n with
  | zero =>
      -- The empty indexed union is empty.
      simpa using isFiniteUnionOfLocallyClosed_empty (Y := Y)
  | succ n ih =>
      -- Split off the first piece and apply binary union stability.
      have hEq : (⋃ i : Fin (n + 1), S i) = S 0 ∪ ⋃ i : Fin n, S i.succ := by
        ext x
        simp [Fin.exists_fin_succ]
      rw [hEq]
      exact isFiniteUnionOfLocallyClosed_union (hS 0) (ih fun i ↦ hS i.succ)

/-- Helper for Lemma 5.18.7: tracing a finite union of locally closed subsets to a subspace again
produces a finite union of locally closed subsets. -/
private lemma isFiniteUnionOfLocallyClosed_preimage_val {A E : Set X}
    (hE : IsFiniteUnionOfLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed (A ↓∩ E) := by
  obtain ⟨n, S, hS, hEq⟩ := IsFiniteUnionOfLocallyClosed.exists_eq_iUnion hE
  -- Pull each locally closed piece back along the subtype map.
  rw [hEq]
  have hEq' : A ↓∩ (⋃ i, S i) = ⋃ i, A ↓∩ S i := by
    ext x
    simp
  rw [hEq']
  refine isFiniteUnionOfLocallyClosed_iUnion (Y := A) ?_
  intro i
  exact (hS i).preimage continuous_subtype_val |>.isFiniteUnionOfLocallyClosed

/-- Helper for Lemma 5.18.7: the difference of two locally closed subsets is a finite union of
locally closed subsets. -/
private lemma isFiniteUnionOfLocallyClosed_sdiff_isLocallyClosed {E E' : Set X}
    (hE : IsLocallyClosed E) (hE' : IsLocallyClosed E') :
    IsFiniteUnionOfLocallyClosed (E \ E') := by
  rcases hE with ⟨U, Z, hU, hZ, hEeq⟩
  rcases hE' with ⟨V, C, hV, hC, hE'eq⟩
  -- Split the difference according to whether a point misses the open part or the closed part of
  -- the second locally closed subset.
  have hEq : E \ E' = (U ∩ Z ∩ Vᶜ) ∪ (U ∩ V ∩ Z ∩ Cᶜ) := by
    ext x
    by_cases hxV : x ∈ V <;> by_cases hxC : x ∈ C <;>
      simp [hEeq, hE'eq, hxV, hxC, and_comm]
  rw [hEq]
  refine isFiniteUnionOfLocallyClosed_union
    (((hU.isLocallyClosed.inter hZ.isLocallyClosed).inter
      hV.isClosed_compl.isLocallyClosed).isFiniteUnionOfLocallyClosed)
    ?_
  -- The second branch is again locally closed after reordering the intersections.
  simpa [inter_assoc, inter_left_comm, inter_comm] using
    (((((hU.inter hV).inter hC.isOpen_compl).isLocallyClosed).inter
      hZ.isLocallyClosed).isFiniteUnionOfLocallyClosed)

/-- Helper for Lemma 5.18.7: subtracting a locally closed subset from a finite union of locally
closed subsets preserves the finite-union property. -/
private lemma isFiniteUnionOfLocallyClosed_sdiff_isLocallyClosed_right {E T : Set X}
    (hE : IsFiniteUnionOfLocallyClosed E) (hT : IsLocallyClosed T) :
    IsFiniteUnionOfLocallyClosed (E \ T) := by
  obtain ⟨n, S, hS, hEq⟩ := IsFiniteUnionOfLocallyClosed.exists_eq_iUnion hE
  -- Subtract `T` piecewise from the locally closed decomposition of `E`.
  rw [hEq]
  have hEq' : (⋃ i, S i) \ T = ⋃ i, S i \ T := by
    ext x
    simp
  rw [hEq']
  refine isFiniteUnionOfLocallyClosed_iUnion ?_
  intro i
  exact isFiniteUnionOfLocallyClosed_sdiff_isLocallyClosed (hS i) hT

/-- Helper for Lemma 5.18.7: subtracting a finite indexed union of locally closed subsets from a
finite union of locally closed subsets preserves the finite-union property. -/
private lemma isFiniteUnionOfLocallyClosed_sdiff_iUnion {n : ℕ} {E : Set X}
    {T : Fin n → Set X} (hE : IsFiniteUnionOfLocallyClosed E) (hT : ∀ i, IsLocallyClosed (T i)) :
    IsFiniteUnionOfLocallyClosed (E \ ⋃ i, T i) := by
  let P : ∀ n : ℕ, Prop := fun n ↦
    ∀ {E : Set X} {T : Fin n → Set X}, IsFiniteUnionOfLocallyClosed E →
      (∀ i, IsLocallyClosed (T i)) → IsFiniteUnionOfLocallyClosed (E \ ⋃ i, T i)
  have hP : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro E T hE hT
        -- The empty indexed union contributes nothing.
        simpa using hE
    | succ n ih =>
        intro E T hE hT
        -- Remove the first locally closed piece, then recurse on the tail.
        have hEq : E \ (⋃ i : Fin (n + 1), T i) = (E \ T 0) \ ⋃ i : Fin n, T i.succ := by
          ext x
          simp [Fin.exists_fin_succ, and_assoc]
        rw [hEq]
        exact ih (isFiniteUnionOfLocallyClosed_sdiff_isLocallyClosed_right hE (hT 0))
          (fun i ↦ hT i.succ)
  exact hP n hE hT

/-- Helper for Lemma 5.18.7: finite unions of locally closed subsets are stable under set
difference. -/
private lemma isFiniteUnionOfLocallyClosed_sdiff {E E' : Set X}
    (hE : IsFiniteUnionOfLocallyClosed E) (hE' : IsFiniteUnionOfLocallyClosed E') :
    IsFiniteUnionOfLocallyClosed (E \ E') := by
  obtain ⟨n, T, hT, hEq⟩ := IsFiniteUnionOfLocallyClosed.exists_eq_iUnion hE'
  -- Expand the right-hand side into finitely many locally closed pieces and subtract them one by
  -- one.
  rw [hEq]
  exact isFiniteUnionOfLocallyClosed_sdiff_iUnion hE hT

/-- Helper for Lemma 5.18.7: a nonempty finite union of locally closed subsets in a Jacobson
space contains a point closed in the ambient space. -/
private lemma nonempty_inter_closedPoints_of_isFiniteUnionOfLocallyClosed {E : Set X}
    (hEne : E.Nonempty) (hE : IsFiniteUnionOfLocallyClosed E) : (E ∩ X₀).Nonempty := by
  obtain ⟨n, S, hS, hEq⟩ := IsFiniteUnionOfLocallyClosed.exists_eq_iUnion hE
  -- Pick a nonempty locally closed piece and then use the Jacobson criterion there.
  rw [hEq, Set.nonempty_iUnion] at hEne
  obtain ⟨i, hi⟩ := hEne
  obtain ⟨x, hx, hxclosed⟩ := nonempty_inter_closedPoints hi (hS i)
  refine ⟨x, ?_, hxclosed⟩
  simpa [hEq] using Set.mem_iUnion.2 ⟨i, hx⟩

/-- Helper for Lemma 5.18.7: inclusion of finite unions of locally closed subsets is reflected by
their traces on the closed-point subspace. -/
private lemma subset_of_preimage_closedPoints_subset_of_isFiniteUnionOfLocallyClosed
    {E E' : Set X} (hE : IsFiniteUnionOfLocallyClosed E) (hE' : IsFiniteUnionOfLocallyClosed E')
    (htrace : X₀ ↓∩ E ⊆ X₀ ↓∩ E') : E ⊆ E' := by
  intro x hxE
  by_contra hxE'
  -- A point in the difference forces a closed point in the difference, contradicting the trace
  -- inclusion.
  have hdiff_ne : (E \ E').Nonempty := ⟨x, hxE, hxE'⟩
  have hdiff : IsFiniteUnionOfLocallyClosed (E \ E') := isFiniteUnionOfLocallyClosed_sdiff hE hE'
  obtain ⟨y, hyE, hyclosed⟩ :=
    nonempty_inter_closedPoints_of_isFiniteUnionOfLocallyClosed hdiff_ne hdiff
  have hytrace : (⟨y, hyclosed⟩ : X₀) ∈ X₀ ↓∩ E := by
    simpa using hyE.1
  have hytrace' := htrace hytrace
  exact hyE.2 hytrace'

/-- Helper for Lemma 5.18.7: equality of traces on the closed-point subspace determines a finite
union of locally closed subsets uniquely. -/
private lemma eq_of_preimage_closedPoints_eq_of_isFiniteUnionOfLocallyClosed
    {E E' : Set X} (hE : IsFiniteUnionOfLocallyClosed E) (hE' : IsFiniteUnionOfLocallyClosed E')
    (htrace : X₀ ↓∩ E = X₀ ↓∩ E') : E = E' := by
  -- Recover equality by reflecting inclusion in both directions.
  refine Set.Subset.antisymm
    (subset_of_preimage_closedPoints_subset_of_isFiniteUnionOfLocallyClosed hE hE' ?_)
    (subset_of_preimage_closedPoints_subset_of_isFiniteUnionOfLocallyClosed hE' hE ?_)
  · simp [htrace]
  · simp [htrace]

/-- Lemma 5.18.7: for a Jacobson space `X`, tracing a subset to the closed-point subspace `X₀`
induces a bijection between finite unions of locally closed subsets of `X` and of `X₀`. -/
theorem finiteUnionOfLocallyClosed_preimage_closedPoints_bijOn :
    Set.BijOn (fun E : Set X ↦ X₀ ↓∩ E)
      {E : Set X | IsFiniteUnionOfLocallyClosed E}
      {F : Set X₀ | IsFiniteUnionOfLocallyClosed F} := by
  refine ⟨?_, ?_, ?_⟩
  · intro E hE
    -- Trace preservation is just pullback along the subtype map.
    exact isFiniteUnionOfLocallyClosed_preimage_val hE
  · intro E hE E' hE' htrace
    -- Injectivity is the Stacks argument via a nonempty difference meeting the closed points.
    exact eq_of_preimage_closedPoints_eq_of_isFiniteUnionOfLocallyClosed hE hE' htrace
  · intro F hF
    obtain ⟨n, S, hS, hEq⟩ := IsFiniteUnionOfLocallyClosed.exists_eq_iUnion hF
    choose T hTlc hTrace using fun i ↦
      IsInducing.subtypeVal.isLocallyClosed_iff.mp (hS i)
    refine ⟨⋃ i, T i, ?_, ?_⟩
    · -- Lift the finite locally closed decomposition of `F` piecewise to `X`.
      exact isFiniteUnionOfLocallyClosed_iUnion
        (fun i ↦ (hTlc i).isFiniteUnionOfLocallyClosed)
    · -- The trace of the lifted ambient union recovers `F`.
      rw [hEq]
      ext x
      simp [hTrace]

-- Proof sketch: monotonicity of subtype trace gives the forward implication. For the converse, apply
-- injectivity from the bijection theorem to the finite unions of locally closed subsets `E \ E'`
-- and `∅`; if the traces satisfy inclusion, Jacobsonness forces `E \ E' = ∅`.
/-- The closed-point trace correspondence reflects and preserves inclusion on finite unions of
locally closed subsets. -/
theorem finiteUnionOfLocallyClosed_preimage_closedPoints_subset_iff
    {E E' : Set X} (hE : IsFiniteUnionOfLocallyClosed E) (hE' : IsFiniteUnionOfLocallyClosed E') :
    X₀ ↓∩ E ⊆ X₀ ↓∩ E' ↔ E ⊆ E' := by
  constructor
  · intro htrace
    -- This is the reflected-inclusion half of the correspondence.
    exact subset_of_preimage_closedPoints_subset_of_isFiniteUnionOfLocallyClosed hE hE' htrace
  · intro hsubset x hx
    -- Ordinary preimage monotonicity gives the forward implication.
    exact hsubset hx

-- Proof sketch: locally closed subsets are finite unions of locally closed subsets with one piece,
-- so the forward implication is by trace preservation. For the converse, use surjectivity of
-- the bijection to lift the locally closed trace to a locally closed subset of `X`, then apply the
-- inclusion-reflecting companion theorem in both directions to identify it with `E`.
/-- Within the closed-point trace correspondence of Lemma 5.18.7, finite unions of locally closed
subsets are locally closed exactly when their traces on `X₀` are locally closed. -/
theorem isLocallyClosed_iff_preimage_closedPoints_subtypeVal_of_isFiniteUnionOfLocallyClosed
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsLocallyClosed E ↔ IsLocallyClosed (X₀ ↓∩ E) := by
  constructor
  · intro hElc
    -- Locally closed subsets stay locally closed after pullback to the subtype.
    simpa using hElc.preimage continuous_subtype_val
  · intro htrace
    obtain ⟨T, hTlc, hTtrace⟩ := IsInducing.subtypeVal.isLocallyClosed_iff.mp htrace
    have hT : IsFiniteUnionOfLocallyClosed T := hTlc.isFiniteUnionOfLocallyClosed
    -- Lift the locally closed trace and identify the lift with `E` by trace injectivity.
    have hEq : E = T :=
      eq_of_preimage_closedPoints_eq_of_isFiniteUnionOfLocallyClosed hE hT hTtrace.symm
    simpa [hEq] using hTlc

-- Proof sketch: open subsets are locally closed, so the forward implication is by trace of an
-- open set. For the converse, lift the open trace to an open subset of `X` via the bijection and
-- use the inclusion-preserving correspondence to show that this lift equals `E`.
/-- Within the closed-point trace correspondence of Lemma 5.18.7, finite unions of locally closed
subsets are open exactly when their traces on `X₀` are open. -/
theorem isOpen_iff_preimage_closedPoints_subtypeVal_of_isFiniteUnionOfLocallyClosed
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsOpen E ↔ IsOpen (X₀ ↓∩ E) := by
  constructor
  · intro hEopen
    -- Open subsets pull back to open subsets of the subtype.
    exact hEopen.preimage continuous_subtype_val
  · intro htrace
    rcases isOpen_induced_iff.mp htrace with ⟨U, hUopen, hUtrace⟩
    have hU : IsFiniteUnionOfLocallyClosed U := hUopen.isLocallyClosed.isFiniteUnionOfLocallyClosed
    -- Lift the open trace to an ambient open subset and identify it with `E`.
    have hEq : E = U :=
      eq_of_preimage_closedPoints_eq_of_isFiniteUnionOfLocallyClosed hE hU hUtrace.symm
    simpa [hEq] using hUopen

-- Proof sketch: closed subsets are locally closed, so the forward implication is by trace of a
-- closed set. For the converse, lift the closed trace to a closed subset of `X` via the bijection
-- and again identify that lift with `E` using inclusion reflection.
/-- Within the closed-point trace correspondence of Lemma 5.18.7, finite unions of locally closed
subsets are closed exactly when their traces on `X₀` are closed. -/
theorem isClosed_iff_preimage_closedPoints_subtypeVal_of_isFiniteUnionOfLocallyClosed
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsClosed E ↔ IsClosed (X₀ ↓∩ E) := by
  constructor
  · intro hEclosed
    -- Closed subsets pull back to closed subsets of the subtype.
    exact hEclosed.preimage continuous_subtype_val
  · intro htrace
    rcases isClosed_induced_iff.mp htrace with ⟨Z, hZclosed, hZtrace⟩
    have hZ : IsFiniteUnionOfLocallyClosed Z :=
      hZclosed.isLocallyClosed.isFiniteUnionOfLocallyClosed
    -- Lift the closed trace to an ambient closed subset and identify it with `E`.
    have hEq : E = Z :=
      eq_of_preimage_closedPoints_eq_of_isFiniteUnionOfLocallyClosed hE hZ hZtrace.symm
    simpa [hEq] using hZclosed

end

end

/-! ### Lemma_5_18_8 (from Chap05) -/
open Set TopologicalSpace Topology
open scoped Set.Notation TopologicalSpace

universe u

section

variable {X : Type u} [TopologicalSpace X] [JacobsonSpace X]

local macro "X₀" : term => `(closedPoints X)

/-
Domain-style sampling for constructible traces on the closed-point subspace of a Jacobson space:
- primary domain: constructible subsets, retrocompact opens, and closed-point traces in Jacobson
  spaces;
- sampled owner-level declarations:
  `closedPoints`,
  `JacobsonSpace`,
  `Topology.IsConstructible.isFiniteUnionOfLocallyClosed`,
  `finiteUnionOfLocallyClosed_preimage_closedPoints_bijOn`;
- best owner abstractions: the ambient Jacobson owner `JacobsonSpace X` and the constructible-set
  owner predicate `Topology.IsConstructible`; the closed-point trace itself is the canonical bridge
  `X₀ ↓∩ E`.

Layer triage:
- `source-facing`: the constructible closed-point trace correspondence of Lemma 5.18.8;
- `core/canonical`: `JacobsonSpace X` and `IsConstructible`;
- `bridge/view`: the subtype trace `X₀ ↓∩ E` together with the finite-union bridge from
  `Lemma_5_18_7`.

Primitive data is only the ambient Jacobson structure and the owner predicate `IsConstructible`.
The finite-union-of-locally-closed decomposition and the closed-point trace bijection on those
finite unions are derived API, so this file should phrase its public statements through the
canonical trace notation `X₀ ↓∩ E` and reuse the upstream owner-facing bridge rather than spelling
out a parallel subtype-preimage surface.
-/

-- Proof sketch: combine `finiteUnionOfLocallyClosed_preimage_closedPoints_bijOn` with
-- `Topology.IsConstructible.isFiniteUnionOfLocallyClosed` and the canonical generator description
-- of constructible subsets by open retrocompact subsets. The trace surface should be stated using
-- the canonical subtype-trace notation `X₀ ↓∩ E`.
/-- Helper for Lemma 5.18.8: an open subset containing all closed points of a Jacobson space is
the whole space. -/
private lemma eq_univ_of_isOpen_of_closedPoints_subset {Y : Type*} [TopologicalSpace Y]
    [JacobsonSpace Y] {U : Set Y} (hU : IsOpen U) (hclosed : closedPoints Y ⊆ U) :
    U = Set.univ := by
  -- The Jacobson property forces the closed complement to be empty once it misses all closed
  -- points.
  apply Set.eq_univ_iff_forall.mpr
  intro x
  by_contra hx
  have hclosure : closure (Uᶜ ∩ closedPoints Y) = Uᶜ :=
    closure_inter_closedPoints hU.isClosed_compl
  have htrace_empty : Uᶜ ∩ closedPoints Y = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hy.1 (hclosed hy.2)
  have hx' : x ∈ closure (Uᶜ ∩ closedPoints Y) := by
    simpa [hclosure] using hx
  simpa [htrace_empty] using hx'

/-- Helper for Lemma 5.18.8: compactness of a Jacobson space is detected on its closed points. -/
private lemma isCompact_univ_iff_isCompact_closedPoints {Y : Type*} [TopologicalSpace Y]
    [JacobsonSpace Y] :
    IsCompact (Set.univ : Set Y) ↔ IsCompact (closedPoints Y) := by
  rw [isCompact_iff_finite_subcover, isCompact_iff_finite_subcover]
  constructor
  · intro hcompact ι V hVopen hcover
    -- Upgrade an open cover of the closed points to an open cover of the whole Jacobson space.
    have hUnionOpen : IsOpen (⋃ i, V i) := isOpen_iUnion hVopen
    have hUnionEq : (⋃ i, V i) = (Set.univ : Set Y) :=
      eq_univ_of_isOpen_of_closedPoints_subset hUnionOpen <| by
        simpa using hcover
    obtain ⟨t, ht⟩ := hcompact V hVopen <| by simpa [hUnionEq]
    exact ⟨t, Set.Subset.trans (by simp) ht⟩
  · intro hcompact ι V hVopen hcover
    -- A finite subcover of the closed points already covers the whole space by the same argument.
    have hcover_closed : closedPoints Y ⊆ ⋃ i, V i :=
      Set.Subset.trans (by simp) hcover
    obtain ⟨t, ht⟩ := hcompact V hVopen hcover_closed
    have hFiniteOpen : IsOpen (⋃ i ∈ t, V i) := isOpen_biUnion fun i _ ↦ hVopen i
    have hFiniteEq : (⋃ i ∈ t, V i) = (Set.univ : Set Y) :=
      eq_univ_of_isOpen_of_closedPoints_subset hFiniteOpen ht
    exact ⟨t, by simpa [hFiniteEq]⟩

/-- Helper for Lemma 5.18.8: for an open subset, compactness is equivalent to compactness of its
closed-point trace. -/
private lemma isCompact_iff_preimage_closedPoints_subtypeVal_of_isOpen {U : Set X}
    (hU : IsOpen U) :
    IsCompact U ↔ IsCompact (X₀ ↓∩ U) := by
  haveI : JacobsonSpace U := JacobsonSpace.of_isOpenEmbedding hU.isOpenEmbedding_subtypeVal
  have hClosedPointsImage : IsCompact (closedPoints U) ↔ IsCompact (X₀ ∩ U : Set X) := by
    rw [Subtype.isCompact_iff]
    have hpre : ((↑) : U → X) ⁻¹' X₀ = closedPoints U :=
      hU.isOpenEmbedding_subtypeVal.preimage_closedPoints
    have himage : ((↑) '' (closedPoints U) : Set X) = X₀ ∩ U := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : y ∈ ((↑) : U → X) ⁻¹' X₀ := by
          rw [hpre]
          exact hy
        exact ⟨hy', y.2⟩
      · intro hx
        have hx' : (⟨x, hx.2⟩ : U) ∈ closedPoints U := by
          rw [← hpre]
          exact hx.1
        exact ⟨⟨x, hx.2⟩, hx', rfl⟩
    simpa [himage, Set.inter_comm]
  have hTraceImage : IsCompact (X₀ ↓∩ U) ↔ IsCompact (X₀ ∩ U : Set X) := by
    rw [Subtype.isCompact_iff]
    have himage : ((↑) '' (X₀ ↓∩ U) : Set X) = X₀ ∩ U := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · intro hx
        exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
    simpa [himage]
  -- Move to the open subspace `U`, compare compactness there, and transport both sides back to
  -- the ambient space.
  calc
    IsCompact U ↔ IsCompact (Set.univ : Set U) := by rw [isCompact_iff_isCompact_univ]
    _ ↔ IsCompact (closedPoints U) := isCompact_univ_iff_isCompact_closedPoints
    _ ↔ IsCompact (X₀ ∩ U : Set X) := hClosedPointsImage
    _ ↔ IsCompact (X₀ ↓∩ U) := hTraceImage.symm

/-- Helper for Lemma 5.18.8: tracing an open subset to the closed-point subspace preserves and
reflects retrocompactness. -/
private lemma isRetrocompact_trace_iff_of_isOpen {U : Set X} (hU : IsOpen U) :
    IsRetrocompact U ↔ IsRetrocompact (X₀ ↓∩ U) := by
  constructor
  · intro hUretro
    intro V hVcompact hVopen
    rcases isOpen_induced_iff.mp hVopen with ⟨W, hWopen, hWtrace⟩
    -- Lift the compact open subset of `X₀` to a compact open subset of `X`.
    have hWtraceCompact : IsCompact (X₀ ↓∩ W) := by
      simpa [hWtrace] using hVcompact
    have hWcompact : IsCompact W :=
      (isCompact_iff_preimage_closedPoints_subtypeVal_of_isOpen hWopen).2 hWtraceCompact
    have hUWcompact : IsCompact (U ∩ W) := hUretro hWcompact hWopen
    have hUWopen : IsOpen (U ∩ W) := hU.inter hWopen
    have hTraceCompact : IsCompact (X₀ ↓∩ (U ∩ W)) :=
      (isCompact_iff_preimage_closedPoints_subtypeVal_of_isOpen hUWopen).1 hUWcompact
    -- Rewrite the trace through intersections inside the closed-point subtype.
    simpa [hWtrace, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hTraceCompact
  · intro htrace
    intro V hVcompact hVopen
    -- Test retrocompactness on a compact open `V` by passing to the trace on `X₀`.
    have hTraceVcompact : IsCompact (closedPoints X ↓∩ V) :=
      (isCompact_iff_preimage_closedPoints_subtypeVal_of_isOpen hVopen).1 hVcompact
    have hTraceVopen : IsOpen (closedPoints X ↓∩ V) := hVopen.preimage continuous_subtype_val
    have hTraceUVcompact : IsCompact ((X₀ ↓∩ U) ∩ (closedPoints X ↓∩ V)) :=
      htrace hTraceVcompact hTraceVopen
    have hUVopen : IsOpen (U ∩ V) := hU.inter hVopen
    have hTraceCompact : IsCompact (X₀ ↓∩ (U ∩ V)) := by
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hTraceUVcompact
    exact (isCompact_iff_preimage_closedPoints_subtypeVal_of_isOpen hUVopen).2 hTraceCompact

/-- Helper for Lemma 5.18.8: every open retrocompact subset of the closed-point subspace lifts to
an open retrocompact subset of the ambient Jacobson space. -/
private lemma trace_open_retrocompact_lift {V : Set X₀}
    (hVopen : IsOpen V) (hVretro : IsRetrocompact V) :
    ∃ U : Set X, IsOpen U ∧ IsRetrocompact U ∧ V = X₀ ↓∩ U := by
  rcases isOpen_induced_iff.mp hVopen with ⟨U, hUopen, hUtrace⟩
  have hTraceRetro : IsRetrocompact (X₀ ↓∩ U) := by
    simpa [hUtrace] using hVretro
  have hUretro : IsRetrocompact U := (isRetrocompact_trace_iff_of_isOpen hUopen).2 hTraceRetro
  exact ⟨U, hUopen, hUretro, hUtrace.symm⟩

/-- Lemma 5.18.8: for a Jacobson space `X`, tracing a subset to the closed-point subspace `X₀`
induces a bijective, inclusion-preserving correspondence between constructible subsets of `X` and
constructible subsets of `X₀`. -/
theorem isConstructible_preimage_closedPoints_bijOn :
    Set.BijOn
      (fun E : Set X ↦ X₀ ↓∩ E)
      {E : Set X | IsConstructible E}
      {F : Set X₀ | IsConstructible F} := by
  -- Route correction: surjectivity is proved by constructible induction on open retrocompact
  -- generators, not by the earlier false global `iff` route.
  refine ⟨?_, ?_, ?_⟩
  · intro E hE
    -- Constructible subsets stay constructible after tracing to the closed-point subtype.
    induction hE using IsConstructible.empty_union_induction with
    | open_retrocompact U hUopen hUretro =>
        exact ((isRetrocompact_trace_iff_of_isOpen hUopen).1 hUretro).isConstructible
          (hUopen.preimage continuous_subtype_val)
    | union s hs t ht hs' ht' =>
        simpa using hs'.union ht'
    | compl s hs hs' =>
        simpa using hs'.compl
  · intro E hE E' hE' htrace
    -- Reduce injectivity to the finite-union correspondence from Lemma 5.18.7.
    have hsubset : E ⊆ E' :=
      (finiteUnionOfLocallyClosed_preimage_closedPoints_subset_iff
        hE.isFiniteUnionOfLocallyClosed hE'.isFiniteUnionOfLocallyClosed).1 <| by
          simpa [htrace]
    have hsubset' : E' ⊆ E :=
      (finiteUnionOfLocallyClosed_preimage_closedPoints_subset_iff
        hE'.isFiniteUnionOfLocallyClosed hE.isFiniteUnionOfLocallyClosed).1 <| by
          simpa [htrace]
    exact Set.Subset.antisymm hsubset hsubset'
  · intro F hF
    -- Lift constructible subsets of `X₀` by the same generator induction.
    induction hF using IsConstructible.empty_union_induction with
    | open_retrocompact V hVopen hVretro =>
        rcases trace_open_retrocompact_lift hVopen hVretro with ⟨U, hUopen, hUretro, hUtrace⟩
        exact ⟨U, hUretro.isConstructible hUopen, hUtrace.symm⟩
    | union s hs t ht hs' ht' =>
        rcases hs' with ⟨E, hE, hEtrace⟩
        rcases ht' with ⟨E', hE', hEtrace'⟩
        refine ⟨E ∪ E', hE.union hE', ?_⟩
        ext x
        simp [hEtrace, hEtrace']
    | compl s hs hs' =>
        rcases hs' with ⟨E, hE, hEtrace⟩
        refine ⟨Eᶜ, hE.compl, ?_⟩
        ext x
        simp [hEtrace]

-- Proof sketch: monotonicity of subtype trace gives the forward implication. For the converse, apply
-- injectivity from the constructible bijection theorem to `E \ E'`, using that constructible
-- subsets are closed under Boolean operations.
/-- The constructible closed-point trace correspondence reflects and preserves inclusion. -/
theorem isConstructible_preimage_closedPoints_subset_iff
    {E E' : Set X} (hE : IsConstructible E) (hE' : IsConstructible E') :
    X₀ ↓∩ E ⊆ X₀ ↓∩ E' ↔ E ⊆ E' := by
  -- Use the finite-union reflection theorem after converting constructible sets to that API.
  exact finiteUnionOfLocallyClosed_preimage_closedPoints_subset_iff
    hE.isFiniteUnionOfLocallyClosed hE'.isFiniteUnionOfLocallyClosed

-- Proof sketch: the forward implication is the `MapsTo` direction of the constructible
-- closed-point trace bijection above. For the converse, use its surjectivity.
/-- A constructible subset of a Jacobson space has constructible trace on the closed-point
subspace. The converse requires restricting to traces that actually come from constructible
ambient subsets; it is supplied by the bijection theorem above, not by an arbitrary fixed ambient
subset with the same closed-point trace. -/
theorem isConstructible_preimage_closedPoints_subtypeVal {E : Set X} (hE : IsConstructible E) :
    IsConstructible (X₀ ↓∩ E) := by
  -- This is exactly the `MapsTo` part of the bijection.
  exact isConstructible_preimage_closedPoints_bijOn.mapsTo hE

-- Proof sketch: for an open subset `U`, constructibility is equivalent to retrocompactness, so the
-- previous constructible closed-point trace equivalence upgrades directly to the open
-- retrocompactness statement.
/-- Tracing an open subset to the closed-point subspace preserves and reflects retrocompactness in
a Jacobson space. -/
theorem isRetrocompact_iff_preimage_closedPoints_subtypeVal_of_isOpen {U : Set X} (hU : IsOpen U) :
    IsRetrocompact U ↔ IsRetrocompact (X₀ ↓∩ U) := by
  -- Reuse the compactness bridge on open subspaces.
  exact isRetrocompact_trace_iff_of_isOpen hU

end
