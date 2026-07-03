import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.NoetherianSpace

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_9_1 (from Chap05) -/
universe u

/-
Domain-style sampling for locally Noetherian spaces:
- primary domain: topological Noetherianity and its local open-subspace form
- same-domain declarations inspected:
  `TopologicalSpace.NoetherianSpace`,
  `TopologicalSpace.NoetherianSpace.set`,
  `TopologicalSpace.noetherianSpace_set_iff`,
  `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`

Owner-abstraction choice:
- `source-facing`: `TopologicalSpace.LocallyNoetherianSpace`
- `core/canonical`: `TopologicalSpace.NoetherianSpace` for each open subspace
- `bridge/view`: the derived neighborhood-filter reformulation of the owner field

Primitive data versus derived API:
- primitive data: for each `x : X`, an open neighborhood whose induced topology is Noetherian
- derived API: the neighborhood-filter restatement used by later files
-/

variable {X : Type u} [TopologicalSpace X]

open Topology

namespace TopologicalSpace

/- Companion recall: the textbook notion that a topological space is Noetherian is the canonical
mathlib predicate `TopologicalSpace.NoetherianSpace`, and the descending chain condition on closed
subsets is one of its equivalent formulations via `TopologicalSpace.noetherianSpace_TFAE`. -/
recall TopologicalSpace.NoetherianSpace

/-- Definition 5.9.1: a topological space is locally Noetherian if every point has an open
neighbourhood whose induced topology is Noetherian. The owner field stores this source-facing open
formulation directly, while the neighborhood-filter formulation is derived API built from the
canonical predicate `TopologicalSpace.NoetherianSpace`. -/
class LocallyNoetherianSpace (X : Type u) [TopologicalSpace X] : Prop where
  exists_open (x : X) : ∃ U : Opens X, x ∈ U ∧ NoetherianSpace U

private theorem noetherianSpace_inter_opens (U : Opens X) [NoetherianSpace U] (s : Set X) :
    NoetherianSpace (((U : Set X) ∩ s : Set X)) := by
  let hU : NoetherianSpace (U : Set X) := inferInstance
  exact
    (noetherianSpace_set_iff ((U : Set X) ∩ s)).2 fun t ht ↦
      (noetherianSpace_set_iff (U : Set X)).1 hU t <|
        Set.Subset.trans ht Set.inter_subset_left

/-- Derived neighborhood-filter bridge: every neighborhood contains a Noetherian neighborhood. -/
theorem LocallyNoetherianSpace.exists_mem_nhds_subset [LocallyNoetherianSpace X] (x : X)
    {s : Set X} (hs : s ∈ 𝓝 x) :
    ∃ t : Set X, t ∈ 𝓝 x ∧ t ⊆ s ∧ NoetherianSpace t := by
  rcases LocallyNoetherianSpace.exists_open x with ⟨U, hxU, hU⟩
  refine ⟨((U : Set X) ∩ s : Set X), Filter.inter_mem (U.2.mem_nhds hxU) hs,
    Set.inter_subset_right, ?_⟩
  letI : NoetherianSpace U := hU
  simpa using noetherianSpace_inter_opens U s

/-- Derived neighborhood-filter bridge: a point admits a Noetherian neighborhood in its
neighborhood filter. -/
theorem LocallyNoetherianSpace.exists_mem_nhds [LocallyNoetherianSpace X] (x : X) :
    ∃ s : Set X, s ∈ 𝓝 x ∧ NoetherianSpace s := by
  have h_univ : (Set.univ : Set X) ∈ 𝓝 x := Filter.univ_mem
  rcases LocallyNoetherianSpace.exists_mem_nhds_subset x h_univ with
    ⟨s, hs_nhds, _, hs_noeth⟩
  exact ⟨s, hs_nhds, hs_noeth⟩

/-- Every Noetherian topological space is locally Noetherian. -/
instance [NoetherianSpace X] : LocallyNoetherianSpace X where
  exists_open _ := ⟨⊤, by simp, noetherian_univ_iff.2 inferInstance⟩

end TopologicalSpace

/-! ### Lemma_5_9_2 (from Chap05) -/
/- Domain-style sampling for Lemma 5.9.2:
- primary domain: Noetherian topological spaces and irreducible components
- sampled owner declarations:
  `TopologicalSpace.NoetherianSpace.set`,
  `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`,
  `TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent`,
  `TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible`
- best owner abstraction: the canonical owner is `TopologicalSpace.NoetherianSpace`
- primitive data: the ambient `NoetherianSpace X` instance
- derived API: Noetherianity of subspaces, finiteness of `irreducibleComponents X`, and the
  existence of a nonempty open subset inside an irreducible component

Layer triage:
- `source-facing`: the three textbook consequences recorded in Lemma 5.9.2
- `core/canonical`: the existing `TopologicalSpace.NoetherianSpace` API in mathlib
- `bridge/view`: none needed here, since each clause already has the exact canonical owner-side
  statement

The current file stored only derived API as parallel local theorem names. Since the owner object
and the exact interfaces already exist upstream, the right refinement is direct canonical recall.
-/

/- Lemma 5.9.2 (1): every subspace of a Noetherian topological space is Noetherian. -/
recall TopologicalSpace.NoetherianSpace.set

/- Lemma 5.9.2 (2): a Noetherian topological space has only finitely many irreducible
components. -/
recall TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/- Lemma 5.9.2 (3): every irreducible component of a Noetherian topological space contains a
nonempty open subset of the ambient space. -/
recall TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent

/-! ### Lemma_5_9_3 (from Chap05) -/
/- Domain-style sampling for Noetherianity under continuous/open maps:
- owner abstractions: `TopologicalSpace.NoetherianSpace` and the chapter owner
  `TopologicalSpace.LocallyNoetherianSpace`
- same-domain declarations inspected:
  `TopologicalSpace.NoetherianSpace.range`,
  `TopologicalSpace.noetherianSpace_of_surjective`,
  `TopologicalSpace.LocallyNoetherianSpace.exists_open`,
  `IsOpenMap.isOpen_range`

Layer triage:
- `core/canonical`: `TopologicalSpace.NoetherianSpace.range`
- `source-facing`: local Noetherianity of the range under an open map
- `bridge/view`: the restricted map `U → Set.range f`

Primitive data for clause `(2)` is the owner class `LocallyNoetherianSpace`; the textbook bridge
`LocallyNoetherianSpace.exists_open` and the range neighborhood lemmas for open maps are
derived API. So this file should recall the canonical range theorem for clause `(1)` and keep only
the source-facing permanence theorem for clause `(2)`. -/

open Set Topology

universe u v

namespace TopologicalSpace

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Companion recall for clause (1): the image of a Noetherian topological space under a continuous
map is Noetherian for the induced topology. -/
recall NoetherianSpace.range

-- Proof sketch: for a point `y` of `Set.range f`, choose a preimage `x : X`. By local
-- Noetherianity, `x` has an open Noetherian neighbourhood `U`. Restricting `f` to `U` gives an
-- open continuous map `U → Set.range f`, so its range is an open neighbourhood of `y` in
-- `Set.range f`; clause `(1)` shows that this range is Noetherian.
/-- Lemma 5.9.3: if every point of `X` has an open Noetherian neighbourhood and `f` is open, then
the image `f(X)` is locally Noetherian for the induced topology. -/
theorem LocallyNoetherianSpace.range [LocallyNoetherianSpace X]
    (hcont : Continuous f) (hopen : IsOpenMap f) :
    LocallyNoetherianSpace (Set.range f) := by
  refine ⟨fun y ↦ ?_⟩
  rcases y with ⟨_, ⟨x, rfl⟩⟩
  rcases LocallyNoetherianSpace.exists_open x with ⟨U, hUx, hU⟩
  let g : U → Set.range f := fun z ↦ ⟨f z, ⟨z, rfl⟩⟩
  let xU : U := ⟨x, hUx⟩
  have hg : Continuous g := by
    simpa [g] using (hcont.comp continuous_subtype_val).subtype_mk fun z ↦ ⟨z, rfl⟩
  have hgOpen : IsOpenMap g := by
    simpa [g] using (hopen.comp U.2.isOpenMap_subtype_val).subtype_mk fun z ↦ ⟨z, rfl⟩
  refine ⟨⟨Set.range g, hgOpen.isOpen_range⟩, mem_range_self xU, ?_⟩
  · simpa using NoetherianSpace.range g hg

end

end TopologicalSpace

/-! ### Lemma_5_9_4 (from Chap05) -/
/- Domain-style sampling for finite unions of Noetherian subspaces:
- primary domain: Noetherian topological spaces and finite unions of Noetherian subspaces
- sampled owner declarations:
  `TopologicalSpace.NoetherianSpace`,
  `TopologicalSpace.NoetherianSpace.set`,
  `TopologicalSpace.NoetherianSpace.range`,
  `TopologicalSpace.NoetherianSpace.iUnion`
- best owner abstraction: the canonical owner is `TopologicalSpace.NoetherianSpace`
- primitive data: a finite family `Xᵢ ⊆ X` together with `NoetherianSpace Xᵢ` for each index
- derived API: the induced Noetherianity of the union, already exposed upstream as the owner theorem
  `TopologicalSpace.NoetherianSpace.iUnion`

Layer triage:
- `source-facing`: Lemma 5.9.4, asserting that a finite union of Noetherian subspaces is
  Noetherian
- `core/canonical`: `TopologicalSpace.NoetherianSpace.iUnion`
- `bridge/view`: none needed, since the source statement already coincides with the owner theorem

This file should therefore stay as a direct canonical recall rather than introducing a parallel
local lemma or an unpacked specification theorem.
-/

/- Lemma 5.9.4: if `X` is a topological space and `Xᵢ ⊆ X` is a finite family of subsets such
that each `Xᵢ` is Noetherian with the induced topology, then the union `⋃ i, Xᵢ` is Noetherian
with the induced topology. This is exactly the canonical theorem
`TopologicalSpace.NoetherianSpace.iUnion`. -/
recall TopologicalSpace.NoetherianSpace.iUnion

/-! ### Example_5_9_5 (from Chap05) -/
open Set Topology TopologicalSpace
open Topology.WithLowerSet Topology.IsLowerSet

-- Proof sketch: for `x : WithLowerSet ℕ+`, the initial segment `Iic x` is the canonical
-- neighbourhood of `x` in the lower-set topology and is finite, hence Noetherian as a subspace.
/-- The lower-set topology on the positive integers is locally Noetherian. -/
instance : TopologicalSpace.LocallyNoetherianSpace (WithLowerSet ℕ+) where
  exists_open x := by
    let _ : Finite (Iic x : Set (WithLowerSet ℕ+)) := by
      simpa [ofLowerSetOrderIso.preimage_Iic] using
        (Set.finite_Iic (ofLowerSet x)).preimage_embedding ofLowerSetOrderIso.toEquiv.toEmbedding
    refine ⟨⟨Iic x, isOpen_iff_isLowerSet.2 (isLowerSet_Iic x)⟩, by simp, inferInstance⟩

-- Proof sketch: in the lower-set topology, closed subsets are exactly upper sets. If `x` were a
-- closed point, then `{x}` would be an upper set, hence would also contain `x + 1`, absurd.
/-- Example 5.9.5: the positive integers with the lower-set topology have no closed points, i.e.
`closedPoints (WithLowerSet ℕ+) = ∅`. -/
theorem pnat_withLowerSet_has_no_closed_points :
    closedPoints (WithLowerSet ℕ+) = ∅ := by
  ext x
  rw [Set.mem_empty_iff_false, mem_closedPoints_iff, isClosed_iff_isUpper]
  constructor
  · intro hx
    let y : WithLowerSet ℕ+ := toLowerSet (ofLowerSet x + 1)
    have hxy : x < y := by
      change ofLowerSet x < ofLowerSet y
      simp [y]
    have hy : y ∈ ({x} : Set (WithLowerSet ℕ+)) := hx hxy.le (by simp)
    exact (ne_of_lt hxy) <| by simpa [y] using hy.symm
  · intro hx
    cases hx

/-! ### Lemma_5_9_6 (from Chap05) -/
universe u

open Set Topology

variable {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace

/- Domain-style sampling for Lemma 5.9.6:
- primary domain: Noetherian topological spaces and local connectedness
- sampled owner declarations:
  `TopologicalSpace.LocallyNoetherianSpace.exists_mem_nhds_subset`,
  `TopologicalSpace.locallyConnectedSpace_iff_connected_subsets`,
  `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`,
  `TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent`
- best owner abstraction: the core owner is `TopologicalSpace.LocallyConnectedSpace`; the source
  hypothesis is the chapter owner `TopologicalSpace.LocallyNoetherianSpace`
- primitive data: a Noetherian neighborhood around each point
- derived API: a preconnected neighborhood basis, hence a `LocallyConnectedSpace` instance

Layer triage:
- `source-facing`: Lemma 5.9.6, asserting that locally Noetherian spaces are locally connected
- `core/canonical`: `TopologicalSpace.LocallyConnectedSpace`
- `bridge/view`: the private construction of a preconnected neighborhood inside a Noetherian space

There is no upstream owner theorem in mathlib for the Noetherian-to-locally-connected bridge, so
this file exposes that bridge as the public owner instance
`TopologicalSpace.NoetherianSpace.locallyConnectedSpace` and then uses it for the source-facing
locally Noetherian statement.
-/

private theorem exists_preconnected_mem_nhds [NoetherianSpace X] (x : X) :
    ∃ V : Set X, V ∈ 𝓝 x ∧ IsPreconnected V := by
  classical
  let Z : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let R : irreducibleComponents X → irreducibleComponents X → Prop :=
    fun A B ↦ ((A : Set X) ∩ (B : Set X)).Nonempty
  let T : Set (irreducibleComponents X) := {A | Relation.ReflTransGen R Z A}
  let V : Set X := ⋃ A ∈ T, (A : Set X)
  have hR_symm : Symmetric R := fun A B h ↦ by
    simpa [R, inter_comm] using h
  have hT_path {A B : irreducibleComponents X} (hA : A ∈ T)
      (hAB : Relation.ReflTransGen R A B) :
      B ∈ T ∧
        Relation.ReflTransGen
          (fun A B : irreducibleComponents X ↦
            (((A : Set X) ∩ (B : Set X)).Nonempty) ∧ A ∈ T) A B := by
    induction hAB generalizing hA with
    | refl =>
        exact ⟨hA, .refl⟩
    | @tail B C hAB hBC ih =>
        rcases ih hA with ⟨hB, hAB'⟩
        exact ⟨hB.tail hBC, hAB'.tail ⟨hBC, hB⟩⟩
  have hT_preconnected (A : irreducibleComponents X) (hA : A ∈ T) :
      IsPreconnected (A : Set X) :=
    A.2.1.isConnected.isPreconnected
  have hV_preconnected : IsPreconnected V := by
    have hpre : IsPreconnected (⋃ A ∈ T, (A : Set X)) := by
      refine IsPreconnected.biUnion_of_reflTransGen
        (fun A hA ↦ hT_preconnected A hA) ?_
      intro A hA B hB
      have hAZ : Relation.ReflTransGen R A Z :=
        (Relation.ReflTransGen.symmetric hR_symm) hA
      exact (hT_path hA (hAZ.trans hB)).2
    simpa [V] using hpre
  haveI : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  let U : Set (irreducibleComponents X) := Tᶜ
  have hU_finite : U.Finite := Set.toFinite U
  have hU_union_closed : IsClosed (⋃ A ∈ U, (A : Set X)) := by
    simpa [Set.sUnion_image] using
      (hU_finite.image fun A : irreducibleComponents X ↦ (A : Set X)).isClosed_biUnion
        fun W hW ↦ by
          rcases hW with ⟨A, hAU, rfl⟩
          simpa using isClosed_of_mem_irreducibleComponents (A : Set X) A.2
  have hV_eq : V = (⋃ A ∈ U, (A : Set X))ᶜ := by
    ext y
    constructor
    · intro hy hyU
      rcases mem_iUnion₂.1 hy with ⟨A, hAT, hyA⟩
      rcases mem_iUnion₂.1 hyU with ⟨B, hBU, hyB⟩
      exact hBU (hAT.tail <| by
        simpa [R, inter_comm] using (show ((A : Set X) ∩ B).Nonempty from ⟨y, hyA, hyB⟩))
    · intro hy
      have hy' : y ∈ ⋃₀ irreducibleComponents X := by
        simp [sUnion_irreducibleComponents]
      rcases mem_sUnion.1 hy' with ⟨A, hA, hyA⟩
      let A' : irreducibleComponents X := ⟨A, hA⟩
      by_cases hAT : A' ∈ T
      · exact mem_iUnion₂.2 ⟨A', hAT, hyA⟩
      · exact False.elim (hy (mem_iUnion₂.2 ⟨A', hAT, hyA⟩))
  have hV_open : IsOpen V := by
    rw [hV_eq]
    exact hU_union_closed.isOpen_compl
  have hxV : x ∈ V := by
    exact mem_iUnion₂.2 ⟨Z, .refl, mem_irreducibleComponent⟩
  exact ⟨V, hV_open.mem_nhds hxV, hV_preconnected⟩

/-- A Noetherian topological space is locally connected. -/
instance NoetherianSpace.locallyConnectedSpace [NoetherianSpace X] :
    LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  let x' : U := ⟨x, mem_of_mem_nhds hU⟩
  letI : NoetherianSpace U := inferInstance
  rcases exists_preconnected_mem_nhds x' with ⟨V, hV, hVconn⟩
  let W : Set X := Subtype.val '' V
  have hW_nhdsWithin : W ∈ 𝓝[U] x := by
    simpa [W] using (mem_nhds_subtype_iff_nhdsWithin).1 hV
  have hW_nhds : W ∈ 𝓝 x := by
    rwa [nhdsWithin_eq_nhds.2 hU] at hW_nhdsWithin
  refine ⟨W, hW_nhds, hVconn.image _ continuous_subtype_val.continuousOn, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact z.2

attribute [instance 100] NoetherianSpace.locallyConnectedSpace

/-- Lemma 5.9.6: a locally Noetherian topological space is locally connected. -/
instance locallyConnectedSpace_of_locallyNoetherianSpace [LocallyNoetherianSpace X] :
    LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  rcases LocallyNoetherianSpace.exists_mem_nhds_subset x hU with ⟨E, hE, hEU, hE_noeth⟩
  letI : NoetherianSpace E := hE_noeth
  let x' : E := ⟨x, mem_of_mem_nhds hE⟩
  letI : LocallyConnectedSpace E := NoetherianSpace.locallyConnectedSpace
  rcases
      (locallyConnectedSpace_iff_connected_subsets.mp (show LocallyConnectedSpace E from inferInstance))
        x' Set.univ Filter.univ_mem with
    ⟨V, hV, hV_preconnected, _⟩
  let W : Set X := Subtype.val '' V
  have hW_subset : W ⊆ U := by
    rintro y ⟨z, hz, rfl⟩
    exact hEU z.2
  have hW_within : W ∈ 𝓝[E] x := by
    simpa [W] using (mem_nhds_subtype_iff_nhdsWithin).1 hV
  have hW : W ∈ 𝓝 x := by
    rwa [nhdsWithin_eq_nhds.2 hE] at hW_within
  refine ⟨W, hW, hV_preconnected.image _ continuous_subtype_val.continuousOn, hW_subset⟩

end TopologicalSpace
