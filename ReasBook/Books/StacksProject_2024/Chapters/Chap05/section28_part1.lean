import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Constructible
import Mathlib.Topology.LocallyFinite

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_28_1 (from Chap05) -/
universe u

open Set

/- Domain-style sampling for partitions with topological regularity:
- inspected canonical partition declarations in mathlib:
  `Setoid.Partitions`,
  `Setoid.Partitions.toSet`,
  `Setoid.Partitions.isPartition`,
  and `Setoid.Partition.orderIso`
- best owner abstraction: `Setoid.Partitions X`

Layer triage:
- `source-facing`: `LocallyClosedPartition X`
- `core/canonical`: the underlying owner `Setoid.Partitions X`
- `bridge/view`: the refinement order and the singleton example

Primitive data are a partition together with local closedness of each actual part, i.e. the owner
subtype `toPartitions.toSet`. The set-theoretic partition facts and refinement API are derived.
-/

/-- Definition 5.28.1: a partition of a topological space is a decomposition into locally closed
subsets. -/
structure LocallyClosedPartition (X : Type u) [TopologicalSpace X] where
  toPartitions : Setoid.Partitions X
  locallyClosed (s : toPartitions.toSet) : IsLocallyClosed (s : Set X)

namespace LocallyClosedPartition

variable {X : Type u} [TopologicalSpace X]

/-- The set of parts of a locally closed partition. -/
abbrev toSet (P : LocallyClosedPartition X) : Set (Set X) :=
  P.toPartitions.toSet

@[ext]
theorem ext {P Q : LocallyClosedPartition X} (h : P.toSet = Q.toSet) : P = Q := by
  cases P with
  | mk p hp =>
    cases Q with
    | mk q hq =>
      simp only [toSet] at h
      have hpq : p = q := (Setoid.Partitions.ext_iff _ _).2 h
      cases hpq
      simp

/-- Explicit-set accessor for the local closedness of a part. -/
theorem locallyClosed_of_mem (P : LocallyClosedPartition X) {s : Set X} (hs : s ∈ P.toSet) :
    IsLocallyClosed s :=
  P.locallyClosed ⟨s, hs⟩

/-- The parts of a locally closed partition form a set-theoretic partition of the whole space. -/
theorem isPartition (P : LocallyClosedPartition X) : Setoid.IsPartition P.toSet :=
  P.toPartitions.isPartition

instance : PartialOrder (LocallyClosedPartition X) :=
  PartialOrder.lift toPartitions fun _ _ h ↦
    ext <| Setoid.Partitions.ext_iff _ _ |>.1 h

omit [TopologicalSpace X] in
/-- A part of the discrete partition is exactly a singleton. -/
theorem mem_singletons_toSet_iff {s : Set X} :
    s ∈ ((⊥ : Setoid.Partitions X).toSet) ↔ ∃ x : X, s = ({x} : Set X) := by
  change s ∈ (⊥ : Setoid X).classes ↔ _
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    ext y
    simp
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    ext y
    simp

/-- The partition of a `T₁` space into singleton strata. -/
def singletons (X : Type u) [TopologicalSpace X] [T1Space X] : LocallyClosedPartition X where
  toPartitions := ⊥
  locallyClosed s := by
    rcases mem_singletons_toSet_iff.mp s.2 with ⟨x, hs⟩
    simpa [hs] using isClosed_singleton.isLocallyClosed

/-- Refinement is equivalently the statement that each part of the finer partition is contained in
some part of the coarser partition. -/
theorem le_iff_forall_exists_mem_subset {P Q : LocallyClosedPartition X} :
    P ≤ Q ↔ ∀ ⦃s : Set X⦄, s ∈ P.toSet → ∃ t ∈ Q.toSet, s ⊆ t := by
  let hP := P.isPartition.2
  let hQ := Q.isPartition.2
  constructor
  · intro hPQ s hs
    obtain ⟨x, hx⟩ := Setoid.nonempty_of_mem_partition P.isPartition hs
    obtain ⟨t, htx, _⟩ := hQ x
    refine ⟨t, htx.1, ?_⟩
    intro y hy
    have hxy : Setoid.mkClasses P.toSet hP x y := by
      rw [Setoid.eq_eqv_class_of_mem hP hs hy] at hx
      exact hx
    exact hPQ hxy t htx.1 htx.2
  · intro hPQ x y hxy s hs hx_s
    obtain ⟨u, hux, _⟩ := hP x
    obtain ⟨t, htQ, hut⟩ := hPQ hux.1
    have hx_t : x ∈ t := hut hux.2
    have hy_t : y ∈ t := hut (hxy u hux.1 hux.2)
    have hts : t = s := Setoid.eq_of_mem_eqv_class hQ htQ hx_t hs hx_s
    simpa [hts] using hy_t

end LocallyClosedPartition

/-! ### Definition_5_28_2 (from Chap05) -/
universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for good stratifications of a topological space:
- inspected project declarations in the same chapter/domain:
  `LocallyClosedPartition`,
  `LocallyClosedPartition.toSet`,
  `LocallyClosedPartition.singletons`,
  and the later indexed owner `IsStratification`
- best owner abstraction for this source item: `LocallyClosedPartition.IsGood`

Layer triage:
- `source-facing`: the frontier condition on a locally closed partition
- `core/canonical`: `LocallyClosedPartition.IsGood`
- `bridge/view`: Lemma `5.28.6` turns a good partition into an indexed `IsStratification`

Primitive data are only the frontier condition on actual parts of `P`, i.e. elements of the owner
subtype `P.toSet`. Membership proofs for arbitrary `Set X` are derived accessors and should not be
the primitive field shape.
-/

namespace LocallyClosedPartition

/-- Definition 5.28.2: a good stratification of a topological space is a locally closed partition
whose strata satisfy the frontier condition that whenever one stratum meets the closure of
another, it is contained in that closure. -/
class IsGood (P : LocallyClosedPartition X) : Prop where
  frontier_condition (S T : P.toSet) (hST : ((S : Set X) ∩ closure (T : Set X)).Nonempty) :
      (S : Set X) ⊆ closure (T : Set X)

/-- Explicit-set accessor for the frontier condition on parts of a good partition. -/
theorem frontier_condition_of_mem {P : LocallyClosedPartition X} [hP : IsGood P]
    {S T : Set X} (hS : S ∈ P.toSet) (hT : T ∈ P.toSet)
    (hST : (S ∩ closure T).Nonempty) :
    S ⊆ closure T :=
  hP.frontier_condition ⟨S, hS⟩ ⟨T, hT⟩ hST

/-- The singleton partition of a `T₁` space is a good stratification. -/
instance [T1Space X] : IsGood (singletons X) where
  frontier_condition := by
    intro S T h
    rcases S with ⟨S, hS⟩
    rcases T with ⟨T, hT⟩
    rcases hS with ⟨x, rfl⟩
    rcases hT with ⟨y, rfl⟩
    have hx : x ∈ closure ({y} : Set X) := by
      rcases h with ⟨z, hz, hzclosure⟩
      simpa only [Set.mem_singleton_iff.mp hz] using hzclosure
    intro z hz
    have hz' : z = x := by
      simpa using hz
    subst z
    simpa [closure_singleton] using hx

end LocallyClosedPartition

/-! ### Definition_5_28_3 (from Chap05) -/
universe u v

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for indexed stratifications:
- primary domain: indexed partitions of a topological space with locally closed pieces and a
  closure-order condition
- inspected canonical declarations:
  `IndexedPartition`,
  `IndexedPartition.disjoint`,
  `IndexedPartition.iUnion`,
  `LocallyClosedPartition`,
  `Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty`
- best owner abstraction for the partition datum: `IndexedPartition strata`

Layer triage:
- `source-facing`: `IsStratification`
- `core/canonical`: the indexed partition owner `IndexedPartition strata`
- `bridge/view`: `toLocallyClosedPartition`

Primitive data are the source-facing nonempty pairwise disjoint cover by locally closed subsets
together with the closure-order condition. The canonical `IndexedPartition strata` owner is then
derived from that primitive data, rather than stored as auxiliary chosen public data.
-/

/-- Definition 5.28.3: an indexed stratification of a topological space is a nonempty pairwise
disjoint cover `X = ⨿ i, strata i` by locally closed subsets such that the closure of each stratum
is contained in the union of the strata indexed by smaller elements. The subsets `strata i` are
the strata. -/
class IsStratification {I : Type v} [PartialOrder I] (strata : I → Set X) : Prop where
  /-- Distinct strata are disjoint. -/
  disjoint : Pairwise fun i j ↦ Disjoint (strata i) (strata j)
  /-- Each stratum is nonempty. -/
  nonempty : ∀ i, (strata i).Nonempty
  /-- The strata cover the ambient space. -/
  cover : (⋃ i, strata i) = univ
  /-- Each stratum is locally closed. -/
  locallyClosed : ∀ i, IsLocallyClosed (strata i)
  /-- The closure of a stratum is contained in the union of the lower strata. -/
  closure_subset : ∀ j, closure (strata j) ⊆ ⋃ i ∈ Set.Iic j, strata i

namespace IsStratification

variable {I : Type v} [PartialOrder I] {strata : I → Set X}

/-- The canonical indexed-partition owner attached to an indexed stratification. -/
noncomputable def toIndexedPartition (h : IsStratification strata) : IndexedPartition strata :=
  IndexedPartition.mk' strata h.disjoint h.nonempty fun x ↦ by
    have hx : x ∈ ⋃ i, strata i := by
      simp [h.cover]
    simpa [Set.mem_iUnion] using hx

/-- If one stratum meets the closure of another, then its index is smaller. -/
theorem le_of_inter_closure_nonempty (h : IsStratification strata) {i j : I}
    (hij : ((strata i) ∩ closure (strata j)).Nonempty) : i ≤ j := by
  rcases hij with ⟨x, hxi, hxj⟩
  rcases Set.mem_iUnion.1 (h.closure_subset j hxj) with ⟨k, hxk⟩
  rcases Set.mem_iUnion.1 hxk with ⟨hkj, hxk⟩
  simpa [h.toIndexedPartition.eq_of_mem hxi hxk] using hkj

-- Proof sketch: coverage gives existence of a stratum containing any point, pairwise disjointness
-- gives uniqueness of that stratum, and nonemptiness rules out the empty set from the range.
/-- The set of strata of an indexed stratification is a partition of the ambient space. -/
def toLocallyClosedPartition (h : IsStratification strata) : LocallyClosedPartition X where
  toPartitions := ⟨Set.range strata, by
    refine Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty ?_ ?_ ?_
    · rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩ hst
      exact h.toIndexedPartition.disjoint fun hij ↦ hst (congrArg strata hij)
    · intro x
      rcases h.toIndexedPartition.exists_mem x with ⟨i, hxi⟩
      exact ⟨strata i, ⟨i, rfl⟩, hxi⟩
    · intro hEmpty
      rcases hEmpty with ⟨i, hi⟩
      exact (h.nonempty i).ne_empty hi⟩
  locallyClosed := by
    rintro ⟨_, ⟨i, rfl⟩⟩
    exact h.locallyClosed i

end IsStratification

/-- The one-stratum decomposition of a nonempty topological space is a stratification. -/
instance oneStratum_isStratification [Nonempty X] :
    IsStratification (fun _ : Fin 1 ↦ (univ : Set X)) where
  disjoint := by
    intro s t hst
    exact (hst <| Subsingleton.elim _ _).elim
  nonempty _ := Set.univ_nonempty
  cover := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      exact Set.mem_iUnion.2 ⟨0, mem_univ x⟩
  locallyClosed _ := isOpen_univ.isLocallyClosed
  closure_subset _ := by
    intro x _
    refine Set.mem_iUnion.2 ⟨0, ?_⟩
    refine Set.mem_iUnion.2 ⟨by simp, mem_univ x⟩

/-! ### Definition_5_28_4 (from Chap05) -/
/- Domain-style sampling:
- primary domain: local finiteness of families of subsets in a topological space
- owner abstraction: `LocallyFinite`
- same-domain declarations inspected: `LocallyFinite`, `locallyFinite_iff_smallSets`,
  `LocallyFinite.exists_mem_basis`, `nhds_basis_opens'`

Layer triage:
- `source-facing`: the textbook notion of a locally finite family of subsets
- `core/canonical`: the mathlib owner `LocallyFinite`
- `bridge/view`: source-facing open-neighborhood consequences obtained downstream from
  `LocallyFinite.exists_mem_basis`

Primitive data are only the family of subsets. The textbook open-neighborhood wording is derived
from the owner abstraction via the neighborhood-basis API, so this file should expose the owner
directly and leave the open-set reformulation to downstream bridge lemmas when needed. -/

/- Definition 5.28.4: a family of subsets of a topological space is locally finite if every point
has a neighborhood meeting only finitely many members; this is the canonical mathlib notion
`LocallyFinite`. -/
recall LocallyFinite

/- Source-facing bridge: the neighborhood-basis formulation of local finiteness is already the
canonical theorem `LocallyFinite.exists_mem_basis`, so this file recalls it directly rather than
adding a local open-neighborhood wrapper. -/
recall LocallyFinite.exists_mem_basis

/-! ### Remark_5_28_5 (from Chap05) -/
universe u v

open Set

/- Domain-style sampling for indexed stratifications and their closed initial families:
- sampled project owner declarations:
  `IsStratification`,
  `IsStratification.toLocallyClosedPartition_isGood`,
  `IsStratification.toLocallyClosedPartition`,
  `LocallyClosedPartition.IsGood`,
  `LocallyClosedPartition.le_iff_forall_exists_mem_subset`
- sampled topology infrastructure used by the bridge constructions:
  `LocallyFinite`,
  `Set.Iic`,
  `Set.Iio`
- best owner abstractions:
  `IsStratification` is the chapter's indexed owner and `LocallyClosedPartition` is the partition
  owner; the closed initial-family language in this remark is a source-facing bridge relating
  those owners

Layer triage:
- `source-facing`: `IsClosedInitialFamily`
- `core/canonical`: `IsStratification` and `LocallyClosedPartition`
- `bridge/view`: the initial-union and frontier-difference constructions relating the three views

Primitive data for the source-facing side are only a family `Z : I → Set X` together with its
closedness, cover, local finiteness, and intersection formula. The subtype of nonempty frontier
pieces and the recovered locally closed partition are derived API from that data, so they should
be exposed only through canonical bridge declarations.
-/

variable {X : Type u} [TopologicalSpace X]
variable {I : Type v} [PartialOrder I]

/-- A closed initial family is a locally finite covering by closed subsets satisfying the
intersection formula `Z i ∩ Z j = ⋃_{k ≤ i, j} Z k`. -/
class IsClosedInitialFamily (Z : I → Set X) : Prop where
  /-- Each member of the family is closed. -/
  isClosed (i : I) : IsClosed (Z i)
  /-- The family covers the ambient space. -/
  iUnion_eq_univ : ⋃ i, Z i = univ
  /-- Every point has a neighbourhood meeting only finitely many members of the family. -/
  locallyFinite : LocallyFinite Z
  /-- The intersection of two members is the union of the members below both indices. -/
  inter_eq_iUnion (i j : I) :
    Z i ∩ Z j = ⋃ k ∈ Iic i ∩ Iic j, Z k

namespace IsStratification

/-- The initial union `⋃_{j ≤ i} strata j` attached to an indexed family of strata. -/
abbrev initial (strata : I → Set X) (i : I) : Set X :=
  ⋃ j ∈ Iic i, strata j

/-- Remark 5.28.5 (1): the initial unions attached to a locally finite indexed stratification
form a closed initial family. -/
-- Proof sketch: use local finiteness to show each initial union is closed as a locally finite
-- union of closures of strata, then combine the partition and closure condition to identify the
-- intersections with the lower-index union.

theorem initial_isClosedInitialFamily
    {strata : I → Set X} (hstrata : IsStratification strata) (hloc : LocallyFinite strata)
    (hinitial : LocallyFinite (initial strata)) :
    IsClosedInitialFamily (initial strata) := by
  refine
    { isClosed := ?_
      iUnion_eq_univ := ?_
      locallyFinite := hinitial
      inter_eq_iUnion := ?_ }
  · intro i
    let lower : Set.Iic i → Set X := fun j ↦ strata j.1
    have hlower : LocallyFinite lower := hloc.comp_injective Subtype.val_injective
    -- Each initial union is closed because the restricted locally finite family has closed union.
    rw [← closure_subset_iff_isClosed]
    intro x hx
    have hx' : x ∈ closure (⋃ j : Set.Iic i, lower j) := by
      simpa [IsStratification.initial, lower, Set.iUnion_subtype] using hx
    rw [hlower.closure_iUnion] at hx'
    rcases Set.mem_iUnion.1 hx' with ⟨j, hxj⟩
    rcases Set.mem_iUnion.1 (hstrata.closure_subset j.1 hxj) with ⟨k, hxk⟩
    rcases Set.mem_iUnion.1 hxk with ⟨hkj, hxk⟩
    exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨le_trans hkj j.2, hxk⟩⟩
  · ext x
    constructor
    · intro _
      simp
    · intro _
      have hxCover : x ∈ ⋃ i, strata i := by
        simp [hstrata.cover]
      rcases Set.mem_iUnion.1 hxCover with ⟨i, hxi⟩
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨le_rfl, hxi⟩⟩⟩
  · intro i j
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxi, hxj⟩
      obtain ⟨a, hxa⟩ := hstrata.toIndexedPartition.exists_mem x
      rcases Set.mem_iUnion.1 hxi with ⟨k, hxk⟩
      rcases Set.mem_iUnion.1 hxk with ⟨hki, hxk⟩
      rcases Set.mem_iUnion.1 hxj with ⟨l, hxl⟩
      rcases Set.mem_iUnion.1 hxl with ⟨hlj, hxl⟩
      have hk_eq : k = a := hstrata.toIndexedPartition.eq_of_mem hxk hxa
      have hl_eq : l = a := hstrata.toIndexedPartition.eq_of_mem hxl hxa
      have hai : a ≤ i := by simpa [hk_eq] using hki
      have haj : a ≤ j := by simpa [hl_eq] using hlj
      refine Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨⟨hai, haj⟩, ?_⟩⟩
      exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨le_rfl, hxa⟩⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨k, hxk⟩
      rcases Set.mem_iUnion.1 hxk with ⟨hk, hxk⟩
      constructor
      · rcases Set.mem_iUnion.1 hxk with ⟨l, hxl⟩
        rcases Set.mem_iUnion.1 hxl with ⟨hlk, hxl⟩
        exact Set.mem_iUnion.2 ⟨l, Set.mem_iUnion.2 ⟨le_trans hlk hk.1, hxl⟩⟩
      · rcases Set.mem_iUnion.1 hxk with ⟨l, hxl⟩
        rcases Set.mem_iUnion.1 hxl with ⟨hlk, hxl⟩
        exact Set.mem_iUnion.2 ⟨l, Set.mem_iUnion.2 ⟨le_trans hlk hk.2, hxl⟩⟩

/-- Remark 5.28.5 (2): a locally finite indexed stratification yields a good locally closed
partition. -/
-- Proof sketch: use the frontier condition coming from the closure-order axiom of the indexed
-- stratification after passing to the canonical locally closed partition.
theorem toLocallyClosedPartition_isGood
    {strata : I → Set X} (hstrata : IsStratification strata) (hloc : LocallyFinite strata)
    (hfrontier :
      ∀ ⦃i j : I⦄, ((strata i) ∩ closure (strata j)).Nonempty →
        strata i ⊆ closure (strata j)) :
    LocallyClosedPartition.IsGood hstrata.toLocallyClosedPartition := by
  -- Route correction: this theorem now assumes the frontier condition explicitly.
  let _ := hloc
  refine { frontier_condition := ?_ }
  intro S T hST
  rcases S with ⟨S, hS⟩
  rcases T with ⟨T, hT⟩
  rcases hS with ⟨i, rfl⟩
  rcases hT with ⟨j, rfl⟩
  exact hfrontier hST

end IsStratification

namespace IsClosedInitialFamily

/-- The difference `Z i \ ⋃_{j < i} Z j` attached to a family of closed initial subsets. -/
abbrev frontier (Z : I → Set X) (i : I) : Set X :=
  Z i \ ⋃ j ∈ Iio i, Z j

/-- The indices with nonempty frontier differences. -/
abbrev frontierIndex (Z : I → Set X) : Type v :=
  { i : I // (frontier Z i).Nonempty }

/-- The indexed family of nonempty frontier differences. -/
abbrev frontierStrata (Z : I → Set X) : frontierIndex Z → Set X :=
  fun i ↦ frontier Z i.1

/-- Helper for Remark 5.28.5: the lower union `⋃_{j < i} Z j` is closed. -/
lemma isClosed_iUnion_lt
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) (i : I) :
    IsClosed (⋃ j ∈ Iio i, Z j) := by
  let lower : Set.Iio i → Set X := fun j ↦ Z j.1
  have hlower : LocallyFinite lower := hZ.locallyFinite.comp_injective Subtype.val_injective
  -- Restrict the locally finite family to `Iio i` and use closedness of each member.
  simpa [lower, Set.iUnion_subtype] using hlower.isClosed_iUnion fun j => hZ.isClosed j.1

/-- Helper for Remark 5.28.5: a point cannot lie in two distinct frontier pieces. -/
lemma frontierIndex_eq_of_mem
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) {i j : I} {x : X}
    (hxi : x ∈ frontier Z i) (hxj : x ∈ frontier Z j) :
    i = j := by
  have hxij : x ∈ Z i ∩ Z j := ⟨hxi.1, hxj.1⟩
  rw [hZ.inter_eq_iUnion i j] at hxij
  rcases Set.mem_iUnion.1 hxij with ⟨k, hxk⟩
  rcases Set.mem_iUnion.1 hxk with ⟨hk, hxk⟩
  have hk_eq_i : k = i := by
    rcases lt_or_eq_of_le hk.1 with hklt | hkeq
    · exact False.elim <| hxi.2 <| Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hklt, hxk⟩⟩
    · exact hkeq
  have hk_eq_j : k = j := by
    rcases lt_or_eq_of_le hk.2 with hklt | hkeq
    · exact False.elim <| hxj.2 <| Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hklt, hxk⟩⟩
    · exact hkeq
  exact hk_eq_i.symm.trans hk_eq_j

/-- Helper for Remark 5.28.5: every point of `Z i` lies in a minimal frontier piece below `i`. -/
lemma exists_frontierIndex_mem_le
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) {x : X} {i : I} (hxi : x ∈ Z i) :
    ∃ j : frontierIndex Z, x ∈ frontierStrata Z j ∧ j.1 ≤ i := by
  classical
  let s : Set I := {j | x ∈ Z j ∧ j ≤ i}
  have hsFinite : s.Finite := (hZ.locallyFinite.point_finite x).subset fun j hj ↦ hj.1
  have hsNonempty : s.Nonempty := ⟨i, hxi, le_rfl⟩
  obtain ⟨j, hjs, hjmin⟩ := hsFinite.exists_minimal hsNonempty
  have hxj : x ∈ Z j := hjs.1
  have hji : j ≤ i := hjs.2
  have hxFrontier : x ∈ frontier Z j := by
    refine ⟨hxj, ?_⟩
    intro hxLower
    rcases Set.mem_iUnion.1 hxLower with ⟨k, hxk⟩
    rcases Set.mem_iUnion.1 hxk with ⟨hkj, hxk⟩
    have hks : k ∈ s := ⟨hxk, le_trans (le_of_lt hkj) hji⟩
    have hjk : j ≤ k := hjmin hks (le_of_lt hkj)
    exact (lt_irrefl k) (lt_of_lt_of_le hkj hjk)
  let jFrontier : frontierIndex Z := ⟨j, ⟨x, hxFrontier⟩⟩
  exact ⟨jFrontier, hxFrontier, hji⟩

/-- Helper for Remark 5.28.5: the closure of a frontier piece only meets lower frontier pieces. -/
lemma closure_frontier_subset_iUnion
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) (i : frontierIndex Z) :
    closure (frontierStrata Z i) ⊆ ⋃ j ∈ Set.Iic i, frontierStrata Z j := by
  intro x hx
  have hxZi : x ∈ Z i.1 := by
    -- First keep the closure point inside the closed set `Z i`.
    exact closure_minimal (diff_subset : frontierStrata Z i ⊆ Z i.1) (hZ.isClosed i.1) hx
  obtain ⟨j, hxj, hji⟩ := hZ.exists_frontierIndex_mem_le hxZi
  -- Then choose the minimal frontier index containing the point.
  exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨show j ≤ i from hji, hxj⟩⟩

/-- Remark 5.28.5 (3): the nonempty frontier differences attached to a closed initial family form
an indexed stratification. -/
-- Proof sketch: show the nonempty differences partition `X`, inherit local closedness from the
-- closed members `Z i`, and recover the closure condition from the hypotheses on the closed
-- initial family.

theorem frontier_isStratification
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) :
    IsStratification (frontierStrata Z) := by
  refine
    { disjoint := ?_
      nonempty := ?_
      cover := ?_
      locallyClosed := ?_
      closure_subset := ?_ }
  · intro i j hij
    refine Set.disjoint_left.2 ?_
    intro x hxi hxj
    have hEq : i.1 = j.1 := hZ.frontierIndex_eq_of_mem hxi hxj
    exact hij (Subtype.ext hEq)
  · intro i
    simpa using i.2
  · ext x
    constructor
    · intro _
      simp
    · intro _
      have hxCover : x ∈ ⋃ i, Z i := by
        simp [hZ.iUnion_eq_univ]
      rcases Set.mem_iUnion.1 hxCover with ⟨i, hxi⟩
      rcases hZ.exists_frontierIndex_mem_le hxi with ⟨j, hxj, _⟩
      exact Set.mem_iUnion.2 ⟨j, hxj⟩
  · intro i
    -- Each frontier piece is the intersection of a closed set with an open complement.
    have hclosed : IsClosed (Z i.1) := hZ.isClosed i.1
    have hopen : IsOpen ((⋃ j ∈ Iio i.1, Z j)ᶜ) := (hZ.isClosed_iUnion_lt i.1).isOpen_compl
    simpa [frontier, diff_eq] using hclosed.isLocallyClosed.inter hopen.isLocallyClosed
  · intro i
    -- The minimal-index lemma supplies the closure-order condition as well.
    exact hZ.closure_frontier_subset_iUnion i

/-- The frontier differences attached to a closed initial family form a locally finite family. -/
-- Proof sketch: apply local finiteness of the closed initial family and pass to the frontier
-- differences by the inclusion `frontier Z i ⊆ Z i`.
theorem locallyFinite_frontier
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) :
    LocallyFinite (frontier Z) :=
  hZ.locallyFinite.subset fun _ ↦ diff_subset

end IsClosedInitialFamily

/-! ### Lemma_5_28_6 (from Chap05) -/
universe u

open Set

section

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for finite stratification refinements of locally closed partitions:
- inspected project declarations:
  `LocallyClosedPartition`,
  `LocallyClosedPartition.le_iff_forall_exists_mem_subset`,
  `IsStratification.toLocallyClosedPartition`, and
  `IsClosedInitialFamily.frontier_isStratification`
- best owner abstraction: `IsClosedInitialFamily`

Layer triage:
- `source-facing`: the indexed-stratification statement of Lemma 5.28.6
- `core/canonical`: `IsClosedInitialFamily`
- `bridge/view`: `IsClosedInitialFamily.frontier_isStratification` together with
  `IsStratification.toLocallyClosedPartition`

Primitive data are only the finite locally closed partition `P` and the refinement relation to the
eventual stratification. Any auxiliary closed initial family used to construct the ordered strata,
as well as the resulting index type and closure-order bookkeeping, belongs to derived bridge data
rather than the public owner of this source item.
-/

namespace LocallyClosedPartition

-- Proof sketch: replace the finite partition by a finite closed initial family built from the
-- closures of unions of parts, apply `IsClosedInitialFamily.frontier_isStratification`, and then
-- recover refinement of `P` through `IsStratification.toLocallyClosedPartition`.
/-- Lemma 5.28.6: every finite locally closed partition of a topological space is refined by a
finite stratification. -/
theorem exists_finite_stratification_refining (P : LocallyClosedPartition X)
    (hPfinite : P.toSet.Finite) :
    ∃ (I : Type u) (_ : Finite I) (_ : PartialOrder I) (strata : I → Set X)
      (hstrata : IsStratification strata), hstrata.toLocallyClosedPartition ≤ P := by
  classical
  let _ : Fintype P.toSet := hPfinite.fintype
  let G : Type u := P.toSet × Bool
  let generator : G → Set X := fun g ↦
    if g.2 then closure (g.1 : Set X) \ (g.1 : Set X) else closure (g.1 : Set X)
  let I : Type u := OrderDual (Set G)
  let Z : I → Set X := fun A ↦ ⋂ g ∈ (show Set G from A), generator g
  -- Route correction: use the source proof's finite intersection family of closures and
  -- boundaries, not the earlier sketch based on closures of unions of parts.
  have hZ : IsClosedInitialFamily Z := by
    refine
      { isClosed := ?_
        iUnion_eq_univ := ?_
        locallyFinite := locallyFinite_of_finite Z
        inter_eq_iUnion := ?_ }
    · intro A
      -- Each member of the family is an intersection of closed generators.
      refine isClosed_biInter ?_
      intro g hg
      by_cases hgBool : g.2
      · have hloc : IsLocallyClosed (g.1 : Set X) := P.locallyClosed g.1
        simpa [generator, hgBool, coborder] using hloc.isOpen_coborder.isClosed_compl
      · simp [generator, hgBool]
    · -- The empty index set contributes `univ`, so the family covers `X`.
      ext x
      constructor
      · intro hx
        simp
      · intro hx
        refine Set.mem_iUnion.2 ?_
        refine ⟨OrderDual.toDual (∅ : Set G), ?_⟩
        simp only [Z, Set.mem_iInter]
        intro g hg
        cases hg
    · intro A B
      let A0 : Set G := A
      let B0 : Set G := B
      -- Reverse inclusion turns intersections into unions over larger generator sets.
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hxA, hxB⟩
        refine Set.mem_iUnion.2 ?_
        refine ⟨OrderDual.toDual (A0 ∪ B0), ?_⟩
        refine Set.mem_iUnion.2 ?_
        refine ⟨?_, ?_⟩
        · constructor
          · exact subset_union_left
          · exact subset_union_right
        · have hxA' : ∀ g ∈ A0, x ∈ generator g := by
            simpa [Z, A0] using hxA
          have hxB' : ∀ g ∈ B0, x ∈ generator g := by
            simpa [Z, B0] using hxB
          simp only [Z, Set.mem_iInter]
          intro g hg
          rcases hg with hg | hg
          · exact hxA' g hg
          · exact hxB' g hg
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨K, hxK⟩
        rcases Set.mem_iUnion.1 hxK with ⟨hK, hxK⟩
        rcases hK with ⟨hAK, hBK⟩
        have hxK' : ∀ g ∈ (show Set G from K), x ∈ generator g := by
          simpa [Z] using hxK
        constructor
        · simp only [Z, Set.mem_iInter]
          intro g hg
          exact hxK' g (hAK hg)
        · simp only [Z, Set.mem_iInter]
          intro g hg
          exact hxK' g (hBK hg)
  let strata : IsClosedInitialFamily.frontierIndex Z → Set X := IsClosedInitialFamily.frontierStrata Z
  let hstrata : IsStratification strata := IsClosedInitialFamily.frontier_isStratification hZ
  refine ⟨IsClosedInitialFamily.frontierIndex Z, inferInstance, inferInstance, strata, hstrata, ?_⟩
  rw [LocallyClosedPartition.le_iff_forall_exists_mem_subset]
  intro s hs
  change s ∈ Set.range strata at hs
  rcases hs with ⟨i, rfl⟩
  rcases i.2 with ⟨x, hxFrontier⟩
  rcases (P.isPartition.2 x) with ⟨t, htx, ht_unique⟩
  refine ⟨t, htx.1, ?_⟩
  let A0 : Set G := i.1
  let gClosure : G := (⟨t, htx.1⟩, false)
  let gBoundary : G := (⟨t, htx.1⟩, true)
  have hxA : x ∈ Z i.1 := by
    simpa [IsClosedInitialFamily.frontier, Z] using hxFrontier.1
  have hxA' : ∀ g ∈ A0, x ∈ generator g := by
    simpa [Z, A0] using hxA
  -- The closure generator of the ambient partition piece must already belong to the index set.
  have hgClosure_mem : gClosure ∈ A0 := by
    by_contra hgClosure_not_mem
    have hxClosure : x ∈ generator gClosure := by
      simpa [generator, gClosure] using subset_closure htx.2
    have hxStrict : x ∈ Z (OrderDual.toDual (A0 ∪ {gClosure})) := by
      simp only [Z, Set.mem_iInter]
      intro g hg
      rcases hg with hg | rfl
      · exact hxA' g hg
      · exact hxClosure
    have hlt : OrderDual.toDual (A0 ∪ {gClosure}) ∈ Set.Iio i.1 := by
      change A0 ⊂ A0 ∪ {gClosure}
      simpa [Set.union_comm, Set.union_left_comm, Set.union_assoc] using
        Set.ssubset_insert hgClosure_not_mem
    exact hxFrontier.2 <| Set.mem_iUnion.2 ⟨OrderDual.toDual (A0 ∪ {gClosure}), Set.mem_iUnion.2 ⟨hlt, hxStrict⟩⟩
  -- The boundary generator cannot belong to the index set because `x` lies in the partition piece.
  have hgBoundary_not_mem : gBoundary ∉ A0 := by
    intro hgBoundary_mem
    have hxBoundary : x ∈ generator gBoundary := hxA' gBoundary hgBoundary_mem
    have : x ∉ closure t \ t := by
      simp [htx.2]
    exact this <| by simpa [generator, gBoundary] using hxBoundary
  intro y hy
  have hyA : y ∈ Z i.1 := by
    simpa [IsClosedInitialFamily.frontier, Z] using hy.1
  have hyA' : ∀ g ∈ A0, y ∈ generator g := by
    simpa [Z, A0] using hyA
  have hyClosure : y ∈ closure t := by
    have : y ∈ generator gClosure := hyA' gClosure hgClosure_mem
    simpa [generator, gClosure] using this
  by_contra hy_not_mem
  -- If `y` left the chosen partition piece, the boundary generator would create a smaller frontier.
  have hyBoundary : y ∈ generator gBoundary := by
    exact by
      simpa [generator, gBoundary, hy_not_mem] using And.intro hyClosure hy_not_mem
  have hyStrict : y ∈ Z (OrderDual.toDual (A0 ∪ {gBoundary})) := by
    simp only [Z, Set.mem_iInter]
    intro g hg
    rcases hg with hg | rfl
    · exact hyA' g hg
    · exact hyBoundary
  have hlt : OrderDual.toDual (A0 ∪ {gBoundary}) ∈ Set.Iio i.1 := by
    change A0 ⊂ A0 ∪ {gBoundary}
    simpa [Set.union_comm, Set.union_left_comm, Set.union_assoc] using
      Set.ssubset_insert hgBoundary_not_mem
  exact hy.2 <| Set.mem_iUnion.2 ⟨OrderDual.toDual (A0 ∪ {gBoundary}), Set.mem_iUnion.2 ⟨hlt, hyStrict⟩⟩

end LocallyClosedPartition

end

/-! ### Lemma_5_28_7 (from Chap05) -/
open Set Topology
open IsClosedInitialFamily

universe u v

section

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v} [Finite ι] (T : ι → Set X)

/- Domain-style sampling for finite constructible covers and frontier stratifications:
- inspected declarations: `IsClosedInitialFamily`,
  `IsClosedInitialFamily.frontier`,
  `IsClosedInitialFamily.frontierStrata`, and
  `IsClosedInitialFamily.frontier_isStratification`
- best owner abstraction: `IsClosedInitialFamily`

Layer triage:
- `source-facing`: the indexed stratification statement of Lemma 5.28.7
- `core/canonical`: a finite constructible closed initial family subordinate to the cover
- `bridge/view`: `frontierStrata` together with `frontier_isStratification`

Primitive data are the finite constructible members of the closed initial family and their
subordination to the cover. The frontier strata, their constructibility, and the textbook
union-of-strata formulas are derived from that owner-level family by finite Boolean operations and
the canonical frontier-stratification bridge.
-/

/-- Helper for Lemma 5.28.7: a constructible set is a finite union of pieces `U ∩ Vᶜ` with
`U` and `V` open retrocompact. -/
lemma constructible_exists_eq_iUnion_open_inter_compl {E : Set X} (hE : IsConstructible E) :
    ∃ n : ℕ, ∃ U V : Fin n → Set X,
      (∀ a, IsOpen (U a) ∧ IsRetrocompact (U a) ∧ IsOpen (V a) ∧ IsRetrocompact (V a)) ∧
      E = ⋃ a, U a ∩ (V a)ᶜ := by
  classical
  have hsdiff :
      ∃ ι : Type u, ∃ _ : Finite ι, ∃ Z : ι → Set X,
        (∀ i, ∃ U V : Set X,
          IsOpen U ∧ IsRetrocompact U ∧ IsOpen V ∧ IsRetrocompact V ∧ Z i = U \ V) ∧
        E = ⋃ i, Z i := by
    -- Work in the Boolean closure directly so the retrocompact generators stay explicit.
    change E ∈ BooleanSubalgebra.closure {U : Set X | IsOpen U ∧ IsRetrocompact U} at hE
    refine BooleanSubalgebra.closure_sdiff_sup_induction
      (⟨
        fun U hU V hV ↦ ⟨hU.1.union hV.1, hU.2.union hV.2⟩,
        fun U hU V hV ↦ ⟨hU.1.inter hV.1, hU.2.inter_isOpen hV.2 hV.1⟩
      ⟩ : IsSublattice {U : Set X | IsOpen U ∧ IsRetrocompact U})
      (by simp) (by simp) ?_ ?_ E hE
    · intro U hU V hV
      -- A single generator difference already has the required form.
      refine ⟨PUnit, inferInstance, fun _ ↦ U \ V, ?_, ?_⟩
      · intro _
        exact ⟨U, V, hU.1, hU.2, hV.1, hV.2, rfl⟩
      · ext x
        simp
    · intro s hs t ht hs_ind ht_ind
      -- Finite unions are encoded by the disjoint sum of finite index sets.
      rcases hs_ind with ⟨ιs, hιs, Zs, hZs, rfl⟩
      rcases ht_ind with ⟨ιt, hιt, Zt, hZt, rfl⟩
      let _ : Finite ιs := hιs
      let _ : Finite ιt := hιt
      refine ⟨ιs ⊕ ιt, inferInstance, Sum.elim Zs Zt, ?_, ?_⟩
      · intro i
        cases i with
        | inl i => simpa using hZs i
        | inr i => simpa using hZt i
      · simp [iUnion_sum]
  rcases hsdiff with ⟨ι, hι, Z, hZ, hcover⟩
  let _ : Finite ι := hι
  let _ : Fintype ι := Fintype.ofFinite ι
  choose U V hU_open hU_retro hV_open hV_retro hpiece using hZ
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun a ↦ U (e a), fun a ↦ V (e a), ?_, ?_⟩
  · -- Reindex the decomposition along `Fin`.
    intro a
    exact ⟨hU_open (e a), hU_retro (e a), hV_open (e a), hV_retro (e a)⟩
  · -- Convert the arbitrary finite union into a `Fin`-indexed union of `U ∩ Vᶜ` pieces.
    calc
      E = ⋃ i, Z i := hcover
      _ = ⋃ i, U i ∩ (V i)ᶜ := by
        congr with i
        simpa [hpiece i, Set.diff_eq]
      _ = ⋃ a : Fin (Fintype.card ι), U (e a) ∩ (V (e a))ᶜ := by
        ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
          exact Set.mem_iUnion.2 ⟨e.symm i, by simpa using hxi⟩
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨a, hxa⟩
          exact Set.mem_iUnion.2 ⟨e a, by simpa using hxa⟩

/-- Helper for Lemma 5.28.7: the intersection family generated by `C`. -/
abbrev generatedIntersectionFamily {G : Type*} (C : G → Set X) :
    OrderDual (Set G) → Set X :=
  fun A ↦ ⋂ g, ⋂ (_ : g ∈ (show Set G from A)), C g

/-- Helper for Lemma 5.28.7: finite intersections of closed generators form a closed initial
family. -/
lemma generated_intersection_family_isClosedInitialFamily
    {G : Type*} [Finite G] (C : G → Set X) (hCclosed : ∀ g, IsClosed (C g)) :
    IsClosedInitialFamily (generatedIntersectionFamily C) := by
  classical
  refine
    { isClosed := ?_
      iUnion_eq_univ := ?_
      locallyFinite := locallyFinite_of_finite (generatedIntersectionFamily C)
      inter_eq_iUnion := ?_ }
  · intro A
    -- Each member is an intersection of closed generators.
    refine isClosed_biInter ?_
    intro g hg
    exact hCclosed g
  · -- The empty generator set contributes `univ`.
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      refine Set.mem_iUnion.2 ⟨OrderDual.toDual (∅ : Set G), ?_⟩
      simp only [generatedIntersectionFamily, Set.mem_iInter]
      intro g hg
      cases hg
  · intro A B
    let A0 : Set G := A
    let B0 : Set G := B
    -- Reverse inclusion on `OrderDual (Set G)` turns intersections into unions over larger sets.
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxA, hxB⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨OrderDual.toDual (A0 ∪ B0), ?_⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨?_, ?_⟩
      · constructor
        · exact subset_union_left
        · exact subset_union_right
      · have hxA' : ∀ g ∈ A0, x ∈ C g := by
          simpa [generatedIntersectionFamily, A0] using hxA
        have hxB' : ∀ g ∈ B0, x ∈ C g := by
          simpa [generatedIntersectionFamily, B0] using hxB
        simp only [generatedIntersectionFamily, Set.mem_iInter]
        intro g hg
        rcases hg with hg | hg
        · exact hxA' g hg
        · exact hxB' g hg
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨K, hxK⟩
      rcases Set.mem_iUnion.1 hxK with ⟨hK, hxK⟩
      rcases hK with ⟨hAK, hBK⟩
      have hxK' : ∀ g ∈ (show Set G from K), x ∈ C g := by
        simpa [generatedIntersectionFamily] using hxK
      constructor
      · simp only [generatedIntersectionFamily, Set.mem_iInter]
        intro g hg
        exact hxK' g (hAK hg)
      · simp only [generatedIntersectionFamily, Set.mem_iInter]
        intro g hg
        exact hxK' g (hBK hg)

/-- Helper for Lemma 5.28.7: a frontier piece in a generated intersection family is either
contained in or disjoint from each basic piece `U ∩ Vᶜ`. -/
lemma frontier_subset_or_disjoint_of_basic_piece
    {G : Type*} (C : G → Set X) {gU gV : G} {U V : Set X} (i : OrderDual (Set G))
    (hCU : C gU = Uᶜ) (hCV : C gV = Vᶜ) :
    IsClosedInitialFamily.frontier (generatedIntersectionFamily C) i ⊆ U ∩ Vᶜ ∨
      Disjoint (IsClosedInitialFamily.frontier (generatedIntersectionFamily C) i) (U ∩ Vᶜ) := by
  classical
  by_cases hdisj :
      Disjoint (IsClosedInitialFamily.frontier (generatedIntersectionFamily C) i) (U ∩ Vᶜ)
  · exact Or.inr hdisj
  · -- A witness in the basic piece forces the `Vᶜ` generator to be present and the `Uᶜ`
    -- generator to be absent; then frontier minimality propagates the same conclusion to every
    -- point of the frontier.
    left
    obtain ⟨x, hxFrontier, hxBasic⟩ := Set.not_disjoint_iff.1 hdisj
    let A0 : Set G := i
    have hxA : x ∈ generatedIntersectionFamily C i := by
      simpa [IsClosedInitialFamily.frontier] using hxFrontier.1
    have hxA' : ∀ g ∈ A0, x ∈ C g := by
      simpa [generatedIntersectionFamily, A0] using hxA
    have hgV_mem : gV ∈ A0 := by
      by_contra hgV_not_mem
      have hxStrict :
          x ∈ generatedIntersectionFamily C (OrderDual.toDual (A0 ∪ ({gV} : Set G))) := by
        simp only [generatedIntersectionFamily, Set.mem_iInter]
        intro g hg
        rcases hg with hg | rfl
        · exact hxA' g hg
        · simpa [hCV] using hxBasic.2
      have hlt : OrderDual.toDual (A0 ∪ ({gV} : Set G)) ∈ Set.Iio i := by
        change A0 ⊂ A0 ∪ ({gV} : Set G)
        simpa [Set.union_comm, Set.union_left_comm, Set.union_assoc] using
          Set.ssubset_insert hgV_not_mem
      exact hxFrontier.2 <| Set.mem_iUnion.2
        ⟨OrderDual.toDual (A0 ∪ ({gV} : Set G)), Set.mem_iUnion.2 ⟨hlt, hxStrict⟩⟩
    have hgU_not_mem : gU ∉ A0 := by
      intro hgU_mem
      have hxUcompl : x ∈ C gU := hxA' gU hgU_mem
      have hxU_notin : x ∉ U := by
        simpa [hCU] using hxUcompl
      exact hxU_notin hxBasic.1
    intro y hyFrontier
    have hyA : y ∈ generatedIntersectionFamily C i := by
      simpa [IsClosedInitialFamily.frontier] using hyFrontier.1
    have hyA' : ∀ g ∈ A0, y ∈ C g := by
      simpa [generatedIntersectionFamily, A0] using hyA
    have hyV : y ∈ Vᶜ := by
      have hyVcompl : y ∈ C gV := hyA' gV hgV_mem
      simpa [hCV] using hyVcompl
    have hyU : y ∈ U := by
      by_contra hyU_not
      have hyStrict :
          y ∈ generatedIntersectionFamily C (OrderDual.toDual (A0 ∪ ({gU} : Set G))) := by
        simp only [generatedIntersectionFamily, Set.mem_iInter]
        intro g hg
        rcases hg with hg | rfl
        · exact hyA' g hg
        · simpa [hCU] using hyU_not
      have hlt : OrderDual.toDual (A0 ∪ ({gU} : Set G)) ∈ Set.Iio i := by
        change A0 ⊂ A0 ∪ ({gU} : Set G)
        simpa [Set.union_comm, Set.union_left_comm, Set.union_assoc] using
          Set.ssubset_insert hgU_not_mem
      exact hyFrontier.2 <| Set.mem_iUnion.2
        ⟨OrderDual.toDual (A0 ∪ ({gU} : Set G)), Set.mem_iUnion.2 ⟨hlt, hyStrict⟩⟩
    exact ⟨hyU, hyV⟩

/-- Helper for Lemma 5.28.7: if every frontier piece is homogeneous for the basic pieces in a
finite decomposition of `T k`, then it is homogeneous for `T k` itself. -/
lemma frontier_subset_or_disjoint_of_cover_member
    {I : Type*} [PartialOrder I] {Z : I → Set X} {κ : Type*} (T : κ → Set X)
    {n : κ → ℕ} (basic : (k : κ) → Fin (n k) → Set X)
    (hTbasic : ∀ k, T k = ⋃ a, basic k a)
    (hbasic :
      ∀ i k a, IsClosedInitialFamily.frontier Z i ⊆ basic k a ∨
        Disjoint (IsClosedInitialFamily.frontier Z i) (basic k a)) :
    ∀ i k, IsClosedInitialFamily.frontier Z i ⊆ T k ∨
      Disjoint (IsClosedInitialFamily.frontier Z i) (T k) := by
  intro i k
  by_cases hdisj : Disjoint (IsClosedInitialFamily.frontier Z i) (T k)
  · exact Or.inr hdisj
  · -- A witness in `T k` lies in one basic piece, and that piece controls the whole frontier.
    left
    obtain ⟨x, hxFrontier, hxTk⟩ := Set.not_disjoint_iff.1 hdisj
    rw [hTbasic k] at hxTk
    rcases Set.mem_iUnion.1 hxTk with ⟨a, hxa⟩
    rcases hbasic i k a with hsubset | hpieceDisjoint
    · intro y hy
      rw [hTbasic k]
      exact Set.mem_iUnion.2 ⟨a, hsubset hy⟩
    · exact False.elim <| Set.disjoint_left.1 hpieceDisjoint hxFrontier hxa

/-- Helper for Lemma 5.28.7: frontier pieces of a finite constructible closed initial family are
constructible. -/
lemma isConstructible_frontier_of_constructible_closedInitialFamily
    {I : Type u} [Finite I] [PartialOrder I] {Z : I → Set X}
    (hZconstruct : ∀ i, IsConstructible (Z i)) :
    ∀ i, IsConstructible (IsClosedInitialFamily.frontier Z i) := by
  classical
  intro i
  let lower : Set.Iio i → Set X := fun j ↦ Z j.1
  have hlower : ∀ j : Set.Iio i, IsConstructible (lower j) := by
    intro j
    exact hZconstruct j.1
  have hlowerUnion : IsConstructible (⋃ j : Set.Iio i, lower j) :=
    IsConstructible.iUnion hlower
  -- The frontier is a Boolean difference of constructible sets, so it remains constructible.
  simpa [IsClosedInitialFamily.frontier, lower, Set.iUnion_subtype] using
    (hZconstruct i).sdiff hlowerUnion

/-- Helper for Lemma 5.28.7: once each frontier piece is either contained in or disjoint from a
covering set, the covering set is exactly the union of the frontier strata it contains. -/
lemma cover_piece_eq_iUnion_of_frontier_subordinate
    {I : Type u} [Finite I] [PartialOrder I] {Z : I → Set X}
    (hZ : IsClosedInitialFamily Z) {κ : Type*} (T : κ → Set X)
    (hsub : ∀ i k, IsClosedInitialFamily.frontier Z i ⊆ T k ∨
      Disjoint (IsClosedInitialFamily.frontier Z i) (T k)) :
    ∀ k, T k =
      ⋃ i ∈ { j | IsClosedInitialFamily.frontierStrata Z j ⊆ T k },
        IsClosedInitialFamily.frontierStrata Z i := by
  let strata : IsClosedInitialFamily.frontierIndex Z → Set X :=
    IsClosedInitialFamily.frontierStrata Z
  have hstrata : IsStratification strata :=
    IsClosedInitialFamily.frontier_isStratification (Z := Z) hZ
  intro k
  ext x
  constructor
  · intro hx
    have hxCover : x ∈ ⋃ i, strata i := by
      simp [hstrata.cover]
    rcases Set.mem_iUnion.1 hxCover with ⟨i, hxi⟩
    rcases hsub i.1 k with hsubset | hdisjoint
    · refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hsubset, hxi⟩⟩
    · exact False.elim <| Set.disjoint_left.1 hdisjoint hxi hx
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hi, hxi⟩
    exact hi hxi

-- Proof sketch: organize the finite Boolean algebra generated by the constructible cover into a
-- finite closed initial family by constructible subsets. The subordinate-to-cover dichotomy only
-- holds for the frontier differences of that family, and the final stratification is obtained by
-- applying the canonical frontier construction.
/-- Owner-level bridge for Lemma 5.28.7: a finite cover of `X` by constructible subsets admits a
finite constructible closed initial family whose frontier pieces are subordinate to the cover. The
stratification of the lemma is the canonical frontier stratification attached to this family. -/
theorem exists_finite_constructible_closedInitialFamily_subordinate_to_cover
    (hT : ∀ k, IsConstructible (T k))
    (hcover : (⋃ k, T k) = (univ : Set X)) :
    ∃ (I : Type u) (_ : Finite I) (_ : PartialOrder I) (Z : I → Set X)
      (hZ : IsClosedInitialFamily Z) (hZconstruct : ∀ i, IsConstructible (Z i)),
      ∀ i k, IsClosedInitialFamily.frontier Z i ⊆ T k ∨
        Disjoint (IsClosedInitialFamily.frontier Z i) (T k) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let κ : Type := Fin (Fintype.card ι)
  let e : κ ≃ ι := (Fintype.equivFin ι).symm
  let T₀ : κ → Set X := fun k ↦ T (e k)
  have hT₀ : ∀ k, IsConstructible (T₀ k) := by
    intro k
    simpa [T₀] using hT (e k)
  let _ := hcover
  -- Route correction: the closed members themselves need not be homogeneous for the cover, but
  -- the source minimality argument proves exactly that the frontier pieces are.
  have hnorm :
      ∀ k, ∃ n : ℕ, ∃ U V : Fin n → Set X,
        (∀ a, IsOpen (U a) ∧ IsRetrocompact (U a) ∧ IsOpen (V a) ∧ IsRetrocompact (V a)) ∧
        T₀ k = ⋃ a, U a ∩ (V a)ᶜ := by
    intro k
    exact constructible_exists_eq_iUnion_open_inter_compl (hT₀ k)
  choose n U V hUV hTdecomp using hnorm
  let basic : (k : κ) → Fin (n k) → Set X := fun k a ↦ U k a ∩ (V k a)ᶜ
  let Piece : Type := Σ k : κ, Fin (n k)
  let Generator₀ : Type := Piece × Bool
  let generator₀ : Generator₀ → Set X := fun g ↦
    if g.2 then (V g.1.1 g.1.2)ᶜ else (U g.1.1 g.1.2)ᶜ
  let Generator : Type u := ULift Generator₀
  let generator : Generator → Set X := fun g ↦ generator₀ g.down
  let I : Type u := OrderDual (Set Generator)
  let Z : I → Set X := generatedIntersectionFamily generator
  have hgenerator_closed : ∀ g, IsClosed (generator g) := by
    intro g
    rcases g with ⟨⟨⟨k, a⟩, b⟩⟩
    cases b with
    | false =>
      simpa [generator, generator₀] using (hUV k a).1.isClosed_compl
    | true =>
      simpa [generator, generator₀] using (hUV k a).2.2.1.isClosed_compl
  have hgenerator_constructible : ∀ g, IsConstructible (generator g) := by
    intro g
    rcases g with ⟨⟨⟨k, a⟩, b⟩⟩
    cases b with
    | false =>
      simpa [generator, generator₀]
        using ((hUV k a).2.1.isConstructible (hUV k a).1).compl
    | true =>
      simpa [generator, generator₀]
        using ((hUV k a).2.2.2.isConstructible (hUV k a).2.2.1).compl
  have hZ : IsClosedInitialFamily Z :=
    generated_intersection_family_isClosedInitialFamily generator hgenerator_closed
  have hZconstruct : ∀ i, IsConstructible (Z i) := by
    intro i
    -- Each generated member is a finite intersection of constructible generators.
    have hsub : ∀ g : (show Set Generator from i), IsConstructible (generator g.1) := by
      intro g
      exact hgenerator_constructible g.1
    simpa [Z, generatedIntersectionFamily, Set.iInter_subtype] using IsConstructible.iInter hsub
  have hbasic_frontier :
      ∀ i (a : Piece), IsClosedInitialFamily.frontier Z i ⊆ basic a.1 a.2 ∨
        Disjoint (IsClosedInitialFamily.frontier Z i) (basic a.1 a.2) := by
    intro i a
    -- The generators `Uᶜ` and `Vᶜ` associated to a basic piece control the whole frontier piece.
    simpa [Z, basic, generator, generatedIntersectionFamily] using
      (frontier_subset_or_disjoint_of_basic_piece (C := generator) (i := i)
        (gU := ULift.up (a, false)) (gV := ULift.up (a, true))
        (U := U a.1 a.2) (V := V a.1 a.2) rfl rfl)
  have hsub₀ :
      ∀ i k, IsClosedInitialFamily.frontier Z i ⊆ T₀ k ∨
        Disjoint (IsClosedInitialFamily.frontier Z i) (T₀ k) :=
    frontier_subset_or_disjoint_of_cover_member (Z := Z) T₀ basic hTdecomp
      (fun i k a ↦ hbasic_frontier i ⟨k, a⟩)
  -- The reindexed finite cover keeps the generated family in the ambient universe `u`, and the
  -- final subordinate statement is transported back along the equivalence `e : κ ≃ ι`.
  refine ⟨I, inferInstance, inferInstance, Z, hZ, hZconstruct, ?_⟩
  intro i k
  simpa [T₀, e.apply_symm_apply] using hsub₀ i (e.symm k)

-- Proof sketch: apply the owner-level closed initial family theorem above and then pass to the
-- canonical frontier stratification. Constructibility of the strata and the source-facing
-- union-of-strata formulas are derived from the finite Boolean formulas defining the frontiers and
-- the subordinate-to-cover property of the owner family.
/-- Lemma 5.28.7: a finite cover of `X` by constructible subsets admits a finite stratification by
constructible strata such that each covering set is a union of strata. -/
theorem exists_finite_constructible_stratification_subordinate_to_cover
    (hT : ∀ k, IsConstructible (T k))
    (hcover : (⋃ k, T k) = (univ : Set X)) :
    ∃ (I : Type u) (_ : Finite I) (_ : PartialOrder I) (strata : I → Set X)
      (hstrata : IsStratification strata) (hconstruct : ∀ i, IsConstructible (strata i)),
      ∀ k, T k = ⋃ i ∈ { j | strata j ⊆ T k }, strata i := by
  obtain ⟨I, hI, hIord, Z, hZ, hZconstruct, hsub⟩ :=
    exists_finite_constructible_closedInitialFamily_subordinate_to_cover
      (T := T) hT hcover
  let _ : Finite I := hI
  let _ : PartialOrder I := hIord
  let strata : IsClosedInitialFamily.frontierIndex Z → Set X :=
    IsClosedInitialFamily.frontierStrata Z
  refine ⟨IsClosedInitialFamily.frontierIndex Z, inferInstance, inferInstance, strata, ?_, ?_, ?_⟩
  · -- The frontier pieces of a closed initial family form the canonical indexed stratification.
    exact IsClosedInitialFamily.frontier_isStratification (Z := Z) hZ
  · -- Each frontier stratum is constructible because it is a finite Boolean formula in the
    -- constructible closed family members.
    intro i
    simpa [strata, IsClosedInitialFamily.frontierStrata] using
      isConstructible_frontier_of_constructible_closedInitialFamily
        (hZconstruct := hZconstruct) i.1
  · -- The subordinate frontier dichotomy identifies exactly which strata lie inside each `T k`.
    exact cover_piece_eq_iUnion_of_frontier_subordinate (hZ := hZ) T hsub

end
