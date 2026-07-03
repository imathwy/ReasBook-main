import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Instances.EReal.Lemmas

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_1_0_42 (from Chap01) -/
universe u

/- Text 1.0.42: a Hausdorff topological space is formalized by the canonical predicate
`T2Space X`, expressing that distinct points admit disjoint neighborhoods. -/
recall T2Space {X : Type u} [TopologicalSpace X] : Prop

/-! ### Text_1_0_43 (from Chap01) -/
universe u

/- Text 1.0.43: in the Hausdorff setting of the text, compactness of a subset `C` is formalized by
the canonical predicate `IsCompact C`. -/
recall IsCompact {X : Type u} [TopologicalSpace X] (C : Set X) : Prop

/- Its canonical open-cover characterization is the theorem
`isCompact_iff_finite_subcover`. -/
recall isCompact_iff_finite_subcover {X : Type u} [TopologicalSpace X] {s : Set X} :
    IsCompact s ↔
      ∀ {ι : Type u} (U : ι → Set X),
        (∀ i, IsOpen (U i)) → s ⊆ ⋃ i, U i → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i

/-! ### Text_1_0_44 (from Chap01) -/
universe u v

open Filter

variable {A : Type u} [Preorder A] [IsDirectedOrder A] [Nonempty A]
variable {X : Type v} [TopologicalSpace X]

/-- Text 1.0.44: a net `ξ` converges to `x` exactly when it is eventually contained in every
neighborhood of `x`; in mathlib this convergence is expressed by `Tendsto ξ atTop (nhds x)`. -/
-- Proof sketch: this is the canonical specialization of `tendsto_iff_forall_eventually_mem`
-- to the target filter `nhds x`, together with the tail characterization of `atTop`.
theorem tendsto_atTop_nhds_iff_forall_exists_forall_ge_mem (ξ : A → X) (x : X) :
    Tendsto ξ atTop (nhds x) ↔
      ∀ V ∈ nhds x, ∃ b, ∀ a ≥ b, ξ a ∈ V := by
  rw [tendsto_iff_forall_eventually_mem]
  constructor
  · intro h V hV
    exact eventually_atTop.mp (h V hV)
  · intro h V hV
    exact eventually_atTop.mpr (h V hV)

/-! ### Text_1_0_45 (from Chap01) -/
universe u v

variable {A : Type u} [Nonempty A] [Preorder A] [IsDirectedOrder A]
variable {X : Type v} [TopologicalSpace X]

/-- Text 1.0.45: for a net `ξ : A → X`, the canonical predicate `MapClusterPt x Filter.atTop ξ`
means that every neighborhood of `x` is visited arbitrarily far out in the directed index set. -/
-- Proof sketch: unfold `MapClusterPt`, rewrite cluster points using
-- `mapClusterPt_iff_frequently`, and then rewrite frequent membership in `Filter.atTop`
-- as the textbook tail condition.
theorem mapClusterPt_atTop_iff_forall_forall_exists_ge_mem_nhds (ξ : A → X) (x : X) :
    MapClusterPt x Filter.atTop ξ ↔
      ∀ V : Set X, V ∈ nhds x → ∀ b : A, ∃ a : A, b ≤ a ∧ ξ a ∈ V := by
  rw [mapClusterPt_iff_frequently]
  constructor
  · intro h V hV b
    exact (Filter.frequently_atTop.mp (h V hV)) b
  · intro h V hV
    exact Filter.frequently_atTop.mpr (h V hV)

/-! ### Text_1_0_46 (from Chap01) -/
open Filter
open scoped Topology

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Text 1.0.46: A point `x` is a sequential cluster point of a sequence `u` if some subsequence of
`u` converges to `x`. -/
def IsSequentialClusterPt (u : ℕ → X) (x : X) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x)

/-- `IsSequentialClusterPt u x` means that some strictly monotone subsequence of `u` converges to
`x`. -/
theorem isSequentialClusterPt_iff_exists_subseq_tendsto {u : ℕ → X} {x : X} :
    IsSequentialClusterPt u x ↔
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) :=
  Iff.rfl

/-- A sequential cluster point is a cluster point in the canonical filter-based sense. -/
theorem IsSequentialClusterPt.mapClusterPt {u : ℕ → X} {x : X}
    (hx : IsSequentialClusterPt u x) :
    MapClusterPt x atTop u := by
  rcases hx with ⟨φ, hφ, hφt⟩
  have hsubcluster : MapClusterPt x atTop (u ∘ φ) := hφt.mapClusterPt
  simpa [Function.comp] using hsubcluster.of_comp hφ.tendsto_atTop

/-- A sequential cluster point is witnessed by a strictly monotone subsequence converging to the
given point. -/
-- Proof sketch: unfold `IsSequentialClusterPt`; the required subsequence is exactly the witness in
-- the definition.
theorem IsSequentialClusterPt.exists_subseq_tendsto {u : ℕ → X} {x : X}
    (hx : IsSequentialClusterPt u x) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) :=
  isSequentialClusterPt_iff_exists_subseq_tendsto.mp hx

/-! ### Text_1_0_47 (from Chap01) -/
universe u v w

open Filter

private structure ClusterHitPair {X : Type u} [TopologicalSpace X] {A : Type v}
    (u : A → X) (x : X) where
  index : A
  neighborhood : Set X
  neighborhood_mem : neighborhood ∈ nhds x
  hit_mem : u index ∈ neighborhood

private instance clusterHitPairPreorder {X : Type u} [TopologicalSpace X] {A : Type v}
    [Preorder A] {u : A → X} {x : X} : Preorder (ClusterHitPair u x) where
  le p q := p.index ≤ q.index ∧ q.neighborhood ⊆ p.neighborhood
  le_refl p := ⟨le_rfl, Set.Subset.rfl⟩
  le_trans p q r hpq hqr := ⟨hpq.1.trans hqr.1, Set.Subset.trans hqr.2 hpq.2⟩

private lemma clusterHitPair_nonempty {X : Type u} [TopologicalSpace X] {A : Type v}
    [Nonempty A] [Preorder A] {u : A → X} {x : X}
    (hcluster : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V) :
    Nonempty (ClusterHitPair u x) := by
  classical
  let a₀ : A := Classical.choice ‹Nonempty A›
  obtain ⟨a, _, ha_mem⟩ := hcluster Set.univ Filter.univ_mem a₀
  exact ⟨⟨a, Set.univ, Filter.univ_mem, ha_mem⟩⟩

private lemma clusterHitPair_directed {X : Type u} [TopologicalSpace X] {A : Type v}
    [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X}
    (hcluster : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V) :
    IsDirectedOrder (ClusterHitPair u x) := by
  refine ⟨?_⟩
  intro p q
  obtain ⟨a₀, hpa₀, hqa₀⟩ := exists_ge_ge p.index q.index
  have hpq_mem : p.neighborhood ∩ q.neighborhood ∈ nhds x :=
    Filter.inter_mem p.neighborhood_mem q.neighborhood_mem
  obtain ⟨a, ha₀a, ha_mem⟩ := hcluster (p.neighborhood ∩ q.neighborhood) hpq_mem a₀
  refine ⟨⟨a, p.neighborhood ∩ q.neighborhood, hpq_mem, ha_mem⟩, ?_, ?_⟩
  · exact ⟨hpa₀.trans ha₀a, Set.inter_subset_left⟩
  · exact ⟨hqa₀.trans ha₀a, Set.inter_subset_right⟩

private lemma clusterHitPair_index_monotone {X : Type u} [TopologicalSpace X] {A : Type v}
    [Preorder A] {u : A → X} {x : X} :
    Monotone (ClusterHitPair.index : ClusterHitPair u x → A) := by
  intro p q hpq
  exact hpq.1

private lemma clusterHitPair_index_tendsto_atTop {X : Type u} [TopologicalSpace X]
    {A : Type v} [Nonempty A] [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X}
    (hcluster : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V) :
    Tendsto (ClusterHitPair.index : ClusterHitPair u x → A) atTop atTop := by
  refine Monotone.tendsto_atTop_atTop clusterHitPair_index_monotone ?_
  intro a₀
  obtain ⟨a, ha₀a, ha_mem⟩ := hcluster Set.univ Filter.univ_mem a₀
  exact ⟨⟨a, Set.univ, Filter.univ_mem, ha_mem⟩, ha₀a⟩

private lemma clusterHitPair_tendsto_nhds {X : Type u} [TopologicalSpace X] {A : Type v}
    [Nonempty A] [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X}
    (hcluster : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V) :
    Tendsto (u ∘ (ClusterHitPair.index : ClusterHitPair u x → A)) atTop (nhds x) := by
  classical
  let a₀ : A := Classical.choice ‹Nonempty A›
  let _ : Nonempty (ClusterHitPair u x) := clusterHitPair_nonempty hcluster
  let _ : IsDirectedOrder (ClusterHitPair u x) := clusterHitPair_directed hcluster
  rw [tendsto_atTop']
  intro V hV
  obtain ⟨a, _, ha_mem⟩ := hcluster V hV a₀
  refine ⟨⟨a, V, hV, ha_mem⟩, ?_⟩
  intro b hb
  exact hb.2 b.hit_mem

private lemma subnet_tendsto_implies_mapClusterPt_atTop {X : Type u} [TopologicalSpace X]
    {A : Type v} [Nonempty A] [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X}
    {B : Type w} [Nonempty B] [Preorder B] [IsDirectedOrder B] {φ : B → A}
    (hφ : Tendsto φ atTop atTop) (hconv : Tendsto (u ∘ φ) atTop (nhds x)) :
    MapClusterPt x atTop u := by
  exact MapClusterPt.of_comp hφ (Filter.Tendsto.mapClusterPt hconv)

/-- Text 1.0.47: a point `x` is a cluster point of a net `u` iff there is a subnet, given by a
monotone cofinal reindexing map, whose reindexed net converges to `x`. -/
-- Proof sketch: for the forward implication, take the directed set of pairs `(a, U)` consisting
-- of an index and a neighborhood of `x` hit by the net, ordered by tail refinement and reverse
-- inclusion of neighborhoods; the projection to `A` is monotone and cofinal, and the reindexed
-- net converges to `x`. For the reverse implication, combine convergence of the subnet with
-- cofinality of the reindexing map to show every neighborhood of `x` is met on every tail of the
-- original net.
theorem mapClusterPt_atTop_iff_exists_subnet_tendsto {X : Type u} [TopologicalSpace X]
    {A : Type v} [Nonempty A] [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X} :
    MapClusterPt x atTop u ↔
      ∃ (B : Type (max u v)) (_ : Nonempty B) (_ : Preorder B) (_ : IsDirectedOrder B)
        (φ : B → A),
        Monotone φ ∧ Tendsto φ atTop atTop ∧ Tendsto (u ∘ φ) atTop (nhds x) := by
  constructor
  · intro hx
    have hx' : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V := by
      rw [mapClusterPt_iff_frequently] at hx
      intro V hV a₀
      have hfreq : ∃ᶠ a in atTop, u a ∈ V := hx V hV
      rw [frequently_atTop] at hfreq
      exact hfreq a₀
    let B : Type (max u v) := ClusterHitPair u x
    let _ : Nonempty B := clusterHitPair_nonempty hx'
    let _ : IsDirectedOrder B := clusterHitPair_directed hx'
    refine ⟨B, inferInstance, inferInstance, inferInstance, ClusterHitPair.index, ?_⟩
    exact ⟨clusterHitPair_index_monotone, clusterHitPair_index_tendsto_atTop hx',
      clusterHitPair_tendsto_nhds hx'⟩
  · rintro ⟨B, _, _, _, φ, _, hφ, hconv⟩
    exact subnet_tendsto_implies_mapClusterPt_atTop hφ hconv

/-! ### Text_1_0_48 (from Chap01) -/
open Set TopologicalSpace

/-- Text 1.0.48: the usual topology on `ℝ` has as a basis the family of open intervals
`(a, b)` with `a < b`. -/
-- Proof sketch: apply `isTopologicalBasis_of_isOpen_of_nhds`; openness of each interval is
-- `isOpen_Ioo`, and the neighborhood basis condition is exactly
-- `mem_nhds_iff_exists_Ioo_subset`.
theorem real_isTopologicalBasis_Ioo :
    TopologicalSpace.IsTopologicalBasis { s : Set ℝ | ∃ a b, a < b ∧ s = Ioo a b } := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro s ⟨a, b, hab, rfl⟩
    exact isOpen_Ioo
  · intro x s hx hs
    rcases mem_nhds_iff_exists_Ioo_subset.1 (hs.mem_nhds hx) with ⟨a, b, hxIoo, hIoo⟩
    exact ⟨Ioo a b, ⟨a, b, hxIoo.1.trans hxIoo.2, rfl⟩, hxIoo, hIoo⟩

/-! ### Text_1_0_49 (from Chap01) -/
open Set
open scoped Topology

namespace EReal

/-- The family of real open intervals together with the lower and upper infinite rays in `EReal`.
-/
abbrev realIntervalRayBasis : Set (Set EReal) :=
  {s | (∃ a b : ℝ, s = Ioo (a : EReal) (b : EReal)) ∨
      (∃ ξ : ℝ, s = Iio (ξ : EReal)) ∨
      ∃ ξ : ℝ, s = Ioi (ξ : EReal)}

/-- Text 1.0.49: the canonical topology on the extended real line `EReal` has as a basis the
family of all embedded real open intervals `(a, b)` together with the lower rays `[-∞, ξ)` and
the upper rays `(ξ, +∞]`, represented in Lean by `Ioo (a : EReal) (b : EReal)`, `Iio (ξ : EReal)`,
and `Ioi (ξ : EReal)`. -/
-- Proof sketch: use that `EReal` carries the order topology and identify the textbook basis as
-- the standard basis by open intervals at finite points together with the one-sided ray bases at
-- `⊥` and `⊤`.
theorem realIntervalRayBasis_isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis realIntervalRayBasis := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro s hs
    rcases hs with hs | hs
    · rcases hs with ⟨a, b, rfl⟩
      exact isOpen_Ioo
    · rcases hs with hs | hs
      · rcases hs with ⟨ξ, rfl⟩
        exact isOpen_Iio
      · rcases hs with ⟨ξ, rfl⟩
        exact isOpen_Ioi
  · intro x u hx hu
    by_cases hbot : x = ⊥
    · subst hbot
      rcases mem_nhds_bot_iff.mp (IsOpen.mem_nhds hu hx) with ⟨ξ, hξ⟩
      exact ⟨Iio (ξ : EReal), Or.inr <| Or.inl ⟨ξ, rfl⟩, bot_lt_coe ξ, hξ⟩
    by_cases htop : x = ⊤
    · subst htop
      rcases mem_nhds_top_iff.mp (IsOpen.mem_nhds hu hx) with ⟨ξ, hξ⟩
      exact ⟨Ioi (ξ : EReal), Or.inr <| Or.inr ⟨ξ, rfl⟩, coe_lt_top ξ, hξ⟩
    lift x to ℝ using ⟨htop, hbot⟩
    have hpre : Real.toEReal ⁻¹' u ∈ 𝓝 x := by
      simpa [nhds_coe] using (IsOpen.mem_nhds hu hx)
    rcases mem_nhds_iff_exists_Ioo_subset.mp hpre with ⟨a, b, hxab, hab⟩
    refine ⟨Ioo (a : EReal) (b : EReal), Or.inl ⟨a, b, rfl⟩, ?_, ?_⟩
    · simpa using hxab
    · simpa [image_coe_Ioo] using image_subset_iff.mpr hab

end EReal

/-! ### Text_1_0_50 (from Chap01) -/
/-- Text 1.0.50 (1): the real line with its usual metric topology is Hausdorff. -/
theorem real_t2Space : T2Space ℝ := inferInstance

/-- Text 1.0.50 (2): the real line with its usual topology is not compact. -/
theorem real_not_compact : ¬ CompactSpace ℝ := by
  simpa [not_compactSpace_iff] using (inferInstance : NoncompactSpace ℝ)

/-! ### Text_1_0_51 (from Chap01) -/
/-- Text 1.0.51: the extended real line `EReal = [-∞, +∞]`, equipped with its canonical order
topology, is compact. The textbook description by real intervals together with rays at `⊥` and
`⊤` describes this same topology. -/
theorem extendedReal_compactSpace : CompactSpace EReal := inferInstance

/-! ### Text_1_0_53_1_33 (from Chap01) -/
open Filter
open scoped Topology

universe u v

/-
Text 1.0.53 (1.33): the source’s notion of lower semicontinuity at a point is the canonical
predicate `LowerSemicontinuousAt`; the textbook’s extended-real-valued case is a specialization of
this mathlib definition.
-/
recall LowerSemicontinuousAt
    {X : Type u} {Y : Type v} [TopologicalSpace X] [Preorder Y] (f : X → Y) (x : X) : Prop

/-- Text 1.0.53 (1.33), neighborhood form: lower semicontinuity of an extended-real-valued
function at a point is equivalently the condition that every strict lower bound of `f x` remains a
strict lower bound of `f` on some neighborhood of `x`. -/
theorem lowerSemicontinuousAt_iff_exists_mem_nhds_forall_lt
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    LowerSemicontinuousAt f x ↔
      ∀ ξ, ξ < f x → ∃ V : Set X, V ∈ 𝓝 x ∧ ∀ y ∈ V, ξ < f y := by
  rw [lowerSemicontinuousAt_iff]
  constructor
  · intro h ξ hξ
    have hlt : {y : X | ξ < f y} ∈ 𝓝 x := h ξ hξ
    rcases
        (Filter.exists_mem_subset_iff :
          (∃ V ∈ 𝓝 x, V ⊆ {y : X | ξ < f y}) ↔ {y : X | ξ < f y} ∈ 𝓝 x).2 hlt with
      ⟨V, hV, hltV⟩
    exact ⟨V, hV, fun y hy ↦ hltV hy⟩
  · intro h ξ hξ
    rcases h ξ hξ with ⟨V, hV, hlt⟩
    exact mem_of_superset hV (fun y hy ↦ hlt y hy)

/-! ### Text_1_0_54 (from Chap01) -/
universe u v

open Filter
open scoped Topology

/-- Text 1.0.54 (1): an extended-real-valued function is lower semicontinuous on the whole space
exactly when it is lower semicontinuous at every point. -/
-- Proof sketch: this is the direct pointwise expansion of the canonical predicate
-- `LowerSemicontinuous`.
theorem lowerSemicontinuous_iff_forall_lowerSemicontinuousAt
    {X : Type u} [TopologicalSpace X] {f : X → EReal} :
    LowerSemicontinuous f ↔ ∀ x, LowerSemicontinuousAt f x :=
  lowerSemicontinuous_iff

/-- Text 1.0.54 (2): an extended-real-valued function is upper semicontinuous at `x` exactly when
its negation is lower semicontinuous at `x`. -/
-- Proof sketch: use that negation on `EReal` reverses the order and transports the defining
-- neighborhoods for lower semicontinuity to those for upper semicontinuity.
theorem upperSemicontinuousAt_iff_lowerSemicontinuousAt_neg
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    UpperSemicontinuousAt f x ↔ LowerSemicontinuousAt (fun y ↦ -f y) x := by
  rw [upperSemicontinuousAt_iff, lowerSemicontinuousAt_iff]
  constructor
  · intro h y hy
    have hxy : f x < -y := EReal.lt_neg_comm.mp hy
    simpa [EReal.lt_neg_comm] using h (-y) hxy
  · intro h y hy
    have hxy : -y < -f x := EReal.neg_lt_neg_iff.2 hy
    simpa [EReal.neg_lt_neg_iff] using h (-y) hxy

private lemma point_mem_of_frequently {X : Type u} [TopologicalSpace X] {x : X}
    {P : X → Prop} (hP : ∃ᶠ z in nhds x, P z) {U : Set X} (hU : U ∈ nhds x) :
    ∃ z, z ∈ U ∧ P z := by
  have hBoth : ∃ᶠ z in nhds x, P z ∧ z ∈ U := by
    simpa [and_left_comm, and_assoc] using hP.and_eventually hU
  rcases hBoth.exists with ⟨z, hzP, hzU⟩
  exact ⟨z, hzU, hzP⟩

private structure NeighborhoodIndex {X : Type u} [TopologicalSpace X] (x : X) where
  carrier : Set X
  mem_nhds : carrier ∈ nhds x

private instance {X : Type u} [TopologicalSpace X] (x : X) : Nonempty (NeighborhoodIndex x) :=
  ⟨⟨Set.univ, Filter.univ_mem⟩⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : LE (NeighborhoodIndex x) :=
  ⟨fun U W ↦ W.carrier ⊆ U.carrier⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : Preorder (NeighborhoodIndex x) where
  le := (· ≤ ·)
  le_refl U := by
    intro y hy
    exact hy
  le_trans U V W hUV hVW := by
    intro y hy
    exact hUV (hVW hy)

private def infNeighborhoodIndex {X : Type u} [TopologicalSpace X] {x : X}
    (U W : NeighborhoodIndex x) : NeighborhoodIndex x :=
  ⟨U.carrier ∩ W.carrier, Filter.inter_mem U.mem_nhds W.mem_nhds⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} :
    IsDirectedOrder (NeighborhoodIndex x) :=
  ⟨fun U W ↦
    ⟨infNeighborhoodIndex U W,
      by
        intro y hy
        exact hy.1,
      by
        intro y hy
        exact hy.2⟩⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} :
    IsDirectedOrder (ULift.{v} (NeighborhoodIndex x)) :=
  ⟨fun U W ↦
    ⟨ULift.up (infNeighborhoodIndex U.down W.down),
      by
        intro y hy
        exact hy.1,
      by
        intro y hy
        exact hy.2⟩⟩

private noncomputable def badUpperNet {X : Type u} [TopologicalSpace X]
    {f : X → EReal} {x : X} {y : EReal} (hfreq : ∃ᶠ z in nhds x, y ≤ f z) :
    NeighborhoodIndex x → X :=
  fun U ↦ Classical.choose (point_mem_of_frequently hfreq U.mem_nhds)

private lemma badUpperNet_mem {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X}
    {y : EReal} (hfreq : ∃ᶠ z in nhds x, y ≤ f z) (U : NeighborhoodIndex x) :
    badUpperNet hfreq U ∈ U.carrier := by
  exact (Classical.choose_spec (point_mem_of_frequently hfreq U.mem_nhds)).1

private lemma le_badUpperNet {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X}
    {y : EReal} (hfreq : ∃ᶠ z in nhds x, y ≤ f z) (U : NeighborhoodIndex x) :
    y ≤ f (badUpperNet hfreq U) := by
  exact (Classical.choose_spec (point_mem_of_frequently hfreq U.mem_nhds)).2

private lemma tendsto_liftedBadUpperNet {X : Type u} [TopologicalSpace X] {f : X → EReal}
    {x : X} {y : EReal} (hfreq : ∃ᶠ z in nhds x, y ≤ f z) :
    Tendsto (fun U : ULift.{v} (NeighborhoodIndex x) ↦ badUpperNet hfreq U.down) atTop
      (nhds x) := by
  rw [Filter.tendsto_def]
  intro U hU
  rw [Filter.mem_atTop_sets]
  refine ⟨ULift.up ⟨U, hU⟩, ?_⟩
  intro W hW
  exact hW (badUpperNet_mem hfreq W.down)

private structure NhdsPoint {X : Type u} [TopologicalSpace X] (x : X) where
  value : X
  carrier : Set X
  value_mem : value ∈ carrier
  carrier_mem_nhds : carrier ∈ nhds x

private instance {X : Type u} [TopologicalSpace X] (x : X) : Nonempty (NhdsPoint x) :=
  ⟨⟨x, Set.univ, by simp, by simp⟩⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : LE (NhdsPoint x) :=
  ⟨fun p q ↦ q.carrier ⊆ p.carrier⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : Preorder (NhdsPoint x) where
  le := (· ≤ ·)
  le_refl p := by
    intro y hy
    exact hy
  le_trans p q r hpq hqr := by
    intro y hy
    exact hpq (hqr hy)

private instance {X : Type u} [TopologicalSpace X] {x : X} : IsDirectedOrder (NhdsPoint x) := by
  refine ⟨?_⟩
  intro p q
  have hMemNhds : p.carrier ∩ q.carrier ∈ nhds x :=
    Filter.inter_mem p.carrier_mem_nhds q.carrier_mem_nhds
  refine ⟨⟨x, p.carrier ∩ q.carrier, mem_of_mem_nhds hMemNhds, hMemNhds⟩, ?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    exact hy.2

private instance {X : Type u} [TopologicalSpace X] {x : X} :
    IsDirectedOrder (ULift.{v} (NhdsPoint x)) :=
  ⟨fun p q ↦
    let r : NhdsPoint x := by
      have hMemNhds : p.down.carrier ∩ q.down.carrier ∈ nhds x :=
        Filter.inter_mem p.down.carrier_mem_nhds q.down.carrier_mem_nhds
      exact ⟨x, p.down.carrier ∩ q.down.carrier, mem_of_mem_nhds hMemNhds, hMemNhds⟩
    ⟨ULift.up r,
      by
        intro y hy
        exact hy.1,
      by
        intro y hy
        exact hy.2⟩⟩

private lemma tendsto_liftedNhdsPoint {X : Type u} [TopologicalSpace X] {x : X} :
    Tendsto (fun p : ULift.{v} (NhdsPoint x) ↦ p.down.value) atTop (nhds x) := by
  rw [Filter.tendsto_def]
  intro U hU
  rw [Filter.mem_atTop_sets]
  refine ⟨ULift.up ⟨x, U, mem_of_mem_nhds hU, hU⟩, ?_⟩
  intro p hp
  exact hp p.down.value_mem

private lemma continuousAt_of_tendsto_liftedNhdsPoint {X : Type u} [TopologicalSpace X]
    {f : X → EReal} {x : X}
    (h : Tendsto (fun p : ULift.{v} (NhdsPoint x) ↦ f p.down.value) atTop (nhds (f x))) :
    ContinuousAt f x := by
  rw [Filter.tendsto_def] at h
  rw [ContinuousAt, Filter.tendsto_def]
  intro V hV
  rcases (Filter.mem_atTop_sets.mp (h V hV)) with ⟨p, hp⟩
  refine Filter.mem_of_superset p.down.carrier_mem_nhds ?_
  intro y hy
  have hyV := hp (ULift.up ⟨y, p.down.carrier, hy, p.down.carrier_mem_nhds⟩) (by
    intro z hz
    exact hz)
  simpa using hyV

/-- Text 1.0.54 (2), net form: upper semicontinuity at `x` is equivalent to the limsup bound
along every convergent net `ξ`. -/
-- Proof sketch: the forward implication composes the convergent net with the canonical limsup
-- characterization `upperSemicontinuousAt_iff_limsup_le`. For the reverse implication, if some
-- threshold `y > f x` is not eventually avoided near `x`, choose from each neighborhood a point
-- where `f` stays at least `y`; the resulting neighborhood-indexed net converges to `x` and has
-- limsup at least `y`, contradicting the assumed net inequality.
theorem upperSemicontinuousAt_iff_net_limsup_le
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    UpperSemicontinuousAt f x ↔
      ∀ {A : Type (max u v)} [Preorder A] [IsDirectedOrder A] (ξ : A → X),
        Tendsto ξ atTop (nhds x) → limsup (f ∘ ξ) atTop ≤ f x := by
  constructor
  · intro h A _ _ ξ hξ
    calc
      limsup (f ∘ ξ) atTop = limsup f (map ξ atTop) := rfl
      _ ≤ limsup f (nhds x) := limsup_le_limsup_of_le hξ
      _ ≤ f x := h.limsup_le
  · intro h
    rw [upperSemicontinuousAt_iff]
    intro y hy
    by_contra hyEvent
    have hyFreq : ∃ᶠ z in nhds x, y ≤ f z := by
      simpa [not_lt] using Filter.not_eventually.mp hyEvent
    let ξ : ULift.{v} (NeighborhoodIndex x) → X := fun U ↦ badUpperNet hyFreq U.down
    have hξ : Tendsto ξ atTop (nhds x) := tendsto_liftedBadUpperNet hyFreq
    have hLimsup : limsup (f ∘ ξ) atTop ≤ f x := h ξ hξ
    have hyLe : y ≤ limsup (f ∘ ξ) atTop := by
      refine le_limsup_of_frequently_le ?_
      exact Filter.Frequently.of_forall fun U ↦ le_badUpperNet hyFreq U.down
    exact (not_le_of_gt hy) (hyLe.trans hLimsup)

/-- Text 1.0.54 (3): an extended-real-valued function is continuous at `x` exactly when it is both
lower semicontinuous and upper semicontinuous at `x`. -/
-- Proof sketch: apply the standard equivalence between continuity at a point and simultaneous
-- lower and upper semicontinuity.
theorem continuousAt_iff_lower_and_upperSemicontinuousAt
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    ContinuousAt f x ↔ LowerSemicontinuousAt f x ∧ UpperSemicontinuousAt f x :=
  continuousAt_iff_lower_upperSemicontinuousAt

/-- Text 1.0.54 (3), net form: continuity at `x` is equivalent to preservation of convergence
along every net converging to `x`. -/
-- Proof sketch: the forward implication composes a convergent net with `ContinuousAt.tendsto`.
-- For the reverse implication, use the universal neighborhood-point net, whose indices are pairs
-- `(y, U)` with `U ∈ 𝓝 x` and `y ∈ U`; convergence of its image shows that some neighborhood of
-- `x` is mapped into each neighborhood of `f x`.
theorem continuousAt_iff_net_tendsto
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    ContinuousAt f x ↔
      ∀ {A : Type (max u v)} [Preorder A] [IsDirectedOrder A] (ξ : A → X),
        Tendsto ξ atTop (nhds x) → Tendsto (f ∘ ξ) atTop (nhds (f x)) := by
  constructor
  · intro h A _ _ ξ hξ
    simpa [Function.comp] using h.tendsto.comp hξ
  · intro h
    let ξ : ULift.{v} (NhdsPoint x) → X := fun p ↦ p.down.value
    have hξ : Tendsto ξ atTop (nhds x) := tendsto_liftedNhdsPoint
    have hImage : Tendsto (f ∘ ξ) atTop (nhds (f x)) := h ξ hξ
    exact continuousAt_of_tendsto_liftedNhdsPoint <| by
      simpa [ξ, Function.comp] using hImage

/-! ### Text_1_0_55 (from Chap01) -/
universe u

namespace ERealFunction

variable {X : Type u} [TopologicalSpace X]

/-- Text 1.0.55: the points where an `EReal`-valued function takes a real value and is continuous
are exactly the points in its effective domain at which it is continuous. -/
theorem mem_effectiveDom_inter_continuousAt_iff_exists_real (f : X → EReal) (x : X) :
    x ∈ effectiveDom f ∩ {y | ContinuousAt f y} ↔
      (∃ r : ℝ, f x = (r : EReal)) ∧ ContinuousAt f x := by
  rw [Set.mem_inter_iff, Set.mem_setOf_eq, mem_effectiveDom_iff_exists_real]

end ERealFunction

/-! ### Text_1_0_56_1_36 (from Chap01) -/
open Filter

universe u

namespace ERealFunction

variable {X : Type u} [TopologicalSpace X]

/-- Text 1.0.56 (1.36): the limit inferior of an extended-real-valued function `f` at `x` is the
filter `liminf` of `f` along the neighborhood filter `nhds x`. -/
noncomputable abbrev liminfAt (f : X → EReal) (x : X) : EReal :=
  liminf f (nhds x)

/-- The textbook neighborhood formula for the pointwise limit inferior. -/
-- Proof sketch: unfold `liminfAt` and specialize the standard filter formula for `Filter.liminf`
-- to the neighborhood filter `nhds x`.
theorem liminfAt_eq_sSup_nhds_sInf (f : X → EReal) (x : X) :
    liminfAt f x = sSup ((fun V : Set X ↦ sInf (f '' V)) '' {V : Set X | V ∈ nhds x}) := by
  simpa [liminfAt] using (liminf_eq_sSup_sInf (nhds x) f)

end ERealFunction

/-! ### Text_1_0_57 (from Chap01) -/
universe u

open Set

/-- Text 1.0.57: for a topological space `X` and a subset `C ⊆ X`, the extended-real indicator
`ν_C`, equal to `0` on `C` and `+∞` on `Cᶜ`, is lower semicontinuous if and only if `C` is
closed. -/
theorem lowerSemicontinuous_indicator_compl_top_iff_isClosed
    {X : Type u} [TopologicalSpace X] (C : Set X) :
    LowerSemicontinuous (indicator Cᶜ fun _ : X ↦ (⊤ : EReal)) ↔ IsClosed C := by
  constructor
  · intro hν
    have hopen :
        IsOpen ((indicator Cᶜ fun _ : X ↦ (⊤ : EReal)) ⁻¹' Ioi (0 : EReal)) :=
      hν.isOpen_preimage (0 : EReal)
    have hpreimage :
        ((indicator Cᶜ fun _ : X ↦ (⊤ : EReal)) ⁻¹' Ioi (0 : EReal)) = Cᶜ := by
      ext x
      by_cases hx : x ∈ C
      · simp [hx]
      · simp [hx, EReal.zero_lt_top]
    simpa [hpreimage] using hopen.isClosed_compl
  · intro hC
    simpa using hC.isOpen_compl.lowerSemicontinuous_indicator (show (0 : EReal) ≤ ⊤ by simp)

/-! ### Text_1_0_58 (from Chap01) -/
universe u

open Filter
open scoped Topology

/- Text 1.0.58: for a subset `C` of a Hausdorff topological space, being sequentially closed is
formalized by the canonical predicate `IsSeqClosed C`, meaning that every convergent sequence in
`C` has its limit in `C`. The separation assumption is not needed for this definition. -/
recall IsSeqClosed

/-- Text 1.0.58: the canonical predicate `IsSeqClosed C` means that every convergent sequence in
`C` has its limit in `C`. This is just the defining equation of `IsSeqClosed`. -/
theorem isSeqClosed_iff_forall_tendsto_mem {X : Type u} [TopologicalSpace X] {C : Set X} :
    IsSeqClosed C ↔
      ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, (∀ n, x n ∈ C) → Tendsto x atTop (𝓝 p) → p ∈ C :=
  Iff.rfl

/-! ### Text_1_0_59 (from Chap01) -/
/- Text 1.0.59: if `C` is a closed subset of a topological space `X`, then `C` is sequentially
closed; equivalently, every sequence in `C` converging to `x` has limit `x ∈ C`. -/
recall IsClosed.isSeqClosed

/-! ### Text_1_0_60 (from Chap01) -/
/- Text 1.0.60: a topological space is sequential exactly when every sequentially closed subset is
closed, so closedness and sequential closedness coincide. This is the canonical class
`SequentialSpace`. -/
recall SequentialSpace

/-! ### Text_1_0_61 (from Chap01) -/
universe u

open Filter

variable {X : Type u} [TopologicalSpace X] [SequentialSpace X]

/-- Text 1.0.61: for an extended-real-valued function on a sequential topological space, lower
semicontinuity is equivalent to sequential lower semicontinuity, meaning that every convergent
sequence satisfies the liminf inequality at its limit.
-/
-- Proof sketch: use `lowerSemicontinuous_iff_isClosed_preimage` to identify lower
-- semicontinuity with closedness of all real sublevel sets, then use `isSeqClosed_iff_isClosed`
-- in a sequential space to pass between closedness and sequential closedness. The sequential
-- closedness of all sublevel sets is equivalent to the stated sequence-`liminf` inequality.
theorem lowerSemicontinuous_iff_forall_seq_tendsto_le_liminf (f : X → EReal) :
    LowerSemicontinuous f ↔
      ∀ ⦃x : X⦄ ⦃u : ℕ → X⦄,
        Tendsto u atTop (nhds x) → f x ≤ liminf (f ∘ u) atTop := by
  constructor
  · intro hf x u hu
    -- Transport the neighborhood-filter `liminf` inequality along the convergent sequence.
    calc
      f x ≤ liminf f (nhds x) := hf.le_liminf x
      _ ≤ liminf f (map u atTop) := liminf_le_liminf_of_le hu
      _ = liminf (f ∘ u) atTop := rfl
  · intro hseq
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro a
    rw [← isSeqClosed_iff_isClosed]
    intro u x hu_mem hu
    -- The sequence hypothesis gives the lower bound at the limit point.
    have hx_le : f x ≤ liminf (f ∘ u) atTop := hseq hu
    -- Pointwise membership in the sublevel set forces the sequence `liminf` below `a`.
    have hliminf_le : liminf (f ∘ u) atTop ≤ a := by
      refine liminf_le_of_frequently_le ?_
      refine Frequently.of_forall fun n ↦ ?_
      simpa [Set.mem_preimage, Set.mem_Iic] using hu_mem n
    -- Combining the two inequalities puts the limit point back in the same sublevel set.
    show x ∈ f ⁻¹' Set.Iic a
    simpa [Set.mem_preimage, Set.mem_Iic] using hx_le.trans hliminf_le

/-! ### Text_1_0_62 (from Chap01) -/
universe u

open Filter

variable {X : Type u} [TopologicalSpace X]

private lemma eventually_mem_compl_of_isSeqClosed {s : Set X} (hs : IsSeqClosed s) {x : ℕ → X}
    {p : X} (hx : Tendsto x atTop (nhds p)) (hp : p ∈ sᶜ) :
    ∀ᶠ n in atTop, x n ∈ sᶜ := by
  by_contra hEvent
  have hFreq : ∃ᶠ n in atTop, x n ∈ s := by
    by_contra hFreq
    apply hEvent
    simpa [Filter.not_frequently] using hFreq
  rcases extraction_of_frequently_atTop hFreq with ⟨φ, hφ_mono, hφ_mem⟩
  exact hp <| hs hφ_mem <| hx.comp hφ_mono.tendsto_atTop

private lemma seqContinuous_ulift_mem_compl_of_isSeqClosed {s : Set X} (hs : IsSeqClosed s) :
    SeqContinuous (fun x : X ↦ ULift.up (x ∈ sᶜ)) := by
  intro x p hx
  by_cases hp : p ∈ sᶜ
  · have hmem : Tendsto (fun n ↦ x n ∈ sᶜ) atTop (nhds True) := by
      rw [tendsto_nhds_true]
      exact eventually_mem_compl_of_isSeqClosed hs hx hp
    simpa [Function.comp, hp] using continuous_uliftUp.seqContinuous hmem
  · have hfalse : Tendsto (fun n ↦ x n ∈ sᶜ) atTop (nhds False) := by
      simp [nhds_false]
    simpa [Function.comp, hp] using continuous_uliftUp.seqContinuous hfalse

/-- Text 1.0.62: a topological space is sequential if and only if every map from it to an
arbitrary topological space is continuous exactly when it is sequentially continuous. -/
-- Proof sketch: For the forward implication, use the existing theorem
-- `continuous_iff_seqContinuous` on a sequential space. For the converse, test the assumed
-- equivalence on the Sierpinski-valued characteristic map of `sᶜ`: sequential closedness of `s`
-- makes this map sequentially continuous, hence continuous, so `sᶜ` is open and `s` is closed.
theorem sequentialSpace_iff_forall_continuous_iff_seqContinuous :
    SequentialSpace X ↔
      ∀ ⦃Y : Type*⦄ [TopologicalSpace Y] (f : X → Y), Continuous f ↔ SeqContinuous f := by
  constructor
  · intro hX Y _ f
    letI : SequentialSpace X := hX
    exact (continuous_iff_seqContinuous : Continuous f ↔ SeqContinuous f)
  · intro h
    refine SequentialSpace.mk fun s hs ↦ ?_
    let f : X → ULift Prop := fun x ↦ ULift.up (x ∈ sᶜ)
    have hcont : Continuous f := (h f).2 (seqContinuous_ulift_mem_compl_of_isSeqClosed hs)
    have hcont' : Continuous (fun x : X ↦ x ∈ sᶜ) := by
      simpa [f, Function.comp] using continuous_uliftDown.comp hcont
    have hopen : IsOpen (sᶜ : Set X) := by
      simpa using (isOpen_iff_continuous_mem : IsOpen (sᶜ : Set X) ↔
        Continuous (fun x : X ↦ x ∈ sᶜ)).2 hcont'
    exact isOpen_compl_iff.mp hopen

/-! ### Text_1_0_63 (from Chap01) -/
universe u

/- Text 1.0.63: for a subset `C` of a metric space `X`, the diameter is the canonical extended
diameter `Metric.ediam C`, and the distance function to `C`, with value `∞` when `C = ∅`, is the
canonical extended infimum-edistance map `fun x ↦ Metric.infEDist x C`. -/
recall Metric.ediam {α : Type u} [PseudoEMetricSpace α] (s : Set α) : ENNReal

/- The distance-to-set function is the canonical extended infimum edistance. -/
recall Metric.infEDist {α : Type u} [PseudoEMetricSpace α] (x : α) (s : Set α) : ENNReal

/- For the empty set, the extended distance-to-set function is constantly `∞`. -/
recall Metric.infEDist_empty

/-! ### Text_1_0_64 (from Chap01) -/
universe u

/- Text 1.0.64: in a metric space, the open ball of center `x` and positive radius `ρ` is the
canonical set `Metric.ball x ρ`; the closed ball and the open-ball description of the induced
metric topology are recalled by the companion canonical API below. -/
recall Metric.ball {α : Type u} [PseudoMetricSpace α] (x : α) (ε : ℝ) : Set α

/- Closed balls in a metric space are formalized by the canonical set `Metric.closedBall x ρ`. -/
recall Metric.closedBall {α : Type u} [PseudoMetricSpace α] (x : α) (ε : ℝ) : Set α

/- Membership in an open ball is characterized by the textbook inequality `dist x y < ρ`. -/
recall Metric.mem_ball' {α : Type u} [PseudoMetricSpace α] {x y : α} {ε : ℝ} :
    y ∈ Metric.ball x ε ↔ dist x y < ε

/- Membership in a closed ball is characterized by the textbook inequality `dist x y ≤ ρ`. -/
recall Metric.mem_closedBall' {α : Type u} [PseudoMetricSpace α] {x y : α} {ε : ℝ} :
    y ∈ Metric.closedBall x ε ↔ dist x y ≤ ε

/- The metric topology on a metric space is characterized by the open-ball basis
`Metric.isOpen_iff`. -/
recall Metric.isOpen_iff {α : Type u} [PseudoMetricSpace α] {s : Set α} :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s

/-! ### Text_1_0_65 (from Chap01) -/
universe u

/- Text 1.0.65: a topological space is metrizable when there exists a metric on the space whose
induced topology coincides with the given topology, formalized by the canonical predicate
`TopologicalSpace.MetrizableSpace`. -/
recall TopologicalSpace.MetrizableSpace (X : Type u) [TopologicalSpace X] : Prop

/-! ### Text_1_0_66 (from Chap01) -/
universe u v

open Filter

variable {X : Type u} [MetricSpace X]

/- Text 1.0.66: in a metric space, convergence of a sequence to a point is expressed by the
canonical filter-theoretic notion `Tendsto u atTop (nhds x)`. -/
recall Tendsto

/-
Text 1.0.66: in a metric space, convergence to `x` is canonically characterized by
`tendsto_iff_dist_tendsto_zero`; the sequence-at-`atTop` formulation is the textbook
specialization recorded below.
-/
recall tendsto_iff_dist_tendsto_zero {α : Type u} {β : Type v} [PseudoMetricSpace α]
    {f : β → α} {l : Filter β} {a : α} :
    Tendsto f l (nhds a) ↔ Tendsto (fun b ↦ dist (f b) a) l (nhds 0)

/-- In a metric space, a sequence converges to `x` exactly when its distances to `x` tend to `0`.
-/
-- Proof sketch: specialize `tendsto_iff_dist_tendsto_zero` to the filter `atTop` on `ℕ`.
theorem sequence_tendsto_iff_dist_tendsto_zero {u : ℕ → X} {x : X} :
    Tendsto u atTop (nhds x) ↔ Tendsto (fun n ↦ dist (u n) x) atTop (nhds 0) := by
  simpa using
    (tendsto_iff_dist_tendsto_zero :
      Tendsto u atTop (nhds x) ↔ Tendsto (fun n ↦ dist (u n) x) atTop (nhds 0))

/-! ### Text_1_0_67 (from Chap01) -/
universe u v

open Filter

variable {X : Type u} [MetricSpace X]

/- Text 1.0.67: a sequence in a metric space is Cauchy when it is formalized by the canonical
predicate `CauchySeq`; the usual metric-space distance criterion and the textbook sequential
formulation of completeness are recorded below as companion statements. -/
recall CauchySeq {α : Type u} {β : Type v} [UniformSpace α] [Preorder β] (u : β → α) : Prop

/- In a metric space, a sequence is Cauchy exactly when its pairwise distances are eventually
arbitrarily small. -/
recall Metric.cauchySeq_iff {α : Type u} {β : Type v} [PseudoMetricSpace α] [Nonempty β]
    [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε

/- Completeness of a metric space is formalized by the canonical typeclass `CompleteSpace X`. -/
recall CompleteSpace (α : Type u) [UniformSpace α] : Prop

/-- Text 1.0.67: a metric space is complete exactly when every Cauchy sequence converges to a
point of the space. -/
-- Proof sketch: use `cauchySeq_tendsto_of_complete` for the forward implication and
-- `Metric.complete_of_cauchySeq_tendsto` for the converse implication.
theorem completeSpace_iff_cauchySeq_tendsto :
    CompleteSpace X ↔ ∀ u : ℕ → X, CauchySeq u → ∃ x : X, Tendsto u atTop (nhds x) := by
  constructor
  · intro hX u hu
    letI : CompleteSpace X := hX
    exact cauchySeq_tendsto_of_complete hu
  · intro h
    exact Metric.complete_of_cauchySeq_tendsto h

/-! ### Text_1_0_68 (from Chap01) -/
universe u

/-
Text 1.0.68: a subset of a topological space, and hence in particular of a Hausdorff space, is
called a `G_δ` set when it is a countable intersection of open sets, formalized by the canonical
predicate `IsGδ`.
-/
recall IsGδ {X : Type u} [TopologicalSpace X] (s : Set X) : Prop

/- Companion recall: a set is `G_δ` exactly when it can be written as the intersection of a
sequence of open sets. -/
recall isGδ_iff_eq_iInter_nat {X : Type u} [TopologicalSpace X] {s : Set X} :
    IsGδ s ↔ ∃ (f : ℕ → Set X), (∀ n, IsOpen (f n)) ∧ s = ⋂ n, f n

/-! ### Text_1_0_69 (from Chap01) -/
universe u

/- Text 1.0.69: for an operator `T : X → X`, the textbook fixed point set `Fix T` is the
canonical mathlib set `Function.fixedPoints T`. -/
recall Function.fixedPoints {α : Type u} (T : α → α) : Set α

/- Companion recall: membership in `Function.fixedPoints T` is exactly the textbook condition
`T x = x`. -/
recall Function.mem_fixedPoints_iff {α : Type u} {T : α → α} {x : α} :
    x ∈ Function.fixedPoints T ↔ T x = x
