module

public import Topology_Munkres_2000.Book.Example_71_1
public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Topology_Munkres_2000.Book.Definition_54_4
public import Topology_Munkres_2000.Book.Definition_9_0_2
public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
public import Mathlib.Topology.Piecewise

public section

open Filter
open scoped Topology

namespace FundamentalGroup

/-- Helper for Example 80.1: inclusion through a nested subspace induces the
same fundamental-group map as direct inclusion into the ambient space. -/
private lemma mapOfSubtype_comp_mapOfSubset
    {X : Type*} [TopologicalSpace X] {A U : Set X} (h : A ⊆ U) (a : A) :
    (mapOfSubtype U ⟨a, h a.property⟩).comp (mapOfSubset h a) =
      mapOfSubtype A a := by
  -- Expose both inclusion maps and compare their action on each loop class.
  ext p
  simp only [MonoidHom.comp_apply]
  rw [mapOfSubset_eq_map_inclusion]
  unfold mapOfSubtype
  have innerMap :
      map (ContinuousMap.inclusion h) a p =
        Path.Homotopic.Quotient.map p (ContinuousMap.inclusion h) :=
    map_apply (ContinuousMap.inclusion h) a p
  -- The composite bundled inclusion reduces to direct subtype inclusion.
  have nestedMap :
      Path.Homotopic.Quotient.map
          (Path.Homotopic.Quotient.map p (ContinuousMap.inclusion h))
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) =
        Path.Homotopic.Quotient.map p
          (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) := by
    exact (Path.Homotopic.Quotient.map_comp
      (p := p) (f := ContinuousMap.inclusion h)
      (g := (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))).symm
  have outerToDirect :
      map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
          ⟨a, h a.property⟩
            (Path.Homotopic.Quotient.map p (ContinuousMap.inclusion h)) =
        map (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) a p := by
    rw [map_apply, map_apply]
    exact nestedMap
  -- Transport the inner computation before applying the quotient-level composition.
  exact (congrArg
    (fun q ↦ map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
      ⟨a, h a.property⟩ q) innerMap).trans outerToDirect

end FundamentalGroup

namespace InfiniteEarring

/-- Helper for Example 80.1: the common origin lies on every component circle. -/
lemma origin_mem_component (n : ℕ+) : origin ∈ component n := by
  -- Reduce to the defining Euclidean sphere equation at the origin.
  rw [mem_component_iff, origin_coe, mem_circle_iff, EuclideanSpace.dist_eq]
  simp [center_apply, Fin.sum_univ_two]

/-- Helper for Example 80.1: points of the `n`th component are at distance at most
`2 * (n : ℝ)⁻¹` from the common origin. -/
lemma dist_origin_le_two_inv {n : ℕ+} {x : Space} (hx : x ∈ component n) :
    dist x origin ≤ 2 * (n : ℝ)⁻¹ := by
  -- The distance to the origin is bounded through the center of the circle.
  calc
    dist x origin = dist (x : Plane) (origin : Plane) := Subtype.dist_eq x origin
    _ = dist (x : Plane) 0 := by rw [origin_coe]
    _ ≤ dist (x : Plane) (center n) + dist (center n) 0 :=
      dist_triangle _ _ _
    _ = (n : ℝ)⁻¹ + (n : ℝ)⁻¹ := by
      rw [(mem_circle_iff (x : Plane) n).mp ((mem_component_iff x n).mp hx)]
      rw [EuclideanSpace.dist_eq]
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast n.property
      simp [center_apply, Fin.sum_univ_two]
    _ = 2 * (n : ℝ)⁻¹ := by ring

/-- Helper for Example 80.1: sufficiently small component circles lie in every
neighborhood of the common origin. -/
lemma eventually_component_subset_nhds {V : Set Space} (hV : V ∈ 𝓝 origin) :
    ∀ᶠ k in Filter.atTop, component (Nat.succPNat k) ⊆ V := by
  -- Choose a metric ball inside the neighborhood, then use the uniform radius bound.
  rw [Metric.mem_nhds_iff] at hV
  obtain ⟨ε, hε, hball⟩ := hV
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun k hk x hx ↦ hball ?_⟩
  rw [Metric.mem_ball]
  refine lt_of_le_of_lt (dist_origin_le_two_inv hx) ?_
  have hkpos : 0 < (k + 1 : ℝ) := by positivity
  have hkbound : 2 / ε < (k + 1 : ℝ) := by
    calc
      2 / ε < N := hN
      _ ≤ k := by exact_mod_cast hk
      _ < k + 1 := by norm_num
  have hdiv : 2 / (k + 1 : ℝ) < ε := by
    rw [div_lt_iff₀ hkpos]
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hkbound
  simpa [Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using hdiv

/-- Helper for Example 80.1: every component circle is closed in the earring. -/
lemma isClosed_component (n : ℕ+) : IsClosed (component n) := by
  -- Expose the sphere equation through its public membership bridge.
  have hcomponent :
      component n = {x : Space | dist (x : Plane) (center n) = (n : ℝ)⁻¹} := by
    ext x
    rw [Set.mem_setOf_eq, mem_component_iff, mem_circle_iff]
  rw [hcomponent]
  exact isClosed_eq (continuous_subtype_val.dist continuous_const) continuous_const

/-- Helper for Example 80.1: every non-origin point of a component is interior
to that component in the infinite earring. -/
lemma mem_interior_component_of_ne_origin {n : ℕ+} {x : Space}
    (hx : x ∈ component n) (hxo : x ≠ origin) : x ∈ interior (component n) := by
  classical
  -- Separate `x` from the origin; all sufficiently late components lie on the origin side.
  have hdist : 0 < dist x origin := dist_pos.mpr hxo
  have horiginBall : Metric.ball origin (dist x origin / 2) ∈ 𝓝 origin :=
    Metric.ball_mem_nhds origin (half_pos hdist)
  obtain ⟨N, htail⟩ := Filter.eventually_atTop.mp
    (eventually_component_subset_nhds horiginBall)
  have hfar : (Metric.closedBall origin (dist x origin / 2))ᶜ ∈ 𝓝 x := by
    apply Metric.isClosed_closedBall.compl_mem_nhds
    rw [Metric.mem_closedBall]
    have hdist' : 0 < dist origin x := by simpa [dist_comm] using hdist
    linarith
  -- Exclude the finitely many early components other than the chosen one.
  let headAvoid : Set Space :=
    ⋂ k ∈ Finset.range N,
      if Nat.succPNat k = n then Set.univ else (component (Nat.succPNat k))ᶜ
  have hhead : headAvoid ∈ 𝓝 x := by
    dsimp [headAvoid]
    rw [Filter.biInter_finset_mem]
    intro k hk
    by_cases hkn : Nat.succPNat k = n
    · simp [hkn]
    · simp only [hkn, if_false]
      apply (isClosed_component (Nat.succPNat k)).compl_mem_nhds
      intro hxk
      have hxinter : x ∈ component (Nat.succPNat k) ∩ component n := ⟨hxk, hx⟩
      have hxorigin : x = origin := Set.mem_singleton_iff.mp
        ((component_inter_component (Nat.succPNat k) n hkn).subset hxinter)
      exact hxo hxorigin
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset (inter_mem hfar hhead) ?_
  intro y hy
  obtain ⟨m, hym⟩ := (mem_carrier_iff (y : Plane)).mp y.property
  have hycomponent : y ∈ component m := (mem_component_iff y m).mpr hym
  by_cases hmN : m.natPred < N
  · by_cases hmn : Nat.succPNat m.natPred = n
    · rw [PNat.succPNat_natPred m] at hmn
      exact hmn ▸ hycomponent
    · have hyhead := Set.mem_iInter₂.mp hy.2 m.natPred
        (Finset.mem_range.mpr hmN)
      simp only [hmn, if_false, Set.mem_compl_iff] at hyhead
      exact False.elim (hyhead (PNat.succPNat_natPred m ▸ hycomponent))
  · have hmge : N ≤ m.natPred := Nat.le_of_not_gt hmN
    have hytail : y ∈ Metric.ball origin (dist x origin / 2) :=
      htail m.natPred hmge (PNat.succPNat_natPred m ▸ hycomponent)
    exact False.elim (hy.1 (Metric.ball_subset_closedBall hytail))

/-- Helper for Example 80.1: the frontier of a component circle consists only
of the common origin. -/
lemma frontier_component_subset_origin (n : ℕ+) :
    frontier (component n) ⊆ {origin} := by
  -- Closedness puts a frontier point on the component, where every other point is interior.
  intro x hx
  have hxcomponent : x ∈ component n := by
    rw [(isClosed_component n).frontier_eq] at hx
    exact hx.1
  rw [Set.mem_singleton_iff]
  by_contra hxo
  exact (mem_frontier_iff_notMem_interior hxcomponent).mp hx
    (mem_interior_component_of_ne_origin hxcomponent hxo)

/-- Helper for Example 80.1: the collapse onto a selected component fixes that
component and sends every other point to the common origin. -/
noncomputable def componentCollapse (n : ℕ+) : Space → Space :=
  fun x ↦ @ite Space (x ∈ component n) (Classical.propDecidable _) x origin

/-- Helper for Example 80.1: the component collapse always lands in its selected
component. -/
lemma componentCollapse_mem (n : ℕ+) (x : Space) :
    componentCollapse n x ∈ component n := by
  -- On the two branches this is respectively the input hypothesis and origin membership.
  classical
  by_cases hx : x ∈ component n
  · simp [componentCollapse, hx]
  · simpa [componentCollapse, hx] using origin_mem_component n

/-- Helper for Example 80.1: the component collapse is continuous. -/
lemma continuous_componentCollapse (n : ℕ+) : Continuous (componentCollapse n) := by
  -- The identity and constant branches agree on the component frontier.
  classical
  unfold componentCollapse
  apply Continuous.if
  · intro x hx
    exact Set.mem_singleton_iff.mp (frontier_component_subset_origin n hx)
  · exact continuous_id
  · exact continuous_const

/-- Helper for Example 80.1: the component collapse fixes every point of its
selected component. -/
lemma componentCollapse_of_mem (n : ℕ+) {x : Space} (hx : x ∈ component n) :
    componentCollapse n x = x := by
  -- Membership selects the identity branch of the piecewise map.
  classical
  simp [componentCollapse, hx]

/-- Helper for Example 80.1: the component collapse as a continuous map into
the selected component. -/
noncomputable def componentCollapseMap (n : ℕ+) : C(Space, component n) :=
  ⟨fun x ↦ ⟨componentCollapse n x, componentCollapse_mem n x⟩,
    (continuous_componentCollapse n).subtype_mk (componentCollapse_mem n)⟩

/-- Helper for Example 80.1: the component collapse map is a left inverse to
the component inclusion. -/
lemma componentCollapseMap_leftInverse (n : ℕ+) :
    Function.LeftInverse (componentCollapseMap n) Subtype.val := by
  -- Coercing back to the earring exposes the identity branch on the component.
  intro x
  apply Subtype.ext
  exact componentCollapse_of_mem n x.property

/-- Helper for Example 80.1: every component circle is a retract of the infinite
earring. -/
lemma component_isRetract (n : ℕ+) : Set.IsRetract (component n) := by
  -- Package the continuous collapse and its left-inverse computation.
  exact (Set.isRetract_iff (component n)).mpr
    ⟨componentCollapseMap n, componentCollapseMap_leftInverse n⟩

universe u v

/-- Helper for Example 80.1: a continuous left inverse induces a left inverse
on fundamental groups, with the endpoint equality made explicit. -/
lemma fundamentalGroupMap_leftInverse_of_leftInverse
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Y, X)) (hgf : Function.LeftInverse g f)
    (x : X) (p : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq g (hgf x) (FundamentalGroup.map f x p) = p := by
  -- Expand both induced maps and descend to a representative loop.
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply]
  induction p using Quotient.ind
  case _ γ =>
    apply Quotient.sound
    -- Pointwise, the composite path is the original path by the supplied left inverse.
    suffices hpath :
        (fun path ↦ path.cast (hgf x).symm (hgf x).symm)
          ((fun path ↦ path.map g.continuous)
            ((fun path ↦ path.map f.continuous) γ)) = γ by
      rw [hpath]
    ext t
    exact hgf (γ t)

/-- Helper for Example 80.1: a continuous map with a continuous left inverse
induces an injective homomorphism on fundamental groups. -/
lemma fundamentalGroupMap_injective_of_leftInverse
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Y, X)) (hgf : Function.LeftInverse g f) (x : X) :
    Function.Injective (FundamentalGroup.map f x) := by
  -- The endpoint-adjusted map induced by `g` is a left inverse on loops.
  exact Function.LeftInverse.injective
    (fundamentalGroupMap_leftInverse_of_leftInverse f g hgf x)

/-- Helper for Example 80.1: the common origin as a point of a selected
component. -/
def componentOrigin (n : ℕ+) : component n :=
  ⟨origin, origin_mem_component n⟩

/-- Helper for Example 80.1: the canonical inclusion of a component into the
infinite earring. -/
def componentInclusion (n : ℕ+) : C(component n, Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Helper for Example 80.1: the fundamental group of a component is identified
with the infinite cyclic group. -/
noncomputable def componentFundamentalGroupEquivInt (n : ℕ+) :
    FundamentalGroup (component n) (componentOrigin n) ≃* Multiplicative ℤ :=
  let e := Classical.choice (componentHomeomorphicCircle n)
  (e.fundamentalGroupMulEquiv (componentOrigin n)).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      (e (componentOrigin n)) 1).trans Circle.fundamentalGroupEquivInt)

/-- Helper for Example 80.1: the fundamental group of every component circle at
the common origin is nontrivial. -/
lemma componentFundamentalGroup_nontrivial (n : ℕ+) :
    Nontrivial (FundamentalGroup (component n) (componentOrigin n)) := by
  -- Transfer nontriviality from `Multiplicative ℤ` through the circle equivalence.
  exact (componentFundamentalGroupEquivInt n).toEquiv.nontrivial

/-- Helper for Example 80.1: inclusion of a component circle into the infinite
earring induces an injective map on fundamental groups. -/
lemma componentMapOfSubtype_injective (n : ℕ+) :
    Function.Injective
      (FundamentalGroup.mapOfSubtype (component n) (componentOrigin n)) := by
  -- Use the defining bundled subtype inclusion controlled by the collapse.
  unfold FundamentalGroup.mapOfSubtype
  exact fundamentalGroupMap_injective_of_leftInverse
      (⟨Subtype.val, continuous_subtype_val⟩ : C(component n, Space))
      (componentCollapseMap n)
      (componentCollapseMap_leftInverse n) (componentOrigin n)

/-- Example 80.1. For every neighborhood `U` of the origin in the infinite earring,
the homomorphism on fundamental groups induced by the inclusion `U → Space` is nontrivial. -/
theorem inclusionMap_ne_one (U : Set Space) (hU : U ∈ 𝓝 origin) :
    FundamentalGroup.mapOfSubtype U ⟨origin, mem_of_mem_nhds hU⟩ ≠ 1 := by
  -- Route correction: expose the earlier inclusion definition locally and keep the
  -- commuting triangle entirely in the canonical `mapOfSubtype` normal form.
  -- Choose one whole component contained in the prescribed neighborhood.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_component_subset_nhds hU)
  let n : ℕ+ := Nat.succPNat N
  have hnU : component n ⊆ U := hN N le_rfl
  let a : component n := componentOrigin n
  have hinjective :
      Function.Injective (FundamentalGroup.mapOfSubtype (component n) a) := by
    exact componentMapOfSubtype_injective n
  have hnontrivial : Nontrivial (FundamentalGroup (component n) a) := by
    exact componentFundamentalGroup_nontrivial n
  obtain ⟨p, hp⟩ := exists_ne (1 : FundamentalGroup (component n) a)
  intro htrivial
  -- Evaluate the nested-inclusion identity on the chosen nonidentity loop.
  have hfactor :
      FundamentalGroup.mapOfSubtype (component n) a p =
        FundamentalGroup.mapOfSubtype U ⟨origin, mem_of_mem_nhds hU⟩
          (FundamentalGroup.mapOfSubset hnU a p) := by
    exact congrArg (fun f ↦ f p)
      (FundamentalGroup.mapOfSubtype_comp_mapOfSubset hnU a).symm
  have hdirect_one : FundamentalGroup.mapOfSubtype (component n) a p = 1 := by
    rw [hfactor, htrivial]
    rfl
  apply hp
  apply hinjective
  exact hdirect_one.trans
    (FundamentalGroup.mapOfSubtype (component n) a).map_one.symm

end InfiniteEarring
