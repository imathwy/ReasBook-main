module

public import Topology_Munkres_2000.Book.Exercise_4_99_2.LocallyMetrizable
public import Topology_Munkres_2000.Book.Theorem_41_4.Paracompact
public import Topology_Munkres_2000.Book.Theorem_40_3
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

public section

universe u

open Set Filter
open scoped Topology

namespace LocallyMetrizableSpace

/-- Helper for Remark 6.0.4: every point of a locally metrizable space lies in an
open metrizable subspace. -/
private theorem exists_isOpen_metrizable_mem {X : Type u} [TopologicalSpace X]
    [LocallyMetrizableSpace X] (x : X) :
    ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ TopologicalSpace.MetrizableSpace U := by
  -- Shrink the metrizable neighborhood to an open neighborhood of the point.
  rcases LocallyMetrizableSpace.exists_metrizable_nhds x with ⟨s, hs, hsm⟩
  rcases mem_nhds_iff.mp hs with ⟨U, hUs, hUo, hxU⟩
  letI : TopologicalSpace.MetrizableSpace s := hsm
  -- The inclusion of the smaller subtype transports the compatible metric topology.
  have hUm : TopologicalSpace.MetrizableSpace U :=
    (Topology.IsEmbedding.inclusion hUs).metrizableSpace
  exact ⟨U, hxU, hUo, hUm⟩

/-- Helper for Remark 6.0.4: a paracompact locally metrizable space has a locally
finite open cover by metrizable subspaces. -/
private theorem exists_locallyFinite_open_metrizableCover
    {X : Type u} [TopologicalSpace X] [ParacompactSpace X] [LocallyMetrizableSpace X] :
    ∃ C : X → Set X,
      (∀ x, IsOpen (C x)) ∧ (⋃ x, C x = Set.univ) ∧ LocallyFinite C ∧
        ∀ x, TopologicalSpace.MetrizableSpace (C x) := by
  classical
  -- First choose one open metrizable neighborhood around each point.
  choose U hxU hUo hUm using fun x : X ↦ exists_isOpen_metrizable_mem x
  have hUcover : ⋃ x, U x = Set.univ :=
    iUnion_eq_univ_iff.mpr fun x ↦ ⟨x, hxU x⟩
  -- Paracompactness supplies a precise locally finite refinement of this cover.
  rcases precise_refinement U hUo hUcover with ⟨C, hCo, hCcover, hClf, hCU⟩
  refine ⟨C, hCo, hCcover, hClf, fun x ↦ ?_⟩
  letI : TopologicalSpace.MetrizableSpace (U x) := hUm x
  -- Each refined member embeds into its assigned metrizable neighborhood.
  exact (Topology.IsEmbedding.inclusion (hCU x)).metrizableSpace

/-- Helper for Remark 6.0.4: an open subset of an open subtype is open after
coercion to the ambient space. -/
private theorem isOpen_coe_of_isOpen_subtype {X : Type u} [TopologicalSpace X]
    {C : Set X} (hC : IsOpen C) {V : Set C} (hV : IsOpen V) :
    IsOpen ((fun y : C ↦ (y : X)) '' V) := by
  -- The subtype coercion from an open set is an open map.
  exact hC.isOpenMap_subtype_val V hV

/-- Helper for Remark 6.0.4: a locally finite open metrizable cover of a
paracompact space yields a sigma-locally finite topological basis. -/
private theorem hasSigmaLocallyFiniteBasis_of_locallyFinite_open_metrizableCover
    {ι : Type u} {X : Type u} [TopologicalSpace X] [ParacompactSpace X]
    (C : ι → Set X) (hCo : ∀ i, IsOpen (C i)) (hCcover : ⋃ i, C i = Set.univ)
    (hClf : LocallyFinite C) (hCm : ∀ i, TopologicalSpace.MetrizableSpace (C i)) :
    HasSigmaLocallyFiniteBasis X := by
  classical
  -- Choose one compatible metric on every member of the locally finite cover.
  let metrics : ∀ i, MetricSpace (C i) := fun i ↦
    @TopologicalSpace.metrizableSpaceMetric (C i) _ (hCm i)
  let radius : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let balls : ℕ → (Σ i, C i) → Set X := fun n z ↦
    (fun y : C z.1 ↦ (y : X)) ''
      @Metric.ball (C z.1) (metrics z.1).toPseudoMetricSpace z.2 (radius n / 2)
  have hballsOpen : ∀ n z, IsOpen (balls n z) := by
    intro n z
    letI : MetricSpace (C z.1) := metrics z.1
    apply isOpen_coe_of_isOpen_subtype (hCo z.1)
    with_reducible_and_instances exact Metric.isOpen_ball
  have hballsCover : ∀ n, ⋃ z, balls n z = Set.univ := by
    intro n
    apply iUnion_eq_univ_iff.mpr
    intro x
    rcases iUnion_eq_univ_iff.mp hCcover x with ⟨i, hxi⟩
    refine ⟨⟨i, ⟨x, hxi⟩⟩, ?_⟩
    refine ⟨⟨x, hxi⟩, ?_, rfl⟩
    letI : MetricSpace (C i) := metrics i
    exact Metric.mem_ball_self (by positivity)
  -- Refine the ball cover independently at each countable radius scale.
  choose D hDo hDcover hDlf hDsub using fun n ↦
    precise_refinement (balls n) (hballsOpen n) (hballsCover n)
  let basisSets : Set (Set X) := ⋃ n, Set.range (D n)
  have hBasisOpen : ∀ U ∈ basisSets, IsOpen U := by
    intro U hU
    rcases Set.mem_iUnion.mp hU with ⟨n, hn⟩
    rcases hn with ⟨z, rfl⟩
    exact hDo n z
  have hBasisNhds : ∀ x U, x ∈ U → IsOpen U →
      ∃ V ∈ basisSets, x ∈ V ∧ V ⊆ U := by
    intro x U hxU hUo
    -- Only finitely many members of the original cover contain the point.
    have hfinite : {i | x ∈ C i}.Finite := hClf.point_finite x
    have hsmall : ∀ i ∈ {i | x ∈ C i}, ∀ᶠ n in atTop,
        ∀ xi : C i, (xi : X) = x →
          @Metric.ball (C i) (metrics i).toPseudoMetricSpace xi (radius n) ⊆
            {y : C i | (y : X) ∈ U} := by
      intro i hxi
      letI : MetricSpace (C i) := metrics i
      let xi : C i := ⟨x, hxi⟩
      have hUi : {y : C i | (y : X) ∈ U} ∈ 𝓝 xi := by
        exact (hUo.preimage continuous_subtype_val).mem_nhds hxU
      have hEventuallyRadius : ∀ᶠ r in 𝓝 (0 : ℝ), Metric.ball xi r ⊆
          {y : C i | (y : X) ∈ U} := eventually_ball_subset hUi
      have hEventually := tendsto_one_div_add_atTop_nhds_zero_nat.eventually hEventuallyRadius
      filter_upwards [hEventually] with n hn
      intro yi hyi
      have hyixi : yi = xi := Subtype.ext hyi
      rwa [hyixi]
    have hUniform : ∀ᶠ n in atTop, ∀ i ∈ {i | x ∈ C i},
        ∀ xi : C i, (xi : X) = x →
          @Metric.ball (C i) (metrics i).toPseudoMetricSpace xi (radius n) ⊆
            {y : C i | (y : X) ∈ U} :=
      hfinite.eventually_all.mpr hsmall
    rcases hUniform.exists with ⟨n, hn⟩
    -- Choose a refined half-radius ball containing the point.
    rcases iUnion_eq_univ_iff.mp (hDcover n) x with ⟨z, hxD⟩
    refine ⟨D n z, ?_, hxD, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨n, ⟨z, rfl⟩⟩
    · intro y hyD
      have hyBall := hDsub n z hyD
      have hxBall := hDsub n z hxD
      rcases hxBall with ⟨xi, hxiBall, hxix⟩
      rcases hyBall with ⟨yi, hyiBall, hyiy⟩
      have hxiMem : x ∈ C z.1 := hxix ▸ xi.property
      have hBallSubset : @Metric.ball (C z.1) (metrics z.1).toPseudoMetricSpace xi (radius n) ⊆
          {w : C z.1 | (w : X) ∈ U} := hn z.1 hxiMem xi hxix
      letI : MetricSpace (C z.1) := metrics z.1
      have hyInLargeBall : yi ∈ Metric.ball xi (radius n) := by
        rw [Metric.mem_ball] at hxiBall hyiBall ⊢
        calc
          dist yi xi ≤ dist yi z.2 + dist z.2 xi := dist_triangle _ _ _
          _ < radius n / 2 + radius n / 2 :=
            add_lt_add hyiBall (by simpa only [dist_comm] using hxiBall)
          _ = radius n := by ring
      exact hyiy ▸ hBallSubset hyInLargeBall
  have hBasis : TopologicalSpace.IsTopologicalBasis basisSets :=
    TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds hBasisOpen hBasisNhds
  -- The scale decomposition witnesses sigma-local finiteness.
  rw [hasSigmaLocallyFiniteBasis_iff]
  refine ⟨basisSets, fun n ↦ Set.range (D n), hBasis, rfl, ?_⟩
  intro n
  exact (hDlf n).on_range

/-- Helper for Remark 6.0.4: every paracompact locally metrizable space has a
sigma-locally finite basis. -/
private theorem hasSigmaLocallyFiniteBasis
    (X : Type u) [TopologicalSpace X] [ParacompactSpace X] [LocallyMetrizableSpace X] :
    HasSigmaLocallyFiniteBasis X := by
  -- Use the cover-level basis theorem through its four stable cover properties.
  rcases exists_locallyFinite_open_metrizableCover (X := X) with
    ⟨C, hCo, hCcover, hClf, hCm⟩
  exact hasSigmaLocallyFiniteBasis_of_locallyFinite_open_metrizableCover
    C hCo hCcover hClf hCm

end LocallyMetrizableSpace

namespace TopologicalSpace

/-- Remark 6.0.4: A topological space is metrizable if and only if it is
paracompact, Hausdorff, and locally metrizable, in the precise form proved in §42. -/
theorem metrizableSpace_iff_paracompact_t2_locallyMetrizable
    (X : Type u) [TopologicalSpace X] :
    MetrizableSpace X ↔ ParacompactSpace X ∧ T2Space X ∧ LocallyMetrizableSpace X := by
  constructor
  · intro hX
    -- Existing metrizable-space instances provide all three necessary properties.
    letI : MetrizableSpace X := hX
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · rintro ⟨hpara, ht2, hlocal⟩
    -- Paracompact Hausdorff spaces are regular, and the helper supplies the basis.
    letI : ParacompactSpace X := hpara
    letI : T2Space X := ht2
    letI : LocallyMetrizableSpace X := hlocal
    have hSigma : HasSigmaLocallyFiniteBasis X :=
      LocallyMetrizableSpace.hasSigmaLocallyFiniteBasis X
    exact (nagataSmirnovMetrization X).mpr ⟨inferInstance, hSigma⟩

end TopologicalSpace

namespace LocallyMetrizableSpace

/-- A paracompact Hausdorff locally metrizable space is metrizable. -/
instance metrizableSpace_of_paracompact_t2 (X : Type u) [TopologicalSpace X]
    [ParacompactSpace X] [T2Space X] [LocallyMetrizableSpace X] :
    TopologicalSpace.MetrizableSpace X := by
  -- Apply the reverse implication of the Smirnov characterization.
  exact (TopologicalSpace.metrizableSpace_iff_paracompact_t2_locallyMetrizable X).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

end LocallyMetrizableSpace
