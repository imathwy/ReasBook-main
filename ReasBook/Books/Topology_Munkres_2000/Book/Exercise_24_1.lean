module

public import Topology_Munkres_2000.Book.Exercise_24_1.UnitInterval
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Dimension.Constructions

public section

open Set

/-- Helper for Exercise 24.1: a homeomorphism preserves connectedness after deleting
corresponding points. -/
private theorem Homeomorph.connectedSpace_complSingleton_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    ConnectedSpace {z : X // z ≠ x} ↔ ConnectedSpace {z : Y // z ≠ e x} := by
  -- Restrict the homeomorphism to the complements of the chosen points.
  have hcompat (z : X) : z ≠ x ↔ e z ≠ e x := by
    constructor
    · exact fun hneq heq ↦ hneq (e.injective heq)
    · exact fun hneq heq ↦ hneq (congrArg e heq)
  exact (e.subtype hcompat).connectedSpace_iff

/-- Helper for Exercise 24.1: deleting any point from the open unit interval disconnects it. -/
private theorem openUnitInterval_complSingleton_not_connected
    (p : Ioo (0 : ℝ) 1) :
    ¬ ConnectedSpace {z : Ioo (0 : ℝ) 1 // z ≠ p} := by
  intro hconnected
  have hleftMem : (p : ℝ) / 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · linarith [p.property.1]
    · linarith [p.property.2]
  let left : Ioo (0 : ℝ) 1 := ⟨(p : ℝ) / 2, hleftMem⟩
  have hrightMem : ((p : ℝ) + 1) / 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · linarith [p.property.1]
    · linarith [p.property.2]
  let right : Ioo (0 : ℝ) 1 := ⟨((p : ℝ) + 1) / 2, hrightMem⟩
  let punctured := {z : Ioo (0 : ℝ) 1 // z ≠ p}
  let coeToReal : punctured → ℝ := fun z ↦ z.1.1
  -- Connectedness of the punctured subtype makes its image in `ℝ` order-connected.
  have hpreconnectedUniv : IsPreconnected (Set.univ : Set punctured) :=
    hconnected.toPreconnectedSpace.isPreconnected_univ
  have hinducing : Topology.IsInducing coeToReal := by
    exact Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have hpreconnected : IsPreconnected (Set.range coeToReal) := by
    rw [← Set.image_univ]
    exact hinducing.isPreconnected_image.mpr hpreconnectedUniv
  have hordConnected : Set.OrdConnected (Set.range coeToReal) :=
    isPreconnected_iff_ordConnected.mp hpreconnected
  -- Points strictly to either side of `p` belong to the punctured image.
  have hleft : (left : ℝ) ∈ Set.range coeToReal := by
    refine ⟨⟨left, ?_⟩, rfl⟩
    intro heq
    have hval := congrArg Subtype.val heq
    dsimp [left] at hval
    linarith [p.property.1]
  have hright : (right : ℝ) ∈ Set.range coeToReal := by
    refine ⟨⟨right, ?_⟩, rfl⟩
    intro heq
    have hval := congrArg Subtype.val heq
    dsimp [right] at hval
    linarith [p.property.2]
  have hpBetween : (p : ℝ) ∈ Icc (left : ℝ) (right : ℝ) := by
    constructor
    · change (p : ℝ) / 2 ≤ p
      linarith [p.property.1]
    · change (p : ℝ) ≤ ((p : ℝ) + 1) / 2
      linarith [p.property.2]
  -- Order-connectedness would put the deleted point back in the image.
  obtain ⟨z, hz⟩ := hordConnected.out hleft hright hpBetween
  have hzval : z.1 = p := Subtype.ext hz
  exact z.property hzval

/-- Helper for Exercise 24.1: deleting the right endpoint of the half-open unit interval
leaves a connected space. -/
private theorem halfOpenUnitInterval_complRightEndpoint_connected
    (endpoint : Ioc (0 : ℝ) 1) (hendpoint : (endpoint : ℝ) = 1) :
    ConnectedSpace {z : Ioc (0 : ℝ) 1 // z ≠ endpoint} := by
  let puncturedSet := {z : Ioc (0 : ℝ) 1 | z ≠ endpoint}
  -- Under coercion to `ℝ`, the punctured half-open interval is exactly `Ioo 0 1`.
  have himage : Subtype.val '' puncturedSet = Ioo (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hlt : (z : ℝ) < 1 := by
        apply lt_of_le_of_ne z.property.2
        intro heq
        apply hz
        apply Subtype.ext
        simpa only [hendpoint] using heq
      exact ⟨z.property.1, hlt⟩
    · intro hx
      have hzmem : x ∈ Ioc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
      let z : Ioc (0 : ℝ) 1 := ⟨x, hzmem⟩
      have hz : z ≠ endpoint := by
        intro heq
        have hval := congrArg Subtype.val heq
        dsimp [z] at hval
        rw [hendpoint] at hval
        exact hx.2.ne hval
      exact ⟨z, hz, rfl⟩
  have hzeroOne : (0 : ℝ) < 1 := by norm_num
  have himagePreconnected : IsPreconnected (Subtype.val '' puncturedSet) := by
    rw [himage]
    exact (isConnected_Ioo hzeroOne).isPreconnected
  have hpreconnected : IsPreconnected puncturedSet :=
    Topology.IsInducing.subtypeVal.isPreconnected_image.mp himagePreconnected
  -- The midpoint witnesses that the punctured interval is nonempty.
  have hhalfMem : (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) 1 := by norm_num
  let half : Ioc (0 : ℝ) 1 := ⟨1 / 2, hhalfMem⟩
  have hhalf : half ∈ puncturedSet := by
    intro heq
    have hval := congrArg Subtype.val heq
    dsimp [half] at hval
    rw [hendpoint] at hval
    norm_num at hval
  have hnonempty : puncturedSet.Nonempty := ⟨half, hhalf⟩
  exact Subtype.connectedSpace ⟨hnonempty, hpreconnected⟩

/-- Helper for Exercise 24.1: deleting one point from the real line disconnects it. -/
private theorem real_complSingleton_not_connected (x : ℝ) :
    ¬ ConnectedSpace {y : ℝ // y ≠ x} := by
  intro hconnected
  -- Connectedness would make the complement of `x` order-connected.
  have hpreconnected : IsPreconnected {y : ℝ | y ≠ x} :=
    isPreconnected_iff_preconnectedSpace.mpr hconnected.toPreconnectedSpace
  have hordConnected : Set.OrdConnected {y : ℝ | y ≠ x} :=
    isPreconnected_iff_ordConnected.mp hpreconnected
  have hleft : x - 1 ∈ {y : ℝ | y ≠ x} := by simp
  have hright : x + 1 ∈ {y : ℝ | y ≠ x} := by simp
  have hxBetween : x ∈ Icc (x - 1) (x + 1) := by
    constructor
    · linarith
    · linarith
  -- The interval between the two sides contains the deleted point.
  exact (hordConnected.out hleft hright hxBetween) rfl

/-- Exercise 24.1 (1a): The open and half-open unit intervals are not homeomorphic. -/
theorem openIntervalNotHomeomorphicHalfOpen :
    ¬ Nonempty (Ioo (0 : ℝ) 1 ≃ₜ Ioc (0 : ℝ) 1) := by
  rintro ⟨e⟩
  have hendpointMem : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := by norm_num
  let endpoint : Ioc (0 : ℝ) 1 := ⟨1, hendpointMem⟩
  let preimageEndpoint : Ioo (0 : ℝ) 1 := e.symm endpoint
  -- Transport connectedness of the endpoint-punctured half-open interval back to `Ioo`.
  have hhalfConnected : ConnectedSpace {z : Ioc (0 : ℝ) 1 // z ≠ endpoint} :=
    halfOpenUnitInterval_complRightEndpoint_connected endpoint rfl
  have hopenConnected : ConnectedSpace
      {z : Ioo (0 : ℝ) 1 // z ≠ preimageEndpoint} := by
    apply (e.connectedSpace_complSingleton_iff preimageEndpoint).mpr
    have hendpointImage : e preimageEndpoint = endpoint := by
      exact e.apply_symm_apply endpoint
    rw [hendpointImage]
    exact hhalfConnected
  exact openUnitInterval_complSingleton_not_connected preimageEndpoint hopenConnected

/-- Part (1b) of Exercise 24.1: The open and closed unit intervals are not homeomorphic. -/
theorem openIntervalNotHomeomorphicClosed :
    ¬ Nonempty (Ioo (0 : ℝ) 1 ≃ₜ Icc (0 : ℝ) 1) := by
  rintro ⟨e⟩
  -- A homeomorphism would transfer compactness of `Icc` to the noncompact open interval.
  letI : CompactSpace (Icc (0 : ℝ) 1) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace (Ioo (0 : ℝ) 1) := e.symm.compactSpace
  have hcompact : IsCompact (Ioo (0 : ℝ) 1) :=
    isCompact_iff_compactSpace.mpr inferInstance
  rw [isCompact_Ioo_iff] at hcompact
  norm_num at hcompact

/-- Part (1c) of Exercise 24.1: The half-open and closed unit intervals are not homeomorphic. -/
theorem halfOpenIntervalNotHomeomorphicClosed :
    ¬ Nonempty (Ioc (0 : ℝ) 1 ≃ₜ Icc (0 : ℝ) 1) := by
  rintro ⟨e⟩
  -- A homeomorphism would transfer compactness of `Icc` to the noncompact half-open interval.
  letI : CompactSpace (Icc (0 : ℝ) 1) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace (Ioc (0 : ℝ) 1) := e.symm.compactSpace
  have hcompact : IsCompact (Ioc (0 : ℝ) 1) :=
    isCompact_iff_compactSpace.mpr inferInstance
  rw [isCompact_Ioc_iff] at hcompact
  norm_num at hcompact

namespace IntervalEmbeddingExample

/-- Part (2a) of Exercise 24.1: The affine image of the closed unit interval lies in the open
unit interval. -/
theorem closedToOpen_mem (x : Icc (0 : ℝ) 1) :
    ((x : ℝ) + 1) / 3 ∈ Ioo (0 : ℝ) 1 := by
  -- The affine rescaling sends both endpoint bounds strictly inside `(0, 1)`.
  constructor
  · linarith [x.property.1]
  · linarith [x.property.2]

/-- The affine map from the closed unit interval into the open unit interval. -/
@[expose]
noncomputable def closedToOpen (x : Icc (0 : ℝ) 1) : Ioo (0 : ℝ) 1 :=
  ⟨((x : ℝ) + 1) / 3, closedToOpen_mem x⟩

/-- The underlying real value of `closedToOpen x`. -/
@[simp]
theorem coe_closedToOpen (x : Icc (0 : ℝ) 1) :
    (closedToOpen x : ℝ) = ((x : ℝ) + 1) / 3 := rfl

/-- Part (2b) of Exercise 24.1: The affine map from the closed unit interval into the open unit
interval is a topological embedding. -/
theorem isEmbedding_closedToOpen : Topology.IsEmbedding closedToOpen := by
  -- Continuity follows from the affine real-valued formula.
  have hcontinuous : Continuous closedToOpen := by
    apply Continuous.subtype_mk
    fun_prop
  -- Equality of affine values recovers equality in the closed interval.
  have hinjective : Function.Injective closedToOpen := by
    intro x y hxy
    apply Subtype.ext
    have hval := congrArg Subtype.val hxy
    simp only [coe_closedToOpen] at hval
    linarith
  exact (hcontinuous.isClosedEmbedding hinjective).isEmbedding

end IntervalEmbeddingExample

/-- Consequence for Exercise 24.1 (4): mutual topological embeddings need not imply
homeomorphism. -/
theorem mutualEmbeddingsNotImplyHomeomorphic :
    Topology.IsEmbedding UnitInterval.openInClosed ∧
      Topology.IsEmbedding IntervalEmbeddingExample.closedToOpen ∧
      ¬ Nonempty (Ioo (0 : ℝ) 1 ≃ₜ Icc (0 : ℝ) 1) :=
  ⟨UnitInterval.isEmbedding_openInClosed,
    IntervalEmbeddingExample.isEmbedding_closedToOpen,
    openIntervalNotHomeomorphicClosed⟩

/-- Part (3) of Exercise 24.1: For `n > 1`, Euclidean `n`-space is not homeomorphic to `ℝ`. -/
theorem euclideanSpaceNotHomeomorphicReal (n : ℕ) (h : 1 < n) :
    ¬ Nonempty ((Fin n → ℝ) ≃ₜ ℝ) := by
  rintro ⟨e⟩
  let origin : Fin n → ℝ := 0
  -- Rank greater than one makes Euclidean space remain connected after deleting the origin.
  have hrank : 1 < Module.rank ℝ (Fin n → ℝ) := by
    rw [rank_fin_fun]
    exact_mod_cast h
  have heuclideanConnected : ConnectedSpace {y : Fin n → ℝ // y ≠ origin} :=
    Subtype.connectedSpace (isConnected_compl_singleton_of_one_lt_rank hrank origin)
  -- The homeomorphism would transfer this connectedness to a punctured real line.
  have hrealConnected : ConnectedSpace {y : ℝ // y ≠ e origin} :=
    (e.connectedSpace_complSingleton_iff origin).mp heuclideanConnected
  exact real_complSingleton_not_connected (e origin) hrealConnected

