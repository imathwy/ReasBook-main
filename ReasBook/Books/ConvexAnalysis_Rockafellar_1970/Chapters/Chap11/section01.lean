import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_11_1_1 (from Chap03) -/
section

open scoped Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

local notation "R2" => Fin 2 → 𝕜
local notation "e₁" => (Pi.single (0 : Fin 2) (1 : 𝕜) : R2)
local notation "e₂" => (Pi.single (1 : Fin 2) (1 : 𝕜) : R2)
local notation "Hepi" => (hyperbolaEpigraph : Set (𝕜 × 𝕜))
/-- The standard coordinate equivalence between the coordinate model `R2` and `𝕜 × 𝕜`. -/
noncomputable def coords : R2 ≃ₗ[𝕜] 𝕜 × 𝕜 :=
  LinearEquiv.finTwoArrow 𝕜 𝕜

/-
Source/core/bridge triage:
- `source-facing`: this text gives a concrete `𝕜²` example (hence in particular `ℝ²`) showing
  that proper separation allows
  one of the two sets to lie in the separating hyperplane.
- `core/canonical`: the owner abstractions are `AffineSubspace 𝕜 R2`, the Chapter 11 relations
  `AffineSubspace.Separates` and `AffineSubspace.SeparatesProperly`, the Chapter 2 owner
  `hyperbolaEpigraph : Set (𝕜 × 𝕜)`, the coordinate bridge `coords`, the concrete hyperplane
  constructor `affineHyperplane`, and the standard predicates `Convex 𝕜`, `IsClosed`, and
  `Disjoint`.
- `bridge/view`: the textbook left-hand set in `R2` is only the pullback
  `coords ⁻¹' hyperbolaEpigraph`; this file keeps that transport as a bridge expression rather
  than introducing a second owner for the same Chapter 2 set.
- Domain-style sampling used here: `hyperbolaEpigraph`, `mem_hyperbolaEpigraph_iff`,
  `AffineSubspace.SeparatesProperly`, `affineHyperplane`, and `mem_affineHyperplane_iff`.
- Primitive data vs derived API: the only new source-facing primitive datum here is the concrete
  ray `nonnegativeXAxisRay`; the x-axis itself is reused directly as the owner
  `affineHyperplane e₂ 0`, while membership rewrites, convexity, closedness, disjointness,
  nonemptiness, and separation are derived theorem-level API.
- Layer target: `source-facing`, as a concrete example rather than an existential wrapper.
-/

omit [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
/-- Membership in the `R2` pullback of `hyperbolaEpigraph` is exactly the defining inequalities
`ξ₁ > 0` and `ξ₂ ≥ ξ₁⁻¹`. -/
@[simp] theorem mem_coords_preimage_hyperbolaEpigraph_iff {ξ : R2} :
    ξ ∈ coords ⁻¹' Hepi ↔ 0 < ξ 0 ∧ ξ 1 ≥ (ξ 0)⁻¹ :=
  by
    simpa [coords] using
      (show (ξ 0, ξ 1) ∈ Hepi ↔ 0 < ξ 0 ∧ (ξ 0)⁻¹ ≤ ξ 1 from
        mem_hyperbolaEpigraph_iff)

variable (𝕜) in
/-- The x-axis in `R2`, represented canonically as the affine hyperplane `ξ₂ = 0`. -/
noncomputable def xAxis : AffineSubspace 𝕜 R2 :=
  affineHyperplane e₂ (0 : 𝕜)

variable (𝕜) in
omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
/-- Membership in `xAxis` is exactly the coordinate equation `ξ₂ = 0`. -/
@[simp] theorem mem_xAxis_iff {ξ : R2} :
    ξ ∈ (xAxis 𝕜 : Set R2) ↔ ξ 1 = 0 := by
  change ξ ∈ ((affineHyperplane e₂ (0 : 𝕜) : AffineSubspace 𝕜 R2) : Set R2) ↔ ξ 1 = 0
  have hpair : (HasLinearPairing.pairingLinear ξ) e₂ = ξ 1 := by
    change ξ ⬝ᵥ (Pi.single (1 : Fin 2) (1 : 𝕜)) = ξ 1
    simp
  constructor
  · intro h
    have hmem : HasPairing.pairing ξ e₂ = (0 : 𝕜) :=
      (mem_affineHyperplane_iff (b := e₂) (x := ξ) (β := (0 : 𝕜))).1 h
    simpa [hpair] using hmem
  · intro h
    have hmem : HasPairing.pairing ξ e₂ = (0 : 𝕜) := by
      simpa [hpair] using h
    exact (mem_affineHyperplane_iff (b := e₂) (x := ξ) (β := (0 : 𝕜))).2 hmem

variable (𝕜) in
/-- The set `{(ξ₁, 0) | ξ₁ ≥ 0}` from Rockafellar's separation example. -/
def nonnegativeXAxisRay : Set R2 :=
  (xAxis 𝕜 : Set R2) ∩ closedHalfSpaceGE e₁ (0 : 𝕜)

omit [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
/-- Membership in `nonnegativeXAxisRay` is exactly the defining conditions `ξ₁ ≥ 0` and
`ξ₂ = 0`. -/
@[simp] theorem mem_nonnegativeXAxisRay_iff {ξ : R2} :
    ξ ∈ nonnegativeXAxisRay 𝕜 ↔ 0 ≤ ξ 0 ∧ ξ 1 = 0 := by
  rw [nonnegativeXAxisRay, Set.mem_inter_iff]
  have hpair : (HasLinearPairing.pairingLinear ξ) e₁ = ξ 0 := by
    change ξ ⬝ᵥ (Pi.single (0 : Fin 2) (1 : 𝕜)) = ξ 0
    simp
  constructor
  · intro h
    refine ⟨?_, mem_xAxis_iff.mp h.1⟩
    exact by
      simpa [hpair] using (mem_closedHalfSpaceGE_iff.mp h.2)
  · intro h
    refine ⟨mem_xAxis_iff.mpr h.2, ?_⟩
    exact mem_closedHalfSpaceGE_iff.mpr <| by
      simpa [hpair] using h.1

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
/-- The `R2` pullback of `hyperbolaEpigraph` is convex. -/
-- Proof sketch: transport the Chapter 2 convexity statement for `hyperbolaEpigraph` across the
-- coordinate equivalence `coords`.
theorem coords_preimage_hyperbolaEpigraph_convex :
    Convex 𝕜 (coords ⁻¹' Hepi) := by
  simpa [coords] using
    Convex.linear_preimage hyperbolaEpigraph_convex coords.toLinearMap

/-- The `R2` pullback of `hyperbolaEpigraph` is closed. -/
-- Proof sketch: transport the Chapter 2 closedness statement for `hyperbolaEpigraph` across the
-- coordinate equivalence `coords`.
theorem isClosed_coords_preimage_hyperbolaEpigraph :
    IsClosed (coords ⁻¹' Hepi) := by
  have hcoords_cont : Continuous (fun ξ : R2 ↦ (ξ 0, ξ 1)) := by
    exact (continuous_apply (0 : Fin 2)).prodMk (continuous_apply (1 : Fin 2))
  simpa [coords] using
    hyperbolaEpigraph_isClosed.preimage hcoords_cont

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
/-- The `R2` pullback of `hyperbolaEpigraph` is nonempty. -/
theorem coords_preimage_hyperbolaEpigraph_nonempty :
    (coords ⁻¹' Hepi).Nonempty := by
  refine ⟨e₁ + e₂, ?_⟩
  rw [mem_coords_preimage_hyperbolaEpigraph_iff]
  norm_num

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
/-- The nonnegative part of the x-axis is convex. -/
-- Proof sketch: it is the intersection of the affine hyperplane `affineHyperplane e₂ 0` with the
-- closed half-space `ξ₁ ≥ 0`, hence is convex.
theorem nonnegativeXAxisRay_convex :
    Convex 𝕜 (nonnegativeXAxisRay 𝕜) := by
  simpa [nonnegativeXAxisRay] using
    (xAxis 𝕜).convex.inter
      (closedHalfSpaceGE_convex e₁ (0 : 𝕜))

omit [IsStrictOrderedRing 𝕜] in
/-- The nonnegative x-axis ray is closed. -/
-- Proof sketch: rewrite as `{ξ | 0 ≤ ξ 0 ∧ ξ 1 = 0}`, then intersect a closed inequality set and
-- a closed coordinate-fiber.
theorem isClosed_nonnegativeXAxisRay :
    IsClosed (nonnegativeXAxisRay 𝕜) := by
  have hrepr : nonnegativeXAxisRay 𝕜 = {ξ : R2 | 0 ≤ ξ 0 ∧ ξ 1 = 0} := by
    ext ξ
    simp [mem_nonnegativeXAxisRay_iff]
  rw [hrepr]
  exact
    (isClosed_le continuous_const (continuous_apply (0 : Fin 2))).inter
      (isClosed_eq (continuous_apply (1 : Fin 2)) continuous_const)

omit [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
/-- The nonnegative x-axis ray is nonempty. -/
theorem nonnegativeXAxisRay_nonempty : (nonnegativeXAxisRay 𝕜).Nonempty := by
  exact ⟨0, by simp⟩

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
/-- The two concrete example sets are disjoint. -/
-- Proof sketch: any point of `nonnegativeXAxisRay` has second coordinate `0`, whereas any point
-- of `coords ⁻¹' hyperbolaEpigraph` has positive first coordinate and thus second coordinate at
-- least `(ξ₁)⁻¹ > 0`.
theorem coords_preimage_hyperbolaEpigraph_disjoint_nonnegativeXAxisRay :
    Disjoint (coords ⁻¹' Hepi) (nonnegativeXAxisRay 𝕜) := by
  rw [Set.disjoint_left]
  intro ξ hξ1 hξ2
  rcases mem_coords_preimage_hyperbolaEpigraph_iff.mp hξ1 with ⟨hξ0, hξ1_ge⟩
  rcases mem_nonnegativeXAxisRay_iff.mp hξ2 with ⟨_, hξ1_zero⟩
  have hξ1_pos : 0 < ξ 1 := lt_of_lt_of_le (by positivity) hξ1_ge
  exact hξ1_pos.ne' hξ1_zero

omit [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
/-- The nonnegative x-axis ray is contained in the x-axis hyperplane. -/
-- Proof sketch: points of `nonnegativeXAxisRay` satisfy `ξ 1 = 0`, and
-- `mem_xAxis_iff` identifies membership in `affineHyperplane e₂ 0` with the same coordinate
-- equation.
theorem nonnegativeXAxisRay_subset_xAxis :
    nonnegativeXAxisRay 𝕜 ⊆ (xAxis 𝕜 : Set R2) := by
  intro ξ hξ
  exact hξ.1

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
/-- The x-axis properly separates the two concrete example sets. -/
-- Proof sketch: use the second standard basis vector as normal and `β = 0`. The set
-- `nonnegativeXAxisRay` lies in the closed half-space `0 ≤ ξ₂`, while every point of
-- `coords ⁻¹' hyperbolaEpigraph` satisfies `ξ₂ ≥ ξ₁⁻¹ > 0`, so the two sets lie in opposite
-- closed half-spaces and the first set is not contained in the hyperplane.
theorem xAxis_separatesProperly_coords_preimage_hyperbolaEpigraph_nonnegativeXAxisRay :
    (xAxis 𝕜) separatesProperly[R2] (coords ⁻¹' Hepi) and (nonnegativeXAxisRay 𝕜) := by
  rw [AffineSubspace.separatesProperly_symm]
  refine ⟨?_, ?_⟩
  · refine ⟨e₂, 0, ?_, ?_, ?_, ?_⟩
    · intro hzero
      have hzero_eval :
          ((HasLinearPairing.pairingLinear.flip (R := 𝕜) e₂ : R2 →ₗ[𝕜] 𝕜) e₂) = 0 :=
        congrArg (fun f : R2 →ₗ[𝕜] 𝕜 => f e₂) hzero
      have hself :
          ((HasLinearPairing.pairingLinear.flip (R := 𝕜) e₂ : R2 →ₗ[𝕜] 𝕜) e₂) = (1 : 𝕜) := by
        change e₂ ⬝ᵥ (Pi.single (1 : Fin 2) (1 : 𝕜)) = (1 : 𝕜)
        simp
      have hone_eq_zero : (1 : 𝕜) = 0 := by
        calc
          (1 : 𝕜) =
              ((HasLinearPairing.pairingLinear.flip (R := 𝕜) e₂ : R2 →ₗ[𝕜] 𝕜) e₂) :=
            hself.symm
          _ = 0 := hzero_eval
      exact one_ne_zero hone_eq_zero
    · rfl
    · intro ξ hξ
      rw [mem_closedHalfSpaceLE_iff]
      rcases mem_nonnegativeXAxisRay_iff.mp hξ with ⟨_, hξ1_zero⟩
      have hpair : HasPairing.pairing ξ e₂ = ξ 1 := by
        change ξ ⬝ᵥ (Pi.single (1 : Fin 2) (1 : 𝕜)) = ξ 1
        simp
      rw [hpair]
      exact hξ1_zero.le
    · intro ξ hξ
      rw [mem_closedHalfSpaceGE_iff]
      rcases mem_coords_preimage_hyperbolaEpigraph_iff.mp hξ with ⟨hξ0, hξ1_ge⟩
      have hpair : HasPairing.pairing ξ e₂ = ξ 1 := by
        change ξ ⬝ᵥ (Pi.single (1 : Fin 2) (1 : 𝕜)) = ξ 1
        simp
      rw [hpair]
      exact le_trans (by positivity) hξ1_ge
  · intro hsubset
    have hpoint : e₁ + e₂ ∈ coords ⁻¹' Hepi := by
      rw [mem_coords_preimage_hyperbolaEpigraph_iff]
      norm_num
    have hxAxis : e₁ + e₂ ∈ (xAxis 𝕜 : Set R2) := hsubset.2 hpoint
    have : ((e₁ + e₂ : R2) 1) = 0 := mem_xAxis_iff.mp hxAxis
    norm_num at this

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
/- Text 11.1.1: for the concrete sets `{(ξ₁, ξ₂) | ξ₁ > 0, ξ₂ ≥ ξ₁⁻¹}` and
`{(ξ₁, 0) | ξ₁ ≥ 0}` in `𝕜²` (hence in `ℝ²`), the x-axis properly separates them while containing
the second set, showing that proper separation allows one of the sets to lie in the separating
hyperplane itself. -/
-- Proof sketch: combine
-- `xAxis_separatesProperly_coords_preimage_hyperbolaEpigraph_nonnegativeXAxisRay` with
-- `nonnegativeXAxisRay_subset_xAxis`.
theorem proper_separation_allows_nonnegativeXAxisRay_in_xAxis :
    (xAxis 𝕜) separatesProperly[R2] (coords ⁻¹' Hepi) and (nonnegativeXAxisRay 𝕜) ∧
      nonnegativeXAxisRay 𝕜 ⊆ (xAxis 𝕜 : Set R2) := by
  exact
    ⟨xAxis_separatesProperly_coords_preimage_hyperbolaEpigraph_nonnegativeXAxisRay,
      nonnegativeXAxisRay_subset_xAxis⟩

end

/-! ### Theorem_11_1 (from Chap03) -/
noncomputable section

open scoped Rockafellar

section ProperSeparation

variable {𝕜 : Type*} [CommRing 𝕜] [ConditionallyCompletePartialOrder 𝕜]
variable {X : Type*} [AddCommGroup X] [Module 𝕜 X]
variable {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable {C1 C2 : Set X}

-- The support-function side uses the same primal/dual pairing data as separation, viewed in the
-- opposite orientation and lifted to `WithTopBot`.
local instance instHasPairingDualPrimalWithTopBot : HasPairing Y X (WithTopBot 𝕜) :=
  HasPairing.swap (X := X) (Y := Y) (L := WithTopBot 𝕜)
local notation3:max "δᵛ(" x " | " C ")" => supportFunction (L := WithTopBot 𝕜) C x

/-
Source/core/bridge triage:
- `source-facing`: Theorem 11.1 gives infimum-supremum criteria for proper and strong hyperplane
  separation of two nonempty sets.
- `core/canonical`: the chapter owner abstractions are `AffineSubspace.SeparatesProperly` and
  `AffineSubspace.StronglySeparates`, together with the project owner `supportFunction`.
- `bridge/view`: the textbook projected supremum is the owner value `δᵛ(b | C)`, and
  the projected infimum is its canonical dual `-δᵛ(-b | C)`.
- Domain-style sampling used here: the project declarations `AffineSubspace.SeparatesProperly`,
  `AffineSubspace.StronglySeparates`, and `supportFunction`.
- Primitive data vs derived API: the primitive inputs are the two sets and their nonemptiness; the
  existence of a proper or strong separating hyperplane and the support-function gap conditions are
  theorem-level content.
- Layer target: `source-facing`, stated with the chapter's existing separation owners and a thin
  bridge to the textbook infimum/supremum formulas through the existing support-function owner.
  It is stated on arbitrary pairing spaces over a commutative ring. Since no inner-product-specific
  operation enters these owner statements, and the support-function side only needs the
  extended-order codomain `WithTopBot 𝕜`, the theorem is refined to that canonical pairing
  layer rather than a concrete coordinate model.
-/

/-- Theorem 11.1 (1), stated in the chapter's canonical ambient form: for nonempty sets `C1` and
`C2` in a primal/dual pairing over `𝕜`, a hyperplane separates `C1` and `C2` properly if and only
if there is a dual vector `b` such that the projected infimum on `C1` dominates the projected
supremum on `C2`, while the projected supremum on `C1` strictly exceeds the projected infimum on
`C2`.
Written through the owner notation `δᵛ(· | ·)` in codomain `WithTopBot 𝕜`, this is the source
support-function infimum/supremum criterion. -/
-- Proof sketch: if `H` separates properly, unpack `H.SeparatesProperly C1 C2` into one nonzero
-- equation `⟪x, b⟫ = β` and opposite closed-half-space containments. Those containments force the
-- support-function dual `-δᵛ(-b | C1)` to dominate `δᵛ(b | C2)`, and properness gives strict
-- inequality between `δᵛ(b | C1)` and the dual value `-δᵛ(-b | C2)`. Conversely, choose `β`
-- between these two projected ranges. Condition (b) ensures that not both sets lie in the
-- resulting hyperplane, so `affineHyperplane b β` separates properly.
theorem exists_hyperplane_separating_properly_iff_supportFunction_conditions
    (hC1_nonempty : C1.Nonempty) (hC2_nonempty : C2.Nonempty) :
    (∃ H : AffineSubspace 𝕜 X, H.SeparatesProperly Y C1 C2) ↔
      ∃ b : Y,
        (-δᵛ(-b | C1) ≥ δᵛ(b | C2)) ∧
          (δᵛ(b | C1) > -δᵛ(-b | C2)) := sorry

end ProperSeparation

section StrongSeparation

variable {𝕜 : Type*} [CommRing 𝕜] [ConditionallyCompletePartialOrder 𝕜]
variable {X : Type*} [PseudoMetricSpace X] [AddCommGroup X] [Module 𝕜 X]
variable {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable {C1 C2 : Set X}

-- The support-function side uses the same primal/dual pairing data as separation, viewed in the
-- opposite orientation and lifted to `WithTopBot`.
local instance instHasPairingDualPrimalWithTopBotStrong : HasPairing Y X (WithTopBot 𝕜) :=
  HasPairing.swap (X := X) (Y := Y) (L := WithTopBot 𝕜)
local notation3:max "δᵛ(" x " | " C ")" => supportFunction (L := WithTopBot 𝕜) C x

/-- Theorem 11.1 (2), stated in the chapter's canonical ambient form: for nonempty sets `C1` and
`C2` in a primal/dual pairing pseudometric space over `𝕜`, a hyperplane separates `C1` and `C2`
strongly if and only if there is a dual vector `b` whose projected infimum on `C1` lies strictly
above the projected supremum on `C2`, i.e. Rockafellar's condition (c). Written through the owner
notation `δᵛ(· | ·)`, this is the textbook strict support-function infimum/supremum inequality.
-/
-- Proof sketch: strong separation provides one hyperplane `⟪x, b⟫ = β` and a positive margin
-- `δ`, so every point of `C1` has projection at least `β + δ` while every point of `C2` has
-- projection at most `β - δ`, yielding `-δᵛ(-b | C1) > δᵛ(b | C2)`. Conversely, if such a gap
-- exists, choose `β` strictly between these two extrema and then choose `ε > 0` small enough
-- that the `ε`-thickenings of `C1` and `C2` still stay in opposite open half-spaces, which gives
-- `H.StronglySeparates Y C1 C2`.
theorem exists_hyperplane_separating_strongly_iff_supportFunction_condition
    (hC1_nonempty : C1.Nonempty) (hC2_nonempty : C2.Nonempty) :
    (∃ H : AffineSubspace 𝕜 X, H.StronglySeparates Y C1 C2) ↔
      ∃ b : Y,
        (-δᵛ(-b | C1) > δᵛ(b | C2)) := sorry

end StrongSeparation

end

/-! ### Text_11_1_2 (from Chap03) -/
section

open scoped Pointwise Rockafellar

local notation "R2" => Fin 2 → ℝ
local notation "e₁" => (Pi.single (0 : Fin 2) (1 : ℝ) : R2)
local notation "e₂" => (Pi.single (1 : Fin 2) (1 : ℝ) : R2)
local notation "C₁" => (coords ⁻¹' hyperbolaEpigraph)
local notation "C₂" => (nonnegativeXAxisRay ℝ)
/-
Source/core/bridge triage:
- `source-facing`: Text 11.1.2 upgrades Rockafellar's concrete `R²` example to show that strong
  separation can fail even for disjoint closed convex sets.
- `core/canonical`: the owner abstractions are `IsClosed`, `Convex ℝ`, `Disjoint`,
  `AffineSubspace.StronglySeparates`, and the closure criterion from Theorem 11.4.
- `bridge/view`: the left-hand witness set is reused only as the coordinate pullback
  `coords ⁻¹' hyperbolaEpigraph` of the Chapter 2 owner `hyperbolaEpigraph`; this file does not
  introduce a second owner for that bridge.
- Primitive data vs derived API: the concrete subsets of `R²` are reused from Text 11.1.1 and
  Chapter 2; this file contributes only the new closure-of-difference and
  failure-of-strong-separation facts.
- Domain-style sampling used here: the project declarations `hyperbolaEpigraph`,
  `coords_preimage_hyperbolaEpigraph_convex`, `nonnegativeXAxisRay`, and
  `exists_hyperplane_strongly_separating_iff_zero_notMem_closure_sub`.
- Layer target: `source-facing`, reusing the earlier chapter-level witness sets as the concrete
  counterexample to universal strong separation.
-/

/-- The difference set of the Text 11.1.1 witness pair accumulates at the origin. -/
-- Proof sketch: for each large `t > 0`, the points `![t, t⁻¹] ∈ coords ⁻¹' hyperbolaEpigraph`
-- and `![t, 0] ∈ nonnegativeXAxisRay` differ by `![0, t⁻¹]`, and these differences converge to
-- `0` as `t → +∞`.
theorem zero_mem_closure_sub_witness_pair :
    (0 : R2) ∈ closure (C₁ - C₂) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨(ε / 2) • e₂, ?_, ?_⟩
  · refine Set.mem_sub.mpr ?_
    refine ⟨(2 / ε) • e₁ + (ε / 2) • e₂, ?_, (2 / ε) • e₁, ?_, ?_⟩
    · rw [mem_coords_preimage_hyperbolaEpigraph_iff]
      have hx0 : (((2 / ε) • e₁ + (ε / 2) • e₂ : R2) 0) = 2 / ε := by
        simp
      have hx1 : (((2 / ε) • e₁ + (ε / 2) • e₂ : R2) 1) = ε / 2 := by
        simp
      constructor
      · simpa [hx0] using (show 0 < 2 / ε by positivity)
      · have h_inv : ((2 / ε : ℝ)⁻¹) = ε / 2 := by
          field_simp [hε.ne']
        simp [hx0, hx1, h_inv]
    · rw [mem_nonnegativeXAxisRay_iff]
      have hy0 : (((2 / ε) • e₁ : R2) 0) = 2 / ε := by
        simp
      have hy1 : (((2 / ε) • e₁ : R2) 1) = 0 := by
        simp
      constructor
      · simpa [hy0] using (show 0 ≤ 2 / ε by positivity)
      · simp [hy1]
    · ext i
      fin_cases i
      · simp
      · simp
  · have he₂_norm : ‖(e₂ : R2)‖ = 1 := by
      have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
        ext i
        fin_cases i <;> simp
      rw [Pi.norm_def, huniv, Finset.sup_insert, Finset.sup_singleton]
      norm_num
    have hdist : dist (0 : R2) ((ε / 2) • e₂) = ‖ε / 2‖ := by
      calc
        dist (0 : R2) ((ε / 2) • e₂) = ‖(ε / 2) • e₂‖ := by
          simp [dist_eq_norm]
        _ = ‖ε / 2‖ * ‖(e₂ : R2)‖ := by
          rw [norm_smul]
        _ = ‖ε / 2‖ := by
          simp [he₂_norm]
    have habs : ‖ε / 2‖ = ε / 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      positivity
    rw [hdist, habs]
    linarith

/-- The Text 11.1.1 witness pair admits no strongly separating hyperplane in any pairing
codomain `Y` over `R2`. -/
-- Proof sketch: points `![t, t⁻¹]` in the left-hand set and `![t, 0]` in the right-hand set have
-- distance `t⁻¹`, which tends to `0` as `t → +∞`. Thus `(0 : R2)` lies in the closure of the
-- difference set, so Theorem 11.4's closure criterion rules out strong separation.
variable {Y : Type*}
variable [AddCommMonoid Y] [Module ℝ Y] [HasLinearPairing R2 Y ℝ]

theorem witness_pair_not_strongly_separated :
    ¬ ∃ H : AffineSubspace ℝ R2, H stronglySeparates[Y] C₁ and C₂ := by
  rw [exists_hyperplane_strongly_separating_iff_zero_notMem_closure_sub
    (Y := Y)
    coords_preimage_hyperbolaEpigraph_convex
    coords_preimage_hyperbolaEpigraph_nonempty
    nonnegativeXAxisRay_convex
    nonnegativeXAxisRay_nonempty]
  simpa using zero_mem_closure_sub_witness_pair

/-- Text 11.1.2 in witness form: there exist nonempty disjoint closed convex sets in `R²` that
admit no strongly separating hyperplane in pairing codomain `Y`; a concrete witness pair is `C₁`
and `C₂`. -/
theorem exists_disjoint_closed_convex_sets_not_strongly_separated :
    ∃ C1 C2 : Set R2,
      (IsClosed C1 ∧ Convex ℝ C1 ∧ C1.Nonempty) ∧
      (IsClosed C2 ∧ Convex ℝ C2 ∧ C2.Nonempty) ∧
      Disjoint C1 C2 ∧
      ¬ ∃ H : AffineSubspace ℝ R2, H stronglySeparates[Y] C1 and C2 := by
  refine ⟨C₁, C₂,
    ⟨isClosed_coords_preimage_hyperbolaEpigraph,
      coords_preimage_hyperbolaEpigraph_convex,
      coords_preimage_hyperbolaEpigraph_nonempty⟩,
    ⟨isClosed_nonnegativeXAxisRay,
      nonnegativeXAxisRay_convex,
      nonnegativeXAxisRay_nonempty⟩,
    coords_preimage_hyperbolaEpigraph_disjoint_nonnegativeXAxisRay,
    witness_pair_not_strongly_separated⟩

/-- Text 11.1.2: not every pair of nonempty disjoint closed convex sets in `R²` admits a strongly
separating hyperplane in pairing codomain `Y`; the concrete witness pair is
`coords ⁻¹' hyperbolaEpigraph` and `nonnegativeXAxisRay` from Text 11.1.1. -/
-- Proof sketch: if every disjoint closed convex pair in `R²` admitted strong separation, apply
-- that universal statement to the two explicit counterexample sets and combine the resulting
-- separator with the preceding closedness, convexity, disjointness, and non-separation lemmas.
theorem not_all_disjoint_closed_convex_sets_admit_strong_separation :
    ¬ ∀ C1 C2 : Set R2,
      (IsClosed C1 ∧ Convex ℝ C1 ∧ C1.Nonempty) →
      (IsClosed C2 ∧ Convex ℝ C2 ∧ C2.Nonempty) →
      Disjoint C1 C2 →
      ∃ H : AffineSubspace ℝ R2, H stronglySeparates[Y] C1 and C2 := by
  intro hall
  rcases exists_disjoint_closed_convex_sets_not_strongly_separated with
    ⟨C1, C2, hC1, hC2, hdisj,
      hnot⟩
  exact hnot (hall C1 C2 hC1 hC2 hdisj)

end
