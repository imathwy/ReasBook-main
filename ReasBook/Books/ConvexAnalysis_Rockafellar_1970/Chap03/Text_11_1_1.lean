import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_0_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_1_3
import ConvexAnalysis_Rockafellar_1970.Chap02.HyperbolaEpigraph
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_0_2

-- Declarations for this item will be appended below by the statement pipeline.

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
