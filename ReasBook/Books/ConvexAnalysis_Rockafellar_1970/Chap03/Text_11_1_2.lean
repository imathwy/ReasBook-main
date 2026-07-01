import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_1_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_11_4

-- Declarations for this item will be appended below by the statement pipeline.

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
