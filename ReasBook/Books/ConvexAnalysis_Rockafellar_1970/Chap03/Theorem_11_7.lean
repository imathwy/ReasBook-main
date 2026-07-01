import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_9
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_0_2

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*} {E : Type*} {Y : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 11.7 says that when two nonempty subsets admit a proper separating
  hyperplane and at least one of them is a cone, one can choose such a hyperplane to pass through
  the origin.
- `core/canonical`: the owner abstractions are the chapter predicate `Set.IsCone 𝕜` on subsets
  and the affine-subspace separation predicate `AffineSubspace.SeparatesProperly`.
- `bridge/view`: the textbook phrase "passes through the origin" is represented by the canonical
  owner-membership statement `0 ∈ H`.
- Domain-style sampling used here: the project declaration `Set.IsCone 𝕜` from Definition 2.5.9,
  its owner lemma `Set.IsCone.smul_mem`, `AffineSubspace.SeparatesProperly` and its symmetry
  theorem from Text 11.0.2, and mathlib's `AffineSubspace` owner API.
- Primitive data vs derived API: the primitive inputs are the two sets, their nonemptiness, the
  existence of a proper separator, and a one-sided cone hypothesis on one chosen set.
- Layer target: `source-facing`, stated directly in terms of the canonical affine-subspace owner
  instead of repackaging the hyperplane data.
- Ambient refinement: the public statement uses only the existing cone predicate, the proper-
  separation owner relation, and origin membership in the separator. The one-sided core is
  therefore canonically stated on arbitrary pairing spaces over ordered fields. The symmetric
  theorem below is then stated at the same ordered-field layer via
  `AffineSubspace.SeparatesProperly.symm`.
-/
/-- The one-sided core of Theorem 11.7: when the second set is a cone, a proper separating
hyperplane may be chosen through the origin. The full symmetric theorem below is derived from this
core case using `AffineSubspace.SeparatesProperly.symm`. -/
theorem exists_separatesProperly_through_origin_of_isCone_right
    {C1 C2 : Set E} (hC1_nonempty : C1.Nonempty) (hC2_nonempty : C2.Nonempty)
    (hC2_cone : Set.IsCone 𝕜 C2)
    (hsep : ∃ H : AffineSubspace 𝕜 E, (H separatesProperly[Y] C1 and C2)) :
    ∃ H : AffineSubspace 𝕜 E, (H separatesProperly[Y] C1 and C2) ∧ 0 ∈ H := by
  rcases hsep with ⟨H, hH⟩
  rcases hH.separates with ⟨b, β, hb, rfl, hC1_le, hC2_ge⟩
  have hC2_upper : ∀ x ∈ C2, (⟪x, (-1 : 𝕜) • b⟫ₚ : 𝕜) ≤ -β := by
    intro x hx
    have hx_ge : β ≤ (⟪x, b⟫ₚ : 𝕜) := mem_closedHalfSpaceGE_iff.mp (hC2_ge hx)
    have hneg : (⟪x, (-1 : 𝕜) • b⟫ₚ : 𝕜) = -⟪x, b⟫ₚ := by
      simp [HasLinearPairing.pairing_eq_pairingLinear]
    rw [hneg]
    linarith
  have hC2_bdd : BddAbove ((fun x : E ↦ (⟪x, (-1 : 𝕜) • b⟫ₚ : 𝕜)) '' C2) := by
    refine ⟨-β, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hC2_upper x hx
  have hβ_nonpos : β ≤ 0 := by
    have hnegβ_nonneg : 0 ≤ -β :=
      Set.IsCone.pairing_upperBound_nonneg_of_nonempty hC2_cone hC2_nonempty hC2_upper
    linarith
  have hC1_le_zero : C1 ⊆ closedHalfSpaceLE b (0 : 𝕜) := by
    intro x hx
    rw [mem_closedHalfSpaceLE_iff]
    exact le_trans (mem_closedHalfSpaceLE_iff.mp (hC1_le hx)) hβ_nonpos
  have hC2_ge_zero : C2 ⊆ closedHalfSpaceGE b (0 : 𝕜) := by
    intro x hx
    rw [mem_closedHalfSpaceGE_iff]
    have hx_nonpos : (⟪x, (-1 : 𝕜) • b⟫ₚ : 𝕜) ≤ 0 :=
      Set.IsCone.pairing_nonpos_of_bddAbove hC2_cone hC2_bdd x hx
    have hneg : (⟪x, (-1 : 𝕜) • b⟫ₚ : 𝕜) = -⟪x, b⟫ₚ := by
      simp [HasLinearPairing.pairing_eq_pairingLinear]
    rw [hneg] at hx_nonpos
    linarith
  refine ⟨affineHyperplane b (0 : 𝕜), ?_, ?_⟩
  · refine ⟨⟨b, 0, hb, rfl, hC1_le_zero, hC2_ge_zero⟩, ?_⟩
    intro hboth
    rcases hC1_nonempty with ⟨x1, hx1⟩
    have hβ_nonneg : 0 ≤ β := by
      have hx1H : x1 ∈ (affineHyperplane b (0 : 𝕜) : AffineSubspace 𝕜 E) := hboth.1 hx1
      have hx1_eq : (⟪x1, b⟫ₚ : 𝕜) = 0 := by
        simpa [mem_affineHyperplane_iff] using hx1H
      have hx1_le : (⟪x1, b⟫ₚ : 𝕜) ≤ β := mem_closedHalfSpaceLE_iff.mp (hC1_le hx1)
      linarith
    have hβ_zero : β = 0 := by linarith
    have h_aff : (affineHyperplane b (0 : 𝕜) : AffineSubspace 𝕜 E) = affineHyperplane b β := by
      simp [hβ_zero]
    exact hH.not_both_subset <| by simpa [h_aff] using hboth
  · simp

end

section

open scoped Rockafellar

variable {𝕜 : Type*} {E : Type*} {Y : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜]

/-- Theorem 11.7, stated in the canonical ambient form: if nonempty sets `C1` and `C2` admit a
proper separating hyperplane and at least one of them is a cone, then they admit a proper
separating hyperplane which passes through the origin. -/
-- Proof sketch: by symmetry, reduce to the case that `C2` is a cone. If
-- `affineHyperplane b β` separates `C1` and `C2` properly, conic closure of `C2` forces
-- `C2 ⊆ closedHalfSpaceGE b 0` and hence `β ≤ 0`; therefore `C1 ⊆ closedHalfSpaceLE b 0`. The
-- homogeneous hyperplane `affineHyperplane b 0` still separates the two sets. If both sets lay in
-- that new hyperplane, nonemptiness of `C1` would force `β ≥ 0`, hence `β = 0`, contradicting
-- properness of the original separator.
theorem exists_separatesProperly_through_origin_of_one_isCone
    {C1 C2 : Set E} (hC1_nonempty : C1.Nonempty) (hC2_nonempty : C2.Nonempty)
    (hcone : Set.IsCone 𝕜 C1 ∨ Set.IsCone 𝕜 C2)
    (hsep : ∃ H : AffineSubspace 𝕜 E, (H separatesProperly[Y] C1 and C2)) :
    ∃ H : AffineSubspace 𝕜 E, (H separatesProperly[Y] C1 and C2) ∧ 0 ∈ H := by
  rcases hcone with hC1_cone | hC2_cone
  · have hsep' : ∃ H : AffineSubspace 𝕜 E, (H separatesProperly[Y] C2 and C1) := by
      rcases hsep with ⟨H, hH⟩
      exact ⟨H, hH.symm⟩
    rcases
        exists_separatesProperly_through_origin_of_isCone_right
          hC2_nonempty hC1_nonempty hC1_cone hsep'
      with
      ⟨H, hH, h0H⟩
    exact ⟨H, hH.symm, h0H⟩
  · exact
      exists_separatesProperly_through_origin_of_isCone_right
        hC1_nonempty hC2_nonempty hC2_cone hsep

end
