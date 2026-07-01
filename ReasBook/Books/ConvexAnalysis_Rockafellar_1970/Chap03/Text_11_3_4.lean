import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_7_10
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_3_2

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*} {V : Type*}
variable [CommRing 𝕜] [LE 𝕜]
variable [TopologicalSpace V]
variable [AddCommGroup V] [Module 𝕜 V]
variable (Y : Type*)
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 V} {C : Set V}

/-- Text 11.3.4: a non-trivial supporting hyperplane to `C` is a supporting hyperplane to `C`
that does not contain `C` itself. -/
def IsNontrivialSupportingHyperplane (H : AffineSubspace 𝕜 V) (C : Set V) : Prop :=
  H.IsSupportingHyperplane Y C ∧ ¬ C ⊆ H

/-- A non-trivial supporting hyperplane is, in particular, a supporting hyperplane. -/
-- Proof sketch: this is the first conjunct in the definition of
-- `IsNontrivialSupportingHyperplane`.
theorem IsNontrivialSupportingHyperplane.isSupportingHyperplane
    (h : H.IsNontrivialSupportingHyperplane Y C) :
    H.IsSupportingHyperplane Y C :=
  h.1

/-- A non-trivial supporting hyperplane does not contain the set it supports. -/
-- Proof sketch: this is the second conjunct in the definition of
-- `IsNontrivialSupportingHyperplane`.
theorem IsNontrivialSupportingHyperplane.not_subset
    (h : H.IsNontrivialSupportingHyperplane Y C) :
    ¬ C ⊆ H :=
  h.2

end AffineSubspace

end

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E]
variable [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜] [HasContinuousPairing E Y 𝕜]

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 E} {C : Set E}

/-- A non-trivial supporting hyperplane is a hyperplane. -/
theorem IsNontrivialSupportingHyperplane.is_hyperplane [FiniteDimensional 𝕜 E]
    (h : H.IsNontrivialSupportingHyperplane Y C) :
    H.is_hyperplane :=
  h.isSupportingHyperplane.is_hyperplane

/-- A non-trivial supporting hyperplane through `x` yields a nonzero pairing normal `b` such that
the pairing functional `z ↦ ⟪z, b⟫ₚ` attains its maximum over `C` at `x` and is not constant on
`C`. -/
theorem IsNontrivialSupportingHyperplane.exists_nonzero_pairing_maximizing
    {x : E} (h : H.IsNontrivialSupportingHyperplane Y C) (hx : x ∈ H) :
    ∃ b : Y, b ≠ 0 ∧ IsMaxOn (fun z : E ↦ (⟪z, b⟫ₚ : 𝕜)) C x ∧
      ∃ y ∈ C, (⟪y, b⟫ₚ : 𝕜) < ⟪x, b⟫ₚ := by
  rcases isSupportingHyperplane_iff.mp h.isSupportingHyperplane with
      ⟨b, β, hH, hbflip, hs⟩
  have hb0 : b ≠ 0 := Set.ne_zero_of_pairingLinear_flip_ne_zero
    hbflip
  refine ⟨b, hb0, ?_⟩
  constructor
  · refine isMaxOn_iff.2 ?_
    intro y hy
    have hy_le : (⟪y, b⟫ₚ : 𝕜) ≤ β := mem_closedHalfSpaceLE_iff.mp <| hs.subset hy
    have hx_eq : (⟪x, b⟫ₚ : 𝕜) = β := by
      rw [hH] at hx
      exact mem_affineHyperplane_iff.mp hx
    have hx_eq' : β = (⟪x, b⟫ₚ : 𝕜) := hx_eq.symm
    simpa [hx_eq'] using hy_le
  · rcases Set.not_subset.mp h.not_subset with ⟨y, hyC, hy_notH⟩
    refine ⟨y, hyC, ?_⟩
    have hy_le : (⟪y, b⟫ₚ : 𝕜) ≤ β := mem_closedHalfSpaceLE_iff.mp <| hs.subset hyC
    have hy_not_aff : y ∉ ((affineHyperplane b β : AffineSubspace 𝕜 E) : Set E) := by
      simpa [hH] using hy_notH
    have hy_ne : (⟪y, b⟫ₚ : 𝕜) ≠ β := by
      intro hy_eq
      apply hy_not_aff
      exact mem_affineHyperplane_iff.mpr hy_eq
    have hy_lt_beta : (⟪y, b⟫ₚ : 𝕜) < β := lt_of_le_of_ne hy_le hy_ne
    have hx_eq : (⟪x, b⟫ₚ : 𝕜) = β := by
      rw [hH] at hx
      exact mem_affineHyperplane_iff.mp hx
    have hx_eq' : β = (⟪x, b⟫ₚ : 𝕜) := hx_eq.symm
    simpa [hx_eq'] using hy_lt_beta

/-- A non-trivial supporting hyperplane through `x` yields a linear functional that attains its
maximum over `C` at `x` and is not constant on `C`. -/
theorem IsNontrivialSupportingHyperplane.exists_nonconstant_linearMap_maximizing
    {x : E} (h : H.IsNontrivialSupportingHyperplane Y C) (hx : x ∈ H) :
    ∃ f : E →ₗ[𝕜] 𝕜, IsMaxOn f C x ∧ ∃ y ∈ C, f y < f x := by
  rcases h.exists_nonzero_pairing_maximizing hx with ⟨b, _hb0, hmax, y, hyC, hy_lt⟩
  refine ⟨HasLinearPairing.pairingLinear.flip b, ?_⟩
  constructor
  · simpa [HasLinearPairing.pairing_eq_pairingLinear] using hmax
  · exact ⟨y, hyC, by simpa [HasLinearPairing.pairing_eq_pairingLinear] using hy_lt⟩

end AffineSubspace

end

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E]
variable [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜] [HasContinuousPairing E Y 𝕜]

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 E} {C : Set E}

/-- A non-trivial supporting hyperplane through `x` yields a nonzero normal vector to `C` at `x`,
with strict inequality at some point of `C`. -/
theorem IsNontrivialSupportingHyperplane.exists_nonzero_normal_pairing_lt
    {x : E} (h : H.IsNontrivialSupportingHyperplane Y C) (hxC : x ∈ C) (hxH : x ∈ H) :
    ∃ b : Y, b ≠ 0 ∧ b ∈ N[𝕜](x | C) ∧
      ∃ y ∈ C, (⟪y, b⟫ₚ : 𝕜) < ⟪x, b⟫ₚ := by
  rcases isSupportingHyperplane_iff.mp h.isSupportingHyperplane with
      ⟨b, β, hH, hbflip, hs⟩
  have hb0 : b ≠ 0 := Set.ne_zero_of_pairingLinear_flip_ne_zero
    hbflip
  have hx_eq : (⟪x, b⟫ₚ : 𝕜) = β := by
    rw [hH] at hxH
    exact mem_affineHyperplane_iff.mp hxH
  have hnormal : b ∈ N[𝕜](x | C) := by
    rw [mem_normalCone_iff]
    refine ⟨hxC, ?_⟩
    intro y hy
    have hy_le : (⟪y, b⟫ₚ : 𝕜) ≤ β := mem_closedHalfSpaceLE_iff.mp (hs.subset hy)
    have hx_eq' : β = (⟪x, b⟫ₚ : 𝕜) := hx_eq.symm
    have hyx : (⟪y, b⟫ₚ : 𝕜) ≤ ⟪x, b⟫ₚ := by
      simpa [hx_eq'] using hy_le
    have hsub_nonneg : (0 : 𝕜) ≤ (⟪x, b⟫ₚ : 𝕜) - ⟪y, b⟫ₚ := sub_nonneg.mpr hyx
    simpa [sub_eq_add_neg, map_add, map_neg, add_assoc, add_left_comm, add_comm] using
      hsub_nonneg
  rcases Set.not_subset.mp h.not_subset with ⟨y, hyC, hy_notH⟩
  have hy_le : (⟪y, b⟫ₚ : 𝕜) ≤ β := mem_closedHalfSpaceLE_iff.mp (hs.subset hyC)
  have hy_ne : (⟪y, b⟫ₚ : 𝕜) ≠ β := by
    intro hy_eq
    apply hy_notH
    simpa [hH] using mem_affineHyperplane_iff.mpr hy_eq
  have hy_lt : (⟪y, b⟫ₚ : 𝕜) < ⟪x, b⟫ₚ := by
    have hy_lt_beta : (⟪y, b⟫ₚ : 𝕜) < β := lt_of_le_of_ne hy_le hy_ne
    have hx_eq' : β = (⟪x, b⟫ₚ : 𝕜) := hx_eq.symm
    simpa [hx_eq'] using hy_lt_beta
  exact ⟨b, hb0, hnormal, y, hyC, hy_lt⟩
end AffineSubspace

end
