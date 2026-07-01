import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_3_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_7

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*} {V : Type*}
variable [CommRing 𝕜] [LE 𝕜]
variable [TopologicalSpace V]
variable [AddCommGroup V] [Module 𝕜 V]

/-
Source/core/bridge triage:
- `source-facing`: Text 11.3.2 defines what it means for a hyperplane to support a set `C`.
- `core/canonical`: the owner layer uses `AffineSubspace` and `AffineSubspace.affineHyperplane`
  for hyperplanes and the supporting-half-space owner `s supports C`.
- `bridge/view`: the textbook's first sentence is the source-facing owner definition; the concrete
  closed-half-space presentation is a theorem-level bridge in normed ordered scalar settings.
- Primitive data vs derived API: the primitive owner input is the affine subspace `H`; being a
  supporting hyperplane is a derived `Prop` on `H` and `C`, obtained from one supporting half-space.
- Topology-language choice: this owner keeps the ambient boundary operator `frontier` on purpose.
  The supported object is an ambient half-space `s : Set V`, so boundary contact is ambient by
  construction; intrinsic/relative restatements are theorem-level views downstream.
-/

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 V} {C : Set V}

/-- Text 11.3.2: an affine subspace `H` is a supporting hyperplane to `C` when its underlying set
is the boundary of some supporting half-space to `C`. -/
def IsSupportingHyperplane (Y : Type*) [AddCommMonoid Y] [Module 𝕜 Y]
    [HasLinearPairing V Y 𝕜] (H : AffineSubspace 𝕜 V) (C : Set V) : Prop :=
  ∃ s : Set V, (s supports[Y,𝕜] C) ∧ frontier s = H

/-- Textbook-facing notation for "supporting hyperplane". -/
scoped[Rockafellar] notation:50 H " supportsHyperplane[" Y "] " C =>
  AffineSubspace.IsSupportingHyperplane Y H C

end AffineSubspace

end

section

open scoped Rockafellar
open Set

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
local notation:50 s " supports " C =>
  s supports[Y,𝕜] C

private theorem frontier_closedHalfSpaceLE_eq_affineHyperplane
    {b : Y} {β : 𝕜}
    (hb : (HasLinearPairing.pairingLinear.flip b : E →ₗ[𝕜] 𝕜) ≠ 0) :
    frontier (closedHalfSpaceLE b β : Set E) =
      ((affineHyperplane b β : AffineSubspace 𝕜 E) : Set E) := by
  let f : E →ₗ[𝕜] 𝕜 := HasLinearPairing.pairingLinear.flip b
  let fCL : E →L[𝕜] 𝕜 := ⟨f, by
    simpa [f] using
      (HasContinuousPairing.continuous_pairing_left (X := E) (Y := Y) (𝕜 := 𝕜) b)⟩
  have hcont : Continuous f := by
    simpa [f] using
      (HasContinuousPairing.continuous_pairing_left (X := E) (Y := Y) (𝕜 := 𝕜) b)
  have hfCL : fCL ≠ 0 := by
    intro h0
    apply hb
    ext x
    exact congrArg (fun g : E →L[𝕜] 𝕜 => g x) h0
  have hopen : IsOpenMap f := by
    simpa [f, fCL] using (fCL.isOpenMap_of_ne_zero hfCL)
  have hpre : (closedHalfSpaceLE b β : Set E) = f ⁻¹' Set.Iic β := by
    ext x
    simp [f, closedHalfSpaceLE]
  calc
    frontier (closedHalfSpaceLE b β : Set E)
        = frontier (f ⁻¹' Set.Iic β) := by simp [hpre]
    _ = f ⁻¹' frontier (Set.Iic β : Set 𝕜) :=
      (hopen.preimage_frontier_eq_frontier_preimage hcont _).symm
    _ = f ⁻¹' ({β} : Set 𝕜) := by simp
    _ = ((affineHyperplane b β : AffineSubspace 𝕜 E) : Set E) := by
      ext x
      simp [f, mem_affineHyperplane_iff]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [HasContinuousPairing E Y 𝕜] [OrderTopology 𝕜] in
private theorem closedHalfSpaceGE_eq_closedHalfSpaceLE_neg (b : Y) (β : 𝕜) :
    (closedHalfSpaceGE b β : Set E) = closedHalfSpaceLE (((-1 : 𝕜) • b) : Y) (-β) := by
  ext x
  constructor
  · intro hx
    have hx_ge : β ≤ ⟪x, b⟫ₚ := mem_closedHalfSpaceGE_iff.mp hx
    have hx_le : ⟪x, (((-1 : 𝕜) • b) : Y)⟫ₚ ≤ -β := by
      simpa using (neg_le_neg hx_ge)
    exact mem_closedHalfSpaceLE_iff.mpr hx_le
  · intro hx
    have hx_le : ⟪x, (((-1 : 𝕜) • b) : Y)⟫ₚ ≤ -β :=
      mem_closedHalfSpaceLE_iff.mp hx
    have hx_ge : β ≤ ⟪x, b⟫ₚ := by
      exact neg_le_neg_iff.mp (by simpa using hx_le)
    exact mem_closedHalfSpaceGE_iff.mpr hx_ge

/-- A supporting hyperplane is exactly the affine hyperplane bounding some supporting closed
half-space for `C`, cut out by a nontrivial pairing functional. -/
theorem isSupportingHyperplane_iff :
    (H supportsHyperplane[Y] C) ↔
      ∃ b : Y, ∃ β : 𝕜, H = affineHyperplane b β ∧
        (HasLinearPairing.pairingLinear.flip b : E →ₗ[𝕜] 𝕜) ≠ 0 ∧
        (closedHalfSpaceLE b β supports C) := by
  constructor
  · rintro ⟨s, hs, hfrontier⟩
    rcases hs.isClosedHalfSpace with ⟨b, β, hb, hle | hge⟩
    · rcases hle with rfl
      have hset : (H : Set E) = ((affineHyperplane b β : AffineSubspace 𝕜 E) : Set E) := by
        calc
          (H : Set E) = frontier (closedHalfSpaceLE b β : Set E) := by
            simpa using hfrontier.symm
          _ = ((affineHyperplane b β : AffineSubspace 𝕜 E) : Set E) :=
            frontier_closedHalfSpaceLE_eq_affineHyperplane hb
      have hH : H = affineHyperplane b β := by
        ext x
        simpa using congrArg (fun t : Set E => x ∈ t) hset
      exact ⟨b, β, hH, hb, by simpa using hs⟩
    · rcases hge with rfl
      have hbneg : (HasLinearPairing.pairingLinear.flip (((-1 : 𝕜) • b) : Y) : E →ₗ[𝕜] 𝕜) ≠ 0 := by
        simpa using hb
      have hfrontier' :
          frontier (closedHalfSpaceLE (((-1 : 𝕜) • b) : Y) (-β) : Set E) = (H : Set E) := by
        simpa [closedHalfSpaceGE_eq_closedHalfSpaceLE_neg] using hfrontier
      have hset :
          (H : Set E) =
            ((affineHyperplane (((-1 : 𝕜) • b) : Y) (-β) : AffineSubspace 𝕜 E) : Set E) := by
        calc
          (H : Set E) = frontier (closedHalfSpaceLE (((-1 : 𝕜) • b) : Y) (-β) : Set E) := by
            simpa using hfrontier'.symm
          _ = ((affineHyperplane (((-1 : 𝕜) • b) : Y) (-β) : AffineSubspace 𝕜 E) : Set E) :=
            frontier_closedHalfSpaceLE_eq_affineHyperplane hbneg
      have hH : H = affineHyperplane (((-1 : 𝕜) • b) : Y) (-β) := by
        ext x
        simpa using congrArg (fun t : Set E => x ∈ t) hset
      refine ⟨(((-1 : 𝕜) • b) : Y), -β, hH, hbneg, ?_⟩
      simpa [closedHalfSpaceGE_eq_closedHalfSpaceLE_neg] using hs
  · rintro ⟨b, β, hH, hb, hs⟩
    refine ⟨closedHalfSpaceLE b β, hs, ?_⟩
    have hfrontier : frontier (closedHalfSpaceLE b β : Set E) =
        ((affineHyperplane b β : AffineSubspace 𝕜 E) : Set E) :=
      frontier_closedHalfSpaceLE_eq_affineHyperplane hb
    simpa [hH] using hfrontier

/-- A supporting hyperplane comes with a nontrivial pairing normal in the Chapter 1 sense. -/
theorem IsSupportingHyperplane.hasNormal (h : H supportsHyperplane[Y] C) :
    ∃ b : Y, H.HasNormal b := by
  rcases isSupportingHyperplane_iff.mp h with ⟨b, β, hH, hb, _hs⟩
  exact ⟨b, ⟨β, hb, hH⟩⟩

/-- A supporting hyperplane is a hyperplane. -/
theorem IsSupportingHyperplane.is_hyperplane [FiniteDimensional 𝕜 E]
    (h : H supportsHyperplane[Y] C) :
    H.is_hyperplane := by
  rcases h.hasNormal with ⟨b, hb⟩
  exact hb.is_hyperplane

end AffineSubspace

end
