import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_0_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*} {V : Type*}
variable [CommRing 𝕜] [Preorder 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-
Source/core/bridge triage:
- `source-facing`: Text 11.0.4 strengthens the separation relation from Text 11.0.1 by requiring
  that neither set meet the separating hyperplane, equivalently that the two sets lie in opposite
  open half-spaces determined by that hyperplane.
- `core/canonical`: the owner abstractions are `AffineSubspace 𝕜 V`, the chapter owner relation
  `AffineSubspace.Separates`, and `Disjoint` for nonintersection with the separating hyperplane.
- `bridge/view`: the source-facing open-half-space witness for strict separation is a bridge
  theorem equivalent to the owner conjunction
  `H.Separates C1 C2 ∧ Disjoint C1 H ∧ Disjoint C2 H`.
- Domain-style sampling used here: `AffineSubspace.Separates`, `Disjoint`,
  `affineHyperplane`, `openHalfSpaceLT`, and `openHalfSpaceGT`.
- Primitive data vs derived API: strict separation reuses the primitive owner relation
  `H.Separates C1 C2` and adds the two nonintersection clauses `Disjoint C1 H` and
  `Disjoint C2 H`; the open-half-space witness is derived bridge API.
- Layer target: canonical owner-first, refining strict separation as an intrinsic strengthening of
  `AffineSubspace.Separates` instead of duplicating hyperplane witness data in a parallel owner.
- Ambient refinement: as in Text 11.0.1, the owner objects `AffineSubspace`, `affineHyperplane`,
  and the half-space declarations already live at the ordered pairing layer, so strict separation
  should not be pinned to the real scalar specialization.
-/

namespace AffineSubspace

variable {Y : Type*}
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]
variable {H : AffineSubspace 𝕜 V} {C1 C2 : Set V}

/-- Text 11.0.4 at the owner layer: strict separation is ordinary separation together with the
additional requirement that neither set meets the separating hyperplane. The source-facing
open-half-space witness presentation is provided by
`strictlySeparates_iff_exists_openHalfSpace`. -/
def StrictlySeparates (Y : Type*) [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]
    (H : AffineSubspace 𝕜 V) (C1 C2 : Set V) : Prop :=
  H.Separates Y C1 C2 ∧ Disjoint C1 H ∧ Disjoint C2 H

/-- Strict separation includes ordinary separation. -/
theorem StrictlySeparates.separates (h : H.StrictlySeparates Y C1 C2) :
    H.Separates Y C1 C2 :=
  h.1

/-- In a strict separation, the left set is disjoint from the hyperplane. -/
theorem StrictlySeparates.disjoint_left (h : H.StrictlySeparates Y C1 C2) :
    Disjoint C1 H :=
  h.2.1

/-- In a strict separation, the right set is disjoint from the hyperplane. -/
theorem StrictlySeparates.disjoint_right (h : H.StrictlySeparates Y C1 C2) :
    Disjoint C2 H :=
  h.2.2

/-- Strict separation is monotone under shrinking either of the two sets. -/
theorem StrictlySeparates.mono {D1 D2 : Set V} (h : H.StrictlySeparates Y D1 D2)
    (hC1 : C1 ⊆ D1) (hC2 : C2 ⊆ D2) :
    H.StrictlySeparates Y C1 C2 := by
  rcases h.1 with ⟨b, β, hb, hH, hD1, hD2⟩
  refine ⟨⟨b, β, hb, hH, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    exact hD1 (hC1 hx)
  · intro x hx
    exact hD2 (hC2 hx)
  · exact Set.disjoint_left.mpr fun x hxC hxH ↦ Set.disjoint_left.mp h.2.1 (hC1 hxC) hxH
  · exact Set.disjoint_left.mpr fun x hxC hxH ↦ Set.disjoint_left.mp h.2.2 (hC2 hxC) hxH

/-- Unfolding characterization of strict separation at the canonical owner layer. -/
@[simp] theorem strictlySeparates_iff_separates_and_disjoint {H : AffineSubspace 𝕜 V}
    {C1 C2 : Set V} :
    H.StrictlySeparates Y C1 C2 ↔ H.Separates Y C1 C2 ∧ Disjoint C1 H ∧ Disjoint C2 H :=
  Iff.rfl

end AffineSubspace

end

section

open scoped Rockafellar

variable {𝕜 : Type*} {V : Type*}
variable [CommRing 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

namespace AffineSubspace

variable {Y : Type*}
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]

private theorem subset_openHalfSpaceLT_of_subset_closedHalfSpaceLE_of_disjoint_affineHyperplane
    {C : Set V} {b : Y} {β : 𝕜} (hC : C ⊆ closedHalfSpaceLE b β)
    (h_disj : Disjoint C ((affineHyperplane b β : AffineSubspace 𝕜 V) : Set V)) :
    C ⊆ openHalfSpaceLT b β := by
  intro x hx
  rw [mem_openHalfSpaceLT_iff]
  have hle : ⟪x, b⟫ₚ ≤ β := mem_closedHalfSpaceLE_iff.mp <| hC hx
  have hne : ⟪x, b⟫ₚ ≠ β := by
    intro h_eq
    exact (Set.disjoint_left.mp h_disj hx) <| by
      simpa using h_eq
  exact lt_of_le_of_ne hle hne

private theorem subset_openHalfSpaceGT_of_subset_closedHalfSpaceGE_of_disjoint_affineHyperplane
    {C : Set V} {b : Y} {β : 𝕜} (hC : C ⊆ closedHalfSpaceGE b β)
    (h_disj : Disjoint C ((affineHyperplane b β : AffineSubspace 𝕜 V) : Set V)) :
    C ⊆ openHalfSpaceGT b β := by
  intro x hx
  rw [mem_openHalfSpaceGT_iff]
  have hge : β ≤ ⟪x, b⟫ₚ := mem_closedHalfSpaceGE_iff.mp <| hC hx
  have hne : β ≠ ⟪x, b⟫ₚ := by
    intro h_eq
    exact (Set.disjoint_left.mp h_disj hx) <| by
      simpa using h_eq.symm
  exact lt_of_le_of_ne hge hne

private theorem disjoint_affineHyperplane_of_subset_openHalfSpaceLT
    {C : Set V} {b : Y} {β : 𝕜} (hC : C ⊆ openHalfSpaceLT b β) :
    Disjoint C ((affineHyperplane b β : AffineSubspace 𝕜 V) : Set V) := by
  refine Set.disjoint_left.mpr fun x hxC hxH ↦ ?_
  have hlt : ⟪x, b⟫ₚ < β := mem_openHalfSpaceLT_iff.mp <| hC hxC
  have h_eq : ⟪x, b⟫ₚ = β := by
    simpa using hxH
  exact hlt.ne h_eq

private theorem disjoint_affineHyperplane_of_subset_openHalfSpaceGT
    {C : Set V} {b : Y} {β : 𝕜} (hC : C ⊆ openHalfSpaceGT b β) :
    Disjoint C ((affineHyperplane b β : AffineSubspace 𝕜 V) : Set V) := by
  refine Set.disjoint_left.mpr fun x hxC hxH ↦ ?_
  have hgt : β < ⟪x, b⟫ₚ := mem_openHalfSpaceGT_iff.mp <| hC hxC
  have h_eq : ⟪x, b⟫ₚ = β := by
    simpa using hxH
  exact hgt.ne h_eq.symm

/-- Source-facing bridge: strict separation is equivalent to one nontrivial hyperplane equation
whose induced opposite open half-spaces contain `C1` and `C2`. -/
-- Proof sketch: from the canonical owner `H.Separates C1 C2 ∧ Disjoint C1 H ∧ Disjoint C2 H`,
-- unpack the separating hyperplane witness from `H.Separates C1 C2` and upgrade closed to open
-- half-space containments using disjointness from that same hyperplane. Conversely, strict
-- containments imply the closed containments for `H.Separates C1 C2` and force disjointness from
-- the hyperplane boundary.
theorem strictlySeparates_iff_exists_openHalfSpace {H : AffineSubspace 𝕜 V} {C1 C2 : Set V} :
    H.StrictlySeparates Y C1 C2 ↔
      ∃ b : Y, ∃ β : 𝕜,
        (HasLinearPairing.pairingLinear.flip b : V →ₗ[𝕜] 𝕜) ≠ 0 ∧
        H = affineHyperplane b β ∧
        C1 ⊆ openHalfSpaceLT b β ∧ C2 ⊆ openHalfSpaceGT b β := by
  constructor
  · intro h
    rcases h with ⟨hsep, hC1_disj, hC2_disj⟩
    rcases hsep with ⟨b, β, hb, hH, hC1, hC2⟩
    refine ⟨b, β, hb, hH, ?_, ?_⟩
    · exact
        subset_openHalfSpaceLT_of_subset_closedHalfSpaceLE_of_disjoint_affineHyperplane hC1 <| by
          simpa [hH] using hC1_disj
    · exact
        subset_openHalfSpaceGT_of_subset_closedHalfSpaceGE_of_disjoint_affineHyperplane hC2 <| by
          simpa [hH] using hC2_disj
  · rintro ⟨b, β, hb, hH, hC1, hC2⟩
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨b, β, hb, hH, ?_, ?_⟩
      · intro x hx
        exact (mem_openHalfSpaceLT_iff.mp <| hC1 hx).le
      · intro x hx
        exact mem_closedHalfSpaceGE_iff.mpr <| (mem_openHalfSpaceGT_iff.mp <| hC2 hx).le
    · simpa [hH] using disjoint_affineHyperplane_of_subset_openHalfSpaceLT hC1
    · simpa [hH] using disjoint_affineHyperplane_of_subset_openHalfSpaceGT hC2

end AffineSubspace

end

section

variable {𝕜 : Type*} {V : Type*}
variable [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable {Y : Type*}
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 V} {C1 C2 : Set V}

/-- Strict separation is symmetric in the two sets being separated. -/
-- Proof sketch: use the companion characterization by ordinary separation and hyperplane
-- disjointness, then swap the two set arguments and apply the symmetry from Text 11.0.1.
theorem strictlySeparates_symm :
    H.StrictlySeparates Y C1 C2 ↔ H.StrictlySeparates Y C2 C1 := by
  constructor
  · intro h
    rcases h with ⟨hsep, hC1, hC2⟩
    exact ⟨hsep.symm, hC2, hC1⟩
  · intro h
    rcases h with ⟨hsep, hC2, hC1⟩
    exact ⟨hsep.symm, hC1, hC2⟩

alias ⟨StrictlySeparates.symm, _⟩ := strictlySeparates_symm

end AffineSubspace

end
