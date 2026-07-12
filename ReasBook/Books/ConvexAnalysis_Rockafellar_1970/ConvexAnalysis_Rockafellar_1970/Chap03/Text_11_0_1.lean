import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_0_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

universe u u𝕜

section

variable {𝕜 : Type u𝕜} {V : Type u}
variable [CommRing 𝕜] [Preorder 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-
Source/core/bridge triage:
- `source-facing`: Text 11.0.1 introduces the relation that a hyperplane separates two sets in
  `ℝ^n`.
- `core/canonical`: the owner abstractions are `AffineSubspace 𝕜 V`, the concrete hyperplane
  presentation `affineHyperplane b β`, and the associated oriented closed half-spaces
  `closedHalfSpaceLE b β` and `closedHalfSpaceGE b β`.
- `bridge/view`: the Chapter 1 predicate `H.HasNormal b` is the companion bridge for expressing
  that `b` is normal to `H`, while the separation relation itself is stated directly in terms of
  one nontrivial pairing-normal hyperplane equation `H = affineHyperplane b β` and one fixed
  half-space orientation. Swapping the sets is derived by negating both the normal and the level.
- Domain-style sampling used here: the project declarations `AffineSubspace.HasNormal`,
  `affineHyperplane`, `affineHyperplane_eq_iff`, `AffineSubspace.is_hyperplane`,
  `closedHalfSpaceLE`, and `closedHalfSpaceGE`.
- Primitive data vs derived API: the primitive owner data is the affine subspace `H` together
  with one nontrivial pairing-functional hyperplane equation and one oriented pair of half-space
  containments; the opposite orientation is derived by negation, and the normal-vector and
  hyperplane predicates are derived API.
- Layer target: `source-facing`, as the Chapter 11 owner relation for ordinary hyperplane
  separation.
- The source-level nonemptiness assumptions on `C1` and `C2` are ambient setup rather than part
  of the separation relation itself, so they are not baked into the definition.
- Ambient refinement: although the source states separation in `R^n`, the owner objects
  `AffineSubspace`, `affineHyperplane`, and the half-space declarations already live at the
  pairing level, so the separation relation should not be pinned to inner-product self-pairings.
  Finite dimensionality is needed only for the derived theorem that a separating affine subspace
  is a hyperplane.
-/

namespace AffineSubspace

variable {Y : Type*}
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]
variable {H : AffineSubspace 𝕜 V} {C1 C2 : Set V}

/-- Text 11.0.1 at the pairing owner layer: an affine subspace `H` separates `C1` and `C2` when
`H` is one nontrivial pairing hyperplane `affineHyperplane b β`, `C1` lies in the closed
half-space `⟪x, b⟫ₚ ≤ β`, and `C2` lies in the opposite closed half-space
`β ≤ ⟪x, b⟫ₚ`. The primitive nondegeneracy side condition is that the induced scalar-valued
functional `HasLinearPairing.pairingLinear.flip b` is nonzero. -/
def Separates (Y : Type*) [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]
    (H : AffineSubspace 𝕜 V) (C1 C2 : Set V) : Prop :=
  ∃ b : Y, ∃ β : 𝕜,
    HasLinearPairing.pairingLinear.flip b ≠ (0 : V →ₗ[𝕜] 𝕜) ∧
    H = affineHyperplane b β ∧
    C1 ⊆ closedHalfSpaceLE b β ∧ C2 ⊆ closedHalfSpaceGE b β

/-- A separating affine subspace comes with a normal vector in the sense of Text 1.7. -/
theorem Separates.hasNormal (h : H.Separates Y C1 C2) :
    ∃ b : Y, b ⟂ₕ H := by
  rcases h with ⟨b, β, hb, hH, _⟩
  exact ⟨b, β, hb, hH⟩

end AffineSubspace

end

section

variable {𝕜 : Type u𝕜} {V : Type u}
variable [Field 𝕜] [Preorder 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

namespace AffineSubspace

variable {Y : Type*}
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]
variable {H : AffineSubspace 𝕜 V} {C1 C2 : Set V}

/-- A separating affine subspace is a hyperplane. -/
theorem Separates.is_hyperplane [FiniteDimensional 𝕜 V]
    (h : H.Separates Y C1 C2) :
    H.is_hyperplane := by
  rcases h.hasNormal with ⟨b, hb⟩
  exact hb.is_hyperplane

end AffineSubspace

end

section

variable {𝕜 : Type u𝕜} {V : Type u}
variable [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

namespace AffineSubspace

variable {Y : Type*}
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]
variable {H : AffineSubspace 𝕜 V} {C1 C2 : Set V}

omit [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜] in
private theorem affineHyperplane_neg_smul (b : Y) (β : 𝕜) :
    (affineHyperplane ((-1 : 𝕜) • b) (-β) : AffineSubspace 𝕜 V) = affineHyperplane b β := by
  ext x
  rw [mem_affineHyperplane_iff, mem_affineHyperplane_iff]
  simp [HasLinearPairing.pairing_eq_pairingLinear]

private theorem separates_swap (h : H.Separates Y C1 C2) :
    H.Separates Y C2 C1 := by
  rcases h with ⟨b, β, hb, hH, hC1, hC2⟩
  refine ⟨(-1 : 𝕜) • b, -β, by simpa using hb, ?_, ?_, ?_⟩
  · rw [hH, affineHyperplane_neg_smul]
  · intro x hx
    rw [mem_closedHalfSpaceLE_iff]
    simpa [HasLinearPairing.pairing_eq_pairingLinear] using
      (neg_le_neg (mem_closedHalfSpaceGE_iff.mp (hC2 hx)))
  · intro x hx
    rw [mem_closedHalfSpaceGE_iff]
    simpa [HasLinearPairing.pairing_eq_pairingLinear] using
      (neg_le_neg (mem_closedHalfSpaceLE_iff.mp (hC1 hx)))

/-- Hyperplane separation is symmetric in the two sets being separated. -/
-- Proof sketch: if `H = affineHyperplane b β` separates `C1` from `C2`, then the same hyperplane
-- also has the equation `H = affineHyperplane ((-1 : 𝕜) • b) (-β)`. This swaps the two half-space
-- containments by multiplying the normal by `-1` and negating the level.
theorem separates_symm :
    H.Separates Y C1 C2 ↔ H.Separates Y C2 C1 := by
  exact ⟨separates_swap, separates_swap⟩

alias ⟨Separates.symm, _⟩ := separates_symm

end AffineSubspace

end
