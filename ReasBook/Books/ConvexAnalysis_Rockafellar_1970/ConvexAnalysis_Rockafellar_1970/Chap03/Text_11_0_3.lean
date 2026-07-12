import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_0_4

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} {V : Type*}
variable [CommRing 𝕜] [Preorder 𝕜]
variable [PseudoMetricSpace V] [AddCommGroup V] [Module 𝕜 V]

/-
Source/core/bridge triage:
- `source-facing`: Text 11.0.3 strengthens Text 11.0.1 by defining when a hyperplane separates
  `C1` and `C2` strongly.
- `core/canonical`: the owner abstraction is the existing strict-separation relation
  `AffineSubspace.StrictlySeparates` from Text 11.0.4.
- `bridge/view`: the textbook thickening `Ci + ε B` is represented by the pointwise set sum
  `Ci + ε • B`, so strong separation is strict separation of these positive ball thickenings.
- Primitive data vs derived API: the primitive owner inputs are the pairing codomain `Y` and the
  affine subspace `H`; strong separation is a derived `Prop` obtained from `StrictlySeparates`
  after introducing the positive thickening parameter `ε`.
- Domain-style sampling used here: the chapter owners `AffineSubspace.StrictlySeparates`,
  `AffineSubspace.StrictlySeparates.mono`,
  `AffineSubspace.strictlySeparates_iff_separates_and_disjoint`,
  and `AffineSubspace.Separates`, together with the chapter unit-ball notation `B` from Text 6.3.
- Layer target: `source-facing`, preserving Rockafellar's stronger notion while reusing the
  existing hyperplane owner relation instead of re-encoding its witness data.
- Ambient refinement: the unit-ball thickening needs only the metric layer, and strict separation
  is now owned at the ordered-ring pairing layer from Text 11.0.4, so this owner should match
  that pairing-plus-metric ambient API rather than a concrete real/inner-product model.
-/

namespace AffineSubspace

variable {Y : Type*}
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]
variable {H : AffineSubspace 𝕜 V} {C1 C2 : Set V}

/-- Text 11.0.3: an affine subspace `H` strongly separates `C1` and `C2` when there exists
`ε > 0` such that the thickenings `C1 + ε • B` and `C2 + ε • B`, where `B` is the chapter unit
ball, are strictly separated by `H` in the sense of Text 11.0.4. -/
def StronglySeparates (Y : Type*) [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]
    (H : AffineSubspace 𝕜 V) (C1 C2 : Set V) : Prop :=
  ∃ ε : 𝕜, 0 < ε ∧ H.StrictlySeparates Y (C1 + ε • B) (C2 + ε • B)

/-- Textbook-facing notation for strong hyperplane separation. -/
scoped[Rockafellar] notation:50 H " stronglySeparates[" Y "] " C1 " and " C2 =>
  AffineSubspace.StronglySeparates Y H C1 C2

/-- Strong separation implies strict separation of the original sets. -/
-- Proof sketch: if `H` strictly separates positive thickenings of `C1` and `C2`, then `0 ∈ B`
-- shows `C1 ⊆ C1 + ε • B` and `C2 ⊆ C2 + ε • B`. Restrict the strict open-half-space
-- containments from the thickenings to the original sets.
theorem StronglySeparates.strictlySeparates (h : H stronglySeparates[Y] C1 and C2) :
    H.StrictlySeparates Y C1 C2 := by
  rcases h with ⟨ε, _, hεsep⟩
  have hzeroB : (0 : V) ∈ B := Metric.mem_closedBall_self zero_le_one
  have subset_thickening (C : Set V) : C ⊆ C + ε • B := by
    intro x hx
    exact Set.mem_add.2 ⟨x, hx, 0, Set.zero_mem_smul_set hzeroB, by simp⟩
  exact hεsep.mono (subset_thickening C1) (subset_thickening C2)

/-- Strong separation is monotone under shrinking either of the two sets. -/
theorem StronglySeparates.mono {D1 D2 : Set V}
    (h : H stronglySeparates[Y] D1 and D2)
    (hC1 : C1 ⊆ D1) (hC2 : C2 ⊆ D2) :
    H stronglySeparates[Y] C1 and C2 := by
  rcases h with ⟨ε, hε, hsep⟩
  exact
    ⟨ε, hε,
      hsep.mono (Set.add_subset_add hC1 subset_rfl) (Set.add_subset_add hC2 subset_rfl)⟩

end AffineSubspace

end

section

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} {V : Type*}
variable [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [PseudoMetricSpace V] [AddCommGroup V] [Module 𝕜 V]
variable {Y : Type*}
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 V} {C1 C2 : Set V}

/-- Strong separation is symmetric in the two sets being separated. -/
-- Proof sketch: keep the same thickening radius `ε`; rewrite strict separation as ordinary
-- separation plus disjointness of both sets from `H`, swap the separation term using
-- `AffineSubspace.Separates.symm`, and swap the two disjointness clauses.
theorem stronglySeparates_symm :
    (H stronglySeparates[Y] C1 and C2) ↔ (H stronglySeparates[Y] C2 and C1) := by
  have strictlySeparates_swap {A1 A2 : Set V}
      (h : H.StrictlySeparates (Y := Y) A1 A2) :
      H.StrictlySeparates (Y := Y) A2 A1 := by
    rcases
      (strictlySeparates_iff_separates_and_disjoint (Y := Y) (H := H) (C1 := A1) (C2 := A2)).mp h
      with ⟨hsep, hA1, hA2⟩
    exact
      (strictlySeparates_iff_separates_and_disjoint (Y := Y) (H := H) (C1 := A2) (C2 := A1)).mpr
        ⟨hsep.symm, hA2, hA1⟩
  constructor <;> rintro ⟨ε, hε, hsep⟩ <;> exact ⟨ε, hε, strictlySeparates_swap hsep⟩

alias ⟨StronglySeparates.symm, _⟩ := stronglySeparates_symm

end AffineSubspace

end
