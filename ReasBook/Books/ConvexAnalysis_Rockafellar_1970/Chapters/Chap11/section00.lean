import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_11_0_1 (from Chap03) -/
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

/-! ### Text_11_0_2 (from Chap03) -/
open scoped Rockafellar

section

variable {𝕜 : Type*} {V : Type*} {Y : Type*}
variable [CommRing 𝕜] [Preorder 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]

/- 
Source/core/bridge triage:
- `source-facing`: Text 11.0.2 adds the textbook refinement that a separating hyperplane is
  proper when it does not contain both sets being separated.
- `core/canonical`: the owner abstractions are `AffineSubspace 𝕜 V`, the chapter relation
  `AffineSubspace.Separates`, and its inherited hyperplane API from Text 11.0.1.
- `bridge/view`: the textbook phrase "separates properly" is the ordinary owner relation
  `H.Separates C1 C2` together with the extra one-sided noncontainment clause saying that at least
  one of the two sets is not contained in `H`.
- Domain-style sampling used here: mathlib's `AffineSubspace`, its `SetLike` coercion, and the
  chapter owner declarations `AffineSubspace.Separates`, `AffineSubspace.Separates.hasNormal`,
  and `AffineSubspace.Separates.is_hyperplane`.
- Primitive data vs derived API: the primitive owner data is still the affine subspace `H`;
  proper separation is a derived `Prop` on `H`, `C1`, and `C2` whose primitive strengthening is
  the symmetric condition that `H` does not contain both sets at once, while ordinary separation,
  the one-sided textbook noncontainment disjunction, and hyperplanehood are derived API inherited
  from `H.Separates C1 C2`.
- Layer target: `source-facing`, as a direct strengthening of the imported Chapter 11 owner
  relation `AffineSubspace.Separates`.
- Ambient refinement: as in Text 11.0.1, although the source is stated in `R^n`, this owner
  strengthening uses only the existing separation relation and set containment in `H`, so it is
  canonically stated on arbitrary pairing spaces rather than a fixed Euclidean model.
-/

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 V} {C1 C2 : Set V}

/-- Text 11.0.2: a hyperplane separates `C1` and `C2` properly when it separates them and at
least one of the two sets is not contained in the hyperplane itself. This is equivalent to saying
that the two sets are not both contained in the hyperplane. -/
def SeparatesProperly (Y : Type*) [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]
    (H : AffineSubspace 𝕜 V) (C1 C2 : Set V) : Prop :=
  H.Separates Y C1 C2 ∧ ¬ (C1 ⊆ H ∧ C2 ⊆ H)

/-- Textbook-facing notation for proper hyperplane separation. -/
scoped[Rockafellar] notation:50 H " separatesProperly[" Y "] " C1 " and " C2 =>
  AffineSubspace.SeparatesProperly Y H C1 C2

/-- Proper separation includes ordinary separation. -/
theorem SeparatesProperly.separates
    (h : H separatesProperly[Y] C1 and C2) :
    H.Separates Y C1 C2 :=
  h.1

/-- In a proper separation, the hyperplane does not contain both sets simultaneously. -/
theorem SeparatesProperly.not_both_subset
    (h : H separatesProperly[Y] C1 and C2) :
    ¬ (C1 ⊆ H ∧ C2 ⊆ H) :=
  h.2

/-- In a proper separation, at least one of the two sets is not contained in the hyperplane. -/
theorem SeparatesProperly.not_subset_left_or_right
    (h : H separatesProperly[Y] C1 and C2) :
    ¬ C1 ⊆ H ∨ ¬ C2 ⊆ H := by
  classical
  by_cases hC1 : C1 ⊆ H
  · right
    intro hC2
    exact h.not_both_subset ⟨hC1, hC2⟩
  · exact Or.inl hC1

/-- Proper separation is equivalent to ordinary separation plus one-sided noncontainment. -/
theorem separatesProperly_iff_separates_and_not_subset_left_or_right :
    (H separatesProperly[Y] C1 and C2) ↔
      H.Separates Y C1 C2 ∧ (¬ C1 ⊆ H ∨ ¬ C2 ⊆ H) := by
  constructor
  · intro h
    exact ⟨h.separates, h.not_subset_left_or_right⟩
  · rintro ⟨hsep, hnot⟩
    refine ⟨hsep, ?_⟩
    intro hboth
    rcases hnot with hC1 | hC2
    · exact hC1 hboth.1
    · exact hC2 hboth.2

end AffineSubspace

end

section

variable {𝕜 : Type*} {V : Type*} {Y : Type*}
variable [Field 𝕜] [Preorder 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 V} {C1 C2 : Set V}

/-- A proper separator is a hyperplane. -/
theorem SeparatesProperly.is_hyperplane [FiniteDimensional 𝕜 V]
    (h : H separatesProperly[Y] C1 and C2) :
    H.is_hyperplane :=
  h.separates.is_hyperplane

end AffineSubspace

end

section

variable {𝕜 : Type*} {V : Type*} {Y : Type*}
variable [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 V} {C1 C2 : Set V}

/-- Proper hyperplane separation is symmetric in the two sets being separated. -/
-- Proof sketch: combine the symmetry of `H.Separates C1 C2` from Text 11.0.1 with the symmetric
-- noncontainment condition.
theorem separatesProperly_symm :
    (H separatesProperly[Y] C1 and C2) ↔ (H separatesProperly[Y] C2 and C1) := by
  constructor
  · intro h
    exact ⟨h.separates.symm, by simpa [and_comm] using h.not_both_subset⟩
  · intro h
    exact ⟨h.separates.symm, by simpa [and_comm] using h.not_both_subset⟩

alias ⟨SeparatesProperly.symm, _⟩ := separatesProperly_symm

end AffineSubspace

end

/-! ### Text_11_0_3 (from Chap03) -/
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

/-! ### Text_11_0_4 (from Chap03) -/
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
