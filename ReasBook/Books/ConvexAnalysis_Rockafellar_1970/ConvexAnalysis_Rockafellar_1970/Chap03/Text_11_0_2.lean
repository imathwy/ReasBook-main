import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_0_1

-- Declarations for this item will be appended below by the statement pipeline.

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
