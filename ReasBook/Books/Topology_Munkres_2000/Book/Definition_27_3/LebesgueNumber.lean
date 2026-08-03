module

public import Mathlib.Topology.MetricSpace.Bounded

public section

universe u

/-- A positive real number is a Lebesgue number for a family of sets when every
bounded nonempty set of smaller diameter is contained in a member of the family. -/
def IsLebesgueNumber {X : Type u} [PseudoMetricSpace X]
    (𝒜 : Set (Set X)) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ B : Set X, B.Nonempty → Bornology.IsBounded B →
    Metric.diam B < δ → ∃ U ∈ 𝒜, B ⊆ U

/-- The defining conditions for a Lebesgue number. -/
theorem isLebesgueNumber_iff {X : Type u} [PseudoMetricSpace X]
    {𝒜 : Set (Set X)} {δ : ℝ} :
    IsLebesgueNumber 𝒜 δ ↔
      0 < δ ∧ ∀ B : Set X, B.Nonempty → Bornology.IsBounded B →
        Metric.diam B < δ → ∃ U ∈ 𝒜, B ⊆ U :=
  Iff.rfl

namespace IsLebesgueNumber

/-- A Lebesgue number is positive. -/
theorem pos {X : Type u} [PseudoMetricSpace X] {𝒜 : Set (Set X)} {δ : ℝ}
    (hδ : IsLebesgueNumber 𝒜 δ) : 0 < δ :=
  hδ.1

/-- Every bounded nonempty set of diameter smaller than a Lebesgue number lies
in a member of the family. -/
theorem exists_superset {X : Type u} [PseudoMetricSpace X]
    {𝒜 : Set (Set X)} {δ : ℝ} (hδ : IsLebesgueNumber 𝒜 δ)
    {B : Set X} (hB_nonempty : B.Nonempty)
    (hB_bounded : Bornology.IsBounded B)
    (hB : Metric.diam B < δ) : ∃ U ∈ 𝒜, B ⊆ U :=
  hδ.2 B hB_nonempty hB_bounded hB

/-- A Lebesgue number remains one after enlarging the family of available sets. -/
theorem mono {X : Type u} [PseudoMetricSpace X]
    {𝒜 𝒜' : Set (Set X)} {δ : ℝ} (hδ : IsLebesgueNumber 𝒜 δ)
    (h𝒜 : 𝒜 ⊆ 𝒜') : IsLebesgueNumber 𝒜' δ :=
  ⟨hδ.pos, fun B hB_nonempty hB_bounded hB ↦ by
    obtain ⟨U, hU, hBU⟩ := hδ.exists_superset hB_nonempty hB_bounded hB
    exact ⟨U, h𝒜 hU, hBU⟩⟩

end IsLebesgueNumber
