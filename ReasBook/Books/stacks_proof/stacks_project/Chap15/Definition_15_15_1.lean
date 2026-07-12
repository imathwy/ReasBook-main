import Mathlib
import StacksProject_2024.Chap10.Definition_10_59_1
import StacksProject_2024.Chap10.Lemma_10_66_6

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable (R : Type u) [CommRing R]

/- Domain triage: this item is `source-facing` in commutative algebra. The primitive owner data are
the canonical local-ring predicate `IsLocalRing R` and the pointwise weak-association predicate
`Ideal.IsWeaklyAssociatedToModule R R (maximalIdeal R)`. The class below is just the textbook
bundle of those two existing notions, not a replacement owner. -/
/-- Definition 15.15.1: a commutative ring `R` is auto-associated if it is local and its maximal
ideal is weakly associated to `R` as an `R`-module. -/
@[stacks 05GM]
class IsAutoAssociatedRing : Prop extends IsLocalRing R where
  /-- The maximal ideal of an auto-associated ring is weakly associated to the regular module. -/
  maximalIdeal_weaklyAssociated :
    Ideal.IsWeaklyAssociatedToModule R R (maximalIdeal R)

variable {R}

/-- For a local ring, being auto-associated is exactly weak association of the maximal ideal to the
regular module. -/
theorem isAutoAssociatedRing_iff [IsLocalRing R] :
    IsAutoAssociatedRing R ↔ Ideal.IsWeaklyAssociatedToModule R R (maximalIdeal R) := by
  constructor
  · exact fun h ↦ h.maximalIdeal_weaklyAssociated
  · exact fun h ↦
      { toIsLocalRing := inferInstance
        maximalIdeal_weaklyAssociated := h }

namespace IsAutoAssociatedRing

/-- In an auto-associated ring, some torsion ideal `Ann_R(x)` is an ideal of definition. -/
theorem exists_torsionOf_isIdealOfDefinition [IsAutoAssociatedRing R] :
    ∃ x : R, (Ideal.torsionOf R R x).IsIdealOfDefinition := by
  obtain ⟨x, hx⟩ :
      ∃ x : R, maximalIdeal R ∈ (Ideal.torsionOf R R x).minimalPrimes :=
    IsAutoAssociatedRing.maximalIdeal_weaklyAssociated
  refine ⟨x, ?_⟩
  let J : Ideal R := Ideal.torsionOf R R x
  have hJminimal : J.minimalPrimes = {maximalIdeal R} := by
    ext q
    constructor
    · intro hq
      have hq_le : q ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hq.1.1.ne_top
      exact Set.mem_singleton_iff.mpr <| le_antisymm hq_le (hx.2 hq.1 hq_le)
    · rintro rfl
      simpa [J] using hx
  rw [Ideal.isIdealOfDefinition_iff_isMaximal_radical, IsLocalRing.isMaximal_iff]
  rw [← Ideal.sInf_minimalPrimes, hJminimal, sInf_singleton]

end IsAutoAssociatedRing

end

section

variable (R : Type u) [Field R]

-- Proof sketch: a field is a local ring with maximal ideal `(0)`. The ideal `(0)` is associated
-- to the regular module via `1`, hence weakly associated by
-- `Ideal.IsAssociatedToModule.isWeaklyAssociatedToModule`.
/-- Fields are auto-associated rings. -/
instance : IsAutoAssociatedRing R where
  toIsLocalRing := Field.instIsLocalRing R
  maximalIdeal_weaklyAssociated := by
    rw [maximalIdeal_eq_bot]
    exact
      (show Ideal.IsAssociatedToModule R R (⊥ : Ideal R) from by
        rw [Ideal.isAssociatedToModule_iff_exists_torsionOf]
        refine ⟨Ideal.isPrime_bot, (1 : R), ?_⟩
        ext a
        rw [Ideal.mem_torsionOf_iff, Ideal.mem_bot]
        simp).isWeaklyAssociatedToModule

end
