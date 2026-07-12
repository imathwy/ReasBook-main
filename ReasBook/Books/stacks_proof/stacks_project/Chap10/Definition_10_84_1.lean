import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Ordinal
open Order

universe u v w x

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Submodule

/-- A submodule is countably generated if it is spanned by a countable subset. -/
def CountablyGenerated (P : Submodule R M) : Prop :=
  ∃ s : Set M, s.Countable ∧ Submodule.span R s = P

/-- `Submodule.CountablyGenerated` means precisely that the submodule is spanned by a countable
subset. -/
theorem countablyGenerated_iff {P : Submodule R M} :
    P.CountablyGenerated ↔ ∃ s : Set M, s.Countable ∧ Submodule.span R s = P :=
  Iff.rfl

end Submodule

namespace Module

variable (R M)

/-- A module is countably generated if some countable subset spans it. -/
def CountablyGenerated : Prop :=
  (⊤ : Submodule R M).CountablyGenerated

/-- `Module.CountablyGenerated` means precisely that the module is spanned by a countable subset. -/
theorem countablyGenerated_iff :
    Module.CountablyGenerated R M ↔
      ∃ s : Set M, s.Countable ∧ Submodule.span R s = (⊤ : Submodule R M) :=
  Iff.rfl

/-- An `R`-module is a direct sum of countably generated submodules. -/
def IsDirectSumOfCountablyGenerated : Prop :=
  ∃ (ι : Type x) (_ : DecidableEq ι) (summand : ι → Submodule R M),
    DirectSum.IsInternal summand ∧ ∀ i, (summand i).CountablyGenerated

/-- `Module.IsDirectSumOfCountablyGenerated` records an internal direct-sum decomposition by
countably generated submodules. -/
theorem isDirectSumOfCountablyGenerated_iff :
    Module.IsDirectSumOfCountablyGenerated.{u, v, x} R M ↔
      ∃ (ι : Type x) (summand : ι → Submodule R M),
        iSupIndep summand ∧ iSup summand = ⊤ ∧ ∀ i, (summand i).CountablyGenerated := by
  constructor
  · rintro ⟨ι, _, summand, hsum, hcount⟩
    show ∃ (ι : Type x) (summand : ι → Submodule R M),
      iSupIndep summand ∧ iSup summand = ⊤ ∧ ∀ i, (summand i).CountablyGenerated
    refine ⟨ι, summand, ?_⟩
    rcases (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp hsum with
      ⟨hindep, htop⟩
    exact ⟨hindep, htop, hcount⟩
  · rintro ⟨ι, summand, hindep, htop, hcount⟩
    classical
    show Module.IsDirectSumOfCountablyGenerated.{u, v, x} R M
    refine ⟨ι, inferInstance, summand, ?_, hcount⟩
    exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨hindep, htop⟩

end Module

/-- Definition 10.84.1: a direct sum dévissage of an `R`-module `M` is an ordinal-indexed
increasing family of submodules starting at `0`, exhausting `M`, continuous at limit ordinals,
and such that each successor stage is a direct summand of the next stage. -/
@[stacks 058U]
structure DirectSumDevissage (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    where
  length : Ordinal.{w}
  length_pos : 0 < length
  stages : Ordinal.{w} →o Submodule R M
  stage_zero : stages 0 = ⊥
  iSup_stages : (⨆ α : Set.Iio length, stages α.1) = ⊤
  stage_limit :
    ∀ {α : Ordinal.{w}}, α < length → IsSuccLimit α → stages α = ⨆ β : Set.Iio α, stages β.1
  stage_succ_isCompl :
    ∀ {α : Ordinal.{w}}, α + 1 < length →
      ∃ q : Submodule R (stages (α + 1)),
        IsCompl ((stages α).comap (stages (α + 1)).subtype) q

namespace DirectSumDevissage

variable (D : DirectSumDevissage R M)

/-- The stage family of a direct sum dévissage is increasing. -/
theorem monotone_stages : Monotone D.stages :=
  D.stages.monotone

/-- The predecessor stage, viewed as a submodule of the corresponding successor stage. -/
abbrev predecessorStage (α : Ordinal.{w}) :
    Submodule R (D.stages (α + 1)) :=
  (D.stages α).comap (D.stages (α + 1)).subtype

/-- A direct sum dévissage is Kaplansky if every successor quotient is countably generated. -/
def IsKaplansky : Prop :=
  ∀ ⦃α : Ordinal.{w}⦄, α + 1 < D.length →
    Module.CountablyGenerated R (D.stages (α + 1) ⧸ D.predecessorStage α)

end DirectSumDevissage

end
