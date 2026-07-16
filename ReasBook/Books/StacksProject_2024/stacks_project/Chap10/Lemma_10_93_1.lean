import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_84_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_88_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Module

/-
Source/core/bridge triage:
* source-facing: Lemma `10.93.1`, the projectivity criterion for countably generated flat
  Mittag-Leffler modules.
* core/canonical owners: `Module.CountablyGenerated` from `Definition_10_84_1` and
  `Module.MittagLeffler` from `Definition_10_88_7`.
* bridge/view: the local finite-to-countably-generated theorem below.
-/
section

variable (R : Type u) (M : Type v)
variable [Ring R] [AddCommGroup M] [Module R M]

/-- A finite module is countably generated. -/
theorem countablyGenerated_of_finite [Module.Finite R M] :
    CountablyGenerated R M := sorry

end

section

variable {R : Type u} {M : Type v}
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [Flat R M] [MittagLeffler R M]

-- Proof sketch: apply Lazard's theorem to write `M` as a filtered colimit of finite free modules,
-- use the countable-generation hypothesis and the Mittag-Leffler condition to replace this by a
-- countable directed subsystem, and then apply the exactness of inverse limits for countable
-- Mittag-Leffler systems to show that `Hom_R(M, -)` preserves short exact sequences.
/-- Lemma 10.93.1: if an `R`-module `M` is flat, Mittag-Leffler, and countably generated, then
`M` is projective. -/
theorem projective_of_flat_of_mittagLeffler_of_countablyGenerated
    (hcg : CountablyGenerated R M) :
    Projective R M := sorry

end

end Module
