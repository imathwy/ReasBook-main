import Mathlib
import StacksProject_2024.Chap10.Definition_10_103_1
import StacksProject_2024.Chap10.Lemma_10_72_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

namespace Module

/-
Source/core/bridge triage:
* source-facing: `Module.MaximalCohenMacaulay R M`, the local maximal Cohen-Macaulay condition;
* core/canonical: the owner class `Module.CohenMacaulay`;
* bridge/view: `MaximalCohenMacaulay.toCohenMacaulay` and the local depth notation
  `moduleDepth R M`.

Primitive data are exactly the finiteness assumption and the source-facing equality comparing the
local depth of `M` to `ringKrullDim R`. The Cohen-Macaulay owner condition is derived API and
should be recovered through a bridge theorem/instance rather than stored as primitive public data.
-/
/-- Definition 10.103.8: a finite `R`-module over a Noetherian local ring is maximal
Cohen-Macaulay when its depth equals the Krull dimension of `R`. Since `ringKrullDim` takes
values in `WithBot ℕ∞`, the depth is compared in the same codomain via the canonical coercion
`WithTop ℕ = ℕ∞ → WithBot ℕ∞`. -/
class MaximalCohenMacaulay : Prop extends Module.Finite R M where
  depth_eq_ringKrullDim : .some (moduleDepth R M) = ringKrullDim R

namespace MaximalCohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

theorem nontrivial (h : MaximalCohenMacaulay R M) : Nontrivial M := by
  by_contra hM
  letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
  have hsmul : maximalIdeal R • (⊤ : Submodule R M) = ⊤ := by
    simpa using (Subsingleton.elim (maximalIdeal R • (⊤ : Submodule R M)) ⊤)
  have hdepth_top : moduleDepth R M = ⊤ :=
    Ideal.depth_eq_top_of_smul_top (maximalIdeal R) M hsmul
  have hdim_top : ringKrullDim R = ⊤ := by
    simpa [hdepth_top] using h.depth_eq_ringKrullDim.symm
  exact ringKrullDim_ne_top hdim_top

/-- A maximal Cohen-Macaulay module has support dimension equal to the Krull dimension of the
base ring. -/
theorem supportDim_eq_ringKrullDim (h : MaximalCohenMacaulay R M) :
    Module.supportDim R M = ringKrullDim R := by
  letI : Module.Finite R M := h.toFinite
  letI : Nontrivial M := h.nontrivial
  apply le_antisymm
  · exact Module.supportDim_le_ringKrullDim R M
  · rw [← h.depth_eq_ringKrullDim]
    exact depth_le_supportDim

/-- A maximal Cohen-Macaulay module is Cohen-Macaulay. -/
theorem toCohenMacaulay (h : MaximalCohenMacaulay R M) : Module.CohenMacaulay R M :=
  letI : Module.Finite R M := h.toFinite
  Module.CohenMacaulay.mk <| by
    calc
      Module.supportDim R M = ringKrullDim R := supportDim_eq_ringKrullDim h
      _ = .some (moduleDepth R M) := h.depth_eq_ringKrullDim.symm

end MaximalCohenMacaulay

/-- The source-facing maximal Cohen-Macaulay condition implies the chapter owner condition. -/
instance cohenMacaulay_of_maximalCohenMacaulay [MaximalCohenMacaulay R M] :
    Module.CohenMacaulay R M :=
  ‹MaximalCohenMacaulay R M›.toCohenMacaulay

end Module

end
