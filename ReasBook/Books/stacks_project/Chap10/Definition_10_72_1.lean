import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Regular.RegularSequence

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory.Sequence
open scoped ENat

namespace Ideal

variable {R : Type u} [CommRing R]

/-
Source/core/bridge triage:
* source-facing: `Ideal.depth I M`, the Stacks depth of a finite module with respect to an ideal;
* core/canonical: `Sequence.IsRegular M rs`, the owner notion for regular sequences from mathlib;
* bridge/view: `moduleDepth R M`, the local-ring specialization to the maximal ideal.

Primitive data are only the ideal `I`, the module `M`, and the owner predicate `IsRegular M rs`.
The set of admissible lengths and the local specialization are derived from that owner API.
-/
/-- The set of lengths of `M`-regular sequences whose terms all lie in the ideal `I`. -/
def regularSequenceLengths (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    Set ℕ∞ :=
  {d | ∃ rs : List R, IsRegular M rs ∧ Ideal.ofList rs ≤ I ∧ d = rs.length}

/-- Definition 10.72.1: for a finite `R`-module `M`, the `I`-depth of `M` is `∞` when `IM = M`,
and otherwise it is the supremum of the lengths of `M`-regular sequences contained in `I`. -/
noncomputable def depth (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ℕ∞ :=
  if I • (⊤ : Submodule R M) = ⊤ then
    ⊤
  else
    sSup (regularSequenceLengths I M)

/-- If `IM = M`, then the `I`-depth of `M` is infinite. -/
@[simp] theorem depth_eq_top_of_smul_top (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) = ⊤) :
    depth I M = ⊤ := by
  simp [depth, hIM]

/-- If `IM ≠ M`, then the `I`-depth of `M` is the supremum of the lengths of `M`-regular
sequences contained in `I`. -/
theorem depth_eq_sSup_lengths_of_smul_top_ne_top (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) :
    depth I M = sSup (regularSequenceLengths I M) := by
  simp [depth, hIM]

end Ideal

section

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Definition 10.72.1 in the local case: in a local ring, the depth of `M` is the depth with
respect to the maximal ideal. This is the high-reuse bridge/view notation for later local
statements, not a second owner definition. -/
noncomputable abbrev moduleDepth (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ℕ∞ :=
  Ideal.depth (maximalIdeal R) M

end
