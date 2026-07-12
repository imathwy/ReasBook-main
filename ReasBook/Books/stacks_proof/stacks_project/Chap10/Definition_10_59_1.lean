import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Pointwise

section

variable {R : Type u} [CommRing R]

namespace Ideal

section

variable (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

-- Domain-style sampling for the Hilbert-Samuel owners in this file:
-- * primary domain: Hilbert-Samuel functions attached to an ideal and a module in local
--   commutative algebra;
-- * relevant owner APIs in the surrounding ecosystem: `Module.length`,
--   `Ideal.isPrimary_of_isMaximal_radical`, `IsLocalRing.eq_maximalIdeal`,
--   and Proposition `10.59.5`'s numerical-polynomial bridge for rational-valued eventual
--   polynomial statements;
-- * source-facing primitive data: the length-valued functions
--   `hilbertSamuelChi` and `hilbertSamuelPhi`;
-- * derived bridge data: later files pass from these `ℕ∞`-valued owners to `ℚ` by applying
--   `ENat.toNat` under the extra finiteness hypotheses needed there.

/-- The Hilbert-Samuel `χ`-function attached to an ideal `I` and an `R`-module `M`, given by
the lengths of the quotients `M / I^(n + 1) M`. -/
noncomputable def hilbertSamuelChi (n : ℕ) : ℕ∞ :=
  Module.length R (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M))

/-- The Hilbert-Samuel `φ`-function of `M` with respect to the ideal `I`. -/
noncomputable def hilbertSamuelPhi (n : ℕ) : ℕ∞ :=
  Module.length R
    ((I ^ n • ⊤ : Submodule R M) ⧸ (I • ⊤ : Submodule R (I ^ n • ⊤ : Submodule R M)))

end

end Ideal

/-- Source-facing notation for the Hilbert-Samuel `χ`-function. -/
scoped[Ideal] prefix:max "χ_" => Ideal.hilbertSamuelChi

/-- Source-facing notation for the Hilbert-Samuel `φ`-function. -/
scoped[Ideal] prefix:max "φ_" => Ideal.hilbertSamuelPhi

end

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

namespace Ideal

variable (I : Ideal R)

-- Source/core/bridge triage:
-- * source-facing: `Ideal.IsIdealOfDefinition` records the Stacks definition `√I = 𝔪`;
-- * core/canonical: the owner abstraction for the ideal-theoretic consequences is the mathlib
--   predicate `(I.radical).IsMaximal`, which feeds directly into `Ideal.isPrimary_of_isMaximal_radical`;
-- * bridge/view: `isIdealOfDefinition_iff_isMaximal_radical`,
--   `IsIdealOfDefinition.isMaximal_radical`, and `IsIdealOfDefinition.isPrimary` connect the
--   source predicate to that owner API.
/-- Definition 10.59.1: an ideal of a local ring is an ideal of definition if its
radical is the maximal ideal. -/
@[stacks 07DU]
def IsIdealOfDefinition : Prop :=
  I.radical = maximalIdeal R

/-- In a local ring, the source-facing condition `√I = 𝔪` is exactly the canonical owner
statement that `√I` is maximal. -/
theorem isIdealOfDefinition_iff_isMaximal_radical {I : Ideal R} :
    I.IsIdealOfDefinition ↔ I.radical.IsMaximal := by
  rw [IsIdealOfDefinition, IsLocalRing.isMaximal_iff]

/-- An ideal of definition has maximal radical. -/
theorem IsIdealOfDefinition.isMaximal_radical {I : Ideal R} (hI : I.IsIdealOfDefinition) :
    I.radical.IsMaximal :=
  isIdealOfDefinition_iff_isMaximal_radical.1 hI

/-- An ideal of definition is primary, viewed through mathlib's canonical primary-ideal API. -/
theorem IsIdealOfDefinition.isPrimary {I : Ideal R} (hI : I.IsIdealOfDefinition) : I.IsPrimary := by
  exact isPrimary_of_isMaximal_radical hI.isMaximal_radical

/-- The maximal ideal of a local ring is an ideal of definition. -/
@[simp] theorem maximalIdeal_isIdealOfDefinition :
    (maximalIdeal R).IsIdealOfDefinition := by
  simpa [IsIdealOfDefinition] using (maximalIdeal.isMaximal R).isPrime.radical

end Ideal

end
