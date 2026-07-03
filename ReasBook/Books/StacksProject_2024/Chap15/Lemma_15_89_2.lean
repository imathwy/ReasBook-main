import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.QuasiIso
import StacksProject_2024.Chap15.Definition_15_89_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ChainComplex
open scoped DirectSum

universe u

/-
Domain-style sampling for ideal-power torsion resolutions:
- primary domain: chain-complex resolutions of modules whose terms are direct sums of ideal-power
  quotients;
- same-domain declarations inspected:
  `QuasiIso`,
  `Module.IsIdealPowerTorsion`,
  `ChainComplex.IsFreeResolution`,
  `ChainComplex.IsFiniteFreeResolution`;
- best owner abstraction: the augmented chain complex data
  `π : F ⟶ moduleSingle[R] M` together with the canonical owner
  `QuasiIso π`; the source-specific extra datum is only the termwise direct-sum-of-quotients
  predicate on `F`;
- primitive data: the augmented chain complex and the degreewise direct-sum-of-quotients property;
- derived API: exactness and surjectivity of the resolution are carried by the canonical
  chain-complex owner `QuasiIso π`, while closure of `Module.IsIdealPowerTorsion` under linear
  equivalence and direct sums belongs to the module owner API rather than to a parallel
  chain-complex-specific wrapper.

Layer triage:
- `source-facing`: the existence of an infinite resolution by direct sums of quotients `R ⧸ I^n`;
- `core/canonical`: the augmented chain-complex owner with `QuasiIso π`;
- `bridge/view`: the termwise predicate recording that each degree is a direct sum of ideal-power
  quotients.

The previous local wrapper duplicated the chain-complex owner `QuasiIso π`. This file should
express the same mathematics directly over the canonical augmentation together with the
source-specific termwise quotient condition, reusing the owner-level `Module.IsIdealPowerTorsion`
API from `Definition_15_89_1` rather than re-declaring it locally.
-/

namespace ChainComplex

/-- A chain complex of `R`-modules is termwise a direct sum of quotients `R ⧸ I^n`, with the
exponent allowed to vary from summand to summand and from degree to degree. The summand index may
live in the module universe of the complex. -/
def IsTermwiseDirectSumOfIdealPowerQuotients
    {R : Type u} [CommRing R] (I : Ideal R) (F : ChainComplex (ModuleCat R) ℕ) : Prop :=
  ∀ n : ℕ, ∃ (ι : Type u) (exponent : ι → ℕ),
    Nonempty (F.X n ≃ₗ[R] (⨁ j : ι, R ⧸ (I ^ exponent j)))

section

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {F : ChainComplex (ModuleCat R) ℕ}

namespace IsTermwiseDirectSumOfIdealPowerQuotients

/-- Every term of a chain complex that is a direct sum of quotients `R ⧸ I^n` is `I`-power
torsion. This is derived API from the direct-sum presentation, not additional primitive data. -/
theorem isIdealPowerTorsion
    (hF : F.IsTermwiseDirectSumOfIdealPowerQuotients I) (n : ℕ) :
    Module.IsIdealPowerTorsion I (F.X n) := by
  rcases hF n with ⟨ι, exponent, ⟨e⟩⟩
  have hsum : Module.IsIdealPowerTorsion I (⨁ j : ι, R ⧸ (I ^ exponent j)) :=
    Module.isIdealPowerTorsion_directSum I fun j ↦
      Module.isIdealPowerTorsion_quotient_pow I (exponent j)
  exact (Module.isIdealPowerTorsion_iff_of_linearEquiv I e).2 hsum

end IsTermwiseDirectSumOfIdealPowerQuotients

end

end ChainComplex

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : ModuleCat R)

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (single₀ (ModuleCat R)) M

-- Proof sketch: for each `m : M`, choose a power `I^(n_m)` annihilating `m` and obtain a
-- canonical surjection from the direct sum of the cyclic quotients `R ⧸ I^(n_m)` onto `M`. Its
-- kernel is again `I`-power torsion, so iterating the same construction yields an exact infinite
-- resolution by such direct sums.
/-- Lemma 15.89.2: an `I`-power torsion `R`-module admits an infinite resolution whose terms are
direct sums of quotients `R ⧸ I^n` with the exponent `n` allowed to vary from summand to summand. -/
theorem exists_infinite_ideal_power_quotient_resolution
    (hM : Module.IsIdealPowerTorsion I M) :
    ∃ (F : ChainComplex (ModuleCat R) ℕ)
      (π : F ⟶ moduleSingle[R] M),
        QuasiIso π ∧ F.IsTermwiseDirectSumOfIdealPowerQuotients I := sorry

end
