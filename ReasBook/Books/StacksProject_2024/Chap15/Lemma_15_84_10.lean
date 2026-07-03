import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import StacksProject_2024.Chap15.Definition_15_84_1
import StacksProject_2024.Chap15.Lemma_15_60_1

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Flat R A] [Algebra.FinitePresentation R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.84.10:
- primary domain: relative perfectness in derived categories and residue-field fibers over primes
  of the base ring;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `derivedTensorWithAlgebra`,
  the scoped notation `K ⊗[R]^L[S]`,
  `DerivedCategory.IsGE`;
- best owner abstraction: this lemma is `source-facing` on the chapter owner
  `DerivedCategory.IsPerfectOver R`, while the fiber test should use the existing derived
  scalar-extension owner `derivedTensorWithAlgebra (algebraMap R p.asIdeal.ResidueField)` applied
  to the restricted object over `R`, rather than a local duplicate fiber functor;
- primitive vs. derived:
  primitive data are the pseudo-coherent object `K : D(A)`, its bounded-below condition in
  `D(A)`, and the bounded-below conditions on its residue-field fibers after restricting scalars
  to `R`;
  the derived-fiber construction itself is already owned upstream by `derivedTensorWithAlgebra`,
  so this file should not keep a parallel local abbreviation for it;
- source/core/bridge triage:
  `source-facing`: the iff criterion below;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `derivedTensorWithAlgebra`, and `K.IsGE`;
  `bridge/view`: the canonical restriction-of-scalars functor
    `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory`.
-/

-- Proof sketch: for `→`, relative perfection already gives finite tor dimension over `R`, hence
-- `K` is bounded below and every derived residue-field fiber is bounded below. For `←`, use the
-- flat finite-presentation reduction to a polynomial algebra, apply the local residue-field
-- criterion to get perfectness after localizing at primes of `A`, deduce global perfectness from
-- the bounded-below hypothesis, and then conclude relative perfectness over `R`.
/-- Lemma 15.84.10: let `R → A` be flat and of finite presentation, and let `K ∈ D(A)` be
pseudo-coherent. Then `K` is `R`-perfect if and only if `K` is bounded below and, for every prime
ideal `𝔭 ⊂ R`, the derived fiber `K ⊗_R^{\mathbf L} κ(𝔭)` is bounded below. -/
theorem isPerfectOver_iff_boundedBelow_and_primeResidueFields_boundedBelow
    (K : DModA) (hK : K.IsPseudoCoherent) :
    DerivedCategory.IsPerfectOver R K ↔
      (∃ n : ℤ, K.IsGE n) ∧
        ∀ p : PrimeSpectrum R,
          ∃ n : ℤ,
            (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) ⊗[R]^L[
              p.asIdeal.ResidueField]).IsGE n :=
  sorry

end

end CategoryTheory
