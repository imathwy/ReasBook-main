import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap15.Definition_15_112_7
import StacksProject_2024.Chap15.Lemma_15_115_2

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing Algebra Polynomial
open scoped UniformizerRoot

universe u v

noncomputable section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L]
variable [Algebra.IsSeparable (FractionRing A) L]

/-- Predicate asserting that after adjoining an `e`th root of the chosen uniformizer `π`, the
field `L` embeds over `FractionRing A` into a field that is unramified with respect to the
discrete valuation ring `A[π^(1/e)] = uniformizerRootExtensionRing π e`. The fraction field of
`A[π^(1/e)]` plays the role of `K[π^(1/e)]`. -/
def HasUnramifiedLiftOverUniformizerRootExtensionIndex (L : Type v) [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] [Algebra.IsSeparable (FractionRing A) L]
    (π : A) (e : ℕ) : Prop :=
  1 ≤ e ∧ PrimeToResidueCharacteristic A e ∧
    ∃ (_ : IsDomain (A[π^(1/e)]))
      (_ : IsDiscreteValuationRing (A[π^(1/e)])),
      ∃ (L' : Type (max u v)) (_ : Field L')
        (_ : Algebra (A[π^(1/e)]) L')
        (_ : Algebra (FractionRing (A[π^(1/e)])) L')
        (_ : IsScalarTower (A[π^(1/e)]) (FractionRing (A[π^(1/e)])) L')
        (_ : FiniteDimensional (FractionRing (A[π^(1/e)])) L')
        (_ : Algebra.IsSeparable (FractionRing (A[π^(1/e)])) L')
        (_ : Algebra (FractionRing A) (FractionRing (A[π^(1/e)])))
        (_ : Algebra (FractionRing A) L')
        (_ : IsScalarTower (FractionRing A) (FractionRing (A[π^(1/e)])) L')
        (_ : Algebra L L')
        (_ : IsScalarTower (FractionRing A) L L'),
        IsUnramifiedWithRespectTo (A[π^(1/e)]) L'

/-- Predicate asserting that there is a prime-to-residue-characteristic integer `e₀` such that for
every prime-to-residue-characteristic `d ≥ 1`, the index `d * e₀` satisfies the radical-extension
criterion above. -/
def HasEventuallyUnramifiedLiftOverUniformizerRootExtensions (L : Type v) [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] [Algebra.IsSeparable (FractionRing A) L]
    (π : A) : Prop :=
  ∃ e₀ : ℕ, 1 ≤ e₀ ∧ PrimeToResidueCharacteristic A e₀ ∧
    ∀ d : ℕ, 1 ≤ d → PrimeToResidueCharacteristic A d →
      HasUnramifiedLiftOverUniformizerRootExtensionIndex L π (d * e₀)

-- Proof sketch: `(2) → (1)` combines Lemma `15.115.2` with Lemmas `15.115.5` and `15.115.6`:
-- `A[π^(1/e)] / A` is tamely ramified when `e` is prime to the residue characteristic, an
-- unramified extension above it stays tame, and tameness descends to the intermediate field `L`.
-- `(3) → (2)` is immediate by taking `d = 1`. For `(1) → (3)`, let `e₀` be the least common
-- multiple of the ramification indices of the branches of the integral closure of `A` in `L`; for
-- each prime-to-residue-characteristic `d`, set `e = d * e₀`, form `A[π^(1/e)]`, decompose
-- `L ⊗_K K[π^(1/e)]` into fields, and apply Abhyankar's lemma together with Lemma `15.112.5` to
-- show that each local factor over `A[π^(1/e)]` is unramified.
/-- Lemma 15.115.7: for a discrete valuation ring `A` with fraction field `FractionRing A`, a
chosen uniformizer `π`, and a finite separable extension `L / FractionRing A`, the following are
equivalent: `L` is tamely ramified with respect to `A`; there exists an integer `e ≥ 1` invertible
in the residue field of `A` such that after adjoining an `e`th root of `π`, the field `L` embeds
into an extension unramified with respect to `A[π^(1/e)]`; and there exists an integer `e₀ ≥ 1`
invertible in the residue field of `A` such that the same conclusion holds for every multiple
`d * e₀` with `d ≥ 1` invertible in the residue field of `A`. -/
theorem isTamelyRamifiedWithRespectTo_tfae_uniformizerRootExtensionCriterion
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) :
    List.TFAE
      [ IsTamelyRamifiedWithRespectTo A L
      , ∃ e : ℕ, HasUnramifiedLiftOverUniformizerRootExtensionIndex L π e
      , HasEventuallyUnramifiedLiftOverUniformizerRootExtensions L π
      ] := sorry

end
