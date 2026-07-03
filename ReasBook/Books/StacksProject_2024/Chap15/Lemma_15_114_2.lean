import Mathlib
import StacksProject_2024.Chap15.Lemma_15_114_1_Krasner_s_lemma

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

universe u

section

variable {A Khat M : Type u}

variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field Khat] [Algebra (AdicCompletion (maximalIdeal A) A) Khat]
variable [IsFractionRing (AdicCompletion (maximalIdeal A) A) Khat]
variable [Algebra A Khat] [IsScalarTower A (AdicCompletion (maximalIdeal A) A) Khat]
variable [Algebra (FractionRing A) Khat] [IsScalarTower A (FractionRing A) Khat]
variable [Field M] [Algebra Khat M] [FiniteDimensional Khat M] [Algebra.IsSeparable Khat M]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/- Domain-style sampling:
- primary domain: finite separable extensions of fraction fields of discrete valuation rings and
  their descent along completion;
- sampled owner-level declarations:
  `Field.exists_primitive_element`,
  `Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt`,
  `IsKrasner.krasner`,
  `IsTamelyRamifiedWithRespectTo`;
- best owner abstraction: the base field owner is the canonical fraction field `FractionRing A`,
  and the completion comparison is the standard base-change object `Khat ⊗[FractionRing A] L`
  viewed through a `Khat`-algebra equivalence, with `FractionRing A → Khat` constrained by the
  canonical tower `A → ACompletion → Khat`;
- primitive data: the discrete valuation ring `A`, the chosen fraction field `Khat` of its
  maximal-ideal completion together with its compatible `A`- and `FractionRing A`-algebra
  structures, and the finite separable extension `M / Khat`;
- derived API: existence of a finite separable extension of `FractionRing A` whose base change to
  `Khat` recovers `M`.

Layer triage:
- `source-facing`: `exists_finite_separable_extension_with_completion_baseChange`;
- `core/canonical`: `FractionRing A`, `TensorProduct`, `AlgEquiv`, and the sampled mathlib
  primitive-element / approximation / Krasner owners;
- `bridge/view`: the `Khat`-algebra equivalence between the descended base change and `M`.
-/

local notation "K" => FractionRing A

-- Proof sketch: choose a primitive element `θ` for `M/Khat`, approximate its minimal polynomial
-- over the completed discrete valuation ring by a monic polynomial over `A`, apply Krasner's lemma
-- to get a nearby root in `M`, and identify the resulting simple `K`-extension `L` after tensoring
-- with `Khat`, using the completion tower to interpret the tensor product over `K`.
/-- Lemma 15.114.2: if `A` is a discrete valuation ring with fraction field `K`, `Khat` is the
fraction field of the maximal-ideal adic completion of `A` equipped with the compatible tower
`A → A^∧ → Khat` and induced map `K = FractionRing A → Khat`, and `M / Khat` is finite separable,
then there exists a finite separable extension `L / K` whose base change to `Khat` is isomorphic
to `M`. -/
theorem exists_finite_separable_extension_with_completion_baseChange :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L), Nonempty ((Khat ⊗[K] L) ≃ₐ[Khat] M) := sorry

end
