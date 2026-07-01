import Mathlib
import stacks_project.Chap10.Lemma_10_150_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open LinearMap

variable {A : Type u} {B : Type u} {M : Type u} {N : Type u}
variable [CommRing A] [CommRing B] [Algebra A B]
variable (S : Submonoid B)
variable [AddCommGroup M] [AddCommGroup N]
variable [Module B M] [Module B N] [Module A M] [Module A N]
variable [IsScalarTower A B M] [IsScalarTower A B N]

/- Domain-style sampling for Lemma 10.133.12:
- primary domain: relative differential operators under localization of the ambient algebra;
- sampled owner declarations:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `LocalizedModule.equivTensorProduct`,
  `existsUnique_baseChange_extension_of_isDifferentialOperatorOfOrder_of_formallyEtale`;
- best owner abstraction: the canonical base-change extension theorem for formally étale maps,
  specialized here to the localization map `B → Localization S`;
- primitive data: an `A`-linear map `D : M →ₗ[A] N` together with the owner predicate
  `D.IsDifferentialOperatorOfOrder B k`;
- derived API: the localization-specific extension/uniqueness statement, obtained by transporting
  the formally étale base-change owner along `LocalizedModule.equivTensorProduct`.

Source/core/bridge triage:
- `source-facing`: the localization statement in the wording of Lemma 10.133.12;
- `core/canonical`: the later chapter owner
  `existsUnique_baseChange_extension_of_isDifferentialOperatorOfOrder_of_formallyEtale`;
- `bridge/view`: the identification of localized modules with tensor-product base change via
  `LocalizedModule.equivTensorProduct`. -/

-- Proof sketch: specialize the canonical formally étale base-change extension theorem to the
-- localization map `B → Localization S`, then transport the resulting tensor-product operator
-- across `LocalizedModule.equivTensorProduct`. The extension identity is checked on generators
-- `m ↦ m/1`, and the order condition is preserved because the transport maps are
-- `Localization S`-linear, hence order `0`.
/-- Lemma 10.133.12: an `A`-linear differential operator `D : M → N` of order `k` extends
uniquely to an `A`-linear differential operator `S⁻¹M → S⁻¹N` of the same order. -/
lemma existsUnique_localizedModule_extension_of_isDifferentialOperatorOfOrder
    {D : M →ₗ[A] N} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder B k) :
    ∃! E : LocalizedModule S M →ₗ[A] LocalizedModule S N,
      E.comp ((LocalizedModule.mkLinearMap S M).restrictScalars A) =
          ((LocalizedModule.mkLinearMap S N).restrictScalars A).comp D ∧
        E.IsDifferentialOperatorOfOrder (Localization S) k := by
  sorry

end
