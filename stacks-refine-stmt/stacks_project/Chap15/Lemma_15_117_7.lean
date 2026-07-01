import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap15.Remark_15_115_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open PrimeSpectrum

universe u v w x y

noncomputable section

/-
Domain-style sampling for Lemma 15.117.7:
- primary domain: reduced tensor-product base change for extensions of discrete valuation rings,
  together with the canonical comparison map from the base-changed integral closure `A'` to `B'`;
- sampled owner declarations:
  `reducedTensorBaseChangeIntegralClosureMap`,
  `reducedTensorBaseChangeIntegralClosure_isDedekindRing`,
  `primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure`,
  `Algebra.finite_of_essFiniteType_of_isAlgebraic`;
- best owner abstraction: the `core/canonical` owner is the comparison map
  `reducedTensorBaseChangeIntegralClosureMap` from Remark `15.115.1`; the three numbered clauses
  here are `source-facing` consequences of that owner;
- primitive data: the DVR extension `A ⊆ B`, the fraction fields `K ⊆ L`, the algebraic base
  change field `K' / K`, and the source hypothesis that the integral closure `A'` is Noetherian;
- derived API: Noetherian consequences for `B'`, the induced surjection on spectra, and the
  residue-field finite-type statement via the canonical residue-field algebra.

Source/core/bridge triage:
- `source-facing`: the Noetherian conclusion in clause `(1)` and the residue-field finiteness
  statement in clause `(3)`, both under the ambient source hypothesis `[IsNoetherianRing A']`;
- `core/canonical`: the map `reducedTensorBaseChangeIntegralClosureMap`, the owner theorem
  `reducedTensorBaseChangeIntegralClosure_isDedekindRing`, and its spectrum-surjectivity companion
  `primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure`;
- `bridge/view`: clause `(2)` is exact-interface reuse of that upstream spectrum-surjectivity
  theorem, reused inside the source-faithful Noetherian context rather than through a duplicate
  local shell; clause `(3)` should be derived from the canonical residue-field finiteness owner,
  with the induced
  `κ(comap q)`-algebra structure on `κ(q)` kept as proof-local scaffolding rather than as the main
  public datum.
-/

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K' : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B] [Algebra.EssFiniteType A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra B L] [Algebra A L] [Algebra K L]
variable [IsFractionRing B L] [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K'] [Algebra A K'] [Algebra K K'] [IsScalarTower A K K']
variable [Algebra.IsAlgebraic K K']

local notation "A'" => integralClosure A K'
local notation "L'" => (L ⊗[K] K') ⧸ nilradical (L ⊗[K] K')
local notation "B'" => integralClosure B L'

local instance l'CommRing : CommRing L' :=
  Ideal.Quotient.commRing _

-- Proof sketch: write `B` as a localization of a finite type `A`-algebra, choose a finite
-- subextension `K₀ / K` inside `K' / K` containing the coefficients of a finite presentation
-- after base change, and descend the reduced tensor-product normalization to that finite stage.
-- The corresponding normalization over `K₀` is Noetherian by the finite base-change case of
-- Remark `15.115.1`; base change back to `K'` then recovers `B'`.
section BaseChange

section

/-- Lemma 15.117.7 (1): if `A → B` is an essentially finite type extension of discrete valuation
rings, `K'/K` is algebraic, and the integral closure `A'` of `A` in `K'` is Noetherian, then the
integral closure `B'` of `B` in `L' = (L ⊗[K] K')_red` is Noetherian. -/
theorem isNoetherianRing_integralClosure_of_reducedTensorProduct_baseChange
    (hA' : IsNoetherianRing (integralClosure A K'))
    : IsNoetherianRing B' := by
  sorry

-- Proof sketch: clause `(2)` is already the upstream owner theorem for the canonical map
-- `reducedTensorBaseChangeIntegralClosureMap : A' → B'` from Remark `15.115.1`, so the present
-- file should keep it as a direct recall rather than rebuilding a parallel local statement.
/- Lemma 15.117.7 (2): under the same Noetherian hypothesis on `A'`, the induced map
`Spec(B') → Spec(A')` is the upstream owner theorem
`primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure`. -/
recall primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure

/- Proof sketch: the canonical map `A' → B'` from Remark `15.115.1` is integral, so for every
prime `q` of `B'` the induced residue-field extension `κ(q ∩ A') → κ(q)` is algebraic. Since the
same residue-field map is also essentially of finite type by the canonical prime-residue-field
owner, the field-level theorem `Algebra.finite_of_essFiniteType_of_isAlgebraic` makes it module
finite, hence finite type. -/
/-- Lemma 15.117.7 (3): under the same hypotheses, including that `A'` is Noetherian, for every
prime `q` of `B'`, the corresponding residue field extension `κ(q) / κ(q ∩ A')` is finitely
generated. -/
theorem residueField_finiteType_of_reducedTensorProduct_baseChange
    (hA' : IsNoetherianRing (integralClosure A K'))
    (q : PrimeSpectrum B') :
    Algebra.FiniteType (q.asIdeal.under A').ResidueField q.asIdeal.ResidueField := by
  sorry

end

end BaseChange

end
