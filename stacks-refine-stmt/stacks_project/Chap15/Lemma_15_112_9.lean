import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing Algebra

universe u v w

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type v} [Field L] [Algebra A L]
variable {M : Type w} [Field M] [Algebra A M] [Algebra L M] [IsScalarTower A L M]

local notation "B" => integralClosure A L
local notation "C" => integralClosure A M

/- Domain-style sampling for unramifiedness in an integral-closure tower:
- primary domain: commutative algebra of unramified local extensions detected on integral closures
  over a discrete valuation ring;
- core/canonical owner: `Algebra.IsUnramifiedAt`;
- bridge APIs used here: `AlgHom.mapIntegralClosure`, `Ideal.under`, `Ideal.LiesOver.trans`, and
  `Algebra.IsUnramifiedAt.comp`;
- source/core/bridge triage: this item is a `bridge/view` lemma specialized to the tower
  `A ⊆ B ⊆ C`, while the actual owner predicate remains `Algebra.IsUnramifiedAt`.

Primitive data are only the pointwise unramified hypotheses on `B/A` and `C/B`. The induced
`B`-algebra structure on `C` is derived canonically from the tower map `L → M` via
`AlgHom.mapIntegralClosure`; no separate public tower-map wrapper is needed. -/

noncomputable local instance : Algebra B C :=
  ((IsScalarTower.toAlgHom A L M).mapIntegralClosure : B →ₐ[A] C).toAlgebra

local instance :
    IsScalarTower A B C := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  ext
  simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A L M]

-- Proof sketch: for `P : Ideal C`, let `p := P.under B`. Then `p` lies over `maximalIdeal A`,
-- and `P` lies over `p`. Apply the two hypotheses to get `Algebra.IsUnramifiedAt A p` and
-- `Algebra.IsUnramifiedAt B P`, then compose them with `Algebra.IsUnramifiedAt.comp`.
/-- Lemma 15.112.9: let `B = integralClosure A L` and `C = integralClosure A M`. If every maximal
ideal of `B` over `maximalIdeal A` is unramified over `A`, and every maximal ideal of `C` over
`maximalIdeal A` is unramified over the intermediate integral closure `B`, then every maximal
ideal of `C` over `maximalIdeal A` is unramified over `A`. -/
theorem isUnramifiedAt_of_integralClosure_tower
    (hL : ∀ (p : Ideal B) [p.IsMaximal] [p.LiesOver (maximalIdeal A)],
      Algebra.IsUnramifiedAt A p)
    (hM : ∀ (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
        Algebra.IsUnramifiedAt B P)
    (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    Algebra.IsUnramifiedAt A P := sorry

end
