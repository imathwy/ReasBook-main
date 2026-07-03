import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [Algebra.IsAlgebraic K L]

local notation "B" => integralClosure A L

/- Domain-style sampling for Definition 15.113.3:
- primary domain: ramification theory of finite Galois extensions, specifically the subgroup
  owners attached to an ideal of the integral closure;
- sampled owner declarations:
  `MulAction.stabilizer`,
  `Ideal.inertia`,
  `Ideal.inertia_le_stabilizer`,
  `IsIntegralClosure.MulSemiringAction`;
- best owner abstraction: the subgroup-valued owners `MulAction.stabilizer` and `Ideal.inertia`;
- primitive data: an ideal `m : Ideal B`, together with the induced `Gal(L/K)`-action on `B`;
- derived API: the maximal-ideal specialization used later in the chapter, plus the decomposition
  and inertia fields and the residue-field actions built from it.

Layer triage:
- `source-facing`: naming the decomposition group and inertia group attached to a maximal ideal;
- `core/canonical`: `MulAction.stabilizer Gal(L/K) m` and `m.inertia Gal(L/K)`;
- `bridge/view`: the specialization from an arbitrary ideal to the maximal-ideal situation in the
  textbook.

This file should therefore recall those subgroup owners directly, with no parallel local wrapper
API. -/

local instance integralClosureMulSemiringAction :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

variable (m : Ideal B)

/- Definition 15.113.3 (1): for an ideal `m` of `B = integralClosure A L`, the canonical
decomposition-group owner is the stabilizer of `m` in `Gal(L / K)`. For a maximal ideal, this is
the textbook decomposition group. -/
set_option linter.hashCommand false in
#check (MulAction.stabilizer Gal(L/K) m)

/- Definition 15.113.3 (2): for an ideal `m` of `B`, the canonical inertia-group owner is the
ideal-theoretic inertia subgroup of `Gal(L / K)` attached to `m`. For a maximal ideal, this is the
textbook inertia group. -/
set_option linter.hashCommand false in
#check (m.inertia Gal(L/K))

end
