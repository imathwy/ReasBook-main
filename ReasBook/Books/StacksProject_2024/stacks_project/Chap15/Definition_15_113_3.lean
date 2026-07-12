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

/-- Definition 15.113.3: the decomposition group attached to an ideal `m` of
`B = integralClosure A L` is the stabilizer of `m` in `Gal(L / K)`. For a maximal ideal, this
specializes to the textbook decomposition group. -/
abbrev decompositionGroup : Subgroup (Gal(L/K)) :=
  -- The source-facing decomposition group is the canonical stabilizer subgroup.
  MulAction.stabilizer Gal(L/K) m

/-- Helper for Definition 15.113.3: the inertia group attached to an ideal `m` of `B` is the
canonical ideal-theoretic inertia subgroup of `Gal(L / K)`. For a maximal ideal, this is the
textbook inertia group, equivalently the kernel of the residue-field action from the
decomposition group. -/
abbrev inertiaGroup : Subgroup (Gal(L/K)) :=
  -- The source-facing inertia group is the canonical ideal-theoretic owner.
  m.inertia Gal(L/K)

end
